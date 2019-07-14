// Testing candidates
//
// After candidates have been simplified, the only match pairs that
// remain are those that require some sort of test. The functions here
// identify what tests are needed, perform the tests, and then filter
// the candidates based on the result.

use crate::build::Builder;
use crate::build::matches::{Candidate, MatchPair, Test, TestKind, TargetBlockBuilder};
use crate::hair::*;
use crate::hair::pattern::compare_const_vals;
use rustc_data_structures::bit_set::BitSet;
use rustc_data_structures::fx::FxHashMap;
use rustc::ty::{self, Ty, adjustment::{PointerCast}};
use rustc::ty::util::IntTypeExt;
use rustc::ty::layout::VariantIdx;
use rustc::mir::*;
use rustc::hir::RangeEnd;
use syntax_pos::symbol::sym;

use std::cmp::Ordering;

#[derive(Debug)]
struct TestTargetBlockBuilder<'tcx, 'a> {
    test: &'a Test<'tcx>,
    source_info: SourceInfo,
    success: BasicBlock,
    fail: BasicBlock,
}

impl<'tcx, 'a> TargetBlockBuilder<'tcx> for TestTargetBlockBuilder<'tcx, 'a> {
    fn target_blocks(self, this: &mut Builder<'_, 'tcx>) -> Vec<BasicBlock> {
        let num_targets = self.test.targets();
        let mut blocks: Vec<BasicBlock> = Vec::with_capacity(num_targets);

        // Create the otherwise block
        let otherwise_block = this.cfg.start_new_block();
        this.cfg.terminate(otherwise_block, self.source_info, TerminatorKind::Goto {
            target: self.fail
        });

        match self.test.kind {
            // For a varant switch on an enum, targets for all missing discriminants
            // in the test's variants should be the otherwise block.
            TestKind::Switch { ref variants, ref adt_def } => {
                for (idx, _) in adt_def.discriminants(this.hir.tcx()) {
                    if variants.contains(idx) {
                        let block = this.cfg.start_new_block();
                            this.cfg.terminate(block, self.source_info, TerminatorKind::Goto {
                            target: self.success
                        });
                        blocks.push(block);
                    } else {
                        blocks.push(otherwise_block);
                    }
                }
            }
            // For most test kinds all but the last block are success blocks
            _ => {
                // Each success block for the subtest should jump to the success block.
                for _ in 0..(num_targets - 1) {
                    let block = this.cfg.start_new_block();
                    this.cfg.terminate(block, self.source_info, TerminatorKind::Goto {
                        target: self.success
                    });
                    blocks.push(block);
                }
            }
        }

        // The last block for the subtest should jump to the failure block.
        blocks.push(otherwise_block);

        blocks
    }
}

impl<'a, 'tcx> Builder<'a, 'tcx> {
    /// Lower a `Vec` of `MatchPair`s
    fn lower_pairs<'pat>(
        &mut self,
        match_pairs: Vec<MatchPair<'pat, 'tcx>>
    ) -> Vec<(Option<Test<'tcx>>, MatchPair<'pat, 'tcx>)> {
        let mut tests: Vec<(Option<Test<'tcx>>, MatchPair<'pat, 'tcx>)> = Vec::new();
        for pair in match_pairs {
            let mut test_kind = match self.lower_pair(&pair) {
                Some(kind) => kind,
                None => {
                    tests.push((None, pair));
                    continue;
                }
            };

            // If the current `TestKind` is a switch, we should
            // only have one that exists in the tests vector
            // that is populated with all of the variants. Look
            // for a pre-existing test.
            match test_kind {
                TestKind::SwitchInt {
                    switch_ty: ref mut new_switch_ty,
                    options: ref mut new_options,
                    indices: ref mut new_indices,
                    ..
                } => {
                    let mut found = false;
                    for (test_opt, test_pair) in tests.iter_mut() {
                        let test = match test_opt {
                            Some(test) if test_pair.place == pair.place => test,
                            _ => continue,
                        };
                        match test.kind {
                            TestKind::SwitchInt {
                                switch_ty: ref mut found_switch_ty,
                                options: ref mut found_options,
                                indices: ref mut found_indices,
                                ..
                            } => {
                                self.add_cases_to_switch_from_pat(
                                    pair.pattern,
                                    found_switch_ty,
                                    found_options,
                                    found_indices
                                );
                                found = true;
                                break;
                            }
                            _ => (),
                        }
                    }
                    // If a pre-existing test was not found, add a new
                    // test.
                    if !found {
                        self.add_cases_to_switch_from_pat(
                            pair.pattern,
                            new_switch_ty,
                            new_options,
                            new_indices
                        );
                        tests.push((
                            Some(Test { span: pair.pattern.span, kind: test_kind }),
                            pair
                        ));
                    }
                }
                TestKind::Switch { variants: ref mut new_variants, .. } => {
                    match *pair.pattern.kind {
                        PatternKind::Variant { ref subpatterns, .. } => {
                            let mut found = false;
                            if subpatterns.is_empty() {
                                for (test_opt, test_pair) in tests.iter_mut() {
                                    let test = match test_opt {
                                        Some(test) if test_pair.place == pair.place => test,
                                        _ => continue,
                                    };
                                    match test.kind {
                                        TestKind::Switch {
                                            variants: ref mut found_variants,
                                            ..
                                        } => match *test_pair.pattern.kind {
                                            PatternKind::Variant { ref subpatterns, .. }
                                                    if subpatterns.is_empty() => {
                                                self.add_variants_to_switch_from_pat(
                                                    pair.pattern,
                                                    found_variants
                                                );
                                                found = true;
                                                break;
                                            }
                                            _ => { continue; }
                                        }
                                        _ => (),
                                    }
                                }
                            }
                            // If a pre-existing test was not found, add a new
                            // test.
                            if !found {
                                self.add_variants_to_switch_from_pat(
                                    pair.pattern,
                                    new_variants
                                );
                                tests.push((
                                    Some(Test { span: pair.pattern.span, kind: test_kind }),
                                    pair
                                ));
                            }
                        }
                        _ => bug!("Created Switch from a {:?}", pair.pattern),
                    }
                }
                _ => {
                    tests.push((
                        Some(Test { span: pair.pattern.span, kind: test_kind }),
                        pair
                    ));
                }
            }
        }
        tests
    }

    /// Lower a patterns `PatternKind` into a `TestKind`.
    fn lower_pair<'pat>(&mut self, match_pair: &MatchPair<'pat, 'tcx>) -> Option<TestKind<'tcx>> {
        match *match_pair.pattern.kind {
            PatternKind::Variant { ref adt_def, substs: _, variant_index: _, subpatterns: _ } => {
                Some(TestKind::Switch {
                    adt_def: adt_def.clone(),
                    variants: BitSet::new_empty(adt_def.variants.len()),
                })
            }

            PatternKind::Constant { .. } if is_switch_ty(match_pair.pattern.ty) => {
                // For integers, we use a `SwitchInt` match, which allows
                // us to handle more cases.
                Some(TestKind::SwitchInt {
                    switch_ty: match_pair.pattern.ty,

                    // these maps are empty to start; cases are
                    // added below in add_cases_to_switch
                    options: vec![],
                    indices: Default::default(),
                })
            }

            PatternKind::Constant { value } => {
                Some(TestKind::Eq {
                    value,
                    ty: match_pair.pattern.ty.clone()
                })
            }

            PatternKind::Range(range) => {
                assert!(range.ty == match_pair.pattern.ty);
                Some(TestKind::Range(range))
            }

            PatternKind::Slice { ref prefix, ref slice, ref suffix } => {
                let len = prefix.len() + suffix.len();
                let op = if slice.is_some() {
                    BinOp::Ge
                } else {
                    BinOp::Eq
                };
                Some(TestKind::Len { len: len as u64, op: op })
            }

            PatternKind::Or { ref pats } => {
                let pairs = pats.iter().map(|pat| {
                    MatchPair::new(match_pair.place.clone(), pat)
                }).collect::<Vec<_>>();
                let lowered_pairs = self.lower_pairs(pairs).into_iter().map(|(test_opt, pair)| {
                    let test = test_opt.unwrap_or_else(|| self.error_simplifyable(&pair));
                    let subpat = match *pair.pattern.kind {
                        PatternKind::Variant {
                            ref subpatterns, ref adt_def, variant_index, ..
                        } => {
                            let elem = ProjectionElem::Downcast(
                                Some(adt_def.variants[variant_index].ident.name),
                                variant_index
                            );
                            let downcast_place = pair.place.clone().elem(elem);
                            //let mut next_tests = Vec::new();
                            let next_pairs = subpatterns.iter().map(|subpat| {
                                let new_place = downcast_place.clone();
                                let field_place = new_place.field(subpat.field,
                                                                  subpat.pattern.ty);
                                MatchPair::new(field_place, &subpat.pattern)
                            }).collect::<Vec<_>>();
                            Some(
                                self.lower_pairs(next_pairs)
                                    .into_iter()
                                    .filter_map(|(test, pair)| {
                                        test.map(|x| (pair.place, x))
                                    }).collect::<Vec<_>>()
                            )
                        },
                        _ => None
                    };
                    (test, subpat)
                }).collect::<Vec<_>>();
                Some(TestKind::Or { tests: lowered_pairs })
            }

            PatternKind::AscribeUserType { .. } |
            PatternKind::Array { .. } |
            PatternKind::Wild |
            PatternKind::Binding { .. } |
            PatternKind::Leaf { .. } |
            PatternKind::Deref { .. } => {
                None
            }
        }
    }

    /// Identifies what test is needed to decide if `match_pair` is applicable.
    ///
    /// It is a bug to call this with a simplifiable pattern.
    pub fn test<'pat>(&mut self, match_pair: &MatchPair<'pat, 'tcx>) -> Test<'tcx> {
        Test {
            span: match_pair.pattern.span,
            kind: self.lower_pair(match_pair).unwrap_or_else(|| {
                self.error_simplifyable(match_pair)
            })
        }
    }

    fn add_cases_to_switch_from_pat(&mut self,
                                    pat: &'pat Pattern<'tcx>,
                                    switch_ty: Ty<'tcx>,
                                    options: &mut Vec<u128>,
                                    indices: &mut FxHashMap<&'tcx ty::Const<'tcx>, usize>)
                                    -> bool
    {
        match *pat.kind {
            PatternKind::Constant { value } => {
                let switch_ty = ty::ParamEnv::empty().and(switch_ty);
                indices.entry(value)
                       .or_insert_with(|| {
                           options.push(value.unwrap_bits(self.hir.tcx(), switch_ty));
                           options.len() - 1
                       });
                true
            }
            PatternKind::Variant { .. } => {
                panic!("you should have called add_variants_to_switch instead!");
            }
            PatternKind::Range(range) => {
                // Check that none of the switch values are in the range.
                self.values_not_contained_in_range(range, indices)
                    .unwrap_or(false)
            }
            PatternKind::Slice { .. } |
            PatternKind::Array { .. } |
            PatternKind::Wild |
            PatternKind::Or { .. } |
            PatternKind::Binding { .. } |
            PatternKind::AscribeUserType { .. } |
            PatternKind::Leaf { .. } |
            PatternKind::Deref { .. } => {
                // don't know how to add these patterns to a switch
                false
            }
        }
    }

    pub fn add_cases_to_switch<'pat>(&mut self,
                                     test_place: &Place<'tcx>,
                                     candidate: &Candidate<'pat, 'tcx>,
                                     switch_ty: Ty<'tcx>,
                                     options: &mut Vec<u128>,
                                     indices: &mut FxHashMap<&'tcx ty::Const<'tcx>, usize>)
                                     -> bool
    {
        let match_pair = match candidate.match_pairs.iter().find(|mp| mp.place == *test_place) {
            Some(match_pair) => match_pair,
            _ => { return false; }
        };

        self.add_cases_to_switch_from_pat(match_pair.pattern, switch_ty,
                                          options, indices)
    }

    pub fn add_variants_to_switch_from_pat<'pat>(&mut self,
                                                 pat: &'pat Pattern<'tcx>,
                                                 variants: &mut BitSet<VariantIdx>)
                                                 -> bool
    {
        match *pat.kind {
            PatternKind::Variant { adt_def: _ , variant_index,  .. } => {
                // We have a pattern testing for variant `variant_index`
                // set the corresponding index to true
                variants.insert(variant_index);
                true
            }
            _ => {
                // don't know how to add these patterns to a switch
                false
            }
        }
    }

    pub fn add_variants_to_switch<'pat>(&mut self,
                                        test_place: &Place<'tcx>,
                                        candidate: &Candidate<'pat, 'tcx>,
                                        variants: &mut BitSet<VariantIdx>)
                                        -> bool
    {
        let match_pair = match candidate.match_pairs.iter().find(|mp| mp.place == *test_place) {
            Some(match_pair) => match_pair,
            _ => { return false; }
        };

        self.add_variants_to_switch_from_pat(match_pair.pattern, variants)
    }

    pub(super) fn perform_test<F: TargetBlockBuilder<'tcx>>(
        &mut self,
        block: BasicBlock,
        place: &Place<'tcx>,
        test: &Test<'tcx>,
        target_block_builder: F,
    ) {
        debug!("perform_test({:?}, {:?}: {:?}, {:?})",
               block,
               place,
               place.ty(&self.local_decls, self.hir.tcx()),
               test);

        let source_info = self.source_info(test.span);
        match test.kind {
            TestKind::Switch { adt_def, ref variants } => {
                let target_blocks = target_block_builder.target_blocks(self);
                // Variants is a BitVec of indexes into adt_def.variants.
                let num_enum_variants = adt_def.variants.len();
                let used_variants = variants.count();
                debug_assert_eq!(target_blocks.len(), num_enum_variants + 1);
                let otherwise_block = *target_blocks.last().unwrap();
                let mut targets = Vec::with_capacity(used_variants + 1);
                let mut values = Vec::with_capacity(used_variants);
                let tcx = self.hir.tcx();
                for (idx, discr) in adt_def.discriminants(tcx) {
                    if variants.contains(idx) {
                        debug_assert_ne!(
                            target_blocks[idx.index()],
                            otherwise_block,
                            "no canididates for tested discriminant: {:?}",
                            discr,
                        );
                        values.push(discr.val);
                        targets.push(target_blocks[idx.index()]);
                    } else {
                        debug_assert_eq!(
                            target_blocks[idx.index()],
                            otherwise_block,
                            "found canididates for untested discriminant: {:?}",
                            discr,
                        );
                    }
                }
                targets.push(otherwise_block);
                debug!("num_enum_variants: {}, tested variants: {:?}, variants: {:?}",
                       num_enum_variants, values, variants);
                let discr_ty = adt_def.repr.discr_type().to_ty(tcx);
                let discr = self.temp(discr_ty, test.span);
                self.cfg.push_assign(block, source_info, &discr,
                                     Rvalue::Discriminant(place.clone()));
                assert_eq!(values.len() + 1, targets.len());
                self.cfg.terminate(block, source_info, TerminatorKind::SwitchInt {
                    discr: Operand::Move(discr),
                    switch_ty: discr_ty,
                    values: From::from(values),
                    targets,
                });
            }

            TestKind::SwitchInt { switch_ty, ref options, indices: _ } => {
                let target_blocks = target_block_builder.target_blocks(self);
                let terminator = if switch_ty.sty == ty::Bool {
                    assert!(options.len() > 0 && options.len() <= 2);
                    if let [first_bb, second_bb] = *target_blocks {
                        let (true_bb, false_bb) = match options[0] {
                            1 => (first_bb, second_bb),
                            0 => (second_bb, first_bb),
                            v => span_bug!(test.span, "expected boolean value but got {:?}", v)
                        };
                        TerminatorKind::if_(
                            self.hir.tcx(),
                            Operand::Copy(place.clone()),
                            true_bb,
                            false_bb,
                        )
                    } else {
                        bug!("`TestKind::SwitchInt` on `bool` should have two targets")
                    }
                } else {
                    // The switch may be inexhaustive so we have a catch all block
                    debug_assert_eq!(options.len() + 1, target_blocks.len());
                    TerminatorKind::SwitchInt {
                        discr: Operand::Copy(place.clone()),
                        switch_ty,
                        values: options.clone().into(),
                        targets: target_blocks,
                    }
                };
                self.cfg.terminate(block, source_info, terminator);
            }

            TestKind::Eq { value, ty } => {
                if !ty.is_scalar() {
                    // Use `PartialEq::eq` instead of `BinOp::Eq`
                    // (the binop can only handle primitives)
                    self.non_scalar_compare(
                        block,
                        target_block_builder,
                        source_info,
                        value,
                        place,
                        ty,
                    );
                } else {
                    if let [success, fail] = *target_block_builder.target_blocks(self) {
                        let val = Operand::Copy(place.clone());
                        let expect = self.literal_operand(test.span, ty, value);
                        self.compare(block, success, fail, source_info, BinOp::Eq, expect, val);
                    } else {
                        bug!("`TestKind::Eq` should have two target blocks");
                    }
                }
            }

            TestKind::Range(PatternRange { ref lo, ref hi, ty, ref end }) => {
                let lower_bound_success = self.cfg.start_new_block();
                let target_blocks = target_block_builder.target_blocks(self);

                // Test `val` by computing `lo <= val && val <= hi`, using primitive comparisons.
                let lo = self.literal_operand(test.span, ty, lo);
                let hi = self.literal_operand(test.span, ty, hi);
                let val = Operand::Copy(place.clone());

                if let [success, fail] = *target_blocks {
                    self.compare(
                        block,
                        lower_bound_success,
                        fail,
                        source_info,
                        BinOp::Le,
                        lo,
                        val.clone(),
                    );
                    let op = match *end {
                        RangeEnd::Included => BinOp::Le,
                        RangeEnd::Excluded => BinOp::Lt,
                    };
                    self.compare(lower_bound_success, success, fail, source_info, op, val, hi);
                } else {
                    bug!("`TestKind::Range` should have two target blocks");
                }
            }

            TestKind::Len { len, op } => {
                let target_blocks = target_block_builder.target_blocks(self);

                let usize_ty = self.hir.usize_ty();
                let actual = self.temp(usize_ty, test.span);

                // actual = len(place)
                self.cfg.push_assign(block, source_info,
                                     &actual, Rvalue::Len(place.clone()));

                // expected = <N>
                let expected = self.push_usize(block, source_info, len);

                if let [true_bb, false_bb] = *target_blocks {
                    // result = actual == expected OR result = actual < expected
                    // branch based on result
                    self.compare(
                        block,
                        true_bb,
                        false_bb,
                        source_info,
                        op,
                        Operand::Move(actual),
                        Operand::Move(expected),
                    );
                } else {
                    bug!("`TestKind::Len` should have two target blocks");
                }
            }

            TestKind::Or { ref tests } => {
                // FIXME(dlrobertson): decrease the amount of debug logging below.
                debug!("==== BUILDING OR-PATTERN ====");
                // An or pattern can either pass or fail.
                let (success, fail) = {
                    if let [success, fail] = *target_block_builder.target_blocks(self) {
                        (success, fail)
                    } else {
                        bug!("or-pattern should generate only a success and failure block");
                    }
                };

                // Set up the current block and a otherwise block before
                // iterating over the subtests.
                let mut current_block = self.cfg.start_new_block();
                let mut otherwise = current_block;

                self.cfg.terminate(block, source_info, TerminatorKind::Goto {
                    target: current_block
                });

                debug!("or-pattern: success={:?} fail={:?} block={:?} current_block={:?}",
                       success, fail, block, current_block);

                for (subtest, subpat) in tests {
                    // Create an otherwise block that will be the current block
                    // for subsequent tests.
                    otherwise = self.cfg.start_new_block();

                    let next_block = match subpat {
                        Some(lowered_tests) if !lowered_tests.is_empty() => {
                            debug!("or-pattern: lowered_tests={:?}",
                                   lowered_tests);

                            let sub_start_block = self.cfg.start_new_block();
                            let mut sub_current_block = sub_start_block;

                            let mut sub_otherwise = sub_start_block;

                            debug!("or-pattern: sub_start_block={:?} sub_crrent_block={:?}",
                                   sub_start_block, sub_current_block);

                            for (place, subtest) in lowered_tests.iter() {
                                sub_otherwise = self.cfg.start_new_block();
                                debug!("subtest={:?} current={:?} otherwise={:?} fail={:?}",
                                       subtest, sub_current_block, sub_otherwise, fail);
                                // Create the target block builder.
                                let target_block_builder = TestTargetBlockBuilder {
                                    test: &subtest,
                                    source_info: source_info,
                                    success: sub_otherwise,
                                    fail: fail,
                                };

                                // Perform the subtest.
                                self.perform_test(sub_current_block,
                                                  &place.clone(),
                                                  &subtest,
                                                  target_block_builder);
                                // Set the current block to the otherwise block of the previous
                                // test.
                                sub_current_block = sub_otherwise;
                            }

                            self.cfg.terminate(sub_otherwise, source_info,
                                               TerminatorKind::Goto { target: success });

                            sub_start_block
                        }
                        _ => {
                            success
                        }
                    };
                    debug!("or-pattern: next_block={:?}", next_block);

                    // Create the target block builder.
                    let target_block_builder = TestTargetBlockBuilder {
                        test: &subtest,
                        source_info: source_info,
                        success: next_block,
                        fail: otherwise,
                    };
                    debug!("or-pattern: target_block_builder={:?}",
                           target_block_builder);

                    // Perform the subtest.
                    self.perform_test(current_block,
                                      &place.clone(),
                                      subtest,
                                      target_block_builder);

                    // Set the current block to the otherwise block of the previous
                    // test.
                    current_block = otherwise;
                }
                debug!("or-pattern: finishing with otherwise={:?} fail={:?}",
                       otherwise, fail);

                // The lastotherwise block should jump to the or-pattern's
                // failure block.
                self.cfg.terminate(otherwise, source_info, TerminatorKind::Goto {
                    target: fail
                });
                debug!("===== ENDING OR-PATTERN =====");
            }
        }
    }

    /// Compare using the provided built-in comparison operator
    fn compare(
        &mut self,
        block: BasicBlock,
        success_block: BasicBlock,
        fail_block: BasicBlock,
        source_info: SourceInfo,
        op: BinOp,
        left: Operand<'tcx>,
        right: Operand<'tcx>,
    ) {
        let bool_ty = self.hir.bool_ty();
        let result = self.temp(bool_ty, source_info.span);

        // result = op(left, right)
        self.cfg.push_assign(
            block,
            source_info,
            &result,
            Rvalue::BinaryOp(op, left, right),
        );

        // branch based on result
        self.cfg.terminate(
            block,
            source_info,
            TerminatorKind::if_(
                self.hir.tcx(),
                Operand::Move(result),
                success_block,
                fail_block,
            ),
        );
    }

    /// Compare two `&T` values using `<T as std::compare::PartialEq>::eq`
    fn non_scalar_compare<F: TargetBlockBuilder<'tcx>>(
        &mut self,
        block: BasicBlock,
        target_block_builder: F,
        source_info: SourceInfo,
        value: &'tcx ty::Const<'tcx>,
        place: &Place<'tcx>,
        mut ty: Ty<'tcx>,
    ) {
        use rustc::middle::lang_items::EqTraitLangItem;

        let mut expect = self.literal_operand(source_info.span, value.ty, value);
        let mut val = Operand::Copy(place.clone());

        // If we're using `b"..."` as a pattern, we need to insert an
        // unsizing coercion, as the byte string has the type `&[u8; N]`.
        //
        // We want to do this even when the scrutinee is a reference to an
        // array, so we can call `<[u8]>::eq` rather than having to find an
        // `<[u8; N]>::eq`.
        let unsize = |ty: Ty<'tcx>| match ty.sty {
            ty::Ref(region, rty, _) => match rty.sty {
                ty::Array(inner_ty, n) => Some((region, inner_ty, n)),
                _ => None,
            },
            _ => None,
        };
        let opt_ref_ty = unsize(ty);
        let opt_ref_test_ty = unsize(value.ty);
        match (opt_ref_ty, opt_ref_test_ty) {
            // nothing to do, neither is an array
            (None, None) => {},
            (Some((region, elem_ty, _)), _) |
            (None, Some((region, elem_ty, _))) => {
                let tcx = self.hir.tcx();
                // make both a slice
                ty = tcx.mk_imm_ref(region, tcx.mk_slice(elem_ty));
                if opt_ref_ty.is_some() {
                    let temp = self.temp(ty, source_info.span);
                    self.cfg.push_assign(
                        block, source_info, &temp, Rvalue::Cast(
                            CastKind::Pointer(PointerCast::Unsize), val, ty
                        )
                    );
                    val = Operand::Move(temp);
                }
                if opt_ref_test_ty.is_some() {
                    let slice = self.temp(ty, source_info.span);
                    self.cfg.push_assign(
                        block, source_info, &slice, Rvalue::Cast(
                            CastKind::Pointer(PointerCast::Unsize), expect, ty
                        )
                    );
                    expect = Operand::Move(slice);
                }
            },
        }

        let deref_ty = match ty.sty {
            ty::Ref(_, deref_ty, _) => deref_ty,
            _ => bug!("non_scalar_compare called on non-reference type: {}", ty),
        };

        let eq_def_id = self.hir.tcx().require_lang_item(EqTraitLangItem);
        let (mty, method) = self.hir.trait_method(eq_def_id, sym::eq, deref_ty, &[deref_ty.into()]);

        let bool_ty = self.hir.bool_ty();
        let eq_result = self.temp(bool_ty, source_info.span);
        let eq_block = self.cfg.start_new_block();
        let cleanup = self.diverge_cleanup();
        self.cfg.terminate(block, source_info, TerminatorKind::Call {
            func: Operand::Constant(box Constant {
                span: source_info.span,
                ty: mty,

                // FIXME(#54571): This constant comes from user input (a
                // constant in a pattern).  Are there forms where users can add
                // type annotations here?  For example, an associated constant?
                // Need to experiment.
                user_ty: None,

                literal: method,
            }),
            args: vec![val, expect],
            destination: Some((eq_result.clone(), eq_block)),
            cleanup: Some(cleanup),
            from_hir_call: false,
        });

        if let [success_block, fail_block] = *target_block_builder.target_blocks(self) {
            // check the result
            self.cfg.terminate(
                eq_block,
                source_info,
                TerminatorKind::if_(
                    self.hir.tcx(),
                    Operand::Move(eq_result),
                    success_block,
                    fail_block,
                ),
            );
        } else {
            bug!("`TestKind::Eq` should have two target blocks")
        }
    }

    /// Given that we are performing `test` against `test_place`, this job
    /// sorts out what the status of `candidate` will be after the test. See
    /// `test_candidates` for the usage of this function. The returned index is
    /// the index that this candiate should be placed in the
    /// `target_candidates` vec. The candidate may be modified to update its
    /// `match_pairs`.
    ///
    /// So, for example, if this candidate is `x @ Some(P0)` and the `Test` is
    /// a variant test, then we would modify the candidate to be `(x as
    /// Option).0 @ P0` and return the index corresponding to the variant
    /// `Some`.
    ///
    /// However, in some cases, the test may just not be relevant to candidate.
    /// For example, suppose we are testing whether `foo.x == 22`, but in one
    /// match arm we have `Foo { x: _, ... }`... in that case, the test for
    /// what value `x` has has no particular relevance to this candidate. In
    /// such cases, this function just returns None without doing anything.
    /// This is used by the overall `match_candidates` algorithm to structure
    /// the match as a whole. See `match_candidates` for more details.
    ///
    /// FIXME(#29623). In some cases, we have some tricky choices to make.  for
    /// example, if we are testing that `x == 22`, but the candidate is `x @
    /// 13..55`, what should we do? In the event that the test is true, we know
    /// that the candidate applies, but in the event of false, we don't know
    /// that it *doesn't* apply. For now, we return false, indicate that the
    /// test does not apply to this candidate, but it might be we can get
    /// tighter match code if we do something a bit different.
    pub fn sort_candidate<'pat>(
        &mut self,
        test_place: &Place<'tcx>,
        test: &Test<'tcx>,
        candidate: &mut Candidate<'pat, 'tcx>,
    ) -> Option<usize> {
        // Find the match_pair for this place (if any). At present,
        // afaik, there can be at most one. (In the future, if we
        // adopted a more general `@` operator, there might be more
        // than one, but it'd be very unusual to have two sides that
        // both require tests; you'd expect one side to be simplified
        // away.)
        let (match_pair_index, match_pair) = candidate.match_pairs
            .iter()
            .enumerate()
            .find(|&(_, mp)| mp.place == *test_place)?;

        match (&test.kind, &*match_pair.pattern.kind) {
            // If we are performing a variant switch, then this
            // informs variant patterns, but nothing else.
            (&TestKind::Switch { adt_def: tested_adt_def, .. },
             &PatternKind::Variant { adt_def, variant_index, ref subpatterns, .. }) => {
                assert_eq!(adt_def, tested_adt_def);
                self.candidate_after_variant_switch(match_pair_index,
                                                    adt_def,
                                                    variant_index,
                                                    subpatterns,
                                                    candidate);
                Some(variant_index.as_usize())
            }

            (&TestKind::Switch { .. }, _) => None,

            // If we are performing a switch over integers, then this informs integer
            // equality, but nothing else.
            //
            // FIXME(#29623) we could use PatternKind::Range to rule
            // things out here, in some cases.
            (&TestKind::SwitchInt { switch_ty: _, options: _, ref indices },
             &PatternKind::Constant { ref value })
            if is_switch_ty(match_pair.pattern.ty) => {
                let index = indices[value];
                self.candidate_without_match_pair(match_pair_index, candidate);
                Some(index)
            }

            (&TestKind::SwitchInt { switch_ty: _, ref options, ref indices },
             &PatternKind::Range(range)) => {
                let not_contained = self
                    .values_not_contained_in_range(range, indices)
                    .unwrap_or(false);

                if not_contained {
                    // No switch values are contained in the pattern range,
                    // so the pattern can be matched only if this test fails.
                    let otherwise = options.len();
                    Some(otherwise)
                } else {
                    None
                }
            }

            (&TestKind::SwitchInt { .. }, _) => None,

            (&TestKind::Len { len: test_len, op: BinOp::Eq },
             &PatternKind::Slice { ref prefix, ref slice, ref suffix }) => {
                let pat_len = (prefix.len() + suffix.len()) as u64;
                match (test_len.cmp(&pat_len), slice) {
                    (Ordering::Equal, &None) => {
                        // on true, min_len = len = $actual_length,
                        // on false, len != $actual_length
                        self.candidate_after_slice_test(match_pair_index,
                                                        candidate,
                                                        prefix,
                                                        slice.as_ref(),
                                                        suffix);
                        Some(0)
                    }
                    (Ordering::Less, _) => {
                        // test_len < pat_len. If $actual_len = test_len,
                        // then $actual_len < pat_len and we don't have
                        // enough elements.
                        Some(1)
                    }
                    (Ordering::Equal, &Some(_)) | (Ordering::Greater, &Some(_)) => {
                        // This can match both if $actual_len = test_len >= pat_len,
                        // and if $actual_len > test_len. We can't advance.
                        None
                    }
                    (Ordering::Greater, &None) => {
                        // test_len != pat_len, so if $actual_len = test_len, then
                        // $actual_len != pat_len.
                        Some(1)
                    }
                }
            }

            (&TestKind::Len { len: test_len, op: BinOp::Ge },
             &PatternKind::Slice { ref prefix, ref slice, ref suffix }) => {
                // the test is `$actual_len >= test_len`
                let pat_len = (prefix.len() + suffix.len()) as u64;
                match (test_len.cmp(&pat_len), slice) {
                    (Ordering::Equal, &Some(_))  => {
                        // $actual_len >= test_len = pat_len,
                        // so we can match.
                        self.candidate_after_slice_test(match_pair_index,
                                                        candidate,
                                                        prefix,
                                                        slice.as_ref(),
                                                        suffix);
                        Some(0)
                    }
                    (Ordering::Less, _) | (Ordering::Equal, &None) => {
                        // test_len <= pat_len. If $actual_len < test_len,
                        // then it is also < pat_len, so the test passing is
                        // necessary (but insufficient).
                        Some(0)
                    }
                    (Ordering::Greater, &None) => {
                        // test_len > pat_len. If $actual_len >= test_len > pat_len,
                        // then we know we won't have a match.
                        Some(1)
                    }
                    (Ordering::Greater, &Some(_)) => {
                        // test_len < pat_len, and is therefore less
                        // strict. This can still go both ways.
                        None
                    }
                }
            }

            (&TestKind::Range(test),
             &PatternKind::Range(pat)) => {
                if test == pat {
                    self.candidate_without_match_pair(
                        match_pair_index,
                        candidate,
                    );
                    return Some(0);
                }

                let no_overlap = (|| {
                    use std::cmp::Ordering::*;
                    use rustc::hir::RangeEnd::*;

                    let param_env = ty::ParamEnv::empty().and(test.ty);
                    let tcx = self.hir.tcx();

                    let lo = compare_const_vals(tcx, test.lo, pat.hi, param_env)?;
                    let hi = compare_const_vals(tcx, test.hi, pat.lo, param_env)?;

                    match (test.end, pat.end, lo, hi) {
                        // pat < test
                        (_, _, Greater, _) |
                        (_, Excluded, Equal, _) |
                        // pat > test
                        (_, _, _, Less) |
                        (Excluded, _, _, Equal) => Some(true),
                        _ => Some(false),
                    }
                })();

                if no_overlap == Some(true) {
                    // Testing range does not overlap with pattern range,
                    // so the pattern can be matched only if this test fails.
                    Some(1)
                } else {
                    None
                }
            }

            (&TestKind::Range(range), &PatternKind::Constant { value }) => {
                if self.const_range_contains(range, value) == Some(false) {
                    // `value` is not contained in the testing range,
                    // so `value` can be matched only if this test fails.
                    Some(1)
                } else {
                    None
                }
            }

            (&TestKind::Range { .. }, _) => None,

            (&TestKind::Eq { .. }, _) |
            (&TestKind::Len { .. }, _) |
            (&TestKind::Or { .. }, _) => {
                // These are all binary tests.
                //
                // FIXME(#29623) we can be more clever here
                let pattern_test = self.test(&match_pair);
                if pattern_test.kind == test.kind {
                    self.candidate_without_match_pair(match_pair_index, candidate);
                    Some(0)
                } else {
                    None
                }
            }
        }
    }

    fn candidate_without_match_pair(
        &mut self,
        match_pair_index: usize,
        candidate: &mut Candidate<'_, 'tcx>,
    ) {
        candidate.match_pairs.remove(match_pair_index);
    }

    fn candidate_after_slice_test<'pat>(&mut self,
                                        match_pair_index: usize,
                                        candidate: &mut Candidate<'pat, 'tcx>,
                                        prefix: &'pat [Pattern<'tcx>],
                                        opt_slice: Option<&'pat Pattern<'tcx>>,
                                        suffix: &'pat [Pattern<'tcx>]) {
        let removed_place = candidate.match_pairs.remove(match_pair_index).place;
        self.prefix_slice_suffix(
            &mut candidate.match_pairs,
            &removed_place,
            prefix,
            opt_slice,
            suffix);
    }

    fn candidate_after_variant_switch<'pat>(
        &mut self,
        match_pair_index: usize,
        adt_def: &'tcx ty::AdtDef,
        variant_index: VariantIdx,
        subpatterns: &'pat [FieldPattern<'tcx>],
        candidate: &mut Candidate<'pat, 'tcx>,
    ) {
        let match_pair = candidate.match_pairs.remove(match_pair_index);

        // So, if we have a match-pattern like `x @ Enum::Variant(P1, P2)`,
        // we want to create a set of derived match-patterns like
        // `(x as Variant).0 @ P1` and `(x as Variant).1 @ P1`.
        let elem = ProjectionElem::Downcast(
            Some(adt_def.variants[variant_index].ident.name), variant_index);
        let downcast_place = match_pair.place.elem(elem); // `(x as Variant)`
        let consequent_match_pairs =
            subpatterns.iter()
                       .map(|subpattern| {
                           // e.g., `(x as Variant).0`
                           let place = downcast_place.clone().field(subpattern.field,
                                                                      subpattern.pattern.ty);
                           // e.g., `(x as Variant).0 @ P1`
                           MatchPair::new(place, &subpattern.pattern)
                       });

        candidate.match_pairs.extend(consequent_match_pairs);
    }

    fn error_simplifyable<'pat>(&mut self, match_pair: &MatchPair<'pat, 'tcx>) -> ! {
        span_bug!(match_pair.pattern.span,
                  "simplifyable pattern found: {:?}",
                  match_pair.pattern)
    }

    fn const_range_contains(
        &self,
        range: PatternRange<'tcx>,
        value: &'tcx ty::Const<'tcx>,
    ) -> Option<bool> {
        use std::cmp::Ordering::*;

        let param_env = ty::ParamEnv::empty().and(range.ty);
        let tcx = self.hir.tcx();

        let a = compare_const_vals(tcx, range.lo, value, param_env)?;
        let b = compare_const_vals(tcx, value, range.hi, param_env)?;

        match (b, range.end) {
            (Less, _) |
            (Equal, RangeEnd::Included) if a != Greater => Some(true),
            _ => Some(false),
        }
    }

    fn values_not_contained_in_range(
        &self,
        range: PatternRange<'tcx>,
        indices: &FxHashMap<&'tcx ty::Const<'tcx>, usize>,
    ) -> Option<bool> {
        for &val in indices.keys() {
            if self.const_range_contains(range, val)? {
                return Some(false);
            }
        }

        Some(true)
    }
}

impl Test<'_> {
    pub(super) fn targets(&self) -> usize {
        match self.kind {
            // binary tests
            TestKind::Eq { .. } | TestKind::Range(_) |
            TestKind::Len { .. } | TestKind::Or { .. } => {
                2
            }
            TestKind::Switch { adt_def, .. } => {
                // While the switch that we generate doesn't test for all
                // variants, we have a target for each variant and the
                // otherwise case, and we make sure that all of the cases not
                // specified have the same block.
                adt_def.variants.len() + 1
            }
            TestKind::SwitchInt { switch_ty, ref options, .. } => {
                if switch_ty.is_bool() {
                    // `bool` is special cased in `perform_test` to always
                    // branch to two blocks.
                    2
                } else {
                    options.len() + 1
                }
            }
        }
    }
}

fn is_switch_ty(ty: Ty<'_>) -> bool {
    ty.is_integral() || ty.is_char() || ty.is_bool()
}
