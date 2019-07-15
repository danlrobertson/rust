#![feature(or_patterns)]
//~^ WARN the feature `or_patterns` is incomplete and may cause the compiler to crash
#![crate_type="lib"]

pub enum FirstEnum {
    Foo,
    Bar,
    Baz
}

pub fn simple_enum_test(pat: Option<FirstEnum>) -> bool {
    match pat { //~ non-exhaustive patterns: `Some(Baz)` not covered
        Some(FirstEnum::Foo | FirstEnum::Bar) => true,
        None => false,
    }
}

pub fn switch_int_test(pat: Option<usize>) -> bool {
    match pat { //~ non-exhaustive patterns: `Some(_)` not covered
        Some(1 | 2) => true,
        None => false,
    }
}

pub enum SecondEnum {
    StructLike {
        first: usize,
        second: FirstEnum
    },
    CLike
}

pub fn structlike_enum_test(pat: Option<SecondEnum>) -> bool {
    match pat { //~ non-exhaustive patterns: `Some(StructLike { .. })` not covered
        Some(SecondEnum::StructLike { first: 42, .. } | SecondEnum::CLike) => true,
        None => false,
    }
}
