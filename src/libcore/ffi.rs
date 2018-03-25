// Copyright 2018 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Implementation of a `va_list`.

#[cfg(any(all(not(target_arch = "aarch64"), not(target_arch = "powerpc"),
              not(target_arch = "x86_64")),
          windows))]
/// Basic byte pointer variant of a `va_list`.
type VaListImpl = i8;

#[cfg(all(target_arch = "aarch64", not(windows)))]
#[repr(C)]
#[derive(Debug)]
/// AArch64 ABI implementation of a `va_list`. See the
/// [Aarch64 Procedure Call Standard] for more details.
///
/// [AArch64 Procedure Call Standard]:
/// http://infocenter.arm.com/help/topic/com.arm.doc.ihi0055b/IHI0055B_aapcs64.pdf
struct VaListImpl {
    stack: *mut (),
    gr_top: *mut (),
    vr_top: *mut (),
    gr_offs: i32,
    vr_offs: i32,
}

#[cfg(all(target_arch = "powerpc", not(windows)))]
#[repr(C)]
#[derive(Debug)]
/// PowerPC ABI implementation of a `va_list`.
struct VaListImpl {
    gpr: u8,
    fpr: u8,
    reserved: u16,
    overflow_arg_area: *mut (),
    reg_save_area: *mut (),
}

#[cfg(all(target_arch = "x86_64", not(windows)))]
#[repr(C)]
#[derive(Debug)]
/// x86_64 ABI implementation of a `va_list`.
struct VaListImpl {
    gp_offset: i32,
    fp_offset: i32,
    overflow_arg_area: *mut (),
    reg_save_area: *mut (),
}

/// A wrapper for a `va_list`
#[lang = "va_list"]
#[derive(Debug)]
#[repr(transparent)]
pub struct VaList<'a>(&'a mut VaListImpl);

// The VaArgSafe trait needs to be used in public interfaces, however, the trait
// itself must not be allowed to be used outside this module. Allowing users to
// implement the trait for a new type (thereby allowing the va_arg intrinsic to
// be used on a new type) is likely to cause undefined behavior.
//
// FIXME(dlrobertson): In order to use the VaArgSafe trait in a public interface
// but also ensure it cannot be used elsewhere, the trait needs to be public
// within a private module. Once RFC 2145 has been implemented look into
// improving this.
mod sealed_trait {
    /// Trait which whitelists the allowed types to be used with [VaList::arg]
    ///
    /// [VaList::va_arg]: struct.VaList.html#method.arg
    pub trait VaArgSafe {}
}

macro_rules! impl_va_arg_safe {
    ($($t:ty),+) => {
        $(
            impl sealed_trait::VaArgSafe for $t {}
        )+
    }
}

impl_va_arg_safe!{i8, i16, i32, i64, usize}
impl_va_arg_safe!{u8, u16, u32, u64, isize}
impl_va_arg_safe!{f64}

impl<T> sealed_trait::VaArgSafe for *mut T {}
impl<T> sealed_trait::VaArgSafe for *const T {}

impl<'a> VaList<'a> {
    /// Advance to the next arg.
    pub unsafe fn arg<T: sealed_trait::VaArgSafe>(&mut self) -> T {
        va_arg(self)
    }

    /// Copy the `va_list` at the current location.
    pub unsafe fn copy<F, R>(&mut self, f: F) -> R
            where F: for<'copy> FnOnce(VaList<'copy>) -> R {
        let mut ap_impl = ::mem::uninitialized::<VaListImpl>();
        let mut ap = VaList(&mut ap_impl);
        va_copy(&mut ap, self);
        let ret = f(VaList(ap.0));
        va_end(&mut ap);
        ret
    }
}

extern "rust-intrinsic" {
    /// Destroy the arglist `ap` after initialization with `va_start` or
    /// `va_copy`.
    fn va_end(ap: &mut VaList);

    /// Copy the current location of arglist `src` to the arglist `dst`.
    fn va_copy(dst: &mut VaList, src: &VaList);

    /// Loads an argument of type `T` from the `va_list` `ap` and increment the
    /// argument `ap` points to.
    fn va_arg<T: sealed_trait::VaArgSafe>(ap: &mut VaList) -> T;
}
