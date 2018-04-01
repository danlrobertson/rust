// Copyright 2018 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![unstable(feature = "c_variadic",
            reason = "dlrobertson is still working on this",
            issue = "27745")]

//! Implementation of a `va_list`

#[cfg(not(stage0))]
#[lang = "va_list"]
/// A wrapper for a `va_list`
//#[derive(Debug)]
#[repr(C)]
#[unstable(feature = "c_variadic",
           reason = "dlrobertson is still working on this",
           issue = "27745")]
#[derive(Debug)]
pub struct VaList;

#[cfg(not(stage0))]
#[unstable(feature = "c_variadic",
           reason = "This is just a test.",
           issue = "27745")]
impl VaList {
    /// Advance to the next arg.
    pub unsafe fn arg<T: Copy>(&mut self) -> T {
        let tmp = self as *mut _ as *mut i8;
        ::intrinsics::va_arg(tmp)
    }

    /// Copy the `va_list` at the current location.
    pub unsafe fn copy<'ret, F, T>(&self, f: F) -> T
            where F: FnOnce(&mut VaList) -> T, T: 'ret {
        let mut ap: VaList = ::mem::uninitialized::<VaList>();
        ::intrinsics::va_copy(self as *const _ as *const i8, &mut ap as *mut _ as *mut i8);
        let ret = f(&mut ap);
        ::intrinsics::va_end(&mut ap as *const _ as *mut i8);
        ret
    }
}
