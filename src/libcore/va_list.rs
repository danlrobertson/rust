// Copyright 2018 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Implementation of a `va_list`

#![unstable(feature = "c_variadic",
            reason = "dlrobertson is still working on this",
            issue = "27745")]

#[cfg(not(stage0))]
#[lang = "va_list"]
/// A wrapper for a `va_list`
#[derive(Debug)]
#[unstable(feature = "c_variadic",
           reason = "dlrobertson is still working on this",
           issue = "27745")]
pub struct VaList;

#[cfg(not(stage0))]
#[unstable(feature = "c_variadic",
           reason = "This is just a test.",
           issue = "27745")]
/// Standard methods provided for a `VaList`.
pub unsafe trait VaListArg {
    /// Advance to the next arg.
    fn arg<T>(&mut self) -> T;

    /// Copy the `va_list` at the current location.
    fn copy<'ret, F, T>(&self, f: F) -> T
            where F: FnOnce(VaList) -> T, T: 'ret;
}

#[cfg(not(stage0))]
#[unstable(feature = "c_variadic",
           reason = "This is just a test.",
           issue = "27745")]
unsafe impl VaListArg for VaList {
    fn arg<T>(&mut self) -> T {
        panic!("Not implemented yet!");
    }

    fn copy<'ret, F, T>(&self, _f: F) -> T
            where F: FnOnce(VaList) -> T, T: 'ret {
        panic!("Not implemented yet!");
    }
}
