// SPDX-License-Identifier: MPL-2.0
//! Target word sizes.
use vstd::prelude::*;

verus! {

#[cfg(target_pointer_width = "64")]
global size_of usize == 8;

#[cfg(target_pointer_width = "64")]
global size_of isize == 8;

#[cfg(target_pointer_width = "32")]
global size_of usize == 4;

#[cfg(target_pointer_width = "32")]
global size_of isize == 4;

} // verus!
