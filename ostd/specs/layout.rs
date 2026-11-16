// SPDX-License-Identifier: MPL-2.0
//! Target word sizes.
use vstd::prelude::*;

verus! {

// Asterinas is designed for 64-bit architectures.
global size_of usize == 8;

global size_of isize == 8;

} // verus!
