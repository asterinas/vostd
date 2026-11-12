// SPDX-License-Identifier: MPL-2.0
//! Specifications for the free comparison functions missing from `vstd`.
use vstd::{
    prelude::*,
    std_specs::cmp::{OrdSpec, PartialOrdSpec},
};

use core::cmp::Ordering;

verus! {

/// Returns `y` when it compares less than `x`, and returns `x` otherwise.
pub open spec fn spec_ord_min<T: Ord>(x: T, y: T) -> T {
    match y.cmp_spec(&x) {
        Ordering::Less => y,
        Ordering::Equal => x,
        Ordering::Greater => x,
    }
}

/// Returns `x` when `y` compares less than it, and returns `y` otherwise.
pub open spec fn spec_ord_max<T: Ord>(x: T, y: T) -> T {
    match y.cmp_spec(&x) {
        Ordering::Less => x,
        Ordering::Equal => y,
        Ordering::Greater => y,
    }
}

} // verus!
