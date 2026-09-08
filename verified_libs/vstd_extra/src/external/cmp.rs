// SPDX-License-Identifier: MPL-2.0
//! Specifications for the free comparison functions missing from `vstd`.
//!
//! Rust 1.98.0's `library/core/src/cmp.rs` delegates `min` and `max` to
//! `Ord::min` and `Ord::max`. These contracts mirror their existing `vstd`
//! guarantees, conditional on the comparison model. They do not promise
//! `no_unwind`: user-defined comparison implementations may panic.
use vstd::{prelude::*, std_specs::cmp::OrdSpec};

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

/// Returns the minimum, choosing the first argument when they compare equal.
#[verifier::when_used_as_spec(spec_ord_min)]
pub assume_specification<T: Ord>[ core::cmp::min ](x: T, y: T) -> (ret: T)
    ensures
        T::obeys_cmp_spec() ==> ret == spec_ord_min(x, y),
;

/// Returns the maximum, choosing the second argument when they compare equal.
#[verifier::when_used_as_spec(spec_ord_max)]
pub assume_specification<T: Ord>[ core::cmp::max ](x: T, y: T) -> (ret: T)
    ensures
        T::obeys_cmp_spec() ==> ret == spec_ord_max(x, y),
;

} // verus!
