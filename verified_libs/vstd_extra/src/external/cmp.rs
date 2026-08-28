// SPDX-License-Identifier: MPL-2.0
//! Specifications for the free comparison helpers in `core::cmp`.
//!
//! The contracts follow the Rust 1.97.1 implementations in
//! `library/core/src/cmp.rs` (`min` and `max` delegate to the corresponding
//! `Ord` methods).
use core::cmp::Ordering;
use vstd::prelude::*;
use vstd::std_specs::cmp::OrdSpec;

verus! {

/// Specification model of [`core::cmp::min`].
pub open spec fn spec_ord_min<T: Ord>(x: T, y: T) -> T {
    match y.cmp_spec(&x) {
        Ordering::Less => y,
        Ordering::Equal => x,
        Ordering::Greater => x,
    }
}

/// Specification model of [`core::cmp::max`].
pub open spec fn spec_ord_max<T: Ord>(x: T, y: T) -> T {
    match y.cmp_spec(&x) {
        Ordering::Less => x,
        Ordering::Equal => y,
        Ordering::Greater => y,
    }
}

/// Trusted specification of [`core::cmp::min`].
pub assume_specification<T: Ord>[ core::cmp::min ](x: T, y: T) -> (res: T)
    ensures
        T::obeys_cmp_spec() ==> res == spec_ord_min(x, y),
;

/// Trusted specification of [`core::cmp::max`].
pub assume_specification<T: Ord>[ core::cmp::max ](x: T, y: T) -> (res: T)
    ensures
        T::obeys_cmp_spec() ==> res == spec_ord_max(x, y),
;

} // verus!
