//! Specifications for `core::cmp` free functions that `vstd` only models as `Ord` methods.
//!
//! The behavioral wording below is aligned with Rust 1.97.1's `core::cmp` source:
//! <https://doc.rust-lang.org/1.97.1/src/core/cmp.rs.html>.
use core::cmp::Ordering;
use vstd::prelude::*;
use vstd::std_specs::cmp::OrdSpec;

verus! {

/// Compares and returns the minimum of two values.
///
/// Returns the first argument if the comparison determines them to be equal. Rust's free
/// function internally uses an alias to [`Ord::min`].
pub open spec fn spec_cmp_min<T: Ord>(v1: T, v2: T) -> T {
    match v2.cmp_spec(&v1) {
        Ordering::Less => v2,
        Ordering::Equal => v1,
        Ordering::Greater => v1,
    }
}

/// Compares and returns the maximum of two values.
///
/// Returns the second argument if the comparison determines them to be equal. Rust's free
/// function internally uses an alias to [`Ord::max`].
pub open spec fn spec_cmp_max<T: Ord>(v1: T, v2: T) -> T {
    match v2.cmp_spec(&v1) {
        Ordering::Less => v1,
        Ordering::Equal => v2,
        Ordering::Greater => v2,
    }
}

/// Trusted specification of [`core::cmp::min`], whose Rust body is `v1.min(v2)`.
pub assume_specification<T: Ord>[ core::cmp::min ](v1: T, v2: T) -> (r: T)
    ensures
        T::obeys_cmp_spec() ==> r == spec_cmp_min(v1, v2),
;

/// Trusted specification of [`core::cmp::max`], whose Rust body is `v1.max(v2)`.
pub assume_specification<T: Ord>[ core::cmp::max ](v1: T, v2: T) -> (r: T)
    ensures
        T::obeys_cmp_spec() ==> r == spec_cmp_max(v1, v2),
;

} // verus!
