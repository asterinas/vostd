// SPDX-License-Identifier: MPL-2.0
//! Specification for owned-array iteration not yet modeled by `vstd`.
//!
//! The array iterator contract follows Rust 1.97.1's
//! `library/core/src/array/iter.rs` implementation, which initializes an
//! iterator over the array in left-to-right order.
//!
//! # Verified Properties
//!
//! The trusted contract records the iterator's element order, termination,
//! remaining length, and prophetic iterator laws.
use vstd::{prelude::*, std_specs::iter::IteratorSpec};

verus! {

/// Verus proxy for the standard library's array `IntoIter`.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExArrayIntoIter<T, const N: usize>(core::array::IntoIter<T, N>);

/// The array iterator yields the array view from left to right and terminates.
pub assume_specification<T, const N: usize>[ <[T; N] as IntoIterator>::into_iter ](
    array: [T; N],
) -> (iter: <[T; N] as IntoIterator>::IntoIter)
    ensures
        IteratorSpec::obeys_prophetic_iter_laws(&iter),
        IteratorSpec::will_return_none(&iter),
        IteratorSpec::remaining(&iter) == array@,
        IteratorSpec::decrease(&iter) == Some(N as nat),
    opens_invariants none
    no_unwind
;

} // verus!
