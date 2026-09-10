// SPDX-License-Identifier: MPL-2.0
//! Specification for owned-array iteration not yet modeled by `vstd`.
use vstd::{prelude::*, std_specs::iter::IteratorSpec};

verus! {

/// Verus proxy for the standard library's array `IntoIter`.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExArrayIntoIter<T, const N: usize>(core::array::IntoIter<T, N>);

/// The array iterator yields the array view from left to right and terminates.
/// See [`array::into_iter`](https://doc.rust-lang.org/std/primitive.array.html#method.into_iter).
pub assume_specification<T, const N: usize>[ <[T; N] as IntoIterator>::into_iter ](
    array: [T; N],
) -> (iter: <[T; N] as IntoIterator>::IntoIter)
    ensures
        IteratorSpec::obeys_prophetic_iter_laws(&iter),
        IteratorSpec::will_return_none(&iter),
        IteratorSpec::remaining(&iter) == array@,
        IteratorSpec::decrease(&iter) == Some(N as nat),
;

} // verus!
