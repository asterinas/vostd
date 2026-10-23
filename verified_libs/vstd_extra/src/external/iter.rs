// SPDX-License-Identifier: MPL-2.0
//! Specifications for iterator operations not yet modeled by `vstd`.
use core::cmp::Ordering;
use vstd::{
    laws_cmp::obeys_cmp,
    prelude::*,
    std_specs::{cmp::OrdSpec, iter::IteratorSpec},
};

verus! {

/// Consumes the iterator, returning its first minimum or `None` if empty.
///
/// Audited against Rust 1.99.1 (58cf8f9c3), `library/core/src/iter/traits/iterator.rs`:
/// `min` calls `min_by(Ord::cmp)` and retains the first equal minimum.
/// See <https://doc.rust-lang.org/1.99.1/core/iter/trait.Iterator.html#method.min>.
/// TODO: Upstream this model; remove it when equivalent vstd support is available.
#[verifier::external_trait_specification]
pub trait ExIteratorMin {
    type ExternalTraitSpecificationFor: Iterator;

    type Item;

    fn min(self) -> (ret: Option<Self::Item>) where Self: Sized, Self::Item: Ord
        ensures
            iterator_min_post(self, ret),
    ;
}

/// The postcondition is indirect so the external trait need not depend on its extension.
pub uninterp spec fn iterator_min_post<I, A>(iter: I, ret: Option<A>) -> bool;

/// Connects `Iterator::min` to the prophetic iterator model on successful return.
/// Like vstd's provided-method specs in `std_specs/iter.rs`, this model trusts
/// `obeys_prophetic_iter_laws()` to include consistency of consuming methods with
/// `next`. Constraining the underlying implementations remains a vstd TODO.
/// Ordering guarantees additionally require vstd's comparison laws.
pub broadcast axiom fn axiom_iterator_min_postcondition<
    A: Ord,
    I: Iterator<Item = A> + IteratorSpec,
>(iter: I, ret: Option<A>)
    requires
        iter.obeys_prophetic_iter_laws(),
        #[trigger] iterator_min_post(iter, ret),
    ensures
        iter.will_return_none(),
        ret is None <==> iter.remaining().len() == 0,
        ret matches Some(least) ==> {
            &&& iter.remaining().contains(least)
            &&& obeys_cmp::<A>() ==> {
                &&& forall|k: int|
                    #![trigger iter.remaining()[k]]
                    0 <= k < iter.remaining().len() ==> least.cmp_spec(&iter.remaining()[k])
                        != Ordering::Greater
                &&& exists|j: int|
                    0 <= j < iter.remaining().len() && iter.remaining()[j] == least && forall|
                        k: int,
                    |
                        0 <= k < j ==> (#[trigger] iter.remaining()[k]).cmp_spec(&least)
                            == Ordering::Greater
            }
        },
;

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
