// SPDX-License-Identifier: MPL-2.0
//! Specifications for iterator operations not yet modeled by `vstd`.
use core::{
    iter::{Skip, StepBy},
    slice::Iter,
};

use core::cmp::Ordering;
use vstd::{
    laws_cmp::obeys_cmp,
    prelude::*,
    std_specs::{cmp::OrdSpec, iter::IteratorSpec},
};

verus! {

/// Consumes the iterator, returning its first minimum or `None` if empty.
///
/// Audited against Rust 1.100.0 (0ef1bc386), `library/core/src/iter/traits/iterator.rs`:
/// `min` calls `reduce(Ord::min)` and retains the first equal minimum for lawful `Ord`.
/// See <https://doc.rust-lang.org/1.100.0/core/iter/trait.Iterator.html#method.min>.
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
/// Membership and ordering guarantees additionally require vstd's comparison laws.
pub broadcast axiom fn axiom_iterator_min_postcondition<
    A: Ord,
    I: Iterator<Item = A> + IteratorSpec,
>(iter: I, ret: Option<A>)
    requires
        iter.obeys_prophetic_iter_laws(),
        #[trigger] iterator_min_post(iter, ret),
    ensures
        iter.produces().all(|p: bool| p),
        ret is None <==> iter.remaining().len() == 0,
        obeys_cmp::<A>() ==> (ret matches Some(least) ==> {
            &&& iter.remaining().contains(least)
            &&& forall|k: int|
                #![trigger iter.remaining()[k]]
                0 <= k < iter.remaining().len() ==> least.cmp_spec(&iter.remaining()[k])
                    != Ordering::Greater
            &&& exists|j: int|
                0 <= j < iter.remaining().len() && iter.remaining()[j] == least && forall|k: int|
                    0 <= k < j ==> (#[trigger] iter.remaining()[k]).cmp_spec(&least)
                        == Ordering::Greater
        }),
;

/// Consumes the iterator, returning its last maximum or `None` if empty.
///
/// Audited against Rust 1.100.0 (0ef1bc386), `library/core/src/iter/traits/iterator.rs`:
/// `max` calls `reduce(Ord::max)` and retains the last equal maximum for lawful `Ord`.
/// See <https://doc.rust-lang.org/1.100.0/core/iter/trait.Iterator.html#method.max>.
/// TODO: Upstream this model; remove it when equivalent vstd support is available.
#[verifier::external_trait_specification]
pub trait ExIteratorMax {
    type ExternalTraitSpecificationFor: Iterator;

    type Item;

    fn max(self) -> (ret: Option<Self::Item>) where Self: Sized, Self::Item: Ord
        ensures
            iterator_max_post(self, ret),
    ;
}

/// The postcondition is indirect so the external trait need not depend on its extension.
pub uninterp spec fn iterator_max_post<I, A>(iter: I, ret: Option<A>) -> bool;

/// Connects `Iterator::max` to the prophetic iterator model on successful return.
/// Like vstd's provided-method specs in `std_specs/iter.rs`, this model trusts
/// `obeys_prophetic_iter_laws()` to include consistency of consuming methods with
/// `next`. Constraining the underlying implementations remains a vstd TODO.
/// Membership and ordering guarantees additionally require vstd's comparison laws.
pub broadcast axiom fn axiom_iterator_max_postcondition<
    A: Ord,
    I: Iterator<Item = A> + IteratorSpec,
>(iter: I, ret: Option<A>)
    requires
        iter.obeys_prophetic_iter_laws(),
        #[trigger] iterator_max_post(iter, ret),
    ensures
        iter.produces().all(|p: bool| p),
        ret is None <==> iter.remaining().len() == 0,
        obeys_cmp::<A>() ==> (ret matches Some(greatest) ==> {
            &&& iter.remaining().contains(greatest)
            &&& forall|k: int|
                #![trigger iter.remaining()[k]]
                0 <= k < iter.remaining().len() ==> greatest.cmp_spec(&iter.remaining()[k])
                    != Ordering::Less
            &&& exists|j: int|
                0 <= j < iter.remaining().len() && iter.remaining()[j] == greatest && forall|k: int|

                    j < k < iter.remaining().len() ==> (#[trigger] iter.remaining()[k]).cmp_spec(
                        &greatest,
                    ) == Ordering::Less
        }),
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
        IteratorSpec::produces(&iter) == Seq::new(N as nat, |i: int| true),
        IteratorSpec::remaining(&iter) == array@,
        IteratorSpec::decrease(&iter) == Some(N as nat),
;

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(I)]
pub struct ExStepBy<I>(StepBy<I>);

#[verifier::external_trait_specification]
pub trait ExIteratorStepBy {
    type ExternalTraitSpecificationFor: Iterator;

    fn step_by(self, step: usize) -> (ret: StepBy<Self>) where Self: Sized
        requires
            step > 0,
        ensures
            step_by_post(self, step, ret),
    ;
}

pub uninterp spec fn step_by_post<I>(iter: I, step: usize, ret: StepBy<I>) -> bool;

/// Rust 1.100.0 core/src/iter/adapters/step_by.rs yields the first item and
/// then every second item of this skipped byte slice.
pub broadcast axiom fn axiom_step_by_byte_pairs<'a>(
    iter: Skip<Iter<'a, u8>>,
    ret: StepBy<Skip<Iter<'a, u8>>>,
)
    requires
        #[trigger] step_by_post(iter, 2, ret),
        iter.obeys_prophetic_iter_laws(),
    ensures
        ret.obeys_prophetic_iter_laws(),
        ret.remaining().len() == (iter.remaining().len() + 1) / 2,
        ret.produces() == Seq::new(ret.remaining().len(), |i: int| true),
        forall|i: int|
            0 <= i < ret.remaining().len() ==> (#[trigger] ret.remaining()[i]) == iter.remaining()[i
                * 2],
;

} // verus!
