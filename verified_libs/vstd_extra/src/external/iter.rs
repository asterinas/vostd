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

/// Consumes the iterator, returning its last maximum according to `compare`, or `None` if empty.
///
/// Audited against Rust 1.100.0 (0ef1bc386), `library/core/src/iter/traits/iterator.rs`:
/// `max_by` calls `reduce(|x, y| if compare(&x, &y) == Ordering::Greater { x } else { y })`
/// and therefore retains the last maximal element for any total-preorder comparator.
/// See <https://doc.rust-lang.org/1.100.0/core/iter/trait.Iterator.html#method.max_by>.
/// TODO: Upstream this model; remove it when equivalent vstd support is available.
#[verifier::external_trait_specification]
pub trait ExIteratorMaxBy {
    type ExternalTraitSpecificationFor: Iterator;

    type Item;

    fn max_by<F>(self, compare: F) -> (ret: Option<Self::Item>) where
        Self: Sized,
        F: FnMut(&Self::Item, &Self::Item) -> Ordering,

        requires
            (forall|x: &Self::Item, y: &Self::Item| #[trigger] compare.requires((x, y)))
                || iterator_max_by_req(self, compare),
        ensures
            iterator_max_by_post(self, compare, ret),
    ;
}

/// Indirect precondition for `Iterator::max_by` so `ExIteratorMaxBy` need not depend on `IteratorSpec`.
pub uninterp spec fn iterator_max_by_req<I, F>(iter: I, compare: F) -> bool;

/// Satisfies `Iterator::max_by`'s comparator precondition for any prophetic iterator whose
/// comparator accepts every ordered pair of elements yielded by `iter`.
pub broadcast axiom fn axiom_iterator_max_by_req<
    I: Iterator + IteratorSpec,
    F: FnMut(&I::Item, &I::Item) -> Ordering,
>(iter: I, compare: F)
    requires
        iter.obeys_prophetic_iter_laws(),
        forall|i: int, j: int|
            0 <= i < j < iter.remaining().len() && iter.produces()[i] && iter.produces()[j]
                ==> #[trigger] compare.requires((&iter.remaining()[i], &iter.remaining()[j])),
    ensures
        #[trigger] iterator_max_by_req(iter, compare),
;

/// The postcondition is indirect so the external trait need not depend on its extension.
pub uninterp spec fn iterator_max_by_post<I, F, A>(iter: I, compare: F, ret: Option<A>) -> bool;

/// Whether `ord` is a lawful total preorder on `elems` and every return value of `compare`
/// on elements of `elems` agrees with `ord`.
#[verifier::opaque]
pub open spec fn comparator_agrees_with_preorder<A, F: FnMut(&A, &A) -> Ordering>(
    elems: Seq<A>,
    compare: F,
    ord: spec_fn(A, A) -> Ordering,
) -> bool {
    &&& forall|i: int, j: int, o: Ordering|
        0 <= i < elems.len() && 0 <= j < elems.len() && #[trigger] compare.ensures(
            (&elems[i], &elems[j]),
            o,
        ) ==> o == ord(elems[i], elems[j])
    &&& forall|i: int|
        0 <= i < elems.len() ==> #[trigger] ord(elems[i], elems[i]) == Ordering::Equal
    &&& forall|i: int, j: int|
        0 <= i < elems.len() && 0 <= j < elems.len() ==> (#[trigger] ord(elems[i], elems[j])
            == Ordering::Greater <==> ord(elems[j], elems[i]) == Ordering::Less)
    &&& forall|i: int, j: int, k: int|
        0 <= i < elems.len() && 0 <= j < elems.len() && 0 <= k < elems.len() && #[trigger] ord(
            elems[i],
            elems[j],
        ) != Ordering::Less && #[trigger] ord(elems[j], elems[k]) != Ordering::Less ==> ord(
            elems[i],
            elems[k],
        ) != Ordering::Less
}

/// Connects `Iterator::max_by` to the prophetic iterator model on successful return.
/// Like `axiom_iterator_max_postcondition`, this trusts `obeys_prophetic_iter_laws()`
/// for consistency of consuming methods with `next`. Ordering optimality additionally
/// requires `comparator_agrees_with_preorder`.
pub broadcast axiom fn axiom_iterator_max_by_postcondition<
    A,
    F: FnMut(&A, &A) -> Ordering,
    I: Iterator<Item = A> + IteratorSpec,
>(iter: I, compare: F, ret: Option<A>)
    requires
        iter.obeys_prophetic_iter_laws(),
        #[trigger] iterator_max_by_post(iter, compare, ret),
    ensures
        iter.produces().all(|p: bool| p),
        ret is None <==> iter.remaining().len() == 0,
        ret matches Some(greatest) ==> {
            &&& iter.remaining().contains(greatest)
            &&& forall|ord: spec_fn(A, A) -> Ordering| #[trigger]
                comparator_agrees_with_preorder(iter.remaining(), compare, ord) ==> {
                    &&& forall|k: int|
                        #![trigger iter.remaining()[k]]
                        0 <= k < iter.remaining().len() ==> ord(greatest, iter.remaining()[k])
                            != Ordering::Less
                    &&& exists|j: int|
                        0 <= j < iter.remaining().len() && iter.remaining()[j] == greatest
                            && forall|k: int|
                            j < k < iter.remaining().len() ==> ord(
                                greatest,
                                #[trigger] iter.remaining()[k],
                            ) == Ordering::Greater
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
        IteratorSpec::produces(&iter) == Seq::new(N as nat, |i: int| true),
        IteratorSpec::remaining(&iter) == array@,
        IteratorSpec::decrease(&iter) == Some(N as nat),
;

} // verus!
