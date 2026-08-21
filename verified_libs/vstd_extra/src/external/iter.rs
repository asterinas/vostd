//! Specifications for standard iterator adapters not modeled by `vstd`.
//!
//! The behavioral wording below is aligned with Rust 1.97.1's by-value array iterator and filter
//! sources:
//! - <https://doc.rust-lang.org/1.97.1/src/core/array/iter.rs.html>
//! - <https://doc.rust-lang.org/1.97.1/src/core/iter/adapters/filter.rs.html>
//! - <https://doc.rust-lang.org/1.97.1/src/core/iter/traits/iterator.rs.html>
use core::{array::IntoIter as ArrayIntoIter, iter::Filter};
use vstd::{prelude::*, std_specs::iter::IteratorSpec};

verus! {

/// A by-value array iterator.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExArrayIntoIter<T, const N: usize>(ArrayIntoIter<T, N>);

/// Local proof-model marker for an iterator represented by [`iterator_remaining`].
pub uninterp spec fn iterator_model_valid<I>(iter: I) -> bool;

/// Local proof model of the elements that an iterator has not yielded yet, in yield order.
pub uninterp spec fn iterator_remaining<I, Item>(iter: I) -> Seq<Item>;

/// Creates a consuming iterator, that is, one that moves each value out of the array (from start
/// to end).
///
/// The array cannot be used after calling this unless `T` implements `Copy`, so the whole array
/// is copied.
pub assume_specification<T, const N: usize>[ <[T; N] as IntoIterator>::into_iter ](
    array: [T; N],
) -> (iter: <[T; N] as IntoIterator>::IntoIter)
    ensures
        iterator_model_valid(iter),
        iterator_remaining::<_, T>(iter) == array@,
        iter.obeys_prophetic_iter_laws(),
        iter.will_return_none(),
        iter.remaining() == array@,
        iter.decrease() == Some(N as nat),
;

/// An iterator that filters the elements of `iter` with `predicate`.
///
/// This struct is created by the [`Iterator::filter`] method. Iterators are lazy and do nothing
/// unless consumed.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(I)]
#[verifier::reject_recursive_types(P)]
pub struct ExFilter<I, P>(Filter<I, P>);

#[verifier::external_trait_specification]
/// Specification of [`Iterator::filter`].
pub trait ExIteratorFilter {
    type ExternalTraitSpecificationFor: Iterator;

    type Item;

    /// Creates an iterator which uses a closure to determine if an element should be yielded.
    ///
    /// Given an element, the closure must return `true` or `false`. The returned iterator yields
    /// only the elements for which the closure returns `true`. In Rust's implementation,
    /// `iter.filter(f).next()` is equivalent to `iter.find(f)`.
    fn filter<P>(self, predicate: P) -> (filtered: Filter<Self, P>) where
        Self: Iterator + Sized,
        P: FnMut(&<Self as Iterator>::Item) -> bool,

        requires
            iterator_model_valid(self),
            forall|i: int|
                0 <= i < iterator_remaining::<Self, <Self as Iterator>::Item>(self).len() ==> (
                #[trigger] predicate.requires(
                    (&iterator_remaining::<Self, <Self as Iterator>::Item>(self)[i],),
                )),
        ensures
            iterator_model_valid(filtered),
            forall|keep: spec_fn(<Self as Iterator>::Item) -> bool|
                #![auto]
                (forall|i: int, result: bool|
                    #![auto]
                    0 <= i < iterator_remaining::<Self, <Self as Iterator>::Item>(self).len()
                        ==> predicate.ensures(
                        (&iterator_remaining::<Self, <Self as Iterator>::Item>(self)[i],),
                        result,
                    ) ==> result == keep(
                        iterator_remaining::<Self, <Self as Iterator>::Item>(self)[i],
                    )) ==> iterator_remaining::<_, <Self as Iterator>::Item>(filtered)
                    == iterator_remaining::<Self, <Self as Iterator>::Item>(self).filter(keep),
    ;
}

/// Connects the local remaining-sequence model to `vstd`'s prophetic iterator model.
pub axiom fn axiom_iterator_model<I: Iterator>(iter: I)
    ensures
        #[trigger] iterator_model_valid(iter) ==> {
            &&& IteratorSpec::obeys_prophetic_iter_laws(&iter)
            &&& IteratorSpec::will_return_none(&iter)
            &&& IteratorSpec::remaining(&iter) == iterator_remaining::<I, I::Item>(iter)
            &&& IteratorSpec::decrease(&iter) is Some
        },
;

} // verus!
