//! Verus specifications for the third-party `smallvec` crate, trusted as TCB from
//! inspection of the `smallvec-1.15.0` source (`src/lib.rs`) and centralized here
//! rather than beside an OSTD caller. `cpu/set.rs` is currently the only consumer
//! (`SmallVec<[u64; 2]>`).
//!
//! The model is a `Seq<A::Item>`: the views below equate every executed `SmallVec`
//! operation to a `Seq` operation, and `Deref`/`DerefMut` bridge to the std
//! `[A::Item]` slice so that indexing, `len`, and `iter` reuse `vstd`'s slice
//! specifications rather than being re-axiomatized.
//!
//! `SmallVec::new` asserts at construction that `A` is a well-formed `Array` impl
//! (its reported size matches the real layout); a custom `unsafe impl Array` could
//! trip this. So every operation below is guarded by `obeys_smallvec_array::<A>`,
//! which unfolds to smallvec's own construction assert. Only the two arrays
//! used by OSTD have checked guard lemmas — `lemma_smallvec_array_u64_2` and
//! `lemma_smallvec_array_atomic_u64_2`; any other `A: Array` needs a
//! correspondingly trusted size/alignment fact.
//!
//! Allocation-growth panics (capacity overflow past `isize::MAX`) are noted on each
//! spec and, where a `requires` fits, excluded by that precondition;
//! `SmallVec::reserve` rounds the capacity up to the next power of two, so those
//! bounds use a factor of 2.
use core::{
    ops::{Deref, DerefMut, Index, IndexMut},
    slice::SliceIndex,
    sync::atomic::AtomicU64,
};
use smallvec::{Array, SmallVec};
use vstd::{
    layout::{align_of, size_of},
    prelude::*,
    slice::SliceIndexSpec,
    std_specs::iter::{FromIteratorSpec, IteratorSpec},
};

verus! {

// `global layout` accepts only named types, so aliases are needed for arrays.
type U64Array2 = [u64; 2];

type AtomicU64Array2 = [AtomicU64; 2];

// rustc checks these declarations; together they provide the element and array
// sizes and alignments needed to prove `obeys_smallvec_array` below.
global layout u64 is size == 8, align == 8;

global layout U64Array2 is size == 16, align == 8;

global layout AtomicU64 is size == 8, align == 8;

global layout AtomicU64Array2 is size == 16, align == 8;

/// Verus declaration for `smallvec::Array`; only the element type `Item` is surfaced.
#[verifier::external_trait_specification]
pub trait ExArray {
    type ExternalTraitSpecificationFor: Array;

    type Item;
}

/// Opaque external wrapper for the owned small-vector type `SmallVec<A>`.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(A)]
pub struct ExSmallVec<A: Array>(SmallVec<A>);

/// The contents of a `SmallVec`, modelled as a sequence of its elements.
pub uninterp spec fn smallvec_view<A: Array>(v: &SmallVec<A>) -> Seq<A::Item>;

/// The element count that `A`'s smallvec `Array` impl reports (`A::size()`).
/// No `Array` bound, so the mirrors below can state it for every array `N`.
pub uninterp spec fn smallvec_array_size<A>() -> nat;

/// Whether `A` is a well-formed standard `Array` impl, i.e. smallvec's
/// `SmallVec::new` construction assert holds: the reported element count and
/// the alignment of `A` are consistent with the real layouts of `A` and
/// `A::Item`. The two array instances used by OSTD satisfy this guard via the
/// concrete lemmas below; any other impl needs corresponding layout and size facts.
pub open spec fn obeys_smallvec_array<A: Array>() -> bool {
    size_of::<A>() == smallvec_array_size::<A>() * size_of::<A::Item>() && align_of::<A>()
        >= align_of::<A::Item>()
}

/// Mirrors smallvec's `Array::size()`: an array `[T; N]` reports its own
/// length `N`. Trusted from the smallvec 1.15.0 source; impls exist only for
/// its fixed size list (no `const_generics`), and other sizes can't be used
/// as `A: Array` anywhere below.
pub broadcast axiom fn axiom_smallvec_array_size_of_array<T, const N: usize>()
    ensures
        #![trigger smallvec_array_size::<[T; N]>()]
        smallvec_array_size::<[T; N]>() == N,
;

/// The `[u64; 2]` used by `CpuSet` is a well-formed `SmallVec` backing store.
/// Its concrete layout declarations above are checked by rustc.
pub broadcast proof fn lemma_smallvec_array_u64_2()
    ensures
        #[trigger] obeys_smallvec_array::<[u64; 2]>(),
{
    broadcast use axiom_smallvec_array_size_of_array;

}

/// The `[AtomicU64; 2]` used by `AtomicCpuSet` is a well-formed `SmallVec`
/// backing store. Its concrete layout declarations above are checked by rustc.
pub broadcast proof fn lemma_smallvec_array_atomic_u64_2()
    ensures
        #[trigger] obeys_smallvec_array::<[AtomicU64; 2]>(),
{
    broadcast use axiom_smallvec_array_size_of_array;

}

/// `SmallVec`'s single-position indexing precondition is the slice bounds check.
pub broadcast axiom fn axiom_smallvec_index_req<A: Array>(v: &SmallVec<A>, index: usize)
    requires
        obeys_smallvec_array::<A>(),
    ensures
        #![trigger <SmallVec<A> as vstd::std_specs::core::IndexSpec<usize>>::index_req(v, &index)]
        <SmallVec<A> as vstd::std_specs::core::IndexSpec<usize>>::index_req(v, &index) == (index
            < smallvec_view(v).len()),
;

pub broadcast group group_smallvec_models {
    lemma_smallvec_array_u64_2,
    lemma_smallvec_array_atomic_u64_2,
    axiom_smallvec_index_req,
}

/// Constructs a new, empty `SmallVec`.
///
/// Asserts at construction that `A` is a well-formed `Array` impl; the guard admits
/// only the trusted instances in `group_smallvec_models`.
pub assume_specification<A: Array>[ SmallVec::<A>::new ]() -> (ret: SmallVec<A>)
    requires
        obeys_smallvec_array::<A>(),
    ensures
        smallvec_view(&ret) == Seq::<A::Item>::empty(),
;

/// Constructs a new, empty `SmallVec` with the given heap capacity, which is not modelled.
///
/// Panics on capacity overflow if `n * size_of::<A::Item>()` exceeds `isize::MAX`; the bound
/// is enforced by `Layout::from_size_align` in the private `layout_array` (called from `try_grow`).
pub assume_specification<A: Array>[ SmallVec::<A>::with_capacity ](n: usize) -> (ret: SmallVec<A>)
    requires
        obeys_smallvec_array::<A>(),
        n * size_of::<A::Item>() <= isize::MAX,
    ensures
        smallvec_view(&ret) == Seq::<A::Item>::empty(),
;

/// The number of elements.
pub assume_specification<A: Array>[ SmallVec::<A>::len ](v: &SmallVec<A>) -> usize
    requires
        obeys_smallvec_array::<A>(),
    returns
        smallvec_view(v).len() as usize,
;

/// Borrows the element at `index`.
pub assume_specification<A: Array, I: SliceIndex<[A::Item]>>[ SmallVec::<A>::index ](
    v: &SmallVec<A>,
    index: I,
) -> (output: &<I as SliceIndex<[A::Item]>>::Output)
    ensures
        obeys_smallvec_array::<A>() ==> exists|slice: &[A::Item]| #[trigger]
            slice@ == smallvec_view(v) && call_ensures(
                <I as SliceIndex<[A::Item]>>::index,
                (index, slice),
                output,
            ),
;

/// Mutably borrows the element at `index`; writes through the borrow are reflected
/// in the `SmallVec`'s final view.
pub assume_specification<A: Array, I: SliceIndex<[A::Item]>>[ SmallVec::<A>::index_mut ](
    v: &mut SmallVec<A>,
    index: I,
) -> (output: &mut <I as SliceIndex<[A::Item]>>::Output)
    ensures
        obeys_smallvec_array::<A>() ==> exists|slice: &mut [A::Item]| #[trigger]
            slice@ == smallvec_view(old(v)) && final(slice)@ == smallvec_view(final(v))
                && call_ensures(<I as SliceIndex<[A::Item]>>::index_mut, (index, slice), output),
;

/// Appends `value` to the end.
///
/// Panics on capacity overflow when full, if growing to the next power of two of
/// `len + 1` would exceed `isize::MAX / size_of::<A::Item>()`; the bound uses a
/// factor of 2 for the power-of-two rounding.
pub assume_specification<A: Array>[ SmallVec::<A>::push ](v: &mut SmallVec<A>, value: A::Item)
    requires
        obeys_smallvec_array::<A>(),
        2 * (smallvec_view(v).len() + 1) * size_of::<A::Item>() <= isize::MAX,
    ensures
        smallvec_view(final(v)) == smallvec_view(old(v)).push(value),
;

/// Resizes so the length is `new_len`, cloning `value` into new positions. Mirrors `Vec::resize`.
///
/// Panics on capacity overflow when growing, if the allocation rounded up to the
/// next power of two of `new_len` would exceed `isize::MAX / size_of::<A::Item>()`.
pub assume_specification<A: Array>[ SmallVec::<A>::resize ](
    v: &mut SmallVec<A>,
    new_len: usize,
    value: A::Item,
) where A::Item: Clone
    requires
        obeys_smallvec_array::<A>(),
        2 * new_len * size_of::<A::Item>() <= isize::MAX,
    ensures
        new_len <= smallvec_view(old(v)).len() ==> smallvec_view(final(v)) == smallvec_view(
            old(v),
        )[..new_len],
        new_len > smallvec_view(old(v)).len() ==> {
            &&& smallvec_view(final(v)).len() == new_len
            &&& smallvec_view(final(v))[..smallvec_view(old(v)).len()] == smallvec_view(old(v))
            &&& forall|i: int|
                #![trigger smallvec_view(final(v))[i]]
                smallvec_view(old(v)).len() <= i < new_len ==> cloned::<A::Item>(
                    value,
                    smallvec_view(final(v))[i],
                )
        },
;

/// Views the elements as a borrowed slice.
pub assume_specification<A: Array>[ SmallVec::<A>::as_slice ](v: &SmallVec<A>) -> (ret: &[A::Item])
    requires
        obeys_smallvec_array::<A>(),
    ensures
        ret@ == smallvec_view(v),
;

/// Views the elements as a mutably borrowed slice; writes through the returned borrow are
/// reflected in the `SmallVec`'s final view.
pub assume_specification<A: Array>[ SmallVec::<A>::as_mut_slice ](v: &mut SmallVec<A>) -> (ret:
    &mut [A::Item])
    requires
        obeys_smallvec_array::<A>(),
    ensures
        ret@ == smallvec_view(old(v)),
        final(ret)@ == smallvec_view(final(v)),
;

/// `SmallVec` derefs to a slice over exactly its own elements; the guard is an
/// ensures-implication since `requires` is disallowed on trait-method specs.
pub assume_specification<A: Array>[ <SmallVec<A> as Deref>::deref ](v: &SmallVec<A>) -> (ret:
    &[A::Item])
    ensures
        obeys_smallvec_array::<A>() ==> ret@ == smallvec_view(v),
;

/// `SmallVec` derefs mutably to a slice over exactly its own elements; a mutation performed
/// through the returned borrow is reflected in the `SmallVec`'s final view (guard as an
/// ensures-implication for the same reason as [`Deref`]).
pub assume_specification<A: Array>[ <SmallVec<A> as DerefMut>::deref_mut ](
    v: &mut SmallVec<A>,
) -> (ret: &mut [A::Item])
    ensures
        obeys_smallvec_array::<A>() ==> {
            &&& ret@ == smallvec_view(old(v))
            &&& final(ret)@ == smallvec_view(final(v))
        },
;

/// Verus proxy for the owned `SmallVec` iterator `smallvec::IntoIter`
/// (mirrors the array-IntoIter precedent in `crate::external::iter`).
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(A)]
pub struct ExSmallVecIntoIter<A: Array>(smallvec::IntoIter<A>);

/// Consumes the `SmallVec`, yielding exactly its elements from left to right,
/// once each. Guarded as an ensures-implication since `requires` is
/// disallowed on trait-method specs (same as [`Deref`]).
pub assume_specification<A: Array>[ <SmallVec<A> as IntoIterator>::into_iter ](
    v: SmallVec<A>,
) -> (iter: <SmallVec<A> as IntoIterator>::IntoIter)
    ensures
        obeys_smallvec_array::<A>() ==> {
            &&& IteratorSpec::obeys_prophetic_iter_laws(&iter)
            &&& IteratorSpec::will_return_none(&iter)
            &&& IteratorSpec::remaining(&iter) == smallvec_view(&v)
            &&& IteratorSpec::decrease(&iter) == Some(smallvec_view(&v).len())
        },
;

/// Collecting a terminated iterator into a `SmallVec` yields exactly its
/// remaining elements, in order; the axiom slot for `FromIteratorSpecImpl`,
/// which cannot be implemented here because both `SmallVec` and
/// `FromIteratorSpecImpl` are defined in external crates (orphan rule, E0117).
/// Consequently `from_iter_ensures` remains uninterpreted for `SmallVec`, so
/// local proof/spec code alone cannot prove this equality. Eliminating this
/// trusted boundary requires either an upstream spec implementation or replacing
/// `collect()` with operations such as `SmallVec::new()` and `push()` that already
/// have usable contracts.
/// Panics on capacity overflow like `push`; a no-panic caller needs
/// `2 * remaining.len() * size_of::<A::Item>() <= isize::MAX`.
pub broadcast axiom fn axiom_smallvec_from_iter_ensures<A: Array>(
    remaining: Seq<A::Item>,
    s: SmallVec<A>,
)
    ensures
        obeys_smallvec_array::<A>() ==> #[trigger] FromIteratorSpec::from_iter_ensures(remaining, s)
            == (remaining == smallvec_view(&s)),
;

} // verus!
