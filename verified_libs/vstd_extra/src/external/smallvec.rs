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
//! trip this. So every operation below is guarded by `obeys_smallvec_array::<A>`
//! and only the trusted instances in `group_smallvec_models` (currently `[u64; 2]`)
//! are admitted by broadcast axioms. Any other `A: Array` cannot satisfy the guard
//! without an added axiom, so the model never assumes invokability for an arbitrary
//! `A`.
//!
//! Allocation-growth panics (capacity overflow past `isize::MAX`) are noted on each
//! spec and excluded by an additional `requires`; `SmallVec::reserve` rounds the
//! capacity up to the next power of two, so those bounds use a factor of 2.
use core::{
    ops::{Deref, DerefMut, Index, IndexMut},
    slice::SliceIndex,
};
use smallvec::{Array, SmallVec};
use vstd::{layout::size_of, prelude::*, slice::SliceIndexSpec};

verus! {

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

/// Whether `A` is a well-formed standard `Array` impl, i.e. `SmallVec::new`'s
/// construction-time validity assert holds. Only the instances in
/// `group_smallvec_models` are trusted (add an axiom there to admit new `A`s).
pub uninterp spec fn obeys_smallvec_array<A: Array>() -> bool;

/// The standard `[u64; 2]` array (the `CpuSet` backing store) is a well-formed `Array`.
pub broadcast axiom fn axiom_smallvec_array_u64_2()
    ensures
        #[trigger] obeys_smallvec_array::<[u64; 2]>(),
;

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
    axiom_smallvec_array_u64_2,
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
        ).subrange(0, new_len as int),
        new_len > smallvec_view(old(v)).len() ==> {
            &&& smallvec_view(final(v)).len() == new_len
            &&& smallvec_view(final(v)).subrange(0, smallvec_view(old(v)).len() as int)
                == smallvec_view(old(v))
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

} // verus!
