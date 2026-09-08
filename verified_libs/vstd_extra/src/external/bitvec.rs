//! Verus specifications for the third-party `bitvec` crate, trusted as TCB from
//! inspection of the `bitvec-1.0.1` source (`store.rs`, `order.rs`,
//! `vec/{api,ops}.rs`, `slice/{api,ops}.rs`) and centralized here rather than beside
//! an OSTD caller. `id-alloc` is currently the only consumer (`BitVec<u8, Lsb0>`).
//!
//! Contracts are admitted only for trusted primitive storage (`u8`, `u32`, `usize`,
//! `u64` on 64-bit, with `Lsb0`). `BitStore` alone is insufficient: `Cell`, atomic,
//! or alias-safe storage can mutate through a shared reference, and implementing the
//! external traits grants no model guarantees. Contracts are therefore guarded by an
//! uninterpreted model predicate assumed only for those instances; primitive storage
//! has `Mem = Self` and `Unalias = Self` (its internal `Access`/`Alias` types are not
//! admitted).
//!
//! The model is a `Seq<bool>`; the views below equate every executed `bitvec`
//! operation to a `Seq` operation, so all reasoning in `id-alloc` stays at the
//! `Seq<bool>` level.
use bitvec::{
    order::{BitOrder, Lsb0},
    slice::{BitSlice, BitSliceIndex},
    store::BitStore,
    vec::BitVec,
};
use core::ops::{Deref, DerefMut, Index, Range};
use vstd::{prelude::*, std_specs::core::IndexSpec};

macro_rules! bitvec_model_axiom {
    ($name:ident, $t:ty) => {
        ::vstd::prelude::verus! {
            pub broadcast axiom fn $name()
                ensures
                    #[trigger] obeys_bitvec_model::<$t, Lsb0>(),
            ;
        }
};
}

// Keep instances separate so pruning an unused type does not remove the others.
bitvec_model_axiom!(axiom_u8_bitvec_model, u8);
bitvec_model_axiom!(axiom_u32_bitvec_model, u32);
bitvec_model_axiom!(axiom_usize_bitvec_model, usize);
#[cfg(target_pointer_width = "64")]
bitvec_model_axiom!(axiom_u64_bitvec_model, u64);

verus! {

/// Verus declaration for bitvec's default `Lsb0` bit order (a zero-sized marker).
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExLsb0(Lsb0);

/// Type-level declaration only; this does not assume any `BitStore` semantics.
#[verifier::external_trait_specification]
pub trait ExBitStore: 'static + core::fmt::Debug {
    type ExternalTraitSpecificationFor: bitvec::store::BitStore;
}

/// Type-level declaration only; this does not assume any `BitOrder` semantics.
#[verifier::external_trait_specification]
pub trait ExBitOrder: 'static {
    type ExternalTraitSpecificationFor: bitvec::order::BitOrder;
}

/// Verus declaration for bitvec's `BitSliceIndex` trait. Only the associated types
/// are surfaced; `id-alloc` uses the `Range<usize>` instance, whose `Immut` is a
/// `&BitSlice`.
#[verifier::external_trait_specification]
pub trait ExBitSliceIndex<'a, T: BitStore, O: BitOrder> {
    type ExternalTraitSpecificationFor: BitSliceIndex<'a, T, O>;

    type Immut;

    type Mut;
}

/// Opaque external wrapper for the owned bitmap type.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(O)]
pub struct ExBitVec<T: BitStore, O: BitOrder>(BitVec<T, O>);

/// Opaque external wrapper for the borrowed bit-slice type.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(O)]
pub struct ExBitSlice<T: BitStore, O: BitOrder>(BitSlice<T, O>);

/// The full bitmap, modelled as a sequence of booleans.
pub uninterp spec fn bitvec_view<T: BitStore, O: BitOrder>(b: &BitVec<T, O>) -> Seq<bool>;

/// The content of a borrowed bit-slice, modelled as a sequence of booleans.
pub uninterp spec fn bitslice_view<T: BitStore, O: BitOrder>(b: &BitSlice<T, O>) -> Seq<bool>;

/// Whether storage and order support the immutable sequence model. Only the
/// concrete instances in `group_bitvec_models` are trusted below.
pub uninterp spec fn obeys_bitvec_model<T: BitStore, O: BitOrder>() -> bool;

/// The only index and `get` specializations covered by this bridge.
pub uninterp spec fn obeys_bitslice_index_model<T: BitStore, O: BitOrder, Idx>() -> bool where
    BitSlice<T, O>: Index<Idx>,
;

pub uninterp spec fn obeys_bitslice_get_model<'a, T: BitStore, O: BitOrder, I>() -> bool where
    I: BitSliceIndex<'a, T, O>,
;

pub broadcast axiom fn axiom_usize_bitslice_index_model<T: BitStore, O: BitOrder>()
    requires
        obeys_bitvec_model::<T, O>(),
    ensures
        #[trigger] obeys_bitslice_index_model::<T, O, usize>(),
;

pub broadcast axiom fn axiom_range_bitslice_get_model<'a, T: BitStore, O: BitOrder>()
    requires
        obeys_bitvec_model::<T, O>(),
    ensures
        #[trigger] obeys_bitslice_get_model::<'a, T, O, Range<usize>>(),
;

pub broadcast group group_bitvec_models {
    axiom_u8_bitvec_model,
    axiom_u32_bitvec_model,
    axiom_usize_bitvec_model,
    axiom_usize_bitslice_index_model,
    axiom_range_bitslice_get_model,
    #[cfg(target_pointer_width = "64")]
    axiom_u64_bitvec_model,
}

/// Derefs to a `BitSlice` over exactly the `BitVec`'s own bits.
pub assume_specification<'a, T: BitStore, O: BitOrder>[ <BitVec<T, O> as Deref>::deref ](
    bv: &'a BitVec<T, O>,
) -> (ret: &'a <BitVec<T, O> as Deref>::Target)
    ensures
        obeys_bitvec_model::<T, O>() ==> bitslice_view(ret) == bitvec_view(bv),
;

/// A `BitVec` derefs mutably to a `BitSlice` over exactly its own bits; a mutation
/// performed through the returned borrow is reflected in the `BitVec`'s final view.
pub assume_specification<'a, T: BitStore, O: BitOrder>[ <BitVec<T, O> as DerefMut>::deref_mut ](
    bv: &'a mut BitVec<T, O>,
) -> (ret: &'a mut <BitVec<T, O> as Deref>::Target)
    ensures
        obeys_bitvec_model::<T, O>() ==> {
            &&& bitslice_view(ret) == bitvec_view(old(bv))
            &&& bitvec_view(final(bv)) == bitslice_view(final(ret))
        },
;

/// Constructs an empty `BitVec` (length 0). The capacity hint is not modelled.
/// Panics if `capacity` exceeds `BitSlice::<T, O>::MAX_BITS` (= `usize::MAX >> 3`);
/// callers must keep `capacity` within that bound.
pub assume_specification<T: BitStore, O: BitOrder>[ BitVec::<T, O>::with_capacity ](
    capacity: usize,
) -> (ret: BitVec<T, O>)
    requires
        obeys_bitvec_model::<T, O>(),
        capacity <= usize::MAX / 8,
    ensures
        bitvec_view(&ret).len() == 0,
;

/// Resizes the `BitVec` to `new_len`, filling new positions with `value` and
/// preserving existing bits up to the shorter length. Panics if `new_len` exceeds
/// `BitSlice::<T, O>::MAX_BITS` (= `usize::MAX >> 3`).
pub assume_specification<T: BitStore, O: BitOrder>[ BitVec::<T, O>::resize ](
    bv: &mut BitVec<T, O>,
    new_len: usize,
    value: bool,
)
    requires
        obeys_bitvec_model::<T, O>(),
        new_len <= usize::MAX / 8,
    ensures
        bitvec_view(final(bv)).len() == new_len,
        forall|i: int|
            #![trigger bitvec_view(final(bv))[i]]
            0 <= i < new_len ==> bitvec_view(final(bv))[i] == (if i < bitvec_view(old(bv)).len() {
                bitvec_view(old(bv))[i]
            } else {
                value
            }),
;

/// The number of bits.
pub assume_specification<T: BitStore, O: BitOrder>[ BitVec::<T, O>::len ](
    bv: &BitVec<T, O>,
) -> usize
    requires
        obeys_bitvec_model::<T, O>(),
    returns
        bitvec_view(bv).len() as usize,
;

/// Reads a single bit (panics if `idx` is out of bounds); the `usize` result is
/// related to the model by [`axiom_bitvec_index_usize`].
pub uninterp spec fn bitvec_index_value<'a, T: BitStore, O: BitOrder, Idx>(
    bv: &'a BitVec<T, O>,
    idx: Idx,
) -> &'a <BitVec<T, O> as Index<Idx>>::Output where BitSlice<T, O>: Index<Idx>;

pub assume_specification<'a, T: BitStore, O: BitOrder, Idx>[ <BitVec<T, O> as Index<Idx>>::index ](
    bv: &'a BitVec<T, O>,
    idx: Idx,
) -> (ret: &'a <BitVec<T, O> as Index<Idx>>::Output) where BitSlice<T, O>: Index<Idx>
    ensures
        obeys_bitvec_model::<T, O>() && obeys_bitslice_index_model::<T, O, Idx>() ==> ret
            == bitvec_index_value(bv, idx),
;

/// The indexed `usize` bit equals the model value.
pub broadcast axiom fn axiom_bitvec_index_usize<T: BitStore, O: BitOrder>(
    bv: &BitVec<T, O>,
    idx: usize,
)
    requires
        obeys_bitvec_model::<T, O>(),
    ensures
        #![trigger bitvec_index_value(bv, idx)]
        *bitvec_index_value(bv, idx) == bitvec_view(bv)[idx as int],
;

/// `BitVec`'s `Index` precondition (`index_req`): the index must be in `[0, len)`,
/// the condition under which `BitVec::index` does not panic.
pub broadcast axiom fn axiom_bitvec_index_req<T: BitStore, O: BitOrder>(bv: &BitVec<T, O>, i: usize)
    requires
        obeys_bitvec_model::<T, O>(),
    ensures
        #![trigger <BitVec<T, O> as IndexSpec<usize>>::index_req(bv, &i)]
        <BitVec<T, O> as IndexSpec<usize>>::index_req(bv, &i) == (i < bitvec_view(bv).len()),
;

/// Bit length is bounded by `BitSlice::<T, O>::MAX_BITS` (= `usize::MAX >> 3`).
pub broadcast axiom fn axiom_bitvec_len_bound<T: BitStore, O: BitOrder>(bv: &BitVec<T, O>)
    requires
        obeys_bitvec_model::<T, O>(),
    ensures
        #![trigger bitvec_view(bv)]
        bitvec_view(bv).len() <= (usize::MAX as int) / 8,
;

/// Writes a single bit. Panics if `index` is out of bounds.
pub assume_specification<T: BitStore, O: BitOrder>[ BitSlice::<T, O>::set ](
    bv: &mut BitSlice<T, O>,
    index: usize,
    value: bool,
)
    requires
        obeys_bitvec_model::<T, O>(),
        index < bitslice_view(bv).len(),
    ensures
        bitslice_view(final(bv)) == bitslice_view(old(bv)).update(index as int, value),
;

/// Borrows a part of the bit-slice (`get` is generic over `I`); the `Range<usize>`
/// result is related to a sub-range by [`axiom_bitslice_get_range`].
pub uninterp spec fn bitslice_get_value<'a, T: BitStore, O: BitOrder, I: BitSliceIndex<'a, T, O>>(
    bv: &BitSlice<T, O>,
    idx: I,
) -> Option<<I as BitSliceIndex<'a, T, O>>::Immut>;

pub assume_specification<'a, T: BitStore, O: BitOrder, I: BitSliceIndex<'a, T, O>>[ BitSlice::<
    T,
    O,
>::get ](bv: &'a BitSlice<T, O>, idx: I) -> Option<<I as BitSliceIndex<'a, T, O>>::Immut>
    requires
        obeys_bitvec_model::<T, O>(),
        obeys_bitslice_get_model::<'a, T, O, I>(),
    returns
        bitslice_get_value(bv, idx),
;

/// For a `Range<usize>`, `get` returns `Some` of a bit-slice equal to the
/// sub-range `bitslice_view(bv).subrange(start, end)` when
/// `0 <= start <= end <= bitslice_view(bv).len()`, and `None` otherwise.
pub broadcast axiom fn axiom_bitslice_get_range<'a, T: BitStore, O: BitOrder>(
    bv: &BitSlice<T, O>,
    range: Range<usize>,
)
    requires
        obeys_bitvec_model::<T, O>(),
    ensures
        #![trigger bitslice_get_value(bv, range)]
        match bitslice_get_value(bv, range) {
            Some(s) => {
                &&& 0 <= range.start <= range.end <= bitslice_view(bv).len()
                &&& bitslice_view(s) == bitslice_view(bv).subrange(
                    range.start as int,
                    range.end as int,
                )
            },
            None => !(0 <= range.start <= range.end <= bitslice_view(bv).len()),
        },
;

/// The first index holding a `0` bit, counted from the start of the slice.
pub assume_specification<T: BitStore, O: BitOrder>[ BitSlice::<T, O>::first_zero ](
    bv: &BitSlice<T, O>,
) -> (ret: Option<usize>)
    requires
        obeys_bitvec_model::<T, O>(),
    ensures
        match ret {
            Some(j) => {
                &&& 0 <= j < bitslice_view(bv).len()
                &&& !bitslice_view(bv)[j as int]
                &&& forall|i: int|
                    #![trigger bitslice_view(bv)[i]]
                    0 <= i < j ==> bitslice_view(bv)[i]
            },
            None => forall|i: int|
                #![trigger bitslice_view(bv)[i]]
                0 <= i < bitslice_view(bv).len() ==> bitslice_view(bv)[i],
        },
;

} // verus!
