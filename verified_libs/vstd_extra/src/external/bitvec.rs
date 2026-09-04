//! Verus specifications for the third-party `bitvec` crate.
//!
//! These specifications are determined by careful inspection of the `bitvec-1.1.1`
//! source code and documentation, and are trusted as TCB. They are centralized here
//! (per the "Centralize trusted boundaries" guideline) rather than beside an OSTD
//! caller. `id-alloc` is currently the only consumer; it uses the concrete type
//! `BitVec<u8, Lsb0>`, but the methods are generic over the storage type `T` and bit
//! order `O`, so the specs keep those generic and pin only the index type.
//!
//! The abstract model of a bitmap is a `Seq<bool>`. The `BitVec`/`BitSlice` views
//! below expose that model; every executed `bitvec` operation `id-alloc` performs is
//! equated to a `Seq` operation here, so all reasoning in `id-alloc` stays at the
//! `Seq<bool>` level. The storage type and bit order do not affect the model.
//!
//! The deref, index, and `get` operations are specified with
//! `external_fn_specification` wrappers rather than `assume_specification`, because
//! `BitVec`/`BitSlice` (foreign types) deref/index through associated trait types
//! (`Deref::Target`, `Index::Output`, `BitSliceIndex::Immut`) whose reduction is
//! only matched when the wrapper pins the concrete index type and return type.
use bitvec::{
    order::{BitOrder, Lsb0},
    slice::{BitSlice, BitSliceIndex},
    store::BitStore,
    vec::BitVec,
};
use core::ops::{Deref, DerefMut, Index, Range};
use vstd::{prelude::*, std_specs::core::IndexSpec};

verus! {

/// Verus declaration for bitvec's default `Lsb0` bit order (a zero-sized marker).
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExLsb0(Lsb0);

/// Verus declaration for bitvec's `BitStore` marker trait.
#[verifier::external_trait_specification]
pub trait ExBitStore: 'static + core::fmt::Debug {
    type ExternalTraitSpecificationFor: bitvec::store::BitStore;
}

/// Verus declaration for bitvec's `BitOrder` marker trait.
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

/// A `BitVec` derefs to a `BitSlice` over exactly its own bits. Specified with
/// `assume_specification` (per-impl) so it overrides vstd's generic `Deref` trait
/// spec, which otherwise loses the `bitslice_view` connection at auto-deref call
/// sites (`bv.set(..)`, `bv.get(..)`).
pub assume_specification<'a, T: BitStore, O: BitOrder>[ <BitVec<T, O> as Deref>::deref ](
    bv: &'a BitVec<T, O>,
) -> (ret: &'a <BitVec<T, O> as Deref>::Target)
    ensures
        bitslice_view(ret) == bitvec_view(bv),
;

/// A `BitVec` derefs mutably to a `BitSlice` over exactly its own bits; a mutation
/// performed through the returned borrow is reflected in the `BitVec`'s final view.
pub assume_specification<'a, T: BitStore, O: BitOrder>[ <BitVec<T, O> as DerefMut>::deref_mut ](
    bv: &'a mut BitVec<T, O>,
) -> (ret: &'a mut <BitVec<T, O> as Deref>::Target)
    ensures
        bitslice_view(ret) == bitvec_view(old(bv)),
        bitvec_view(final(bv)) == bitslice_view(final(ret)),
;

/// Constructs an empty `BitVec` (length 0). The capacity hint is not modelled.
pub assume_specification<T: BitStore, O: BitOrder>[ BitVec::<T, O>::with_capacity ](
    capacity: usize,
) -> (ret: BitVec<T, O>)
    ensures
        bitvec_view(&ret).len() == 0,
;

/// Resizes the `BitVec` to `new_len`, filling new positions with `value` and
/// preserving existing bits up to the shorter length.
pub assume_specification<T: BitStore, O: BitOrder>[ BitVec::<T, O>::resize ](
    bv: &mut BitVec<T, O>,
    new_len: usize,
    value: bool,
) -> (ret: ())
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
) -> (ret: usize)
    ensures
        ret == bitvec_view(bv).len(),
;

/// Reads a single bit. Panics if `idx` is out of bounds. The postcondition is
/// expressed abstractly via [`bitvec_index_value`]; the `usize` instance is related
/// to the model by [`axiom_bitvec_index_usize`].
pub uninterp spec fn bitvec_index_value<'a, T: BitStore, O: BitOrder, Idx>(
    bv: &'a BitVec<T, O>,
    idx: Idx,
) -> &'a <BitVec<T, O> as Index<Idx>>::Output where BitSlice<T, O>: Index<Idx>;

#[verifier(external_fn_specification)]
pub fn bitvec_index<'a, T: BitStore, O: BitOrder, Idx>(bv: &'a BitVec<T, O>, idx: Idx) -> (ret:
    &'a <BitVec<T, O> as Index<Idx>>::Output) where BitSlice<T, O>: Index<Idx>
    ensures
        ret == bitvec_index_value(bv, idx),
{
    <BitVec<T, O> as Index<Idx>>::index(bv, idx)
}

/// For an in-bounds `usize` index, the indexed bit equals the model value.
pub broadcast axiom fn axiom_bitvec_index_usize<T: BitStore, O: BitOrder>(
    bv: &BitVec<T, O>,
    idx: usize,
)
    requires
        idx < bitvec_view(bv).len(),
    ensures
        #![trigger bitvec_index_value(bv, idx)]
        *bitvec_index_value(bv, idx) == bitvec_view(bv)[idx as int],
;

/// `BitVec`'s `Index` precondition (`index_req`) is ordinary bounds checking: the
/// index must be in `[0, len)`. vstd's generic `IndexSpec` leaves `index_req`
/// uninterpreted for the foreign `BitVec` (no `IndexSpecImpl` exists, and the orphan
/// rule forbids adding one), so this TCB axiom supplies the intended meaning —
/// exactly the condition under which `BitVec::index` does not panic.
pub broadcast axiom fn axiom_bitvec_index_req<T: BitStore, O: BitOrder>(bv: &BitVec<T, O>, i: usize)
    ensures
        #![trigger <BitVec<T, O> as IndexSpec<usize>>::index_req(bv, &i)]
        <BitVec<T, O> as IndexSpec<usize>>::index_req(bv, &i) == (i < bitvec_view(bv).len()),
;

/// A `BitVec`'s length is a `usize`, hence at most `usize::MAX`. The `len`
/// `assume_specification` only fires at exec `.len()` calls, so without this axiom
/// `bitvec_view(bv).len()` is unconstrained away from call sites (breaking overflow
/// checks like `start + offset`).
pub broadcast axiom fn axiom_bitvec_len_bound<T: BitStore, O: BitOrder>(bv: &BitVec<T, O>)
    ensures
        #![trigger bitvec_view(bv)]
        bitvec_view(bv).len() <= usize::MAX as int,
;

/// Writes a single bit. Panics if `index` is out of bounds.
pub assume_specification<T: BitStore, O: BitOrder>[ BitSlice::<T, O>::set ](
    bv: &mut BitSlice<T, O>,
    index: usize,
    value: bool,
) -> (ret: ())
    requires
        index < bitslice_view(bv).len(),
    ensures
        bitslice_view(final(bv)) == bitslice_view(old(bv)).update(index as int, value),
;

/// Borrows a part of the bit-slice (`get` is generic over the index type `I`).
/// The postcondition is expressed abstractly via [`bitslice_get_value`]; the
/// `Range<usize>` instance is related to a sub-range by [`axiom_bitslice_get_range`].
pub uninterp spec fn bitslice_get_value<'a, T: BitStore, O: BitOrder, I: BitSliceIndex<'a, T, O>>(
    bv: &BitSlice<T, O>,
    idx: I,
) -> Option<<I as BitSliceIndex<'a, T, O>>::Immut>;

#[verifier(external_fn_specification)]
pub fn bitslice_get<'a, T: BitStore, O: BitOrder, I: BitSliceIndex<'a, T, O>>(
    bv: &'a BitSlice<T, O>,
    idx: I,
) -> (ret: Option<<I as BitSliceIndex<'a, T, O>>::Immut>)
    ensures
        ret == bitslice_get_value(bv, idx),
{
    bv.get(idx)
}

/// For a valid `Range<usize>`, `get` succeeds with a bit-slice equal to the
/// corresponding sub-range of the original.
pub broadcast axiom fn axiom_bitslice_get_range<'a, T: BitStore, O: BitOrder>(
    bv: &BitSlice<T, O>,
    range: Range<usize>,
)
    requires
        0 <= range.start <= range.end <= bitslice_view(bv).len(),
    ensures
        #![trigger bitslice_get_value(bv, range)]
        match bitslice_get_value(bv, range) {
            Some(s) => bitslice_view(s) == bitslice_view(bv).subrange(
                range.start as int,
                range.end as int,
            ),
            None => false,
        },
;

/// The first index holding a `0` bit, counted from the start of the slice.
pub assume_specification<T: BitStore, O: BitOrder>[ BitSlice::<T, O>::first_zero ](
    bv: &BitSlice<T, O>,
) -> (ret: Option<usize>)
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
