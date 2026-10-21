//! Trusted claims about reparameterizing a frame handle's metadata type.
//!
//! Three kinds of claim, kept apart on purpose:
//!
//! - **Permitted** — `can_transmute` for one pair of metadata types. Supplied only
//!   for the pairs this crate actually casts between, so a
//!   pair with no axiom here cannot be transmuted at all.
//! - **Produced** — what the resulting handle looks like, as a struct literal. A
//!   layout claim about the compiled struct, and nothing more.
//! - **Ownership** — what the cast does to the permission the handle carries
//!   ([`reparam_perm`] and the `axiom_reparam_perm_*` family).
//!
//! None of these is an identity claim. That the slot *really holds* the target type
//! is established per call site — by `is_::<M>` for the frame downcast, by
//! `UniqueFrame::transmute_requires` for a repurpose, by a slot read for the
//! segment downcast.
//!
//! One axiom is missing from this file: `axiom_segment_reparam` stays in
//! `mm::frame::segment`. It states its conclusion as a `Segment` struct literal,
//! and `Segment`'s fields are private — a publicly visible spec signature may not
//! construct a datatype whose fields are not equally visible. `Frame` and
//! `UniqueFrame` have `pub` fields, which is why their counterparts could move.
use vstd::prelude::*;
use vstd_extra::{
    ownership::OwnerOf,
    transmute::{can_transmute, transmuted},
};

use core::marker::PhantomData;

use crate::mm::frame::{AnyFrameMeta, Frame, UniqueFrame};
#[cfg(feature = "dyn_supertrait")]
use crate::mm::frame::{segment::Segment, untyped::AnyUFrameMeta};
use crate::specs::mm::frame::{
    frame_specs::FrameRawPerms,
    meta_owners::{FracMetadataPerm, MetaSlotStorage, MetadataPerm, recorded_meta_id},
};

verus! {

// ---------------------------------------------------------------------------
// Ownership: what a cast does to the permission
// ---------------------------------------------------------------------------
/// How a permission is reinterpreted when a handle is reparameterized from
/// metadata type `A` to metadata type `B`. Uninterpreted and axiomatized
/// for individual pairs `A` and `B`.
///
/// `P` is the permission itself, not the `Tracked<Option<_>>` a handle stores it
/// in: `FracMetadataPerm` for `Frame`, `MetadataPerm` for `UniqueFrame`,
/// `Seq<FrameRawPerms>` for `Segment`. The reparam axioms below do the unwrapping.
pub uninterp spec fn reparam_perm<A: ?Sized, B: ?Sized, P>(p: P) -> P;

/// Erasing a sized metadata type leaves the permission alone.
pub axiom fn axiom_reparam_perm_erase<M: AnyFrameMeta>(p: FracMetadataPerm)
    ensures
        reparam_perm::<M, dyn AnyFrameMeta, FracMetadataPerm>(p) == p,
;

/// Recovering a metadata type from an erased handle leaves the permission alone.
pub axiom fn axiom_reparam_perm_recover<M: AnyFrameMeta>(p: FracMetadataPerm)
    ensures
        reparam_perm::<dyn AnyFrameMeta, M, FracMetadataPerm>(p) == p,
;

/// Reparameterizing between two sized metadata types also converts the permission.
pub axiom fn axiom_reparam_perm_between<A: AnyFrameMeta, B: AnyFrameMeta>(p: MetadataPerm)
    ensures
        reparam_perm::<A, B, MetadataPerm>(p) == (MetadataPerm {
            storage_perm: p.storage_perm,
            vtable_ptr_perm: p.vtable_ptr_perm,
            meta_type_id: recorded_meta_id::<B>(),
        }),
;

/// Erasing an *untyped* metadata type leaves the permission alone.
#[cfg(feature = "dyn_supertrait")]
pub axiom fn axiom_reparam_perm_erase_untyped<M: AnyUFrameMeta>(p: Seq<FrameRawPerms>)
    ensures
        reparam_perm::<M, dyn AnyUFrameMeta, Seq<FrameRawPerms>>(p) == p,
;

/// Narrowing an erased handle to the untyped erasure leaves the permission alone.
#[cfg(all(feature = "type_id", feature = "dyn_supertrait"))]
pub axiom fn axiom_reparam_perm_narrow_untyped(p: Seq<FrameRawPerms>)
    ensures
        reparam_perm::<dyn AnyFrameMeta, dyn AnyUFrameMeta, Seq<FrameRawPerms>>(p) == p,
;

// ---------------------------------------------------------------------------
// Frame
// ---------------------------------------------------------------------------
/// What reparameterizing a frame handle's metadata type produces.
///
/// Describes a transmute rather than licensing one: `can_transmute` is a
/// *precondition* here, supplied for the pairs we actually permit by
/// [`axiom_frame_erase_transmutable`] and [`axiom_frame_recover_transmutable`].
/// Stating it as a conclusion instead would have made every `Frame<A>` to
/// `Frame<B>` transmute available for the asking.
///
/// The layout claim is about the *compiled* struct. `Frame<M>` is a
/// `PPtr<MetaSlot>` beside a `PhantomData<M>` and two `Tracked` fields, and ghost
/// and tracked fields are erased at compile time -- so what actually exists at
/// runtime is one pointer, identically for every `M`. `Frame` cannot carry
/// `#[repr(transparent)]`, because rustc will not count `Ghost`/`Tracked` fields
/// as trivially zero-sized; that is an attribute-level refusal, not a layout fact,
/// and the layout fact is what this asserts. If `Frame` ever gains a second *exec*
/// field, this becomes false.
///
/// The slot permission carries across unchanged, which is well-typed because
/// `PointsTo<MetaSlot>` does not mention `M`. The metadata permission does not: it
/// is reinterpreted by [`reparam_perm`], collapsed by whichever
/// `axiom_reparam_perm_*` covers the pair.
#[verifier::external_body]
pub proof fn axiom_frame_reparam<A: ?Sized, B: ?Sized>(f: Frame<A>)
    requires
        can_transmute::<Frame<A>, Frame<B>>(f),
    ensures
        transmuted::<Frame<A>, Frame<B>>(f) == (Frame::<B> {
            ptr: f.ptr,
            _marker: PhantomData,
            #[cfg(verus_keep_ghost_body)]
            tracked_slot_perm: f.tracked_slot_perm,
            #[cfg(verus_keep_ghost_body)]
            tracked_metadata_perm: Tracked(
                match f.tracked_metadata_perm@ {
                    Some(p) => Some(reparam_perm::<A, B, FracMetadataPerm>(p)),
                    None => None,
                },
            ),
        }),
{
}

/// Erasing a frame's metadata type is a valid transmute.
///
/// The layout argument is [`axiom_frame_reparam`]'s: `M` appears in `Frame<M>`
/// only under a `PhantomData` and in ghost fields, so erasing it to
/// `dyn AnyFrameMeta` leaves one `PPtr<MetaSlot>` on both sides. `M` is sized and
/// bounded by `AnyFrameMeta`, so the coercion is one Rust would accept.
#[verifier::external_body]
pub proof fn axiom_frame_erase_transmutable<M: AnyFrameMeta>(f: Frame<M>)
    ensures
        can_transmute::<Frame<M>, Frame<dyn AnyFrameMeta>>(f),
{
}

/// Recovering a static metadata type from an erased frame is a valid transmute.
///
/// The converse of [`axiom_frame_erase_transmutable`].
#[verifier::external_body]
pub proof fn axiom_frame_recover_transmutable<M: AnyFrameMeta>(f: Frame<dyn AnyFrameMeta>)
    ensures
        can_transmute::<Frame<dyn AnyFrameMeta>, Frame<M>>(f),
{
}

// ---------------------------------------------------------------------------
// UniqueFrame
// ---------------------------------------------------------------------------
/// What reparameterizing a unique handle's metadata type produces.
///
/// The [`axiom_frame_reparam`] counterpart, and the same shape: a
/// `UniqueFrame<M>` is a `PPtr<MetaSlot>` beside a `PhantomData<M>` and two ghost
/// fields, so what is actually there is one pointer regardless of `M`.
///
/// Representation only. That the slot holds a `B` is an identity claim this does
/// not make -- `UniqueFrame::transmute_requires` is where that lives.
#[verifier::external_body]
pub proof fn axiom_unique_frame_reparam<A: AnyFrameMeta + OwnerOf, B: AnyFrameMeta + OwnerOf>(
    f: UniqueFrame<A>,
)
    requires
        can_transmute::<UniqueFrame<A>, UniqueFrame<B>>(f),
    ensures
        transmuted::<UniqueFrame<A>, UniqueFrame<B>>(f) == (UniqueFrame::<B> {
            ptr: f.ptr,
            _marker: PhantomData,
            #[cfg(verus_keep_ghost_body)]
            tracked_slot_perm: f.tracked_slot_perm,
            #[cfg(verus_keep_ghost_body)]
            tracked_metadata_perm: Tracked(
                match f.tracked_metadata_perm@ {
                    Some(p) => Some(reparam_perm::<A, B, MetadataPerm>(p)),
                    None => None,
                },
            ),
        }),
{
}

/// Reparameterizing a unique handle between two sized metadata types is a valid
/// transmute.
///
/// One axiom rather than the frame layer's erase/recover pair, because there is one
/// shape here: both sides are sized, and `repurpose` may install any metadata type
/// it likes. The breadth is safe precisely because this says nothing about *which*
/// type the slot holds -- `UniqueFrame::transmute_requires` is what stops the
/// reparameterization being useful at the wrong one.
#[verifier::external_body]
pub proof fn axiom_unique_frame_transmutable<A: AnyFrameMeta + OwnerOf, B: AnyFrameMeta + OwnerOf>(
    f: UniqueFrame<A>,
)
    ensures
        can_transmute::<UniqueFrame<A>, UniqueFrame<B>>(f),
{
}

// ---------------------------------------------------------------------------
// Segment
// ---------------------------------------------------------------------------
//
// `axiom_segment_reparam` -- the "produced" claim -- is not here; see the module
// doc. These two are the "permitted" claims, which mention no fields.
/// Erasing a segment's metadata type is a valid transmute.
///
/// `Segment<M>` is a `Range<Paddr>` beside a `PhantomData<M>` and one tracked
/// field, so erasing `M` leaves the range alone.
///
/// Narrower than the frame pair: `AnyUFrameMeta` rather than `AnyFrameMeta`,
/// because `USegment` is `Segment<dyn AnyUFrameMeta>` and that is the single
/// erasure segments perform.
#[cfg(feature = "dyn_supertrait")]
#[verifier::external_body]
pub proof fn axiom_segment_erase_transmutable<M: AnyUFrameMeta>(s: Segment<M>)
    ensures
        can_transmute::<Segment<M>, Segment<dyn AnyUFrameMeta>>(s),
{
}

/// An untyped homogeneous segment may be viewed as a `USegment`.
///
/// The one claim in the segment downcast that is not proved. Both sides are `dyn`,
/// so this is not the sized erasure [`axiom_segment_erase_transmutable`] covers;
/// here untypedness is a runtime fact, and the precondition is discharged by a
/// read of the slot rather than assumed. Layout is not at issue --
/// `axiom_segment_reparam` covers that -- so what is trusted is the metadata claim
/// alone.
///
/// The `len() == 0` disjunct is not a weakening: an empty segment owns no frames,
/// so there is no metadata to misinterpret.
#[cfg(all(feature = "type_id", feature = "dyn_supertrait"))]
#[verifier::external_body]
pub proof fn axiom_segment_untyped_transmutable(s: Segment<dyn AnyFrameMeta>)
    requires
        s.len() == 0 || s.is_untyped(),
    ensures
        can_transmute::<Segment<dyn AnyFrameMeta>, Segment<dyn AnyUFrameMeta>>(s),
{
}

} // verus!
