//! Embedding of `Frame` lifecycle operations: allocate (`from_unused`),
//! acquire-by-paddr (`from_in_use`), and drop.
//!
//! A frame "handle" in the embedding is just a `paddr`-bearing
//! [`super::FrameEntry`] in [`super::VmStore::frames`]. The proof-side
//! ownership is in `regions.slot_owner(paddr)`
//! (refcount + perms), which the embedded axioms mutate per the
//! corresponding `_spec` helpers in [`crate::specs::mm::frame::meta_specs`].
//!
//! # Methods modeled
//!
//! - `Frame::from_unused`: allocate a fresh handle on a previously-unused slot.
//! - `Frame::from_in_use`: acquire a new handle on an already-in-use slot
//!   (refcount++).
//! - `Frame` drop (via [`crate::mm::frame::Frame`]'s `TrackDrop` impl):
//!   release one handle (refcount--).
//!
//! # Model gaps
//!
//! - **Generic `M: AnyFrameMeta`**: `Frame::from_unused` takes a
//!   `metadata: M` parameter and threads it through the slot's typed storage permission.
//!   We don't model the metadata type — `get_from_unused_spec` itself
//!   ignores `M` and just commits to `usage is Frame`.
//! - **Drop-last-in-place teardown**: when `ref_count == 1`, dropping
//!   the handle invokes the metadata destructor (which may require
//!   `storage.is_init`, `in_list.value() == 0`). We model this by
//!   carrying the relevant precondition into the drop axiom but
//!   leaving the post-state uncommitted on those fields.
use vstd::prelude::*;
use vstd_extra::ownership::*;

use crate::specs::{
    arch::*,
    mm::{
        frame::{
            mapping::frame_to_index, meta_owners::PageUsage, meta_region_owners::MetaRegionOwners,
        },
        page_table::cursor::owners::CursorOwner,
    },
};

use crate::mm::{
    Paddr,
    frame::{
        MetaSlot,
        meta::{REF_COUNT_MAX, REF_COUNT_UNIQUE, REF_COUNT_UNUSED},
    },
    vm_space::UserPtConfig,
};

use super::{FrameEntry, tracked_frame_entry_new};

verus! {

// =============================================================================
// _embedded axioms
// =============================================================================
/// Mirror of [`crate::mm::frame::Frame::from_unused`]
pub axiom fn frame_from_unused_embedded(
    tracked regions: &mut MetaRegionOwners,
    paddr: Paddr,
) -> (tracked res: Option<()>)
    requires
        old(regions).inv(),
        valid_frame_paddr(paddr) ==> old(regions).contains(frame_to_index(paddr)),
    ensures
        final(regions).inv(),
        !valid_frame_paddr(paddr) ==> res is None,
        res is Some ==> MetaSlot::get_from_unused_spec(
            paddr,
            false,
            *old(regions),
            *final(regions),
        ),
        res is Some ==> MetaSlot::slot_perm_reparked_spec(paddr, *old(regions), *final(regions)),
        // Non-interference: failure leaves `regions` unchanged.
        res is None ==> *final(regions) == *old(regions),
        forall|c: CursorOwner<'_, UserPtConfig>|
            #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
;

/// Mirror of [`crate::mm::frame::Frame::from_in_use`].
pub axiom fn frame_from_in_use_embedded(
    tracked regions: &mut MetaRegionOwners,
    paddr: Paddr,
) -> (tracked res: Option<()>)
    requires
        old(regions).inv(),
        valid_frame_paddr(paddr) ==> old(regions).contains(frame_to_index(paddr)),
    ensures
        final(regions).inv(),
        !valid_frame_paddr(paddr) ==> res is None,
        res is Some ==> MetaSlot::get_from_in_use_success(paddr, *old(regions), *final(regions)),
        res is None ==> *final(regions) == *old(regions),
        res is Some ==> {
            let so = final(regions).slot_owner(paddr);
            &&& so.ref_count() != REF_COUNT_UNUSED
            &&& so.ref_count() != REF_COUNT_UNIQUE
            &&& so.storage_perm().is_init()
            // Op::FrameFromInUse models `Frame::<dyn AnyFrameMeta>::
            // from_in_use` for data frames.
            &&& so.usage is Frame
        },
        final(regions).slots == old(regions).slots,
        forall|c: CursorOwner<'_, UserPtConfig>|
            #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
;

/// Mirror of [`crate::mm::frame::Frame`]'s `Drop::drop`.
pub axiom fn frame_drop_embedded(tracked regions: &mut MetaRegionOwners, paddr: Paddr)
    requires
        old(regions).inv(),
        old(regions).contains(frame_to_index(paddr)),
        old(regions).slot_owner(paddr).ref_count() > 0,
        old(regions).slot_owner(paddr).ref_count() != REF_COUNT_UNUSED,
        old(regions).slot_owner(paddr).ref_count() <= REF_COUNT_MAX,
        old(regions).slot_owner(paddr).ref_count() == 1 ==> {
            &&& old(regions).slot_owner(paddr).storage_perm().is_init()
            &&& old(regions).slot_owner(paddr).in_list_perm.value() == 0
            &&& old(regions).slot_owner(paddr).paths_in_pt.is_empty()
        },
    ensures
        final(regions).inv(),
        forall|i: int|
            #![trigger final(regions).slot_owners[i]]
            i != frame_to_index(paddr) ==> final(regions).slot_owners[i] == old(
                regions,
            ).slot_owners[i],
        final(regions).slots == old(regions).slots,
        final(regions).slot_owners.dom() == old(regions).slot_owners.dom(),
        final(regions).slot_owner(paddr).slot_vaddr == old(regions).slot_owner(paddr).slot_vaddr,
        final(regions).slot_owner(paddr).usage == old(regions).slot_owner(paddr).usage,
        final(regions).slot_owner(paddr).paths_in_pt == old(regions).slot_owner(paddr).paths_in_pt,
        old(regions).slot_owner(paddr).ref_count() == 1 ==> final(regions).slot_owner(
            paddr,
        ).paths_in_pt.is_empty(),
        final(regions).slot_owner(paddr).in_list_perm == old(regions).slot_owner(
            paddr,
        ).in_list_perm,
        old(regions).slot_owner(paddr).ref_count() == 1 ==> final(regions).slot_owner(
            paddr,
        ).paths_in_pt.is_empty(),
        final(regions).slot_owner(paddr).in_list_perm == old(regions).slot_owner(
            paddr,
        ).in_list_perm,
        old(regions).slot_owner(paddr).ref_count() == 1 ==> final(regions).slot_owner(
            paddr,
        ).ref_count() == REF_COUNT_UNUSED,
        old(regions).slot_owner(paddr).ref_count() > 1 ==> final(regions).slot_owner(
            paddr,
        ).ref_count() == (old(regions).slot_owner(paddr).ref_count() - 1) as u64,
        old(regions).slot_owner(paddr).ref_count() > 1 ==> final(regions).slot_owner(
            paddr,
        ).storage_perm() == old(regions).slot_owner(paddr).storage_perm(),
        // ---- embedding inv chaining ----
        forall|c: CursorOwner<'_, UserPtConfig>|
            #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
;

// =============================================================================
// step proofs
// =============================================================================
/// Per-op step for `Op::FrameFromUnused`.
pub(super) proof fn from_unused_step(
    tracked regions: &mut MetaRegionOwners,
    paddr: Paddr,
) -> (tracked res: Option<FrameEntry>)
    requires
        old(regions).inv(),
        valid_frame_paddr(paddr) ==> old(regions).contains(frame_to_index(paddr)),
    ensures
        final(regions).inv(),
        !valid_frame_paddr(paddr) ==> res is None,
        res matches Some(e) ==> e.paddr == paddr,
        res is Some ==> MetaSlot::get_from_unused_spec(
            paddr,
            false,
            *old(regions),
            *final(regions),
        ),
        res is Some ==> MetaSlot::slot_perm_reparked_spec(paddr, *old(regions), *final(regions)),
        res is None ==> *final(regions) == *old(regions),
        forall|c: CursorOwner<'_, UserPtConfig>|
            #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
{
    let tracked outcome = frame_from_unused_embedded(regions, paddr);
    match outcome {
        Option::Some(()) => Option::Some(tracked_frame_entry_new(paddr)),
        Option::None => Option::None,
    }
}

/// Per-op step for `Op::FrameFromInUse`.
pub(super) proof fn from_in_use_step(
    tracked regions: &mut MetaRegionOwners,
    paddr: Paddr,
) -> (tracked res: Option<FrameEntry>)
    requires
        old(regions).inv(),
        valid_frame_paddr(paddr) ==> old(regions).contains(frame_to_index(paddr)),
    ensures
        final(regions).inv(),
        !valid_frame_paddr(paddr) ==> res is None,
        res matches Some(e) ==> e.paddr == paddr,
        res is Some ==> MetaSlot::get_from_in_use_success(paddr, *old(regions), *final(regions)),
        res is None ==> *final(regions) == *old(regions),
        // 2b: surface the acquired slot's liveness — see
        // [`frame_from_in_use_embedded`].
        res is Some ==> {
            let so = final(regions).slot_owner(paddr);
            &&& so.ref_count() != REF_COUNT_UNUSED
            &&& so.ref_count() != REF_COUNT_UNIQUE
            &&& so.storage_perm().is_init()
            &&& so.usage is Frame
        },
        final(regions).slots == old(regions).slots,
        forall|c: CursorOwner<'_, UserPtConfig>|
            #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
{
    let tracked outcome = frame_from_in_use_embedded(regions, paddr);
    match outcome {
        Option::Some(()) => Option::Some(tracked_frame_entry_new(paddr)),
        Option::None => Option::None,
    }
}

/// `Op::FrameDrop` precondition over the slot at `paddr`. Mirrors
/// `Frame::drop_requires`.
pub open spec fn drop_pre(regions: MetaRegionOwners, paddr: Paddr) -> bool {
    let so = regions.slot_owner(paddr);
    &&& regions.contains(frame_to_index(paddr))
    &&& so.ref_count() > 0
    &&& so.ref_count() != REF_COUNT_UNUSED
    &&& so.ref_count() <= REF_COUNT_MAX
    &&& so.ref_count() == 1 ==> {
        &&& so.storage_perm().is_init()
        &&& so.in_list_perm.value() == 0
        &&& so.paths_in_pt.is_empty()
    }
}

/// Per-op step for `Op::FrameDrop`.
pub(super) proof fn drop_step(tracked regions: &mut MetaRegionOwners, tracked entry: FrameEntry)
    requires
        old(regions).inv(),
        drop_pre(*old(regions), entry.paddr),
    ensures
        final(regions).inv(),
        final(regions).slots == old(regions).slots,
        forall|i: int|
            #![trigger final(regions).slot_owners[i]]
            i != frame_to_index(entry.paddr) ==> final(regions).slot_owners[i] == old(
                regions,
            ).slot_owners[i],
        final(regions).slot_owner(entry.paddr).in_list_perm == old(regions).slot_owner(
            entry.paddr,
        ).in_list_perm,
        final(regions).slot_owner(entry.paddr).usage == old(regions).slot_owner(entry.paddr).usage,
        final(regions).slot_owner(entry.paddr).paths_in_pt == old(regions).slot_owner(
            entry.paddr,
        ).paths_in_pt,
        old(regions).slot_owner(entry.paddr).ref_count() == 1 ==> final(regions).slot_owner(
            entry.paddr,
        ).paths_in_pt.is_empty(),
        old(regions).slot_owner(entry.paddr).ref_count() == 1 ==> final(regions).slot_owner(
            entry.paddr,
        ).ref_count() == REF_COUNT_UNUSED,
        old(regions).slot_owner(entry.paddr).ref_count() > 1 ==> final(regions).slot_owner(
            entry.paddr,
        ).ref_count() == (old(regions).slot_owner(entry.paddr).ref_count() - 1) as u64,
        old(regions).slot_owner(entry.paddr).ref_count() > 1 ==> final(regions).slot_owner(
            entry.paddr,
        ).storage_perm() == old(regions).slot_owner(entry.paddr).storage_perm(),
        forall|c: CursorOwner<'_, UserPtConfig>|
            #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
{
    frame_drop_embedded(regions, entry.paddr);
}

} // verus!
