//! Embedding of `UniqueFrame` lifecycle operations: allocate
//! ([`unique_from_unused_embedded`]) and drop
//! ([`unique_drop_embedded`]).
//!
//! A `UniqueFrame` handle in the embedding is a `paddr`-bearing
//! [`super::UniqueEntry`] in [`super::VmStore::unique_frames`]. Unlike a
//! shared [`super::FrameEntry`], a unique handle drives its slot's
//! `ref_count` to the `REF_COUNT_UNIQUE` sentinel (`u64::MAX - 1`),
//! which is *not* a participant in the `rc == H + P + cover_count`
//! accounting equation. Exclusivity (`rc == REF_COUNT_UNIQUE ⟹ no
//! shared users`: `handle_count == 0`, `paths_in_pt` empty,
//! `segment_cover_count == 0`) needs **no** dedicated invariant clause:
//! it is *implied* by the equation itself — a user at a `usage == Frame`
//! slot fires the equation's antecedent and demands `rc != UNIQUE`,
//! contradicting `rc == UNIQUE`. So [`unique_drop_embedded`]'s caller
//! recovers the "no users" facts by deriving that contradiction.
//!
//! # Methods modeled
//!
//! - `UniqueFrame::from_unused`: allocate a fresh exclusive handle on a
//!   previously-unused slot. The slot transitions
//!   `usage == Unused, rc == UNUSED` → `usage == Frame, rc == UNIQUE`.
//! - `UniqueFrame` drop: tear down the exclusive handle. The slot
//!   transitions `rc == UNIQUE` → `rc == UNUSED` (last-ref teardown,
//!   uninitialising storage), with `usage` / `paths_in_pt`
//!   (empty) / `in_list` preserved — the same shape as `Frame`'s
//!   last-ref teardown.
//! - `Frame::from_unique` ([`from_unique_embedded`]): convert the
//!   exclusive handle to a shared one — `rc` drops `UNIQUE → 1`,
//!   consuming the [`super::UniqueEntry`] and minting a
//!   [`super::FrameEntry`] (`H: 0 → 1`).
//! - `UniqueFrame::try_from_shared` ([`try_from_shared_embedded`]):
//!   convert a *sole-reference* shared handle (`rc == 1`) back to an
//!   exclusive one — `rc` rises `1 → UNIQUE`, consuming the
//!   `FrameEntry` and minting a `UniqueEntry`. Fallible: if the slot is
//!   not the sole reference (`rc != 1`) the CAS fails and the step is a
//!   no-op (the shared handle is returned unchanged).
//!
//! # Model gaps
//!
//! - **`into_raw` / `from_raw`** (`pub(crate)`-only) and the accessors
//!   (`meta` / `meta_mut` / `repurpose` / `transmute` /
//!   `start_paddr`): no embedding state change / not surfaced.
use vstd::prelude::*;

use vstd_extra::ownership::*;

use crate::specs::{
    arch::has_safe_slot,
    mm::{
        frame::{
            mapping::frame_to_index, meta_owners::PageUsage, meta_region_owners::MetaRegionOwners,
        },
        page_table::cursor::owners::CursorOwner,
    },
};

use crate::mm::{
    frame::meta::{REF_COUNT_UNIQUE, REF_COUNT_UNUSED},
    vm_space::UserPtConfig,
    Paddr,
};

verus! {

// =============================================================================
// _embedded axioms
// =============================================================================
/// Mirror of [`crate::mm::frame::UniqueFrame::from_unused`]. The slot at
/// `paddr` transitions from a free slot (`usage == Unused`,
/// `rc == REF_COUNT_UNUSED`) to an exclusively-held one
/// (`usage == Frame`, `rc == REF_COUNT_UNIQUE`), with its metadata
/// storage initialised, `in_list == 0`, and `paths_in_pt` preserved
/// (it was empty — a free slot has no mappings). The slot perm is
/// re-parked in `regions.slots` (Design B; the exec
/// `slots.tracked_insert` at unique.rs:100), so the `slots` domain is
/// preserved.
///
/// **Preconditions** mirror the exec contract (`usage is Unused`) plus
/// the embedding-natural `rc == REF_COUNT_UNUSED` (which delivers, via
/// [`super::accounting_inv`] clause 1, the "no users" facts needed to
/// re-establish clause 0 at the freshly-UNIQUE slot).
pub axiom fn unique_from_unused_embedded(tracked regions: &mut MetaRegionOwners, paddr: Paddr)
    requires
        old(regions).inv(),
        has_safe_slot(paddr),
        old(regions).slots.contains_key(frame_to_index(paddr)),
        old(regions).slot_owners[frame_to_index(paddr)].usage is Unused,
        old(regions).slot_owners[frame_to_index(paddr)].inner_perms.ref_count.value()
            == REF_COUNT_UNUSED,
    ensures
        final(regions).inv(),
        // Design-B re-park: `slots` domain preserved.
        final(regions).slots =~= old(regions).slots,
        // At `paddr`: UNUSED slot becomes a UNIQUE Frame slot.
        {
            let idx = frame_to_index(paddr);
            let so_old = old(regions).slot_owners[idx];
            let so_new = final(regions).slot_owners[idx];
            &&& so_new.usage == PageUsage::Frame
            &&& so_new.inner_perms.ref_count.value() == REF_COUNT_UNIQUE
            &&& so_new.inner_perms.in_list.value() == 0
            &&& so_new.inner_perms.storage.is_init()
            &&& so_new.paths_in_pt == so_old.paths_in_pt
            &&& so_new.slot_vaddr == so_old.slot_vaddr
        },
        // All other slots fully preserved.
        forall|i: int|
            #![trigger final(regions).slot_owners[i]]
            i != frame_to_index(paddr) ==> final(regions).slot_owners[i] == old(
                regions,
            ).slot_owners[i],
        forall|c: CursorOwner<'_, UserPtConfig>| #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
;

/// Mirror of [`crate::mm::frame::UniqueFrame`]'s `drop`. The sole
/// exclusive handle is released: the slot transitions
/// `rc == REF_COUNT_UNIQUE` → `rc == REF_COUNT_UNUSED` (last-ref
/// teardown via `drop_last_in_place`, uninitialising storage), with
/// `usage`, `paths_in_pt` (empty), `in_list` (0), and `slot_vaddr`
/// preserved.
///
/// **Preconditions** mirror `UniqueFrame::wf_with_region` (the parts
/// expressible at the `regions` level): the slot is UNIQUE with
/// `in_list == 0`, initialised storage, and no PTE mappings
/// (`paths_in_pt.is_empty()`).
pub axiom fn unique_drop_embedded(tracked regions: &mut MetaRegionOwners, paddr: Paddr)
    requires
        old(regions).inv(),
        old(regions).slots.contains_key(frame_to_index(paddr)),
        old(regions).slot_owners[frame_to_index(paddr)].inner_perms.ref_count.value()
            == REF_COUNT_UNIQUE,
        old(regions).slot_owners[frame_to_index(paddr)].inner_perms.in_list.value() == 0,
        old(regions).slot_owners[frame_to_index(paddr)].inner_perms.storage.is_init(),
        old(regions).slot_owners[frame_to_index(paddr)].paths_in_pt.is_empty(),
    ensures
        final(regions).inv(),
        final(regions).slots =~= old(regions).slots,
        // At `paddr`: UNIQUE → UNUSED teardown; usage / paths / in_list
        // / slot_vaddr preserved.
        {
            let idx = frame_to_index(paddr);
            let so_old = old(regions).slot_owners[idx];
            let so_new = final(regions).slot_owners[idx];
            &&& so_new.inner_perms.ref_count.value() == REF_COUNT_UNUSED
            &&& so_new.usage == so_old.usage
            &&& so_new.paths_in_pt == so_old.paths_in_pt
            &&& so_new.inner_perms.in_list == so_old.inner_perms.in_list
            &&& so_new.slot_vaddr == so_old.slot_vaddr
        },
        // All other slots fully preserved.
        forall|i: int|
            #![trigger final(regions).slot_owners[i]]
            i != frame_to_index(paddr) ==> final(regions).slot_owners[i] == old(
                regions,
            ).slot_owners[i],
        forall|c: CursorOwner<'_, UserPtConfig>| #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
;

/// Mirror of [`crate::mm::frame::Frame::from_unique`]. Converts the
/// exclusive handle at `paddr` into a shared one: `rc` drops from the
/// `REF_COUNT_UNIQUE` sentinel to 1, with `usage` (Frame),
/// `paths_in_pt` (empty), `in_list` (0), `storage`, `vtable_ptr`, and
/// `slot_vaddr` preserved (only the count `store` runs). `metaregion_sound`
/// is preserved: a UNIQUE slot has no live PTE (a mapping is a
/// reference), so no cursor's `OwnerSubtree` maps it, and dropping the
/// count to 1 keeps it referenced.
pub axiom fn from_unique_embedded(tracked regions: &mut MetaRegionOwners, paddr: Paddr)
    requires
        old(regions).inv(),
        old(regions).slots.contains_key(frame_to_index(paddr)),
        old(regions).slot_owners[frame_to_index(paddr)].inner_perms.ref_count.value()
            == REF_COUNT_UNIQUE,
    ensures
        final(regions).inv(),
        final(regions).slots =~= old(regions).slots,
        {
            let idx = frame_to_index(paddr);
            let so_old = old(regions).slot_owners[idx];
            let so_new = final(regions).slot_owners[idx];
            &&& so_new.inner_perms.ref_count.value() == 1
            &&& so_new.usage == so_old.usage
            &&& so_new.paths_in_pt == so_old.paths_in_pt
            &&& so_new.inner_perms.in_list == so_old.inner_perms.in_list
            &&& so_new.inner_perms.storage == so_old.inner_perms.storage
            &&& so_new.slot_vaddr == so_old.slot_vaddr
        },
        forall|i: int|
            #![trigger final(regions).slot_owners[i]]
            i != frame_to_index(paddr) ==> final(regions).slot_owners[i] == old(
                regions,
            ).slot_owners[i],
        forall|c: CursorOwner<'_, UserPtConfig>| #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
;

/// Mirror of [`crate::mm::frame::UniqueFrame::try_from_shared`]'s
/// *success* path (the CAS `1 → REF_COUNT_UNIQUE` succeeded). The slot
/// transitions from a sole-reference shared frame (`rc == 1`,
/// `usage == Frame`, no PTE) to an exclusive UNIQUE one, with `usage`,
/// `paths_in_pt` (empty), `in_list` (0), `storage`, `vtable_ptr`, and
/// `slot_vaddr` preserved. (The failure path — `rc != 1` — leaves
/// `regions` untouched and is modeled in the step as a no-op.)
pub axiom fn try_from_shared_embedded(tracked regions: &mut MetaRegionOwners, paddr: Paddr)
    requires
        old(regions).inv(),
        old(regions).slots.contains_key(frame_to_index(paddr)),
        old(regions).slot_owners[frame_to_index(paddr)].inner_perms.ref_count.value() == 1,
        old(regions).slot_owners[frame_to_index(paddr)].usage == PageUsage::Frame,
        old(regions).slot_owners[frame_to_index(paddr)].paths_in_pt.is_empty(),
    ensures
        final(regions).inv(),
        final(regions).slots =~= old(regions).slots,
        {
            let idx = frame_to_index(paddr);
            let so_old = old(regions).slot_owners[idx];
            let so_new = final(regions).slot_owners[idx];
            &&& so_new.inner_perms.ref_count.value() == REF_COUNT_UNIQUE
            &&& so_new.usage == so_old.usage
            &&& so_new.paths_in_pt == so_old.paths_in_pt
            &&& so_new.inner_perms.in_list == so_old.inner_perms.in_list
            &&& so_new.inner_perms.storage == so_old.inner_perms.storage
            &&& so_new.slot_vaddr == so_old.slot_vaddr
        },
        forall|i: int|
            #![trigger final(regions).slot_owners[i]]
            i != frame_to_index(paddr) ==> final(regions).slot_owners[i] == old(
                regions,
            ).slot_owners[i],
        forall|c: CursorOwner<'_, UserPtConfig>| #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
;

} // verus!
