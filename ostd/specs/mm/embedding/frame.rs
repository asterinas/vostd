//! Embedding of `Frame` lifecycle operations: allocate (`from_unused`),
//! acquire-by-paddr (`from_in_use`), and drop.
//!
//! A frame "handle" in the embedding is just a `paddr`-bearing
//! [`super::FrameEntry`] in [`super::VmStore::frames`]. The proof-side
//! ownership is in `regions.slot_owners[frame_to_index_spec(paddr)]`
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
//!   `metadata: M` parameter and threads it through `PointsTo<MetaSlot, Metadata<M>>`.
//!   We don't model the metadata type — `get_from_unused_spec` itself
//!   ignores `M` and just commits to `usage == PageUsage::Frame`.
//! - **Drop-last-in-place teardown**: when `ref_count == 1`, dropping
//!   the handle invokes the metadata destructor (which may require
//!   `storage.is_init`, `in_list.value() == 0`). We model this by
//!   carrying the relevant precondition into the drop axiom but
//!   leaving the post-state uncommitted on those fields.
use vstd::prelude::*;
use vstd_extra::ownership::*;

use crate::mm::frame::{has_safe_slot, MetaSlot};
use crate::mm::vm_space::UserPtConfig;
use crate::mm::Paddr;
use crate::specs::mm::frame::mapping::frame_to_index_spec;
use crate::specs::mm::frame::meta_owners::{REF_COUNT_MAX, REF_COUNT_UNIQUE, REF_COUNT_UNUSED};
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::page_table::cursor::owners::CursorOwner;

use super::{axiom_frame_entry_new, FrameEntry};

verus! {

// =============================================================================
// _embedded axioms
// =============================================================================
/// Mirror of [`crate::mm::frame::Frame::from_unused`] (non-unique branch:
/// `as_unique = false`) **including the Design-B caller re-park**. On
/// `Some`, the slot at `paddr` transitions from `REF_COUNT_UNUSED` to
/// `1`, with `usage == Frame` and `paths_in_pt` preserved, and the
/// slot perm is re-parked into `regions.slots` (domain preserved — see
/// [`MetaSlot::get_from_unused_reparked_spec`]). The embedding *is* the
/// caller of `Frame::from_unused`, and its `FrameEntry` does not carry
/// the perm, so the modeled atomic step is "allocate + re-park".
///
/// `metaregion_sound`-preserves: any `CursorOwner` sound w.r.t. the
/// old `regions` is still sound w.r.t. the new `regions`. This is
/// because the only slot whose state changes is at `paddr`, which
/// must have been UNUSED before (and any sound cursor's `paths_in_pt`
/// can only reference non-UNUSED slots).
pub axiom fn frame_from_unused_embedded(
    tracked regions: &mut MetaRegionOwners,
    paddr: Paddr,
) -> (tracked res: Option<()>)
    requires
        old(regions).inv(),
        // `has_safe_slot`-guarded, mirroring the relaxed exec
        // `Frame::from_unused` `requires`: an out-of-bound / misaligned
        // `paddr` is not a precondition violation — it returns `Err`
        // (here `None`) without touching `regions`.
        has_safe_slot(paddr) ==> old(regions).slots.contains_key(frame_to_index_spec(paddr)),
    ensures
        final(regions).inv(),
        // Liveness, mirroring exec `!has_safe_slot(paddr) ==> r is Err`:
        // a bad `paddr` always fails (and leaves `regions` unchanged via
        // the `None` branch below).
        !has_safe_slot(paddr) ==> res is None,
        // Success branch is conditioned on the slot being unused
        // (per `get_from_unused_reparked_spec` recommends + the body's
        // `MetaSlot::get_from_unused` failing otherwise). The reparked
        // variant keeps the slot perm in `regions.slots` (Design B).
        res is Some ==> MetaSlot::get_from_unused_reparked_spec(
            paddr,
            false,
            *old(regions),
            *final(regions),
        ),
        // Non-interference: failure leaves `regions` unchanged.
        res is None ==> *final(regions) == *old(regions),
        forall|c: CursorOwner<'_, UserPtConfig>|
            #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
;

/// Mirror of [`crate::mm::frame::Frame::from_in_use`]. On `Some`,
/// `inner_perms.ref_count` increments by 1 at `frame_to_index_spec(paddr)`
/// and all other slots are preserved.
pub axiom fn frame_from_in_use_embedded(
    tracked regions: &mut MetaRegionOwners,
    paddr: Paddr,
) -> (tracked res: Option<()>)
    requires
        old(regions).inv(),
        // `has_safe_slot`-guarded, mirroring the relaxed exec
        // `Frame::from_in_use` `requires`: a bad `paddr` returns `Err`
        // (here `None`) without touching `regions`.
        has_safe_slot(paddr) ==> old(regions).slots.contains_key(
            frame_to_index_spec(paddr),
        ),
// Refcount saturation is NOT required: exec
// `MetaSlot::get_from_in_use` `panic_diverge`s on saturation
// (the real Rust panic) — see the relaxed exec `requires`. This
// axiom soundly models the returning path.

    ensures
        final(regions).inv(),
        // Liveness, mirroring exec `!has_safe_slot(paddr) ==> res is Err`.
        !has_safe_slot(paddr) ==> res is None,
        res is Some ==> MetaSlot::get_from_in_use_success(paddr, *old(regions), *final(regions)),
        res is None ==> *final(regions) == *old(regions),
        // 2b: faithful axiom-strengthening. The exec `get_from_in_use`
        // returns `Ok` only when the pre `ref_count` is a live SHARED
        // count in `[1, REF_COUNT_MAX-1]` — `UNUSED` / `UNIQUE` / `0` /
        // saturated all `Err` or `panic_diverge` — and the `Acquire`
        // compare-exchange makes the slot's written metadata visible.
        // So on `Some` the acquired slot is live (non-sentinel
        // `ref_count`) with initialised storage. `get_from_in_use_success`
        // does not surface this, and `MetaSlotOwner::inv` only gives
        // `vtable_ptr.is_init()` for SHARED slots, not `storage`.
        res is Some ==> {
            let so = final(regions).slot_owners[frame_to_index_spec(paddr)];
            &&& so.inner_perms.ref_count.value() != REF_COUNT_UNUSED
            &&& so.inner_perms.ref_count.value() != REF_COUNT_UNIQUE
            &&& so.inner_perms.storage.is_init()
        },
        // `from_in_use` only `inc_ref_count`s — it never touches the
        // slot-perm map, so the `slots` domain is preserved on *both*
        // branches (needed for `VmStore::inv`'s coverage clause).
        final(regions).slots =~= old(regions).slots,
        forall|c: CursorOwner<'_, UserPtConfig>|
            #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
;

/// Mirror of [`crate::mm::frame::Frame`]'s `Drop::drop` — the single
/// real drop, whose (now strengthened) `drop_requires` / `drop_ensures`
/// it reflects verbatim. One axiom; the refcount transition is a single
/// postcondition that covers both behaviors the exec `drop` performs:
///
/// - `old.ref_count == 1`: last-ref teardown — slot → `REF_COUNT_UNUSED`.
/// - `old.ref_count > 1`: refcount decremented by one (slot stays SHARED).
///
/// `requires` mirrors `Frame::drop_requires` (the expressible parts)
/// verbatim — no extra conjunct.
///
/// The `metaregion_sound`-preserves clause below is sound *because of
/// the refcount semantics*, not because of any caller obligation: a
/// page-table mapping is itself a reference (`reference_count()` counts
/// "all the mappings in the page table that point to the frame"). So
/// `ref_count == 1` already implies no cursor's `OwnerSubtree` maps the
/// slot — were it mapped, that mapping would push `ref_count >= 2`.
/// Hence the `ref_count == 1` UNUSED transition cannot break any
/// cursor's `EntryOwner::metaregion_sound`, and `ref_count > 1` keeps
/// the slot SHARED. (Not provable from `drop_ensures` alone, but sound
/// to assert here — same epistemic status as the other `_embedded`
/// axioms reflecting real exec behavior.)
pub axiom fn frame_drop_embedded(tracked regions: &mut MetaRegionOwners, paddr: Paddr)
    requires
        old(regions).inv(),
        old(regions).slots.contains_key(frame_to_index_spec(paddr)),
        old(regions).slot_owners[frame_to_index_spec(paddr)].raw_count == 0,
        old(regions).slot_owners[frame_to_index_spec(paddr)].inner_perms.ref_count.value() > 0,
        old(regions).slot_owners[frame_to_index_spec(paddr)].inner_perms.ref_count.value()
            != REF_COUNT_UNUSED,
        old(regions).slot_owners[frame_to_index_spec(paddr)].inner_perms.ref_count.value()
            <= REF_COUNT_MAX,
        old(regions).slot_owners[frame_to_index_spec(paddr)].inner_perms.ref_count.value() == 1
            ==> {
            &&& old(regions).slot_owners[frame_to_index_spec(paddr)].inner_perms.storage.is_init()
            &&& old(regions).slot_owners[frame_to_index_spec(paddr)].inner_perms.in_list.value()
                == 0
            // Mirrors the FUTURE-plan strengthening of exec
            // `Frame::drop_requires`: at `rc == 1` the dropped handle is
            // the sole reference, so the slot has no live PTE mappings
            // (a mapping would push `rc >= 2`). The exec demands this as
            // a precondition; the embedding's requires must mirror it
            // verbatim or the axiom is logically inconsistent on inputs
            // the exec cannot accept.
            &&& old(regions).slot_owners[frame_to_index_spec(paddr)].paths_in_pt.is_empty()
        },
    ensures
// ---- mirrors strengthened `Frame::drop_ensures` ----

        final(regions).inv(),
        forall|i: usize|
            #![trigger final(regions).slot_owners[i]]
            i != frame_to_index_spec(paddr) ==> final(regions).slot_owners[i] == old(
                regions,
            ).slot_owners[i],
        final(regions).slots =~= old(regions).slots,
        final(regions).slot_owners.dom() =~= old(regions).slot_owners.dom(),
        final(regions).slot_owners[frame_to_index_spec(paddr)].raw_count == old(
            regions,
        ).slot_owners[frame_to_index_spec(paddr)].raw_count,
        final(regions).slot_owners[frame_to_index_spec(paddr)].self_addr == old(
            regions,
        ).slot_owners[frame_to_index_spec(paddr)].self_addr,
        final(regions).slot_owners[frame_to_index_spec(paddr)].usage == old(
            regions,
        ).slot_owners[frame_to_index_spec(paddr)].usage,
        final(regions).slot_owners[frame_to_index_spec(paddr)].paths_in_pt == old(
            regions,
        ).slot_owners[frame_to_index_spec(paddr)].paths_in_pt,
        // `ref_count == 1` ⟹ the torn-down slot has no page-table
        // mappings. A mapping is itself a reference (see the doc
        // comment above: `reference_count()` counts the mappings), so a
        // mapped slot would have `ref_count >= 2`. Hence `paths_in_pt`
        // is empty — same epistemic status as the `metaregion_sound`-
        // preserves clause (sound to assert, reflecting real exec; not
        // derivable from the incomplete `drop_pre` predicate alone).
        old(regions).slot_owners[frame_to_index_spec(paddr)].inner_perms.ref_count.value() == 1
            ==> final(regions).slot_owners[frame_to_index_spec(paddr)].paths_in_pt.is_empty(),
        // `drop` never touches the free-list `in_list` field (the
        // decrement branch leaves it; `drop_last_in_place` preserves
        // it). Needed for `VmStore::inv`'s `in_list` coverage (#4).
        final(regions).slot_owners[frame_to_index_spec(paddr)].inner_perms.in_list == old(
            regions,
        ).slot_owners[frame_to_index_spec(paddr)].inner_perms.in_list,
        old(regions).slot_owners[frame_to_index_spec(paddr)].inner_perms.ref_count.value() == 1
            ==> final(regions).slot_owners[frame_to_index_spec(paddr)].inner_perms.ref_count.value()
            == REF_COUNT_UNUSED,
        old(regions).slot_owners[frame_to_index_spec(paddr)].inner_perms.ref_count.value() > 1
            ==> final(regions).slot_owners[frame_to_index_spec(paddr)].inner_perms.ref_count.value()
            == (old(regions).slot_owners[frame_to_index_spec(paddr)].inner_perms.ref_count.value()
            - 1) as u64,
        // Storage preservation in the decrement branch (rc>1): the
        // exec `fetch_sub` only touches `ref_count`; only the rc==1
        // teardown branch invokes `drop_last_in_place` (which uninits
        // storage). Needed so the embedding accounting clause's
        // `storage.is_init` carries across non-teardown drops.
        old(regions).slot_owners[frame_to_index_spec(paddr)].inner_perms.ref_count.value() > 1
            ==> final(regions).slot_owners[frame_to_index_spec(paddr)].inner_perms.storage == old(
            regions,
        ).slot_owners[frame_to_index_spec(paddr)].inner_perms.storage,
        // ---- embedding inv chaining ----
        forall|c: CursorOwner<'_, UserPtConfig>|
            #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
;

// =============================================================================
// step proofs
// =============================================================================
/// Per-op step for `Op::FrameFromUnused`. On success, allocates a
/// `FrameEntry { paddr }` for the dispatcher to register.
pub(super) proof fn from_unused_step(
    tracked regions: &mut MetaRegionOwners,
    paddr: Paddr,
) -> (tracked res: Option<FrameEntry>)
    requires
        old(regions).inv(),
        has_safe_slot(paddr) ==> old(regions).slots.contains_key(frame_to_index_spec(paddr)),
    ensures
        final(regions).inv(),
        !has_safe_slot(paddr) ==> res is None,
        res matches Some(e) ==> e.paddr == paddr,
        res is Some ==> MetaSlot::get_from_unused_reparked_spec(
            paddr,
            false,
            *old(regions),
            *final(regions),
        ),
        res is None ==> *final(regions) == *old(regions),
        forall|c: CursorOwner<'_, UserPtConfig>|
            #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
{
    let tracked outcome = frame_from_unused_embedded(regions, paddr);
    match outcome {
        Option::Some(()) => Option::Some(axiom_frame_entry_new(paddr)),
        Option::None => Option::None,
    }
}

/// Per-op step for `Op::FrameFromInUse`. On success, allocates a fresh
/// `FrameEntry { paddr }` even though one or more handles may already
/// exist (each adds +1 to refcount).
pub(super) proof fn from_in_use_step(
    tracked regions: &mut MetaRegionOwners,
    paddr: Paddr,
) -> (tracked res: Option<FrameEntry>)
    requires
        old(regions).inv(),
        has_safe_slot(paddr) ==> old(regions).slots.contains_key(
            frame_to_index_spec(paddr),
        ),
// Saturation `panic_diverge`s in exec — not a precondition.

    ensures
        final(regions).inv(),
        !has_safe_slot(paddr) ==> res is None,
        res matches Some(e) ==> e.paddr == paddr,
        res is Some ==> MetaSlot::get_from_in_use_success(paddr, *old(regions), *final(regions)),
        res is None ==> *final(regions) == *old(regions),
        // 2b: surface the acquired slot's liveness — see
        // [`frame_from_in_use_embedded`].
        res is Some ==> {
            let so = final(regions).slot_owners[frame_to_index_spec(paddr)];
            &&& so.inner_perms.ref_count.value() != REF_COUNT_UNUSED
            &&& so.inner_perms.ref_count.value() != REF_COUNT_UNIQUE
            &&& so.inner_perms.storage.is_init()
        },
        final(regions).slots =~= old(regions).slots,
        forall|c: CursorOwner<'_, UserPtConfig>|
            #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
{
    let tracked outcome = frame_from_in_use_embedded(regions, paddr);
    match outcome {
        Option::Some(()) => Option::Some(axiom_frame_entry_new(paddr)),
        Option::None => Option::None,
    }
}

/// `Op::FrameDrop` precondition over the slot at `paddr`. Mirrors
/// `Frame::drop_requires` (expressible parts) verbatim — no extra
/// embedding obligation. There is no caller-visible
/// decrement-vs-teardown choice — the single [`frame_drop_embedded`]
/// axiom covers both via one postcondition keyed on the live refcount.
pub open spec fn drop_pre(regions: MetaRegionOwners, paddr: Paddr) -> bool {
    let so = regions.slot_owners[frame_to_index_spec(paddr)];
    &&& regions.slots.contains_key(frame_to_index_spec(paddr))
    &&& so.raw_count == 0
    &&& so.inner_perms.ref_count.value() > 0
    &&& so.inner_perms.ref_count.value() != REF_COUNT_UNUSED
    &&& so.inner_perms.ref_count.value() <= REF_COUNT_MAX
    &&& so.inner_perms.ref_count.value() == 1 ==> {
        &&& so.inner_perms.storage.is_init()
        &&& so.inner_perms.in_list.value() == 0
        &&& so.paths_in_pt.is_empty()
    }
}

/// Per-op step for `Op::FrameDrop`. The caller has already extracted
/// the entry from the store. One drop; the single axiom's
/// refcount-keyed postcondition gives decrement (`> 1`) or
/// UNUSED-teardown (`== 1`) — no branching here.
pub(super) proof fn drop_step(tracked regions: &mut MetaRegionOwners, tracked entry: FrameEntry)
    requires
        old(regions).inv(),
        drop_pre(*old(regions), entry.paddr),
    ensures
        final(regions).inv(),
        final(regions).slots =~= old(regions).slots,
        forall|i: usize|
            #![trigger final(regions).slot_owners[i]]
            i != frame_to_index_spec(entry.paddr) ==> final(regions).slot_owners[i] == old(
                regions,
            ).slot_owners[i],
        // `raw_count` / `in_list` preserved at the dropped slot too —
        // `drop` touches only `ref_count` (+ storage on teardown). Keeps
        // `VmStore::inv`'s `raw_count` / `in_list` coverage (#4).
        final(regions).slot_owners[frame_to_index_spec(entry.paddr)].raw_count == old(
            regions,
        ).slot_owners[frame_to_index_spec(entry.paddr)].raw_count,
        final(regions).slot_owners[frame_to_index_spec(entry.paddr)].inner_perms.in_list == old(
            regions,
        ).slot_owners[frame_to_index_spec(entry.paddr)].inner_perms.in_list,
        // Surface the rest of `frame_drop_embedded`'s ensures at the
        // dropped slot — needed by `step_frame_drop` to discharge the
        // accounting clause (Stage 5).
        final(regions).slot_owners[frame_to_index_spec(entry.paddr)].usage == old(
            regions,
        ).slot_owners[frame_to_index_spec(entry.paddr)].usage,
        final(regions).slot_owners[frame_to_index_spec(entry.paddr)].paths_in_pt == old(
            regions,
        ).slot_owners[frame_to_index_spec(entry.paddr)].paths_in_pt,
        // `ref_count == 1` ⟹ no mappings ⟹ empty `paths_in_pt` at the
        // torn-down slot — see [`frame_drop_embedded`].
        old(regions).slot_owners[frame_to_index_spec(entry.paddr)].inner_perms.ref_count.value()
            == 1 ==> final(regions).slot_owners[frame_to_index_spec(
            entry.paddr,
        )].paths_in_pt.is_empty(),
        // rc transition (mirrors `frame_drop_embedded` exactly).
        old(regions).slot_owners[frame_to_index_spec(entry.paddr)].inner_perms.ref_count.value()
            == 1 ==> final(regions).slot_owners[frame_to_index_spec(
            entry.paddr,
        )].inner_perms.ref_count.value() == REF_COUNT_UNUSED,
        old(regions).slot_owners[frame_to_index_spec(entry.paddr)].inner_perms.ref_count.value() > 1
            ==> final(regions).slot_owners[frame_to_index_spec(
            entry.paddr,
        )].inner_perms.ref_count.value() == (old(regions).slot_owners[frame_to_index_spec(
            entry.paddr,
        )].inner_perms.ref_count.value() - 1) as u64,
        // Storage preservation in the decrement branch (rc>1).
        old(regions).slot_owners[frame_to_index_spec(entry.paddr)].inner_perms.ref_count.value() > 1
            ==> final(regions).slot_owners[frame_to_index_spec(entry.paddr)].inner_perms.storage
            == old(regions).slot_owners[frame_to_index_spec(entry.paddr)].inner_perms.storage,
        forall|c: CursorOwner<'_, UserPtConfig>|
            #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
{
    frame_drop_embedded(regions, entry.paddr);
}

} // verus!
