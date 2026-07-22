//! Embedding of `Segment` lifecycle operations: contiguous-range
//! allocate ([`segment_from_unused_embedded`]) and drop
//! ([`lemma_segment_drop_embedded`]).
//!
//! A segment "handle" in the embedding is a `range`-bearing
//! [`super::SegmentEntry`] in [`super::VmStore::segments`]. Each
//! `SegmentEntry` represents one outstanding `Segment<M>` covering its
//! physical range; per-frame `raw_count` contributions are summed via
//! [`super::segment_cover_count`].
//!
//! # Methods modeled
//!
//! - `Segment::from_unused`: allocate a fresh segment over a range of
//!   previously-unused slots. Each frame in the range transitions
//!   `usage == Unused` → `Frame`, `rc` 0 → 1, `raw_count` 0 → 1.
//! - `Segment` drop: release the segment's forgotten reference at each
//!   frame in the range. Each frame's `rc` decrements; if the rc reaches
//!   the UNUSED sentinel (no other references), the slot transitions to
//!   UNUSED.
//!
//! # Model gaps
//!
//! - **Generic `M: AnyFrameMeta`** + the `metadata_fn` closure: the
//!   embedding doesn't carry the per-frame metadata. The axioms commit
//!   only to `usage == PageUsage::Frame` (matching the exec
//!   `Segment::from_unused` contract).
//! - **Split / slice / next / clone / into_raw / from_raw**: deferred
//!   to follow-up; the base `from_unused` + drop pair is enough to
//!   exercise the Shape-B `raw_count == segment_cover_count`
//!   invariant.
use core::ops::Range;

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
    frame::meta::{REF_COUNT_MAX, REF_COUNT_UNIQUE, REF_COUNT_UNUSED},
    vm_space::UserPtConfig,
    Paddr,
};

use super::{frame::frame_drop_embedded, tracked_segment_entry_new, SegmentEntry};

verus! {

// =============================================================================
// _embedded axioms
// =============================================================================

/// Mirror of [`crate::mm::frame::Segment::from_unused`] for a contiguous
/// range. On `Some`, every frame in `range`:
/// - transitions from `REF_COUNT_UNUSED` to 1,
/// - has `usage` set to `Frame`,
/// - has `raw_count` bumped to 1 (the segment's forgotten reference),
/// - and its slot perm is re-parked in `regions.slots` (Design B).
///
/// `None` covers misalignment / out-of-bound / empty-range — same
/// shape as the exec `Result<_, GetFrameError>` return.
///
/// **Preconditions** mirror the exec contract: every frame slot in
/// `range` must currently be UNUSED (via `paddr_range_not_in_use`).
/// In practice the embedding's caller establishes this from
/// `structural_inv`'s slot-perm coverage + accounting clause 1
/// (UNUSED ⟹ no users) once the range is known UNUSED.
pub axiom fn segment_from_unused_embedded(
    tracked regions: &mut MetaRegionOwners,
    range: Range<Paddr>,
) -> (res: Option<()>)
    requires
        old(regions).inv(),
        range.start % PAGE_SIZE == 0,
        range.end % PAGE_SIZE == 0,
        range.start < range.end,
        range.end <= MAX_PADDR,
        // Every frame in `range` is currently UNUSED — discharged from
        // `accounting_inv` clause 1 by the caller.
        forall|paddr: Paddr|
            #![trigger frame_to_index(paddr)]
            (range.start <= paddr < range.end && paddr % PAGE_SIZE == 0)
                ==> old(regions).slot_owners[frame_to_index(paddr)]
                        .inner_perms.ref_count.value() == REF_COUNT_UNUSED,
        forall|paddr: Paddr|
            #![trigger frame_to_index(paddr)]
            (range.start <= paddr < range.end && paddr % PAGE_SIZE == 0)
                ==> old(regions).slots.contains_key(frame_to_index(paddr)),
    ensures
        final(regions).inv(),
        // `slots` domain preserved (Design B re-parking).
        final(regions).slots == old(regions).slots,
        // On success: each frame in range transitions to a Frame-usage,
        // rc=1, raw_count=1 SHARED slot.
        res is Some ==> forall|paddr: Paddr|
            #![trigger frame_to_index(paddr)]
            (range.start <= paddr < range.end && paddr % PAGE_SIZE == 0)
                ==> {
                    let idx = frame_to_index(paddr);
                    let so = final(regions).slot_owners[idx];
                    &&& so.usage == PageUsage::Frame
                    &&& so.inner_perms.ref_count.value() == 1
                    &&& so.paths_in_pt.is_empty()
                    &&& so.inner_perms.in_list.value() == 0
                    &&& so.inner_perms.storage.is_init()
                },
        // Slots OUTSIDE the range are fully preserved.
        res is Some ==> forall|i: int|
            #![trigger final(regions).slot_owners[i]]
            i < crate::specs::mm::frame::mapping::max_meta_slots()
            && !(range.start <= crate::specs::mm::frame::mapping::index_to_frame(i)
                    < range.end)
                ==> final(regions).slot_owners[i] == old(regions).slot_owners[i],
        // Unparked (page-table-node) slots are untouched: allocation only
        // transitions the (previously UNUSED, parked) covered slots, never
        // a PT root whose perm is not parked in `regions.slots`. Preserves
        // the embedding's slot-perm coverage exception.
        res is Some ==> forall|i: int|
            #![trigger final(regions).slot_owners[i]]
            !old(regions).slots.contains_key(i) ==> final(regions).slot_owners[i] == old(
                regions,
            ).slot_owners[i],
        // On failure: regions unchanged.
        res is None ==> *final(regions) == *old(regions),
        // metaregion_sound preservation (no PT-node-mutation, so any
        // cursor sound w.r.t. pre is sound w.r.t. post).
        forall|c: CursorOwner<'_, UserPtConfig>| #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
;

/// Mirror of [`crate::mm::frame::Segment`]'s drop loop. Releases the
/// segment's forgotten reference at every frame in `range`: each
/// frame's `rc` and `raw_count` decrement by 1; if `rc` reaches 0,
/// the slot transitions to UNUSED.
///
/// **Preconditions**: the segment relates to `regions` (each covered
/// slot has `raw_count == 1` from THIS segment's contribution and
/// `rc >= 1`). When the segment is the sole reference at a frame
/// (`rc == 1`), the drop tears down that slot.
///
/// In the embedding, the per-segment `raw_count == 1` form is
/// generalized to `raw_count == segment_cover_count`, so after drop
/// each covered slot's `raw_count` is `pre_cover_count - 1`. This
/// proof derives the range-wide transition by recursively applying the
/// single-frame [`frame_drop_embedded`] boundary; the embedding's
/// [`super::structural_inv`] re-chains via segment removal.
pub proof fn lemma_segment_drop_embedded(
    tracked regions: &mut MetaRegionOwners,
    range: Range<Paddr>,
)
    requires
        old(regions).inv(),
        range.start % PAGE_SIZE == 0,
        range.end % PAGE_SIZE == 0,
        range.start < range.end,
        range.end <= MAX_PADDR,
        // Every covered slot has `raw_count >= 1` (this segment
        // contributes at least 1), `rc >= 1` and `rc <= REF_COUNT_MAX`
        // (SHARED).
        forall|paddr: Paddr|
            #![trigger frame_to_index(paddr)]
            (range.start <= paddr < range.end && paddr % PAGE_SIZE == 0)
                ==> {
                    let so = old(regions).slot_owners[frame_to_index(paddr)];
                    &&& so.inner_perms.ref_count.value() >= 1
                    &&& so.inner_perms.ref_count.value()
                            <= REF_COUNT_MAX
                    &&& so.usage == PageUsage::Frame
                    // At rc==1 (sole reference being dropped), no PTE
                    // points to this frame — required for the
                    // teardown's `drop_last_in_place_safety_cond`.
                    &&& so.inner_perms.ref_count.value() == 1
                        ==> so.paths_in_pt.is_empty()
                },
    ensures
        final(regions).inv(),
        final(regions).slots == old(regions).slots,
        // For each covered slot: `raw_count -= 1`; rc -= 1 or
        // transition to UNUSED (when pre rc == 1).
        forall|paddr: Paddr|
            #![trigger frame_to_index(paddr)]
            (range.start <= paddr < range.end && paddr % PAGE_SIZE == 0)
                ==> {
                    let idx = frame_to_index(paddr);
                    let so_old = old(regions).slot_owners[idx];
                    let so_new = final(regions).slot_owners[idx];
                    &&& so_new.usage == so_old.usage
                    &&& so_new.paths_in_pt == so_old.paths_in_pt
                    &&& so_new.slot_vaddr == so_old.slot_vaddr
                    &&& so_new.inner_perms.in_list == so_old.inner_perms.in_list
                    &&& so_old.inner_perms.ref_count.value() == 1
                        ==> so_new.inner_perms.ref_count.value() == REF_COUNT_UNUSED
                    &&& so_old.inner_perms.ref_count.value() > 1
                        ==> so_new.inner_perms.ref_count.value()
                                == (so_old.inner_perms.ref_count.value() - 1) as u64
                },
        // Slots OUTSIDE the range are fully preserved.
        forall|i: int|
            #![trigger final(regions).slot_owners[i]]
            i < crate::specs::mm::frame::mapping::max_meta_slots()
            && !(range.start <= crate::specs::mm::frame::mapping::index_to_frame(i)
                    < range.end)
                ==> final(regions).slot_owners[i] == old(regions).slot_owners[i],
        // Unparked (page-table-node) slots are untouched: drop only frees
        // the segment's covered (Frame) slots, never a PT root whose perm
        // is not parked in `regions.slots`. Preserves the embedding's
        // slot-perm coverage exception.
        forall|i: int|
            #![trigger final(regions).slot_owners[i]]
            !old(regions).slots.contains_key(i) ==> final(regions).slot_owners[i] == old(
                regions,
            ).slot_owners[i],
        forall|c: CursorOwner<'_, UserPtConfig>| #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
    decreases range.end - range.start,
{
    assert(regions.slot_owners.contains_key(frame_to_index(range.start)));
    frame_drop_embedded(regions, range.start);

    if range.start + PAGE_SIZE < range.end {
        let ghost tail: Range<Paddr> = Range {
            start: (range.start + PAGE_SIZE) as Paddr,
            end: range.end,
        };
        lemma_segment_drop_embedded(regions, tail);
    }
}

/// Mirror of [`crate::mm::frame::Segment::next`]'s "pop one frame"
/// effect. At the popped paddr (= `range.start` pre):
/// - `raw_count -= 1` (the segment's forgotten reference at this
///   frame is consumed by `Frame::from_raw`).
/// - `ref_count` UNCHANGED (the rc contribution "transfers" from the
///   segment's forgotten reference to the newly-restored `Frame<M>`
///   handle that the caller now owns).
/// - all other slot fields (`usage`, `paths_in_pt`, `storage`, ...)
///   preserved.
///
/// Slots outside the popped paddr are fully preserved.
///
/// **Preconditions** mirror exec `next`: the segment has at least one
/// frame in its range; the popped frame's slot is currently
/// forgotten (`raw_count >= 1`) with a live SHARED `rc`.
pub proof fn segment_next_embedded(
    tracked regions: &mut MetaRegionOwners,
    paddr: Paddr,
)
    requires
        old(regions).inv(),
        paddr % PAGE_SIZE == 0,
        paddr < MAX_PADDR,
        old(regions).slots.contains_key(frame_to_index(paddr)),
        old(regions).slot_owners[frame_to_index(paddr)]
                .inner_perms.ref_count.value() >= 1,
        old(regions).slot_owners[frame_to_index(paddr)]
                .inner_perms.ref_count.value()
            <= REF_COUNT_MAX,
        old(regions).slot_owners[frame_to_index(paddr)].usage
            == PageUsage::Frame,
    ensures
        final(regions).inv(),
        final(regions).slots == old(regions).slots,
        // At paddr: raw_count -= 1, rc unchanged, other fields preserved.
        {
            let idx = frame_to_index(paddr);
            let so_old = old(regions).slot_owners[idx];
            let so_new = final(regions).slot_owners[idx];
            &&& so_new.inner_perms.ref_count == so_old.inner_perms.ref_count
            &&& so_new.usage == so_old.usage
            &&& so_new.slot_vaddr == so_old.slot_vaddr
            &&& so_new.paths_in_pt == so_old.paths_in_pt
            &&& so_new.inner_perms.in_list == so_old.inner_perms.in_list
            &&& so_new.inner_perms.storage == so_old.inner_perms.storage
            &&& so_new.inner_perms.vtable_ptr == so_old.inner_perms.vtable_ptr
        },
        // All other slots fully preserved.
        forall|i: int| #![trigger final(regions).slot_owners[i]]
            i != frame_to_index(paddr)
                ==> final(regions).slot_owners[i] == old(regions).slot_owners[i],
        forall|c: CursorOwner<'_, UserPtConfig>| #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
{
}

// =============================================================================
// step proofs
// =============================================================================

/// Per-op step for `Op::SegmentFromUnused`. On success, returns a
/// fresh [`SegmentEntry`] for the dispatcher to register; on failure,
/// returns `None` and the store is unchanged.
pub(super) proof fn from_unused_step(
    tracked regions: &mut MetaRegionOwners,
    range: Range<Paddr>,
) -> (tracked res: Option<SegmentEntry>)
    requires
        old(regions).inv(),
        range.start % PAGE_SIZE == 0,
        range.end % PAGE_SIZE == 0,
        range.start < range.end,
        range.end <= MAX_PADDR,
        forall|paddr: Paddr|
            #![trigger frame_to_index(paddr)]
            (range.start <= paddr < range.end && paddr % PAGE_SIZE == 0)
                ==> old(regions).slot_owners[frame_to_index(paddr)]
                        .inner_perms.ref_count.value() == REF_COUNT_UNUSED,
        forall|paddr: Paddr|
            #![trigger frame_to_index(paddr)]
            (range.start <= paddr < range.end && paddr % PAGE_SIZE == 0)
                ==> old(regions).slots.contains_key(frame_to_index(paddr)),
    ensures
        final(regions).inv(),
        final(regions).slots == old(regions).slots,
        res matches Some(e) ==> e.range == range,
        res is Some ==> forall|paddr: Paddr|
            #![trigger frame_to_index(paddr)]
            (range.start <= paddr < range.end && paddr % PAGE_SIZE == 0)
                ==> {
                    let idx = frame_to_index(paddr);
                    let so = final(regions).slot_owners[idx];
                    &&& so.usage == PageUsage::Frame
                    &&& so.inner_perms.ref_count.value() == 1
                    &&& so.paths_in_pt.is_empty()
                },
        res is Some ==> forall|i: int|
            #![trigger final(regions).slot_owners[i]]
            i < crate::specs::mm::frame::mapping::max_meta_slots()
            && !(range.start <= crate::specs::mm::frame::mapping::index_to_frame(i)
                    < range.end)
                ==> final(regions).slot_owners[i] == old(regions).slot_owners[i],
        // Unparked (page-table-node) slots untouched (see axiom).
        res is Some ==> forall|i: int|
            #![trigger final(regions).slot_owners[i]]
            !old(regions).slots.contains_key(i) ==> final(regions).slot_owners[i] == old(
                regions,
            ).slot_owners[i],
        res is None ==> *final(regions) == *old(regions),
        forall|c: CursorOwner<'_, UserPtConfig>| #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
{
    let ghost outcome = segment_from_unused_embedded(regions, range);
    match outcome {
        Option::Some(()) => Option::Some(tracked_segment_entry_new(range)),
        Option::None => Option::None,
    }
}

/// Per-op step for `Op::SegmentDrop`. Caller has already extracted the
/// `SegmentEntry` from the store; the axiom performs the per-frame
/// `raw_count -= 1` and `rc` transition.
pub(super) proof fn drop_step(
    tracked regions: &mut MetaRegionOwners,
    tracked entry: SegmentEntry,
)
    requires
        old(regions).inv(),
        entry.range.start % PAGE_SIZE == 0,
        entry.range.end % PAGE_SIZE == 0,
        entry.range.start < entry.range.end,
        entry.range.end <= MAX_PADDR,
        forall|paddr: Paddr|
            #![trigger frame_to_index(paddr)]
            (entry.range.start <= paddr < entry.range.end
                && paddr % PAGE_SIZE == 0) ==> {
                let so = old(regions).slot_owners[frame_to_index(paddr)];
                &&& so.inner_perms.ref_count.value() >= 1
                &&& so.inner_perms.ref_count.value()
                        <= REF_COUNT_MAX
                &&& so.usage == PageUsage::Frame
                &&& so.inner_perms.ref_count.value() == 1
                    ==> so.paths_in_pt.is_empty()
            },
    ensures
        final(regions).inv(),
        final(regions).slots == old(regions).slots,
        forall|paddr: Paddr|
            #![trigger frame_to_index(paddr)]
            (entry.range.start <= paddr < entry.range.end
                && paddr % PAGE_SIZE == 0) ==> {
                let idx = frame_to_index(paddr);
                let so_old = old(regions).slot_owners[idx];
                let so_new = final(regions).slot_owners[idx];
                &&& so_new.usage == so_old.usage
                &&& so_new.paths_in_pt == so_old.paths_in_pt
                &&& so_new.slot_vaddr == so_old.slot_vaddr
                &&& so_new.inner_perms.in_list == so_old.inner_perms.in_list
                &&& so_old.inner_perms.ref_count.value() == 1
                    ==> so_new.inner_perms.ref_count.value() == REF_COUNT_UNUSED
                &&& so_old.inner_perms.ref_count.value() > 1
                    ==> so_new.inner_perms.ref_count.value()
                            == (so_old.inner_perms.ref_count.value() - 1) as u64
            },
        forall|i: int|
            #![trigger final(regions).slot_owners[i]]
            i < crate::specs::mm::frame::mapping::max_meta_slots()
            && !(entry.range.start <= crate::specs::mm::frame::mapping::index_to_frame(i)
                    < entry.range.end)
                ==> final(regions).slot_owners[i] == old(regions).slot_owners[i],
        // Unparked (page-table-node) slots untouched (see axiom).
        forall|i: int|
            #![trigger final(regions).slot_owners[i]]
            !old(regions).slots.contains_key(i) ==> final(regions).slot_owners[i] == old(
                regions,
            ).slot_owners[i],
        forall|c: CursorOwner<'_, UserPtConfig>| #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
{
    lemma_segment_drop_embedded(regions, entry.range);
}

pub axiom fn segment_clone_embedded(
    tracked regions: &mut MetaRegionOwners,
    range: Range<Paddr>,
)
    requires
        old(regions).inv(),
        range.start % PAGE_SIZE == 0,
        range.end % PAGE_SIZE == 0,
        range.start < range.end,
        range.end <= MAX_PADDR,
        // Every covered slot is a live SHARED Frame slot with headroom
        // for one more reference (no saturation).
        forall|paddr: Paddr|
            #![trigger frame_to_index(paddr)]
            (range.start <= paddr < range.end && paddr % PAGE_SIZE == 0)
                ==> {
                    let so = old(regions).slot_owners[frame_to_index(paddr)];
                    &&& so.usage == PageUsage::Frame
                    &&& so.inner_perms.ref_count.value() >= 1
                    &&& so.inner_perms.ref_count.value() + 1 <= REF_COUNT_MAX
                },
    ensures
        final(regions).inv(),
        final(regions).slots =~= old(regions).slots,
        // At each covered slot: rc += 1, every other field preserved.
        forall|paddr: Paddr|
            #![trigger frame_to_index(paddr)]
            (range.start <= paddr < range.end && paddr % PAGE_SIZE == 0)
                ==> {
                    let idx = frame_to_index(paddr);
                    let so_old = old(regions).slot_owners[idx];
                    let so_new = final(regions).slot_owners[idx];
                    &&& so_new.inner_perms.ref_count.value()
                            == (so_old.inner_perms.ref_count.value() + 1) as u64
                    &&& so_new.usage == so_old.usage
                    &&& so_new.slot_vaddr == so_old.slot_vaddr
                    &&& so_new.paths_in_pt == so_old.paths_in_pt
                    &&& so_new.inner_perms.in_list == so_old.inner_perms.in_list
                    &&& so_new.inner_perms.storage == so_old.inner_perms.storage
                    &&& so_new.inner_perms.vtable_ptr == so_old.inner_perms.vtable_ptr
                },
        // Slots OUTSIDE the range are fully preserved.
        forall|i: int|
            #![trigger final(regions).slot_owners[i]]
            i < crate::specs::mm::frame::mapping::max_meta_slots()
            && !(range.start <= crate::specs::mm::frame::mapping::index_to_frame(i)
                    < range.end)
                ==> final(regions).slot_owners[i] == old(regions).slot_owners[i],
        forall|c: CursorOwner<'_, UserPtConfig>| #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
;

} // verus!
