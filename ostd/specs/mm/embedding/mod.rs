//! Deep embedding of the `VmSpace` and `VmReader`/`VmWriter` API.
//!
//! `VmStore` is the abstract state of a caller of these APIs: it holds
//! the [`MetaRegionOwners`] plus a registry of every owner object the
//! caller currently has access to.
//!
//! [`Op`] is an ADT enumerating the public exec API. [`step`] is the
//! single proof-mode dispatcher; it requires `s.inv()` *and* the
//! per-op precondition [`op_pre`] (which says the ids referenced in
//! `op` resolve to existing entries with the right cross-store
//! relationships). `op_pre` contains all preconditions necessary
//! to dispatch each operation, which makes it the cornerstone of soundness.
//! See its documentation for analysis.
//!
//! # Module layout
//!
//! - [`vm_space`]: ops on the [`crate::mm::vm_space::VmSpace`] type
//!   (`new`, drop).
//! - [`cursor`]: ops on `Cursor` / `CursorMut` (open, drop, `query`,
//!   `find_next`, `jump`, `map`, `unmap`, `protect_next`).
//! - [`io`]: ops on `VmReader` / `VmWriter` (creation, drop, the
//!   user-space and kernel-space IO methods).
//! - [`trace`]: explicit-induction theorems over `Seq<Op>`.
//!
//! # Soundness boundary: `_embedded` axioms
//!
//! Each axiom named `<exec_function_path>_embedded` mirrors the
//! `ensures` clause of one public exec function. Naming is the only
//! mechanism keeping the axiom in sync with its exec counterpart;
//! reviewers touching either side should grep for the partner.
//!
//! # Roadmap — DONE / open work
//!
//! All five originally-deferred items have landed. Shape B for
//! segments is fully active: `Op::SegmentFromUnused` /
//! `Op::SegmentDrop` are in the dispatch, [`accounting_inv`] has the
//! generalised `rc == H + P + cover_count` equation, and
//! [`structural_inv`] carries `raw_count == segment_cover_count` +
//! segment-covered ⟹ Frame-usage + segment range well-formedness.
//!
//! 1. **Strengthen [`crate::specs::mm::frame::meta_owners::MetaSlotOwner::inv`]'s
//!    SHARED branch** — DONE. The branch (`0 < rc <= REF_COUNT_MAX`)
//!    now carries `inner_perms.storage.is_init()` and
//!    `inner_perms.in_list.value() == 0`. The `rc == 1 ⟹ ...` guards
//!    on `storage`/`in_list` in
//!    [`crate::mm::frame::Frame::drop_requires`] were dropped.
//!
//! 2. **`Frame::wf(state)`** — DONE at both layers.
//!    - **Embedding layer**: [`lemma_frame_drop_pre_derivable`]
//!      derives all of [`frame::drop_pre`]'s residuals (rc not in
//!      sentinels, `rc <= REF_COUNT_MAX`, `storage.is_init`,
//!      `in_list == 0`, `rc == 1 ⟹ paths empty`) plus the
//!      `rc == 1 ⟹ handle_count == 1` clause from `s.inv()` + the
//!      `FrameEntry`'s registration + the segment-cover hypothesis.
//!      `op_pre[FrameDrop]` and `step_frame_drop` shrink to
//!      id-existence + segment-cover only.
//!    - **Exec layer**: [`crate::mm::frame::Frame::inv_with_regions`]
//!      packages the per-handle cross-object validity (slot/pointer
//!      identity + SHARED rc bounds — `> 0 ∧ ≠ UNUSED ∧ ≠ UNIQUE
//!      ∧ ≤ MAX`). `Frame::drop_requires` is refactored to read
//!      `self.inv_with_regions(s) ∧ raw_count == 0 ∧ rc == 1 ⟹ paths empty`,
//!      which keeps the drop-specific bits explicit while
//!      consolidating the static "this Frame is valid against
//!      this state" conjuncts.
//!    - `clone_requires` not refactored: would cascade into
//!      `PageTableConfig::clone_requires_concrete` (a trait method
//!      with multiple implementors); left explicit to keep the
//!      change local.
//!    - **Preservation of `inv_with_regions` (FUTURE).** `Frame::inv_with_regions`'s
//!      preservation across drops of *other* handles at the same slot
//!      is currently informal (claimed in the docstring; no
//!      machine-checked proof). To prove it, every `Frame<M>` needs a
//!      tracked ghost "reference-count share" certificate that proves
//!      "I contribute 1 to my slot's `rc`," combined with an aggregate
//!      invariant on `MetaSlotOwner` saying `held_shares == rc.value()`.
//!      Recommended primitive:
//!      [`vstd_extra::resource::ghost_resource::tokens::Token`]
//!      (alias for `CountGhost<(), TOTAL>`) with
//!      `TOTAL = REF_COUNT_MAX`. The resource framework provides
//!      `split` / `combine` / `agree` / `bounded` pre-proven; the
//!      Frame side adds a `Tracked<Token<MAX>>` field and the
//!      `MetaSlotOwner` side adds a
//!      `CountGhostResource<(), MAX>` aggregate of remaining shares
//!      with the linking invariant `rc.value() + remaining == MAX`.
//!      Cursor map / unmap axioms gain share-juggling clauses
//!      (`paths_in_pt += 1` ↔ split off 1 share). The math is proven
//!      by vstd_extra; the integration is a multi-day refactor with
//!      cascading effects on every `MetaRegionOwners` consumer.
//!      The embedding's `handle_count` already provides the equivalent
//!      property at the abstract level, so this is only needed if
//!      downstream code outside the embedding's tracking needs
//!      `Frame::inv_with_regions` preservation proofs.
//!
//! 3a. **Op::Map consumes a `FrameId`** — DONE. `Op::Map { c, fid,
//!     prop }` extracts the matching `FrameEntry` (so `H` at the
//!     mapped slot decrements by 1, paired with the cursor axiom's
//!     `paths_in_pt += 1` at the same slot). Combined with the
//!     `cursor_mut_map_embedded` axiom's per-slot ensures (rc / usage
//!     / storage preserved at target, changed-slots ⟹ PT-node ⟹
//!     `usage != Frame`), [`accounting_inv`]'s Frame-scoped equation
//!     `rc == H + P` chains.
//!
//! 3b. **Op::Query clone modeling** — DONE. The `cursor_query_embedded`
//!     axiom now returns `Option<Paddr>`: `Some(paddr)` when query
//!     resolved a tracked leaf and `clone_item` bumped `rc` at that
//!     slot; `None` otherwise (out-of-range / no leaf / MMIO leaf).
//!     [`step_query`] consumes the paddr to register a fresh
//!     `FrameEntry` so `H` at the cloned slot grows in lockstep with
//!     `rc`, keeping `accounting_inv`'s `rc == H + P` chained.
//!
//! 4. **Strengthen `cursor_mut_unmap_embedded`** — DONE. The axiom
//!    now mirrors exec: universal preservation of
//!    `raw_count`/`in_list`/`usage`/`self_addr`/`vtable_ptr`;
//!    storage preserved at slots ending non-UNUSED; rc doesn't bump
//!    to UNIQUE; at Frame slots the "non-mapping count"
//!    `rc - paths.len` is invariant with both monotonically non-
//!    increasing, and post `rc != 0` (Frame teardown collapses
//!    `rc==0` to `REF_COUNT_UNUSED` atomically); MMIO slots are
//!    untouched (preserving the `MetaSlotOwner::inv` MMIO exception
//!    that allows non-empty `paths_in_pt` at UNUSED).
//!    [`step_unmap`] discharges accounting via case-splits on
//!    Frame / non-Frame / MMIO.
//!
//! 5. **Shape-B segments** — base + split landed; the rest is
//!    documented with status per op.
//!    - **`from_unused` / `drop`** — DONE. Allocate a segment over a
//!      contiguous range of UNUSED frames, and release the segment's
//!      forgotten references with per-frame teardown.
//!    - **`split`** — DONE. Partition the segment at a page-aligned
//!      offset; `regions` is unchanged because per-paddr
//!      `cover_count` is invariant under the partition.
//!      [`lemma_segment_cover_split`] proves the per-paddr
//!      invariance.
//!    - **`clone`** — NOT modeled, pending exec fix. Today exec
//!      `Segment::clone` bumps `rc` but not `raw_count` and doesn't
//!      produce a new `SegmentOwner`, so the clone is un-droppable
//!      from verified code. Planned fix (separate session):
//!      generalise `Frame::from_raw` to `raw_count >= 1` + decrement;
//!      weaken `SegmentOwner::relate_regions` to `raw_count >= 1`;
//!      replace `RCClone for Segment` with an inherent `clone` that
//!      returns `(Self, Tracked<SegmentOwner<M>>)` and per-frame
//!      `from_in_use + ManuallyDrop::new`. Once it ships, the
//!      embedding adds `Op::SegmentClone { sid }` that inserts a
//!      fresh `SegmentEntry` mirroring `sid`'s range.
//!    - **`next`** — DONE. The conversion bridge between
//!      segment-held forgotten references and user-held `Frame<M>`
//!      handles. Per-paddr at the popped slot: `raw_count -= 1`,
//!      `cover_count -= 1`, `H += 1`, `rc` unchanged. The
//!      accounting equation `rc == H + P + cover_count` chains in
//!      lockstep because H and cover decrement/increment together;
//!      structural `raw_count == cover_count` chains via
//!      [`lemma_segment_cover_shrink_front`].
//!    - **`slice`** — NOT modeled, deferred for the same reason as
//!      `clone` (and probably HARDER, despite initial appearances).
//!      Both APIs produce an un-droppable handle (no `SegmentOwner`
//!      returned) and don't bump `raw_count`. A faithful fix
//!      requires generalising `Frame::from_raw`'s precondition from
//!      `raw_count <= 1` to `raw_count >= 1` (with decrement-not-
//!      zero body) so that sliced/cloned segments — which produce
//!      multiple forgotten refs at the same slot — can each be
//!      drop-reclaimed. **An attempted exec fix in this session
//!      revealed unanticipated cascade**: `borrow` / `borrow_paddr`
//!      bridge through `lemma_from_raw_manuallydrop_general` which
//!      assumes the single-forgotten-ref case, and the PT-node
//!      `child_perms_embedding` invariant carries `raw_count <= 1`
//!      without supplying a `>= 1` companion. Tightening one half
//!      breaks the other. Properly resolving this requires either:
//!      (a) per-handle ghost certificates (the `FrameCert` route
//!          documented in the Item 2 future-work note above), or
//!      (b) splitting `from_raw` into two variants — one for the
//!          single-forgotten case (existing) and one for
//!          multi-forgotten (new) — and threading the
//!          discriminator through `SegmentOwner` so `drop` can pick
//!          the right one.
//!      Either path is half-day to multi-day work. `slice` and
//!      `clone` should be tackled together when that engineering
//!      effort is funded; the embedding side is ready to receive
//!      a `cover_count + 1` / `raw_count + 1` Op as soon as the
//!      exec ships the API.
//!    - **`into_raw` / `from_raw`** — `pub(crate)` only in exec, so
//!      the embedding can ignore them.
pub mod cursor;
pub mod frame;
pub mod io;
pub mod segment;
pub mod trace;
pub mod vm_space;

use core::ops::Range;

use vstd::prelude::*;
use vstd_extra::ownership::*;

use crate::mm::frame::{MetaSlot, UFrame, has_safe_slot};
use crate::mm::page_prop::PageProperty;
use crate::mm::vm_space::UserPtConfig;
use crate::mm::vm_space::vm_space_specs::VmSpaceOwner;
use crate::mm::{MAX_USERSPACE_VADDR, Paddr, Vaddr};
use crate::specs::arch::mm::{MAX_PADDR, PAGE_SIZE};
use crate::specs::mm::frame::mapping::{frame_to_index, index_to_frame, max_meta_slots};
use crate::specs::mm::frame::meta_owners::{
    PageUsage, REF_COUNT_MAX, REF_COUNT_UNIQUE, REF_COUNT_UNUSED,
};
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::io::VmIoOwner;
use crate::specs::mm::page_table::cursor::owners::CursorOwner;
use crate::specs::mm::page_table::node::Guards;
use crate::specs::mm::tlb::TlbModel;

verus! {

// =============================================================================
// Types
// =============================================================================
/// Logical identifier for a [`VmSpaceOwner`] in the store.
pub type VmSpaceId = int;

/// Logical identifier for a [`CursorOwner`] in the store.
pub type CursorId = int;

/// Logical identifier for a [`VmIoOwner`] in the store.
pub type VmIoId = int;

/// Logical identifier for a held [`crate::mm::frame::Frame`] handle in the store.
pub type FrameId = int;

/// Logical identifier for a held [`crate::mm::frame::Segment`] handle in
/// the store.
pub type SegmentId = int;

/// Per-Frame entry in the store. Represents one outstanding handle to
/// the slot at `paddr` — i.e., one unit of refcount in
/// `regions.slot_owners[frame_to_index(paddr)]`.
///
/// Multiple `FrameEntry`s may share the same `paddr`; each contributes
/// `+1` to that slot's `inner_perms.ref_count`.
pub tracked struct FrameEntry {
    pub paddr: Paddr,
}

/// Per-Segment entry in the store. Represents one outstanding
/// `Segment<M>` covering the contiguous physical range `range`.
///
/// Per exec [`SegmentOwner::relate_regions`]: every frame slot in
/// `range` carries one *forgotten* reference for this segment — i.e.,
/// `raw_count` at the slot equals the number of `SegmentEntry`s
/// covering it (see [`segment_cover_count`]). The frame's
/// `ref_count >= 1` is bumped by the segment's owning reference (one
/// per frame); the segment does *not* hold a separate `Frame` handle,
/// so the embedding's `frames` map is unrelated to per-segment frame
/// refcounting.
///
/// Multiple `SegmentEntry`s may overlap (e.g. after `clone`); each
/// independently contributes `+1` to every covered slot's `raw_count`
/// and `ref_count`.
///
/// [`SegmentOwner::relate_regions`]: crate::specs::mm::frame::segment::SegmentOwner::relate_regions
pub tracked struct SegmentEntry {
    pub range: Range<Paddr>,
}

/// Number of outstanding `Segment` handles covering the frame slot
/// at `paddr` — i.e., `#{ sid : segments[sid].range covers paddr }`.
/// This is the per-slot `raw_count` term contributed by segments
/// (Design B: each segment holds one forgotten reference per frame
/// in its range, so `raw_count == segment_cover_count(segments, ...)`).
/// Intended to be called on page-aligned paddrs (e.g. via
/// `index_to_frame(idx)`); segment ranges are themselves page-
/// aligned so the resulting count is the same for any paddr within
/// a given page.
pub open spec fn segment_cover_count(segments: Map<SegmentId, SegmentEntry>, paddr: Paddr) -> nat {
    segments.dom().filter(
        |sid: SegmentId| segments[sid].range.start <= paddr && paddr < segments[sid].range.end,
    ).len()
}

/// A positive segment-cover count exhibits a witnessing segment id whose
/// range covers `paddr`. Used to lift `segment_cover_count(..) > 0` into
/// the structural `covered ⟹ usage == Frame` clause (which is keyed by a
/// concrete `(sid, paddr)`), replacing the retired `raw_count` cache.
pub proof fn lemma_segment_cover_witness(
    segments: Map<SegmentId, SegmentEntry>,
    paddr: Paddr,
) -> (sid: SegmentId)
    requires
        segment_cover_count(segments, paddr) > 0,
    ensures
        segments.dom().contains(sid),
        segments[sid].range.start <= paddr < segments[sid].range.end,
{
    let covering = segments.dom().filter(
        |sid: SegmentId| segments[sid].range.start <= paddr && paddr < segments[sid].range.end,
    );
    assert(covering.len() > 0);
    let sid = covering.choose();
    assert(covering.contains(sid));
    sid
}

/// Number of outstanding `Frame` handles whose paddr maps to slot
/// `idx` — i.e. the `#handles(idx)` term of the exact reference-count
/// accounting `ref_count(idx) == #handles(idx) + paths_in_pt(idx).len()`
/// (Stage 5 / full #4).
pub open spec fn handle_count(frames: Map<FrameId, FrameEntry>, idx: usize) -> nat {
    frames.dom().filter(|fid: FrameId| frame_to_index(frames[fid].paddr) == idx).len()
}

/// Handle-count delta under [`Map::insert`] at a fresh id: +1 at the
/// inserted entry's slot, unchanged elsewhere. Discharges the Set /
/// filter arithmetic once so the per-step accounting proofs need only
/// invoke it.
pub proof fn lemma_handle_count_insert_fresh(
    frames: Map<FrameId, FrameEntry>,
    id: FrameId,
    entry: FrameEntry,
    idx: usize,
)
    requires
        !frames.dom().contains(id),
    ensures
        handle_count(frames.insert(id, entry), idx) == handle_count(frames, idx) + (
        if frame_to_index(entry.paddr) == idx {
            1nat
        } else {
            0nat
        }),
{
    let frames2 = frames.insert(id, entry);
    let new_filt = frames2.dom().filter(|fid: FrameId| frame_to_index(frames2[fid].paddr) == idx);
    let old_filt = frames.dom().filter(|fid: FrameId| frame_to_index(frames[fid].paddr) == idx);
    assert(frames2.dom() == frames.dom().insert(id));
    if frame_to_index(entry.paddr) == idx {
        assert(new_filt == old_filt.insert(id)) by {
            assert forall|fid: FrameId| #[trigger] new_filt.contains(fid) implies old_filt.insert(
                id,
            ).contains(fid) by {
                if fid != id {
                    assert(frames2[fid] == frames[fid]);
                }
            };
            assert forall|fid: FrameId| #[trigger]
                old_filt.insert(id).contains(fid) implies new_filt.contains(fid) by {
                if fid != id {
                    assert(frames2[fid] == frames[fid]);
                } else {
                    assert(frames2[id] == entry);
                }
            };
        };
        assert(!old_filt.contains(id));
        assert(new_filt.len() == old_filt.len() + 1);
    } else {
        assert(new_filt == old_filt) by {
            assert forall|fid: FrameId| #[trigger] new_filt.contains(fid) implies old_filt.contains(
                fid,
            ) by {
                if fid != id {
                    assert(frames2[fid] == frames[fid]);
                } else {
                    assert(frames2[id] == entry);
                }
            };
            assert forall|fid: FrameId| #[trigger] old_filt.contains(fid) implies new_filt.contains(
                fid,
            ) by {
                assert(fid != id);
                assert(frames2[fid] == frames[fid]);
            };
        };
    }
}

/// Handle-count delta under [`Map::remove`]: -1 at the removed entry's
/// slot if it was the only one present (or generally `-1` if the entry
/// at `fid` mapped to `idx`), unchanged elsewhere.
pub proof fn lemma_handle_count_remove(frames: Map<FrameId, FrameEntry>, fid: FrameId, idx: usize)
    requires
        frames.dom().contains(fid),
    ensures
        handle_count(frames.remove(fid), idx) == handle_count(frames, idx) - (if frame_to_index(
            frames[fid].paddr,
        ) == idx {
            1nat
        } else {
            0nat
        }),
{
    let frames2 = frames.remove(fid);
    let new_filt = frames2.dom().filter(|gid: FrameId| frame_to_index(frames2[gid].paddr) == idx);
    let old_filt = frames.dom().filter(|gid: FrameId| frame_to_index(frames[gid].paddr) == idx);
    assert(frames2.dom() == frames.dom().remove(fid));
    if frame_to_index(frames[fid].paddr) == idx {
        assert(old_filt.contains(fid));
        assert(new_filt == old_filt.remove(fid)) by {
            assert forall|gid: FrameId| #[trigger] new_filt.contains(gid) implies old_filt.remove(
                fid,
            ).contains(gid) by {
                assert(gid != fid);
                assert(frames2[gid] == frames[gid]);
            };
            assert forall|gid: FrameId| #[trigger]
                old_filt.remove(fid).contains(gid) implies new_filt.contains(gid) by {
                assert(gid != fid);
                assert(frames2[gid] == frames[gid]);
            };
        };
        assert(new_filt.len() == (old_filt.len() - 1) as nat);
    } else {
        assert(!old_filt.contains(fid));
        assert(new_filt == old_filt) by {
            assert forall|gid: FrameId| #[trigger] new_filt.contains(gid) implies old_filt.contains(
                gid,
            ) by {
                assert(gid != fid);
                assert(frames2[gid] == frames[gid]);
            };
            assert forall|gid: FrameId| #[trigger] old_filt.contains(gid) implies new_filt.contains(
                gid,
            ) by {
                assert(gid != fid);
                assert(frames2[gid] == frames[gid]);
            };
        };
    }
}

/// **Embedding-level `Frame::wf(state)`.** Derives the full
/// [`frame::drop_pre`] residual (rc / storage / in_list / paths-empty
/// conjuncts) plus the `rc == 1 ⟹ handle_count == 1` clause from
/// `s.inv()`, given only:
///   - `fid` is a registered handle,
///   - no `SegmentEntry` covers the slot
///     (`segment_cover_count == 0`).
///
/// Replaces the residual `drop_pre` baggage on `op_pre[FrameDrop]` /
/// `step_frame_drop` with a single tracked invariant chain. Every
/// conjunct is recovered from a specific `VmStore::inv` clause:
///   - `slots.contains_key`: structural slot-perm coverage.
///   - `raw_count == 0`: structural `raw_count == segment_cover_count`
///     + the `segment_cover_count == 0` hypothesis.
///   - `rc > 0` / `rc != UNUSED` / `rc != UNIQUE` / `rc == H + P`:
///     accounting clause 4 (active head: H >= 1 since `fid` is
///     registered + structural FrameId⟹Frame-usage).
///   - `rc <= REF_COUNT_MAX`: clause 4 (`rc != UNIQUE`) +
///     `MetaSlotOwner::inv`'s forbidden-range empty
///     (`MAX < rc < UNIQUE ⟹ false`).
///   - `rc == 1 ⟹ storage.is_init ∧ in_list == 0`:
///     `MetaSlotOwner::inv`'s SHARED branch (`0 < rc <= MAX`),
///     which is the Item 1 strengthening.
///   - `rc == 1 ⟹ paths_in_pt.is_empty()`: clause 4 + `H >= 1`
///     gives `1 == H + P` ⟹ `P == 0` ⟹ `paths.len == 0` ⟹
///     `paths.is_empty()`.
///   - `rc == 1 ⟹ handle_count == 1`: clause 4 with `rc == 1`
///     gives `1 == H + P`; with `H >= 1` and `P >= 0`, `H == 1`
///     and `P == 0`.
pub proof fn lemma_frame_drop_pre_derivable<'rcu>(s: VmStore<'rcu>, fid: FrameId)
    requires
        s.inv(),
        s.frames.dom().contains(fid),
        segment_cover_count(s.segments, s.frames[fid].paddr) == 0,
    ensures
        frame::drop_pre(s.regions, s.frames[fid].paddr),
        s.regions.slot_owners[frame_to_index(s.frames[fid].paddr)].inner_perms.ref_count.value()
            == 1 ==> handle_count(s.frames, frame_to_index(s.frames[fid].paddr)) == 1,
{
    let paddr = s.frames[fid].paddr;
    let idx = frame_to_index(paddr);
    // `fid` registered ⟹ paddr in-bound ⟹ idx is a managed slot.
    assert(has_safe_slot(paddr));
    s.regions.inv_implies_correct_addr(paddr);
    assert(idx < max_meta_slots());
    // `fid` registered ⟹ handle_count(s.frames, idx) >= 1.
    assert(s.frames.dom().filter(
        |gid: FrameId| frame_to_index(s.frames[gid].paddr) == idx,
    ).contains(fid));
    assert(handle_count(s.frames, idx) >= 1);
    // Structural FrameId⟹Frame-usage at idx.
    assert(s.regions.slot_owners[idx].usage == PageUsage::Frame);
    // Accounting clause 3 + 4 (active head Frame): pin rc, storage.
    let so = s.regions.slot_owners[idx];
    let rc = so.inner_perms.ref_count.value();
    assert(rc != REF_COUNT_UNUSED);
    assert(rc != REF_COUNT_UNIQUE);
    assert(rc == handle_count(s.frames, idx) + so.paths_in_pt.len());
    assert(so.inner_perms.storage.is_init());
    // rc != UNUSED ⟹ rc > 0 (UNUSED is u64::MAX; rc could still be 0,
    // but clause 4 gives rc == H + P ≥ 1).
    assert(rc > 0);
    // `MetaSlotOwner::inv` SHARED branch: 0 < rc <= MAX ⟹ storage.is_init,
    // in_list == 0, vtable_ptr.is_init.
    assert(s.regions.slot_owners.contains_key(idx));
    assert(s.regions.slot_owners[idx].inv());
    // rc != UNUSED ∧ rc != UNIQUE ∧ rc > 0 ⟹ rc ∈ [1, MAX]
    // (forbidden range MAX < rc < UNIQUE is empty per MetaSlotOwner::inv).
    assert(rc <= REF_COUNT_MAX);
    assert(so.inner_perms.in_list.value() == 0);
    // rc == 1 ⟹ paths empty (from rc == H + P and H >= 1).
    if rc == 1 {
        assert(handle_count(s.frames, idx) + so.paths_in_pt.len() == 1);
        assert(so.paths_in_pt.len() == 0);
        assert(so.paths_in_pt == Set::empty());
        assert(handle_count(s.frames, idx) == 1);
    }
}

/// Whether a [`VmIoOwner`] backs a `VmReader` or a `VmWriter`.
pub enum VmIoKind {
    Reader,
    Writer,
}

/// Per-VmIo entry in the store.
///
/// `vm_space` is `None` for VmIoOwners that have no parent `VmSpace` —
/// kernel-space readers/writers from `VmReader::from_kernel_space` /
/// `VmWriter::from_kernel_space`, and val_owners produced by
/// `read`. `Some(vs)` for entries created by `VmSpace::reader` /
/// `writer`.
///
/// View state is fully determined by `vm_space` + `kind`:
/// - `Some(_)` (userspace, Fallible): `mem_view: None`, exactly as
///   `VmSpace::reader`/`writer` ensure ([vm_space.rs:323/382](crate::mm::vm_space)).
///   Fallible methods are handle-only — no owner-side activation step
///   exists or is needed.
/// - `None && Reader` (kernel reader): `read_view_initialized()`, per
///   `VmReader<Infallible>::from_kernel_space` ensures.
/// - `None && Writer` (kernel writer or `consumed_w` val_owner from
///   `read`): `has_write_view()`, per `from_kernel_space` /
///   [`io::read_step`] ensures.
pub tracked struct VmIoEntry {
    pub vm_space: Option<VmSpaceId>,
    pub kind: VmIoKind,
    pub vaddr: Vaddr,
    pub len: usize,
    pub owner: VmIoOwner,
}

impl VmIoEntry {
    /// Per-entry invariant: derives view state from `vm_space` + `kind`.
    pub open spec fn inv(self) -> bool {
        &&& self.owner.inv()
        &&& match self.vm_space {
            Some(_) => self.owner.mem_view is None,
            None => match self.kind {
                VmIoKind::Reader => self.owner.read_view_initialized(),
                VmIoKind::Writer => self.owner.has_write_view(),
            },
        }
    }

    /// Operand-typing for the Infallible `read`/`write` ops. Exec
    /// `VmReader::<Infallible>::read` / `VmWriter::<Infallible>::write`
    /// are *typed* on kernel (`Infallible`) reader/writer handles; the
    /// embedding proxies "kernel/Infallible" with `vm_space is None` and
    /// reader-vs-writer with `kind`. These are not runtime preconditions
    /// — a userspace (Fallible) handle simply cannot be passed where the
    /// type system demands a kernel one — so they read as a
    /// well-formedness check on the operand, not a checkable obligation.
    /// (`inv` already gives `read_view_initialized` / `has_write_view`
    /// for these cases, exactly what `vm_reader_read_embedded` consumes.)
    pub open spec fn is_kernel_reader(self) -> bool {
        &&& self.vm_space is None
        &&& self.kind == VmIoKind::Reader
    }

    pub open spec fn is_kernel_writer(self) -> bool {
        &&& self.vm_space is None
        &&& self.kind == VmIoKind::Writer
    }
}

/// Whether a cursor is a read-only [`Cursor`] or a mutable [`CursorMut`].
///
/// [`Cursor`]: crate::mm::vm_space::Cursor
/// [`CursorMut`]: crate::mm::vm_space::CursorMut
pub enum CursorKind {
    ReadOnly,
    Mutable,
}

/// Per-cursor entry in the store.
///
/// `guards` is the lock-protocol state for the page-table nodes the
/// cursor holds locked; mirrors what the exec `Cursor` carries via
/// `path: [Option<PageTableGuard<'rcu, C>>; NR_LEVELS]`.
pub tracked struct CursorEntry<'rcu> {
    pub vm_space: VmSpaceId,
    pub kind: CursorKind,
    pub va: Range<Vaddr>,
    pub owner: CursorOwner<'rcu, UserPtConfig>,
    pub guards: Guards<'rcu>,
}

impl<'rcu> CursorEntry<'rcu> {
    /// The portion of the exec `Cursor::invariants(owner, regions, guards)`
    /// expressible from the entry alone (no `regions`).
    ///
    /// Mirrors `crate::mm::page_table::Cursor::invariants` minus
    /// `regions.inv()`, `metaregion_sound(regions)`, and the exec-handle
    /// pieces (`self.inv()` / `self.wf(owner)`). Those live in
    /// [`VmStore::inv`] (regions-touching) and are MODEL GAPS (handle).
    pub open spec fn inv(self) -> bool {
        &&& self.owner.inv()
        &&& self.owner.children_not_locked(self.guards)
        &&& self.owner.nodes_locked(self.guards)
        &&& !self.owner.popped_too_high
    }
}

/// Resource store: the abstract state visible to a caller of the
/// VmSpace + VmReader/VmWriter API.
///
/// `tlb_model` is the global TLB model; mirrors the per-CPU `TlbModel`
/// that `CursorMut::map`/`unmap` and `flusher` operate on. We keep one
/// per store on the conservative assumption that any cursor mutation
/// interacts with it.
pub tracked struct VmStore<'rcu> {
    pub regions: MetaRegionOwners,
    pub tlb_model: TlbModel,
    pub vm_spaces: Map<VmSpaceId, VmSpaceOwner>,
    pub cursors: Map<CursorId, CursorEntry<'rcu>>,
    pub vm_ios: Map<VmIoId, VmIoEntry>,
    pub frames: Map<FrameId, FrameEntry>,
    pub segments: Map<SegmentId, SegmentEntry>,
}

impl<'a, 'rcu> VmStore<'rcu> {
    /// The store's top-level invariant.
    ///
    /// Decomposed into [`structural_inv`] (everything generic store
    /// helpers can preserve when they only touch one of `frames` /
    /// `cursors` / `vm_ios` / `vm_spaces`) and [`accounting_inv`] (the
    /// exact reference-count equation, which couples `frames` with
    /// `regions.slot_owners` and can only be re-established by a *step*
    /// that pairs the two changes — see [`extract_frame`] /
    /// [`insert_frame`] for why the frame-only helpers must require /
    /// ensure only the structural part).
    pub open spec fn inv(self) -> bool {
        self.structural_inv() && self.accounting_inv()
    }

    /// Everything in [`inv`] **except** the accounting equation.
    /// Preserved by any helper that touches at most one of `frames` /
    /// `regions.slot_owners`, since the accounting equation is the only
    /// clause that mentions both. Frame-only helpers
    /// ([`extract_frame`] / [`insert_frame`]) require / ensure this.
    pub open spec fn structural_inv(self) -> bool {
        &&& self.regions.inv()
        // Slot-perm coverage (Design B). Every in-region slot keeps its
        // `simple_pptr::PointsTo<MetaSlot>` parked in `regions.slots`.
        // `MetaRegionOwners::inv` only gives the *forward* direction
        // (`slots.contains_key(i) ==> i < max_meta_slots()`); the reverse
        // is NOT globally true (`UniqueFrame` / `into_raw` / linked-list
        // permanently extract a slot perm). It IS true here because the
        // embedding's `Op` surface contains *no* perm-extracting
        // operation: `FrameFromUnused` re-parks the perm (modeled in
        // [`frame::frame_from_unused_embedded`]), `FrameFromInUse` /
        // `FrameDrop` / `Segment` only shared-borrow it, and every
        // region-mutating cursor op (`Map`/`Unmap`/`ProtectNext`) touches
        // `slot_owners` (refcount / `paths_in_pt`) but never the `slots`
        // map domain. This is what lets [`op_pre`] for `FrameFromUnused`
        // / `FrameFromInUse` be literally `true` (#2 / #3b fully
        // resolved): the `has_safe_slot`-guarded slot-perm precondition
        // of the relaxed exec / axiom is recovered from this clause for
        // the in-bound case and is vacuous out-of-bound.
        &&& forall|idx: usize|
            idx < max_meta_slots() ==> #[trigger] self.regions.slots.contains_key(
                idx,
            )
        // Segment-cover info is sourced directly from the `segments` map
        // via `segment_cover_count` (see `accounting_inv`'s rc equation).
        // The per-slot `raw_count` cache that previously mirrored it has
        // been retired.
        &&& forall|idx: usize|
            idx < max_meta_slots()
                ==> #[trigger] self.regions.slot_owners[idx].inner_perms.in_list.value() == 0
        &&& self.tlb_model.inv()
        &&& forall|id: VmSpaceId| #[trigger]
            self.vm_spaces.dom().contains(id) ==> self.vm_spaces[id].inv()
        &&& forall|id: CursorId| #[trigger]
            self.cursors.dom().contains(id) ==> self.cursors[id].inv()
        &&& forall|id: CursorId| #[trigger]
            self.cursors.dom().contains(id) ==> self.cursors[id].owner.metaregion_sound(
                self.regions,
            )
        &&& forall|id: CursorId| #[trigger]
            self.cursors.dom().contains(id) ==> self.vm_spaces.dom().contains(
                self.cursors[id].vm_space,
            )
        &&& forall|id: VmIoId| #[trigger] self.vm_ios.dom().contains(id) ==> self.vm_ios[id].inv()
        &&& forall|id: VmIoId| #[trigger]
            self.vm_ios.dom().contains(id) ==> (self.vm_ios[id].vm_space matches Some(vs)
                ==> self.vm_spaces.dom().contains(vs))
        &&& forall|id: VmIoId| #[trigger]
            self.vm_ios.dom().contains(id) ==> self.vm_ios[id].vm_space is Some ==> (
            self.vm_ios[id].vaddr as nat) + (self.vm_ios[id].len as nat)
                <= MAX_USERSPACE_VADDR as nat
            // `frames` is bookkeeping for outstanding `Frame` handles. Every
            // registered handle came from a *successful* `from_unused` /
            // `from_in_use`, which (post-relaxation) returns `None` unless
            // `has_safe_slot(paddr)` — so every live `FrameEntry`'s paddr is
            // in-bound. With the slot-perm / `raw_count` / `in_list`
            // coverage clauses above, this discharges `drop_pre`'s
            // `slots.contains_key` (#4-a), `raw_count == 0` (#4-b),
            // `!= REF_COUNT_UNUSED` (#4-d, from the bound), and the
            // `in_list == 0` half of the last-ref conjunct (#4-f).
        &&& forall|fid: FrameId| #[trigger]
            self.frames.dom().contains(fid) ==> has_safe_slot(
                self.frames[fid].paddr,
            )
        // Every registered handle's slot has `usage == PageUsage::Frame`.
        // True by construction: every `Op` that adds a `FrameId`
        // (`FrameFromUnused`, `FrameFromInUse`, `Query` on a tracked
        // leaf) commits to a Frame-usage slot. Carrying this in
        // `structural_inv` makes accounting_inv's Frame-scoped clauses
        // apply automatically at registered handles' paddrs and
        // simplifies `op_pre[Map]` / `step_query` / the Item 4 unmap
        // axiom (no need for the caller to re-establish usage).
        &&& forall|fid: FrameId| #[trigger]
            self.frames.dom().contains(fid) ==> self.regions.slot_owners[frame_to_index(
                self.frames[fid].paddr,
            )].usage
                == PageUsage::Frame
            // Every registered segment has a well-formed range
            // (page-aligned, in-bound, non-empty). Enforced by
            // `op_pre[SegmentFromUnused]`; carried as an invariant so
            // `step_segment_drop` can discharge `segment::drop_step`'s
            // alignment preconditions from `s.inv()` alone.
        &&& forall|sid: SegmentId| #[trigger]
            self.segments.dom().contains(sid) ==> {
                let r = self.segments[sid].range;
                &&& r.start % PAGE_SIZE == 0
                &&& r.end % PAGE_SIZE == 0
                &&& r.start < r.end
                &&& r.end <= MAX_PADDR
            }
            // Every segment-covered slot has `usage == PageUsage::Frame`.
            // True by construction: `Op::SegmentFromUnused` sets the
            // covered slots' usage to Frame, and no op transitions a
            // segment-covered slot back to non-Frame (frame_drop is gated
            // on `segment_cover_count == 0` via `op_pre[FrameDrop]`).
            // Carried here so `step_segment_drop` can derive the per-slot
            // SHARED+Frame conditions from `s.inv()` alone.
        &&& forall|sid: SegmentId, paddr: Paddr|
            #![trigger
                    self.segments.dom().contains(sid),
                    frame_to_index(paddr)]
            self.segments.dom().contains(sid) && self.segments[sid].range.start <= paddr
                < self.segments[sid].range.end && paddr % PAGE_SIZE == 0
                ==> self.regions.slot_owners[frame_to_index(paddr)].usage == PageUsage::Frame
    }

    /// Stage 5 / full #4 — EXACT reference-count accounting.
    ///
    /// Scoped to *active-head* tracked data frames: `usage == Frame`
    /// (excludes PT nodes — different rc semantics — and MMIO), and the
    /// slot is an active head (`#handles > 0 || #mappings > 0`). The
    /// active-head restriction sidesteps huge-page sub-page slots
    /// (j>0): those have `H==0`, `paths.len()==0`, yet `rc>0` via
    /// `frame_sub_pages_valid`, so they are *not* active heads and the
    /// equation does not apply to them (and `op_pre[FrameDrop]` never
    /// targets a sub-page — a `FrameEntry` paddr is always a head).
    ///
    /// For an active head: `rc` is neither sentinel, equals
    /// `#handles + #mappings`, and the slot's metadata storage is
    /// initialised (it is in use).
    ///
    /// The exact equation is *Frame-scoped*. For non-Frame `FrameEntry`
    /// slots, the residual `drop_pre` obligation (rc/storage/in_list/
    /// paths) is carried directly in `op_pre[FrameDrop]` (un-doing
    /// part of #4) until the deferred main-verification refactor
    /// strengthens `MetaSlotOwner::inv` and adds `Frame::wf(state)`.
    ///
    /// **Why split from `structural_inv`:** the equation references
    /// *both* `self.frames` (via `handle_count`) *and*
    /// `self.regions.slot_owners` (via `rc` and `paths_in_pt`), so any
    /// helper that mutates one without the other can break it
    /// transiently. The frame-only store helpers [`extract_frame`] /
    /// [`insert_frame`] therefore cannot ensure this clause alone — a
    /// step that pairs a frame change with the matching regions change
    /// (via a frame / cursor `_embedded` axiom) re-establishes it.
    pub open spec fn accounting_inv(self) -> bool {
        // Stage 5.5c absorption clauses (couple `frames` + `regions`).
        //
        // The earlier usage-independent **handle clause** (Stage 5 / 2b,
        // `H > 0 ⟹ rc ∉ {UNUSED, UNIQUE} ∧ rc ≥ H ∧ storage.is_init`)
        // was **dropped**. Two reasons:
        //
        // (a) It was load-bearing only via Verus SMT heuristics across
        //     `step_cursor_method`/`step_map`/`step_unmap`: the cursor
        //     `_embedded` axioms don't actually constrain `rc`/`storage`
        //     at the touched slot, and accounting_inv preservation
        //     across those steps was working by coincidence. Segments
        //     (Shape B) perturbed the SMT context and broke the chain
        //     — the fragility was always there.
        //
        // (b) The semantically right home for these conjuncts is the
        //     *exec layer*: `MetaSlotOwner::inv`'s SHARED branch should
        //     carry `storage.is_init() ∧ in_list.value() == 0` for any
        //     in-use rc (they're universally true, see the lifecycle
        //     analysis), and `Frame<M>` should have a `wf(state)`
        //     predicate carrying "the slot I refer to is in a valid
        //     state with `rc ≥ handles_for_this_slot`." Then the
        //     embedding's accounting could shrink to just the
        //     Frame-scoped equation (clauses below), and the cursor
        //     axiom interaction goes away because there's nothing
        //     handle-keyed to chain.
        //
        // Until the main-verification refactor in (b) lands,
        // `op_pre[FrameDrop]` carries the full residual `drop_pre`
        // directly. Frame-usage callers discharge it from the
        // Frame-scoped equation clauses below; non-Frame callers carry
        // their own reasoning.
        //
        // See the TODO in segment.rs for the full plan.
        // **UNUSED ⟹ no users.** A live PTE bumps `rc`, so reaching
        // `UNUSED` requires `paths_in_pt.is_empty()`. With segments
        // (Shape B), reaching UNUSED also requires no segment covers
        // the slot — each segment contributes 1 to rc via its
        // forgotten Frame handle.
        &&& forall|idx: usize|
            #![trigger self.regions.slot_owners[idx]]
            idx < max_meta_slots() && self.regions.slot_owners[idx].inner_perms.ref_count.value()
                == REF_COUNT_UNUSED ==> handle_count(self.frames, idx) == 0
                && self.regions.slot_owners[idx].paths_in_pt.is_empty() && segment_cover_count(
                self.segments,
                index_to_frame(idx),
            )
                == 0
            // **Frame in valid rc range ⟹ active head.** Inverse of the
            // active-head guard below — absorbs the pre-active-head assume
            // in `step_frame_from_in_use`. With segments, "active" includes
            // the segment-cover contribution.
        &&& forall|idx: usize|
            #![trigger self.regions.slot_owners[idx]]
            idx < max_meta_slots() && self.regions.slot_owners[idx].usage == PageUsage::Frame
                && self.regions.slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                && self.regions.slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNIQUE
                ==> handle_count(self.frames, idx) > 0
                || self.regions.slot_owners[idx].paths_in_pt.len() > 0 || segment_cover_count(
                self.segments,
                index_to_frame(idx),
            )
                > 0
            // **Frame-slot accounting equation.** Generalised to include
            // segment forgotten references: `rc == H + P + cover_count`.
            // Each segment in `segments` whose range covers the frame
            // contributes +1 to `rc` (via its `ManuallyDrop`'d Frame
            // handle); user-held handles contribute via `H`; live PTEs
            // contribute via `P`. With `segments` empty (pre-activation),
            // `cover_count == 0` and the equation reduces to `rc == H + P`.
        &&& forall|idx: usize|
            #![trigger self.regions.slot_owners[idx]]
            idx < max_meta_slots() && self.regions.slot_owners[idx].usage == PageUsage::Frame && (
            handle_count(self.frames, idx) > 0 || self.regions.slot_owners[idx].paths_in_pt.len()
                > 0 || segment_cover_count(self.segments, index_to_frame(idx)) > 0) ==> {
                let so = self.regions.slot_owners[idx];
                let rc = so.inner_perms.ref_count.value();
                &&& rc != REF_COUNT_UNUSED
                &&& rc != REF_COUNT_UNIQUE
                &&& rc == handle_count(self.frames, idx) + so.paths_in_pt.len()
                    + segment_cover_count(self.segments, index_to_frame(idx))
                &&& so.inner_perms.storage.is_init()
            }
    }
}

// =============================================================================
// Op enum + per-op precondition
// =============================================================================
/// Public exec API of `ostd::mm::vm_space` and `ostd::mm::io`, lifted
/// to data.
pub enum Op {
    NewVmSpace,
    DropVmSpace { vs: VmSpaceId },
    OpenCursor { vs: VmSpaceId, va: Range<Vaddr> },
    OpenCursorMut { vs: VmSpaceId, va: Range<Vaddr> },
    DropCursor { c: CursorId },
    Query { c: CursorId },
    FindNext { c: CursorId, len: usize },
    Jump { c: CursorId, va: Vaddr },
    VirtAddr { c: CursorId },
    Map { c: CursorId, fid: FrameId, prop: PageProperty },
    Unmap { c: CursorId, len: usize },
    ProtectNext { c: CursorId, len: usize },
    NewReader { vs: VmSpaceId, vaddr: Vaddr, len: usize },
    NewWriter { vs: VmSpaceId, vaddr: Vaddr, len: usize },
    NewKernelReader { vaddr: Vaddr, len: usize },
    NewKernelWriter { vaddr: Vaddr, len: usize },
    DropReader { vio: VmIoId },
    DropWriter { vio: VmIoId },
    /// Fallible `VmReader::read_val<T>`. The exec spec carries no
    /// tracked owner params (handle MODEL GAP); the embedding step
    /// is consequently a no-op on `VmStore`.
    ReaderReadVal { source: VmIoId },
    /// Fallible `VmReader::collect`. Same shape as `ReaderReadVal`.
    ReaderCollect { source: VmIoId },
    ReaderLimit { vio: VmIoId, max: usize },
    ReaderSkip { vio: VmIoId, n: usize },
    ReaderQuery { vio: VmIoId },
    /// Fallible `VmWriter::write_val<T>`. Same shape as `ReaderReadVal`.
    WriterWriteVal { writer: VmIoId },
    WriterFillZeros { vio: VmIoId, len: usize },
    WriterLimit { vio: VmIoId, max: usize },
    WriterSkip { vio: VmIoId, n: usize },
    WriterQuery { vio: VmIoId },
    /// Infallible `VmReader::read`. Produces a `consumed_w` val_owner
    /// (registered as a fresh activated Writer entry).
    Read { source: VmIoId, dest: VmIoId },
    /// Infallible `VmWriter::write`. The exec no longer surfaces
    /// `consumed_w`; the embedding does NOT create a fresh entry.
    Write { source: VmIoId, dest: VmIoId },
    /// `Frame::from_unused`: try to allocate a fresh handle on a
    /// previously-unused slot. Registers a [`FrameEntry`] on success.
    FrameFromUnused { paddr: Paddr },
    /// `Frame::from_in_use`: try to acquire a new handle on an
    /// in-use slot. Registers a [`FrameEntry`] on success
    /// (refcount of the slot increments by one).
    FrameFromInUse { paddr: Paddr },
    /// Drop one outstanding `Frame` handle. There is exactly one drop;
    /// the step branches internally on the live refcount (mirroring
    /// exec `drop`): `>= 2` decrements (slot stays SHARED), `== 1`
    /// tears down to UNUSED (requires the slot detached from the page
    /// table — `paths_in_pt.is_empty()`). See [`frame::drop_pre`].
    FrameDrop { fid: FrameId },
    /// `Segment::from_unused`: allocate a fresh segment over a range
    /// of previously-unused slots. Each frame in `range` transitions
    /// `usage == Unused` → `Frame`, `rc` 0 → 1, `raw_count` 0 → 1.
    /// Registers a [`SegmentEntry`] on success.
    SegmentFromUnused { range: Range<Paddr> },
    /// Drop a `Segment` handle. Releases the segment's forgotten
    /// reference at each frame in the range; frames whose `rc`
    /// reaches 1 transition to UNUSED.
    SegmentDrop { sid: SegmentId },
    /// `Segment::split`: split a segment at a page-aligned byte
    /// `offset` from its start, producing two segments covering the
    /// disjoint halves. `regions` is unchanged (per-paddr
    /// `cover_count` is invariant — each covered paddr lands in
    /// exactly one half). Removes `sid` from `s.segments`, inserts
    /// two fresh `SegmentEntry`s.
    SegmentSplit { sid: SegmentId, offset: usize },
    // **Op::SegmentNext is NOT modeled.** It would be the
    // conversion bridge between segment-held forgotten references
    // and user-held Frame handles — at the popped paddr:
    // `raw_count -= 1`, `cover_count -= 1`, `H += 1`, `rc` unchanged.
    // The model is laid out in [`segment::segment_next_embedded`]
    // (axiom present, proof-discharge scaffolded but ends in
    // `assume(false)`); reaching a real `s.inv()` discharge needs
    // SMT-chaining cleanup at the per-paddr assert-forall sites
    // that this pass didn't finish. Tracked as future work alongside
    // `SegmentSlice`.
    /// `Segment::next`: pop the front frame off `sid`'s range,
    /// producing a fresh `Frame<M>` handle (a new `FrameEntry`
    /// registered in `s.frames`). The segment's range shrinks by one
    /// page from the front; if it becomes empty, `sid` is removed
    /// from `s.segments`. The conversion bridge between segment-held
    /// forgotten references and user-held Frame handles: at the
    /// popped paddr `raw_count -= 1`, `cover_count -= 1`, `H += 1`,
    /// `rc` unchanged.
    SegmentNext {
        sid: SegmentId,
    },
    // **Op::SegmentSlice is NOT modeled — same exec gap as
    // `SegmentClone`, plus weaker ensures.**
    //
    // Exec [`crate::mm::frame::Segment::slice`] does
    // `inc_frame_ref_count` per frame in the sub-range (bumps `rc`
    // only, not `raw_count`) and returns just `Self` — no
    // `SegmentOwner`, so the sliced segment is un-droppable from
    // verified code. Compounding this, its `ensures` only commits to
    // `slots`/`slot_owners.dom()` preservation; the per-frame `rc`
    // bumps aren't surfaced. A faithful embedding axiom would need
    // both:
    //   1. The same exec fix as `SegmentClone`
    //      (`Frame::from_raw` precondition relaxation, weakened
    //      `relate_regions`, owner-producing API).
    //   2. Stronger exec ensures pinning the per-frame `rc`/
    //      `raw_count` deltas at sliced paddrs.
    //
    // Once both ship, the embedding can add `Op::SegmentSlice {
    // sid, sub_range }` that inserts a fresh `SegmentEntry` with the
    // sub-range (per-paddr `cover_count += 1` inside sub-range,
    // unchanged outside) and discharges accounting via the same
    // shrink-from-front machinery used by `next`.
    // **Op::SegmentClone is NOT modeled — pending exec fix.**
    //
    // Exec [`crate::mm::frame::Segment::clone`] today bumps `rc` per
    // frame (via `inc_frame_ref_count`) but doesn't bump `raw_count`
    // and doesn't produce a new `SegmentOwner`. The cloned `Segment`
    // is therefore un-droppable from verified code: `Segment::drop`
    // requires a `SegmentOwner` with `relate_regions` (currently
    // pinning `raw_count == 1` per covered slot), and the clone path
    // produces neither the owner nor the matching `raw_count` bump.
    //
    // The planned exec fix (own branch / session):
    //   1. `Frame::from_raw`: generalise `raw_count <= 1` precondition
    //      to `raw_count >= 1` and decrement (not zero) on call.
    //   2. `SegmentOwner::relate_regions`: weaken `raw_count == 1`
    //      to `raw_count >= 1`.
    //   3. Remove `RCClone for Segment`; add inherent
    //      `Segment::clone(&self, …) -> (Self, Tracked<SegmentOwner<M>>)`
    //      whose body per-frame is `from_in_use + ManuallyDrop::new`
    //      (bumping both `rc` and `raw_count`).
    //   4. Rework `Segment::drop` / `Segment::next` loop invariants
    //      for the `raw_count >= 1` form.
    //
    // Once the exec ships those, the embedding can add an `Op` variant
    // that inserts a fresh `SegmentEntry` with the same range as `sid`
    // and bumps the per-paddr `rc`/`raw_count` to match — the
    // `accounting_inv` equation `rc == H + P + cover_count` chains
    // naturally because both `rc` and `cover_count` increment together
    // at each covered paddr.
}

/// Per-op precondition — the conjunction of facts about the store that
/// must hold for an `Op` to be applied. Encodes id-existence,
/// distinctness, cross-store ref-integrity, and the *expressible*
/// portion of the exec-method preconditions (per-op `requires` from
/// the verus_spec annotations). MODEL GAPS (handle inv/wf,
/// `tlb_model.inv()` is in `VmStore::inv`, closure preconditions on
/// `protect_next`, `size_of::<T>()` range bounds on
/// `read_val`/`write_val`/`collect`) are documented in
/// [`super::cursor`] and [`super::io`] axiom comments.
///
/// [`step`] requires `op_pre(*old(s), op)`. Callers must establish the
/// precondition for the specific Op variant they're about to apply.
///
/// SOUNDNESS: when we're done building this model, `op_pre` must be
/// permissive enough to permit every possible call trace. That means
/// that these conditions should reduce to
/// "the relevant objects exist in the store".
pub open spec fn op_pre<'rcu>(s: VmStore<'rcu>, op: Op) -> bool {
    match op {
        Op::NewVmSpace => true,
        Op::DropVmSpace { vs } => s.vm_spaces.dom().contains(vs) && (forall|c: CursorId| #[trigger]
            s.cursors.dom().contains(c) ==> s.cursors[c].vm_space != vs) && (forall|v: VmIoId|
         #[trigger]
            s.vm_ios.dom().contains(v) ==> s.vm_ios[v].vm_space != Some(vs)),
        Op::OpenCursor { vs, va: _ } => s.vm_spaces.dom().contains(vs),
        Op::OpenCursorMut { vs, va: _ } => s.vm_spaces.dom().contains(vs),
        Op::DropCursor { c } => s.cursors.dom().contains(c),
        Op::Query { c } => s.cursors.dom().contains(c),
        Op::FindNext { c, len: _ } => s.cursors.dom().contains(c),
        Op::Jump { c, va: _ } => s.cursors.dom().contains(c),
        Op::VirtAddr { c } => s.cursors.dom().contains(c),
        // Op::Map consumes the FrameEntry for the mapped frame. The
        // consumed handle's reference at the slot is "transferred" to
        // the new PTE — exec map ManuallyDrops the input UFrame
        // (raw_count++ avoided since rc stays bumped) while the PTE
        // adds 1 to rc; net 0 at the mapped slot. This is exactly what
        // lets `accounting_inv`'s clause 4 (`rc == H + P`) chain
        // across map: H decrements (entry consumed), P increments (path
        // inserted), rc unchanged.
        //
        // (Once required `usage == Frame` at the mapped slot; that
        // clause now lives in `structural_inv`'s FrameId⟹Frame-usage
        // invariant, automatically discharged from `s.frames.contains(fid)`.)
        Op::Map { c, fid, prop: _ } => s.cursors.dom().contains(c) && s.frames.dom().contains(fid),
        Op::Unmap { c, len: _ } => s.cursors.dom().contains(c),
        Op::ProtectNext { c, len: _ } => s.cursors.dom().contains(c),
        Op::NewReader { vs, vaddr: _, len: _ } => s.vm_spaces.dom().contains(vs),
        Op::NewWriter { vs, vaddr: _, len: _ } => s.vm_spaces.dom().contains(vs),
        Op::NewKernelReader { vaddr: _, len: _ } => true,
        Op::NewKernelWriter { vaddr: _, len: _ } => true,
        Op::DropReader { vio } => s.vm_ios.dom().contains(vio),
        Op::DropWriter { vio } => s.vm_ios.dom().contains(vio),
        Op::ReaderReadVal { source } => s.vm_ios.dom().contains(source),
        Op::ReaderCollect { source } => s.vm_ios.dom().contains(source),
        Op::ReaderLimit { vio, max: _ } => s.vm_ios.dom().contains(vio),
        Op::ReaderSkip { vio, n: _ } => s.vm_ios.dom().contains(vio),
        Op::ReaderQuery { vio } => s.vm_ios.dom().contains(vio),
        Op::WriterWriteVal { writer } => s.vm_ios.dom().contains(writer),
        Op::WriterFillZeros { vio, len: _ } => s.vm_ios.dom().contains(vio),
        Op::WriterLimit { vio, max: _ } => s.vm_ios.dom().contains(vio),
        Op::WriterSkip { vio, n: _ } => s.vm_ios.dom().contains(vio),
        Op::WriterQuery { vio } => s.vm_ios.dom().contains(vio),
        // exec Infallible `read` is *typed* `VmReader<Infallible>` →
        // `VmWriter<Infallible>`: `source`/`dest` must be a kernel
        // reader/writer (operand well-formedness, not a runtime check —
        // see `VmIoEntry::is_kernel_reader`). `source != dest` keeps the
        // two tracked `&mut` borrows disjoint.
        Op::Read { source, dest } => s.vm_ios.dom().contains(source) && s.vm_ios.dom().contains(
            dest,
        ) && source != dest && s.vm_ios[source].is_kernel_reader()
            && s.vm_ios[dest].is_kernel_writer(),
        // exec Infallible `write`: same operand typing as `read`.
        Op::Write { source, dest } => s.vm_ios.dom().contains(source) && s.vm_ios.dom().contains(
            dest,
        ) && source != dest && s.vm_ios[source].is_kernel_reader()
            && s.vm_ios[dest].is_kernel_writer(),
        Op::FrameFromUnused { paddr: _ } => true,
        Op::FrameFromInUse { paddr: _ } => true,
        // `op_pre[FrameDrop]` is just id-existence + the segment-cover
        // constraint. All other `drop_pre` conjuncts (rc not in
        // sentinels, rc <= MAX, storage.is_init, in_list == 0,
        // rc == 1 ⟹ paths empty / handle_count == 1) plus the
        // handle-clause are derived inside [`step_frame_drop`] from
        // `s.inv()` via [`lemma_frame_drop_pre_derivable`] — the
        // embedding-level `Frame::wf(state)` (Item 2 in the module-
        // docs roadmap). The lemma chains: structural FrameId⟹Frame
        // + structural raw_count == segment_cover_count + accounting
        // clause 4 + `MetaSlotOwner::inv` SHARED branch (Item 1)
        // covers every residual.
        //
        // The remaining `segment_cover_count == 0` is a real per-op
        // obligation — it's the same shape as Item 5 segment
        // disjointness — so it stays in `op_pre` until segments are
        // activated and we can tie it to the segment store directly.
        Op::FrameDrop { fid } => s.frames.dom().contains(fid) && segment_cover_count(
            s.segments,
            s.frames[fid].paddr,
        ) == 0,
        // `Segment::from_unused`: aligned, in-bound, non-empty range;
        // every frame in `range` is currently UNUSED (so we can
        // allocate fresh references). The UNUSED condition is what
        // `accounting_inv` clause 1 ⟹ no users gives us at the slot
        // level; combined with `structural_inv`'s slot-perm coverage,
        // it discharges the `segment_from_unused_embedded` axiom's
        // requires verbatim.
        Op::SegmentFromUnused { range } => range.start % PAGE_SIZE == 0 && range.end % PAGE_SIZE
            == 0 && range.start < range.end && range.end <= MAX_PADDR && forall|paddr: Paddr|
            #![trigger frame_to_index(paddr)]
            (range.start <= paddr < range.end && paddr % PAGE_SIZE == 0)
                ==> s.regions.slot_owners[frame_to_index(paddr)].inner_perms.ref_count.value()
                == REF_COUNT_UNUSED,
        // `Segment` drop: id-existence + range well-formedness is
        // satisfied by every registered `SegmentEntry`; the per-slot
        // SHARED+Frame conditions are derived inside `step_segment_drop`
        // from `s.inv()` (analogue of `lemma_frame_drop_pre_derivable`
        // for segments).
        Op::SegmentDrop { sid } => s.segments.dom().contains(sid),
        // `Segment::split`: id-existence + offset must be page-aligned
        // and strictly between 0 and the segment's size (mirroring
        // exec `assert!`s). Range well-formedness comes from
        // `structural_inv`.
        Op::SegmentSplit { sid, offset } => s.segments.dom().contains(sid) && offset % PAGE_SIZE
            == 0 && 0 < offset && offset < (s.segments[sid].range.end
            - s.segments[sid].range.start),
        // `Segment::next`: id-existence. Range well-formedness from
        // `structural_inv` (range.start < range.end + page-aligned).
        Op::SegmentNext { sid } => s.segments.dom().contains(sid),
    }
}

// =============================================================================
// Store helpers: extract / insert. These are the *only* functions that
// have preconditions about store membership; per-op steps don't.
// =============================================================================
impl<'rcu> VmStore<'rcu> {
    /// Removes the VmSpaceOwner at `vs` from the store and returns it.
    /// Requires no cursor or VmIo refers to `vs`, and no activated
    /// ranges remain on `vs` (otherwise `inv` would break after the
    /// removal).
    pub proof fn extract_vm_space(tracked &mut self, vs: VmSpaceId) -> (tracked res: VmSpaceOwner)
        requires
            old(self).inv(),
            old(self).vm_spaces.dom().contains(vs),
            forall|c: CursorId| #[trigger]
                old(self).cursors.dom().contains(c) ==> old(self).cursors[c].vm_space != vs,
            forall|v: VmIoId| #[trigger]
                old(self).vm_ios.dom().contains(v) ==> old(self).vm_ios[v].vm_space != Some(vs),
        ensures
            final(self).regions == old(self).regions,
            final(self).tlb_model == old(self).tlb_model,
            final(self).vm_spaces == old(self).vm_spaces.remove(vs),
            final(self).cursors == old(self).cursors,
            final(self).vm_ios == old(self).vm_ios,
            final(self).frames == old(self).frames,
            final(self).segments == old(self).segments,
            res == old(self).vm_spaces[vs],
            final(self).inv(),
    {
        self.vm_spaces.tracked_remove(vs)
    }

    /// Inserts a VmSpaceOwner at the given fresh id. Requires the id is
    /// not already used and the owner satisfies its invariant.
    pub proof fn insert_vm_space(tracked &mut self, vs: VmSpaceId, tracked owner: VmSpaceOwner)
        requires
            old(self).inv(),
            !old(self).vm_spaces.dom().contains(vs),
            owner.inv(),
        ensures
            final(self).regions == old(self).regions,
            final(self).tlb_model == old(self).tlb_model,
            final(self).vm_spaces == old(self).vm_spaces.insert(vs, owner),
            final(self).cursors == old(self).cursors,
            final(self).vm_ios == old(self).vm_ios,
            final(self).frames == old(self).frames,
            final(self).segments == old(self).segments,
            final(self).inv(),
    {
        self.vm_spaces.tracked_insert(vs, owner);
    }

    /// Removes the cursor entry at `c` from the store and returns it.
    pub proof fn extract_cursor(tracked &mut self, c: CursorId) -> (tracked res: CursorEntry<'rcu>)
        requires
            old(self).inv(),
            old(self).cursors.dom().contains(c),
        ensures
            final(self).regions == old(self).regions,
            final(self).tlb_model == old(self).tlb_model,
            final(self).vm_spaces == old(self).vm_spaces,
            final(self).cursors == old(self).cursors.remove(c),
            final(self).vm_ios == old(self).vm_ios,
            final(self).frames == old(self).frames,
            final(self).segments == old(self).segments,
            res == old(self).cursors[c],
            final(self).inv(),
    {
        self.cursors.tracked_remove(c)
    }

    /// Inserts a cursor entry at the given fresh id. Requires the id is
    /// not already used, the entry satisfies its inv, the entry's
    /// `vm_space` is in the store, and the entry's owner is sound w.r.t.
    /// the store's regions.
    pub proof fn insert_cursor(tracked &mut self, c: CursorId, tracked entry: CursorEntry<'rcu>)
        requires
            old(self).inv(),
            !old(self).cursors.dom().contains(c),
            entry.inv(),
            entry.owner.metaregion_sound(old(self).regions),
            old(self).vm_spaces.dom().contains(entry.vm_space),
        ensures
            final(self).regions == old(self).regions,
            final(self).tlb_model == old(self).tlb_model,
            final(self).vm_spaces == old(self).vm_spaces,
            final(self).cursors == old(self).cursors.insert(c, entry),
            final(self).vm_ios == old(self).vm_ios,
            final(self).frames == old(self).frames,
            final(self).segments == old(self).segments,
            final(self).inv(),
    {
        self.cursors.tracked_insert(c, entry);
    }

    /// Removes the VmIo entry at `vio` from the store and returns it.
    pub proof fn extract_vm_io(tracked &mut self, vio: VmIoId) -> (tracked res: VmIoEntry)
        requires
            old(self).inv(),
            old(self).vm_ios.dom().contains(vio),
        ensures
            final(self).regions == old(self).regions,
            final(self).tlb_model == old(self).tlb_model,
            final(self).vm_spaces == old(self).vm_spaces,
            final(self).cursors == old(self).cursors,
            final(self).vm_ios == old(self).vm_ios.remove(vio),
            final(self).frames == old(self).frames,
            final(self).segments == old(self).segments,
            res == old(self).vm_ios[vio],
            final(self).inv(),
    {
        self.vm_ios.tracked_remove(vio)
    }

    /// Inserts a VmIo entry at the given fresh id. Requires the id is
    /// not already used, the entry satisfies its inv, the entry's
    /// `vm_space` (if `Some`) refers to a live VmSpace, the range
    /// bound holds when `vm_space` is `Some`, and (if the entry is
    /// activated) its owner range is disjoint from every existing
    /// activated entry's owner range (preserves the pairwise-disjoint
    /// invariant in [`VmStore::inv`]).
    pub proof fn insert_vm_io(tracked &mut self, vio: VmIoId, tracked entry: VmIoEntry)
        requires
            old(self).inv(),
            !old(self).vm_ios.dom().contains(vio),
            entry.inv(),
            entry.vm_space matches Some(vs) ==> old(self).vm_spaces.dom().contains(vs),
            entry.vm_space is Some ==> (entry.vaddr as nat) + (entry.len as nat)
                <= MAX_USERSPACE_VADDR as nat,
        ensures
            final(self).regions == old(self).regions,
            final(self).tlb_model == old(self).tlb_model,
            final(self).vm_spaces == old(self).vm_spaces,
            final(self).cursors == old(self).cursors,
            final(self).vm_ios == old(self).vm_ios.insert(vio, entry),
            final(self).frames == old(self).frames,
            final(self).segments == old(self).segments,
            final(self).inv(),
    {
        self.vm_ios.tracked_insert(vio, entry);
    }

    /// Removes the FrameEntry at `fid` from the store.
    ///
    /// Requires / ensures only [`structural_inv`] — not full [`inv`].
    /// Removing a frame handle without coordinating with the slot's
    /// `ref_count` breaks [`accounting_inv`] transiently; the *step*
    /// that calls this is responsible for pairing it with the matching
    /// `frame::drop_step` (or `cursor::map_step` once Op::Map consumes
    /// a tracked frame) and re-establishing accounting at the end.
    pub proof fn extract_frame(tracked &mut self, fid: FrameId) -> (tracked res: FrameEntry)
        requires
            old(self).structural_inv(),
            old(self).frames.dom().contains(fid),
        ensures
            final(self).regions == old(self).regions,
            final(self).tlb_model == old(self).tlb_model,
            final(self).vm_spaces == old(self).vm_spaces,
            final(self).cursors == old(self).cursors,
            final(self).vm_ios == old(self).vm_ios,
            final(self).frames == old(self).frames.remove(fid),
            final(self).segments == old(self).segments,
            res == old(self).frames[fid],
            final(self).structural_inv(),
    {
        self.frames.tracked_remove(fid)
    }

    /// Inserts a FrameEntry at the given fresh id. Requires the entry's
    /// paddr be `has_safe_slot` — the per-`FrameEntry` clause of
    /// [`VmStore::inv`] (#4). Every caller establishes this from the
    /// `from_*` axioms' `!has_safe_slot ==> None` (a registered handle
    /// is necessarily in-bound).
    ///
    /// Requires / ensures only [`structural_inv`] — see [`extract_frame`]
    /// for the accounting/structural split rationale.
    pub proof fn insert_frame(tracked &mut self, fid: FrameId, tracked entry: FrameEntry)
        requires
            old(self).structural_inv(),
            !old(self).frames.dom().contains(fid),
            has_safe_slot(entry.paddr),
            // The slot we're registering a handle at must be Frame-usage:
            // structural_inv's FrameId⟹Frame-usage clause. Every caller
            // discharges this from the `from_*` / query axioms which
            // commit to Frame-usage at the cloned slot.
            old(self).regions.slot_owners[frame_to_index(entry.paddr)].usage == PageUsage::Frame,
        ensures
            final(self).regions == old(self).regions,
            final(self).tlb_model == old(self).tlb_model,
            final(self).vm_spaces == old(self).vm_spaces,
            final(self).cursors == old(self).cursors,
            final(self).vm_ios == old(self).vm_ios,
            final(self).frames == old(self).frames.insert(fid, entry),
            final(self).segments == old(self).segments,
            final(self).structural_inv(),
    {
        self.frames.tracked_insert(fid, entry);
    }

    /// Removes the SegmentEntry at `sid` from the store. **Does NOT**
    /// ensure `structural_inv` — extracting a segment without a paired
    /// `regions` decrement breaks the
    /// `raw_count == segment_cover_count` clause at every paddr the
    /// segment covered. The caller's step proof must restore it via
    /// [`segment::drop_step`] before observing `s.inv()` again.
    pub proof fn extract_segment(tracked &mut self, sid: SegmentId) -> (tracked res: SegmentEntry)
        requires
            old(self).segments.dom().contains(sid),
        ensures
            final(self).regions == old(self).regions,
            final(self).tlb_model == old(self).tlb_model,
            final(self).vm_spaces == old(self).vm_spaces,
            final(self).cursors == old(self).cursors,
            final(self).vm_ios == old(self).vm_ios,
            final(self).frames == old(self).frames,
            final(self).segments == old(self).segments.remove(sid),
            res == old(self).segments[sid],
    {
        self.segments.tracked_remove(sid)
    }

    /// Inserts a SegmentEntry at a fresh id. **Does NOT** ensure
    /// `structural_inv` — the caller must pair this with a `regions`
    /// `raw_count` bump at every covered paddr (via
    /// [`segment::from_unused_step`]) before observing `s.inv()`.
    pub proof fn insert_segment(tracked &mut self, sid: SegmentId, tracked entry: SegmentEntry)
        requires
            !old(self).segments.dom().contains(sid),
        ensures
            final(self).regions == old(self).regions,
            final(self).tlb_model == old(self).tlb_model,
            final(self).vm_spaces == old(self).vm_spaces,
            final(self).cursors == old(self).cursors,
            final(self).vm_ios == old(self).vm_ios,
            final(self).frames == old(self).frames,
            final(self).segments == old(self).segments.insert(sid, entry),
    {
        self.segments.tracked_insert(sid, entry);
    }
}

// =============================================================================
// One-step soundness theorem.
// =============================================================================
/// One-step soundness theorem.
///
/// `op_pre(*old(s), op)` is the per-op precondition. Each match arm
/// extracts the relevant entries from the store, calls the per-op step
/// (which has neither preconditions nor `if`-guards on store membership),
/// and inserts any modified or freshly-produced entries back.
pub proof fn step<'rcu>(tracked s: &mut VmStore<'rcu>, op: Op)
    requires
        old(s).inv(),
        op_pre(*old(s), op),
    ensures
        final(s).inv(),
{
    match op {
        Op::NewVmSpace => step_new_vm_space(s),
        Op::DropVmSpace { vs } => step_drop_vm_space(s, vs),
        Op::OpenCursor { vs, va } => step_open_cursor(s, vs, va),
        Op::OpenCursorMut { vs, va } => step_open_cursor_mut(s, vs, va),
        Op::DropCursor { c } => step_drop_cursor(s, c),
        Op::Query { c } => step_query(s, c),
        Op::FindNext { c, len } => step_find_next(s, c, len),
        Op::Jump { c, va } => step_jump(s, c, va),
        Op::VirtAddr { c: _ } => {},
        Op::Map { c, fid, prop } => step_map(s, c, fid, prop),
        Op::Unmap { c, len } => step_unmap(s, c, len),
        Op::ProtectNext { c, len } => step_protect_next(s, c, len),
        Op::NewReader { vs, vaddr, len } => step_new_vm_io(s, vs, vaddr, len, VmIoKind::Reader),
        Op::NewWriter { vs, vaddr, len } => step_new_vm_io(s, vs, vaddr, len, VmIoKind::Writer),
        Op::NewKernelReader { vaddr, len } => step_new_kernel_vm_io(
            s,
            vaddr,
            len,
            VmIoKind::Reader,
        ),
        Op::NewKernelWriter { vaddr, len } => step_new_kernel_vm_io(
            s,
            vaddr,
            len,
            VmIoKind::Writer,
        ),
        Op::DropReader { vio } => step_drop_vm_io(s, vio),
        Op::DropWriter { vio } => step_drop_vm_io(s, vio),
        // Fallible variants: handle-only, no embedding state changes.
        Op::ReaderReadVal { source: _ } => {},
        Op::ReaderCollect { source: _ } => {},
        Op::WriterWriteVal { writer: _ } => {},
        Op::ReaderLimit { vio, max } => step_vm_io_method(s, vio, io::VmIoMethod::ReaderLimit(max)),
        Op::ReaderSkip { vio, n } => step_vm_io_method(s, vio, io::VmIoMethod::ReaderSkip(n)),
        Op::ReaderQuery { vio: _ } => {},
        Op::WriterFillZeros { vio, len } => step_vm_io_method(
            s,
            vio,
            io::VmIoMethod::WriterFillZeros(len),
        ),
        Op::WriterLimit { vio, max } => step_vm_io_method(s, vio, io::VmIoMethod::WriterLimit(max)),
        Op::WriterSkip { vio, n } => step_vm_io_method(s, vio, io::VmIoMethod::WriterSkip(n)),
        Op::WriterQuery { vio: _ } => {},
        // Infallible `read`: produces a fresh activated-Writer val_owner.
        Op::Read { source, dest } => step_read(s, source, dest),
        // Infallible `write`: no longer surfaces consumed_w; just
        // mutates source/dest owners.
        Op::Write { source, dest } => step_write(s, source, dest),
        Op::FrameFromUnused { paddr } => step_frame_from_unused(s, paddr),
        Op::FrameFromInUse { paddr } => step_frame_from_in_use(s, paddr),
        Op::FrameDrop { fid } => step_frame_drop(s, fid),
        Op::SegmentFromUnused { range } => step_segment_from_unused(s, range),
        Op::SegmentDrop { sid } => step_segment_drop(s, sid),
        Op::SegmentSplit { sid, offset } => step_segment_split(s, sid, offset),
        Op::SegmentNext { sid } => step_segment_next(s, sid),
    }
}

// --- Per-arm proof helpers (kept individually so SMT context stays small) ---
/// Stage 5.3: [`accounting_inv`] survives a step that only allocates
/// fresh page-table nodes. `VmSpace::new` / `VmSpace::cursor*` mutate
/// `regions` solely by spinning up PT nodes — their `_embedded` axioms
/// guarantee every *changed* slot went `UNUSED → non-UNUSED, non-Frame`
/// (the changed-slots clause) and left `frames` untouched.
///
/// Under those two facts every slot an accounting clause cares about is
/// provably *unchanged*: a slot carrying a handle, a Frame-usage slot,
/// and a non-UNUSED slot each contradict one hypothesis of the
/// `UNUSED → non-UNUSED, non-Frame` transition, so the old clause
/// carries verbatim.
///
/// Shared by [`step_new_vm_space`], [`step_open_cursor`] and
/// [`step_open_cursor_mut`].
proof fn lemma_accounting_preserved_by_pt_alloc<'rcu>(s_old: VmStore<'rcu>, s_new: VmStore<'rcu>)
    requires
        s_old.inv(),
        s_new.frames == s_old.frames,
        // Segments unchanged ⟹ `segment_cover_count` unchanged.
        s_new.segments == s_old.segments,
        forall|i: usize|
            #![trigger s_new.regions.slot_owners[i]]
            s_new.regions.slot_owners[i] != s_old.regions.slot_owners[i] ==> {
                &&& s_old.regions.slot_owners[i].inner_perms.ref_count.value() == REF_COUNT_UNUSED
                &&& s_new.regions.slot_owners[i].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                &&& s_new.regions.slot_owners[i].usage != PageUsage::Frame
            },
    ensures
        s_new.accounting_inv(),
        // PT-alloc preserves the FrameId⟹Frame-usage structural clause:
        // every existing registered handle's slot was non-UNUSED pre
        // (rc != UNUSED from clause 4 with H >= 1), so PT-alloc's
        // requires (only UNUSED slots may change) leaves it untouched.
        forall|fid: FrameId| #[trigger]
            s_new.frames.dom().contains(fid) ==> s_new.regions.slot_owners[frame_to_index(
                s_new.frames[fid].paddr,
            )].usage == PageUsage::Frame,
        // Likewise for segment-covered ⟹ Frame-usage.
        forall|sid: SegmentId, paddr: Paddr|
            #![trigger
                s_new.segments.dom().contains(sid),
                frame_to_index(paddr)]
            s_new.segments.dom().contains(sid) && s_new.segments[sid].range.start <= paddr
                < s_new.segments[sid].range.end && paddr % PAGE_SIZE == 0
                ==> s_new.regions.slot_owners[frame_to_index(paddr)].usage == PageUsage::Frame,
{
    // Clause 2 — UNUSED ⟹ no users. An UNUSED slot in `s_new` is
    // unchanged (a transitioned slot is non-UNUSED in `s_new`).
    assert forall|idx: usize|
        #![trigger s_new.regions.slot_owners[idx]]
        idx < max_meta_slots() && s_new.regions.slot_owners[idx].inner_perms.ref_count.value()
            == REF_COUNT_UNUSED implies handle_count(s_new.frames, idx) == 0
        && s_new.regions.slot_owners[idx].paths_in_pt.is_empty() && segment_cover_count(
        s_new.segments,
        index_to_frame(idx),
    ) == 0 by {
        assert(s_new.regions.slot_owners[idx] == s_old.regions.slot_owners[idx]);
    };
    // Clause 3 — Frame ∧ non-sentinel ⟹ active head. A Frame-usage slot
    // in `s_new` is unchanged (a transitioned slot is non-Frame).
    assert forall|idx: usize|
        #![trigger s_new.regions.slot_owners[idx]]
        idx < max_meta_slots() && s_new.regions.slot_owners[idx].usage == PageUsage::Frame
            && s_new.regions.slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
            && s_new.regions.slot_owners[idx].inner_perms.ref_count.value()
            != REF_COUNT_UNIQUE implies handle_count(s_new.frames, idx) > 0
        || s_new.regions.slot_owners[idx].paths_in_pt.len() > 0 || segment_cover_count(
        s_new.segments,
        index_to_frame(idx),
    ) > 0 by {
        assert(s_new.regions.slot_owners[idx] == s_old.regions.slot_owners[idx]);
    };
    // Clause 4 — the accounting equation. Same: a Frame-usage slot in
    // `s_new` is unchanged, so the old equation carries.
    assert forall|idx: usize|
        #![trigger s_new.regions.slot_owners[idx]]
        idx < max_meta_slots() && s_new.regions.slot_owners[idx].usage == PageUsage::Frame && (
        handle_count(s_new.frames, idx) > 0 || s_new.regions.slot_owners[idx].paths_in_pt.len() > 0
            || segment_cover_count(s_new.segments, index_to_frame(idx)) > 0) implies {
        let so = s_new.regions.slot_owners[idx];
        let rc = so.inner_perms.ref_count.value();
        &&& rc != REF_COUNT_UNUSED
        &&& rc != REF_COUNT_UNIQUE
        &&& rc == handle_count(s_new.frames, idx) + so.paths_in_pt.len() + segment_cover_count(
            s_new.segments,
            index_to_frame(idx),
        )
        &&& so.inner_perms.storage.is_init()
    } by {
        assert(s_new.regions.slot_owners[idx] == s_old.regions.slot_owners[idx]);
    };
    // Discharge segment-covered ⟹ Frame-usage. Covered slots have
    // cover_count >= 1 ⟹ accounting clause 3 with usage == Frame
    // (from old structural) ⟹ rc != UNUSED. PT-alloc's requires
    // ⟹ slot unchanged ⟹ usage still Frame.
    assert forall|sid: SegmentId, paddr: Paddr|
        #![trigger
            s_new.segments.dom().contains(sid),
            frame_to_index(paddr)]
        s_new.segments.dom().contains(sid) && s_new.segments[sid].range.start <= paddr
            < s_new.segments[sid].range.end && paddr % PAGE_SIZE
            == 0 implies s_new.regions.slot_owners[frame_to_index(paddr)].usage
        == PageUsage::Frame by {
        let idx = frame_to_index(paddr);
        // From old structural: covered ⟹ Frame.
        assert(s_old.regions.slot_owners[idx].usage == PageUsage::Frame);
        // From old accounting clause 4: cover >= 1 ⟹ active head ⟹
        // rc ∈ valid SHARED range ⟹ rc != UNUSED.
        lemma_segment_cover_contains(s_old.segments, sid, paddr);
        assert(s_old.regions.slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED);
        // PT-alloc unchanged.
        assert(s_new.regions.slot_owners[idx] == s_old.regions.slot_owners[idx]);
    };
    // Discharge the FrameId⟹Frame-usage clause. For every registered
    // handle, pre rc != UNUSED (from `s_old.accounting_inv` clause 4
    // with H >= 1 + usage == Frame from `s_old.structural_inv`), so
    // PT-alloc's requires (changed ⟹ pre UNUSED) leaves the slot
    // untouched and usage stays Frame.
    assert forall|fid: FrameId| #[trigger]
        s_new.frames.dom().contains(fid) implies s_new.regions.slot_owners[frame_to_index(
        s_new.frames[fid].paddr,
    )].usage == PageUsage::Frame by {
        let idx = frame_to_index(s_new.frames[fid].paddr);
        // pre H >= 1 since `fid` is in `s_old.frames.dom()`.
        assert(s_old.frames.dom().filter(
            |gid: FrameId| frame_to_index(s_old.frames[gid].paddr) == idx,
        ).contains(fid));
        assert(handle_count(s_old.frames, idx) >= 1);
        // pre accounting_inv clause 4 ⟹ pre rc != UNUSED.
        assert(s_old.regions.slot_owners[idx].usage == PageUsage::Frame);
        assert(s_old.regions.slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED);
        // PT-alloc's requires: changed ⟹ pre UNUSED. Contrapositive:
        // pre non-UNUSED ⟹ unchanged.
        assert(s_new.regions.slot_owners[idx] == s_old.regions.slot_owners[idx]);
    };
}

proof fn step_new_vm_space<'rcu>(tracked s: &mut VmStore<'rcu>)
    requires
        old(s).inv(),
    ensures
        final(s).inv(),
{
    let ghost s_before = *s;
    let tracked owner = vm_space::new_vm_space_step(&mut s.regions);
    let ghost id = fresh_vm_space_id(s.vm_spaces);
    axiom_fresh_vm_space_id_not_in_dom(s.vm_spaces);
    // `VmSpace::new` only allocates fresh PT nodes; accounting carries
    // (every changed slot went UNUSED → non-UNUSED PT node).
    lemma_accounting_preserved_by_pt_alloc(s_before, *s);
    s.insert_vm_space(id, owner);
}

proof fn step_drop_vm_space<'rcu>(tracked s: &mut VmStore<'rcu>, vs: VmSpaceId)
    requires
        old(s).inv(),
        old(s).vm_spaces.dom().contains(vs),
        forall|c: CursorId| #[trigger]
            old(s).cursors.dom().contains(c) ==> old(s).cursors[c].vm_space != vs,
        forall|v: VmIoId| #[trigger]
            old(s).vm_ios.dom().contains(v) ==> old(s).vm_ios[v].vm_space != Some(vs),
    ensures
        final(s).inv(),
{
    let tracked owner = s.extract_vm_space(vs);
    vm_space::drop_vm_space_step(owner);
}

proof fn step_open_cursor<'rcu>(tracked s: &mut VmStore<'rcu>, vs: VmSpaceId, va: Range<Vaddr>)
    requires
        old(s).inv(),
        old(s).vm_spaces.dom().contains(vs),
    ensures
        final(s).inv(),
{
    let ghost s_before = *s;
    let tracked vm_space_ref = s.vm_spaces.tracked_borrow(vs);
    let tracked res = cursor::open_cursor_step(vm_space_ref, &mut s.regions, vs, va);
    // `VmSpace::cursor` only allocates fresh PT nodes; accounting
    // carries (every changed slot went UNUSED → non-UNUSED PT node).
    lemma_accounting_preserved_by_pt_alloc(s_before, *s);
    match res {
        Option::Some(entry) => {
            let ghost id = fresh_cursor_id(s.cursors);
            axiom_fresh_cursor_id_not_in_dom(s.cursors);
            s.insert_cursor(id, entry);
        },
        Option::None => {},
    }
}

proof fn step_open_cursor_mut<'rcu>(tracked s: &mut VmStore<'rcu>, vs: VmSpaceId, va: Range<Vaddr>)
    requires
        old(s).inv(),
        old(s).vm_spaces.dom().contains(vs),
    ensures
        final(s).inv(),
{
    let ghost s_before = *s;
    let tracked vm_space_ref = s.vm_spaces.tracked_borrow(vs);
    let tracked res = cursor::open_cursor_mut_step(vm_space_ref, &mut s.regions, vs, va);
    // `VmSpace::cursor_mut` only allocates fresh PT nodes; accounting
    // carries (every changed slot went UNUSED → non-UNUSED PT node).
    lemma_accounting_preserved_by_pt_alloc(s_before, *s);
    match res {
        Option::Some(entry) => {
            let ghost id = fresh_cursor_id(s.cursors);
            axiom_fresh_cursor_id_not_in_dom(s.cursors);
            s.insert_cursor(id, entry);
        },
        Option::None => {},
    }
}

proof fn step_drop_cursor<'rcu>(tracked s: &mut VmStore<'rcu>, c: CursorId)
    requires
        old(s).inv(),
        old(s).cursors.dom().contains(c),
    ensures
        final(s).inv(),
{
    let tracked entry = s.extract_cursor(c);
    cursor::drop_cursor_step(entry);
}

proof fn step_query<'rcu>(tracked s: &mut VmStore<'rcu>, c: CursorId)
    requires
        old(s).inv(),
        old(s).cursors.dom().contains(c),
    ensures
        final(s).inv(),
{
    let ghost old_frames = s.frames;
    let ghost old_regions = s.regions;
    let tracked mut entry = s.extract_cursor(c);
    let ghost res = cursor::cursor_query_step(&mut entry, &mut s.regions);
    match res {
        Option::None => {
            // No clone happened — slot_owners fully preserved per axiom,
            // s.frames unchanged. accounting_inv chains directly.
            s.insert_cursor(c, entry);
        },
        Option::Some(paddr) => {
            // Exec query cloned a tracked leaf at `paddr` (rc++ at the
            // leaf slot). Register a fresh `FrameEntry` so `H` at that
            // slot grows by 1 in lockstep with `rc`, keeping
            // `accounting_inv`'s clause 4 (`rc == H + P`) chained.
            let ghost target_idx = frame_to_index(paddr);
            s.regions.inv_implies_correct_addr(paddr);
            let ghost id = fresh_frame_id(s.frames);
            axiom_fresh_frame_id_not_in_dom(s.frames);
            let ghost entry_paddr = paddr;
            let tracked frame_entry = axiom_frame_entry_new(paddr);
            s.insert_frame(id, frame_entry);
            // Pre target_idx: usage == Frame (axiom), so by pre clause 3
            // either H_pre > 0 or paths_pre > 0; clause 4 gives
            // pre rc != UNUSED ∧ pre rc != UNIQUE ∧
            // pre rc == pre H + pre paths ∧ pre storage.is_init.
            // The cursor axiom on Some bumps rc to pre rc + 1 (≤ MAX),
            // preserves usage / paths / storage at target_idx, and
            // preserves all other slots fully.
            assert(s.regions.slot_owners[target_idx].usage == PageUsage::Frame);
            // Discharge accounting_inv on (new regions, new frames).
            assert forall|idx: usize|
                #![trigger s.regions.slot_owners[idx]]
                idx < max_meta_slots() && s.regions.slot_owners[idx].inner_perms.ref_count.value()
                    == REF_COUNT_UNUSED implies handle_count(s.frames, idx) == 0
                && s.regions.slot_owners[idx].paths_in_pt.is_empty() && segment_cover_count(
                s.segments,
                index_to_frame(idx),
            ) == 0 by {
                lemma_handle_count_insert_fresh(old_frames, id, frame_entry, idx);
                if idx == target_idx {
                    // post rc = pre rc + 1; pre rc != UNUSED (clause 4),
                    // so post rc > 1 ≠ UNUSED. Contradiction.
                    assert(false);
                } else {
                    // Other slot: fully preserved (cursor axiom), so
                    // pre UNUSED ⟹ pre H=0 ∧ pre paths empty ∧ cover==0;
                    // H unchanged at idx != target_idx (lemma); segments
                    // unchanged.
                    assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
                }
            };
            assert forall|idx: usize|
                #![trigger s.regions.slot_owners[idx]]
                idx < max_meta_slots() && s.regions.slot_owners[idx].usage == PageUsage::Frame
                    && s.regions.slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                    && s.regions.slot_owners[idx].inner_perms.ref_count.value()
                    != REF_COUNT_UNIQUE implies handle_count(s.frames, idx) > 0
                || s.regions.slot_owners[idx].paths_in_pt.len() > 0 || segment_cover_count(
                s.segments,
                index_to_frame(idx),
            ) > 0 by {
                lemma_handle_count_insert_fresh(old_frames, id, frame_entry, idx);
                if idx == target_idx {
                    // The freshly inserted handle gives H > 0 at target.
                    assert(handle_count(s.frames, target_idx) >= 1);
                } else {
                    assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
                }
            };
            assert forall|idx: usize|
                #![trigger s.regions.slot_owners[idx]]
                idx < max_meta_slots() && s.regions.slot_owners[idx].usage == PageUsage::Frame && (
                handle_count(s.frames, idx) > 0 || s.regions.slot_owners[idx].paths_in_pt.len() > 0
                    || segment_cover_count(s.segments, index_to_frame(idx)) > 0) implies {
                let so = s.regions.slot_owners[idx];
                let rc = so.inner_perms.ref_count.value();
                &&& rc != REF_COUNT_UNUSED
                &&& rc != REF_COUNT_UNIQUE
                &&& rc == handle_count(s.frames, idx) + so.paths_in_pt.len() + segment_cover_count(
                    s.segments,
                    index_to_frame(idx),
                )
                &&& so.inner_perms.storage.is_init()
            } by {
                lemma_handle_count_insert_fresh(old_frames, id, frame_entry, idx);
                if idx == target_idx {
                    if old_regions.slot_owners[target_idx].inner_perms.ref_count.value()
                        == REF_COUNT_UNUSED {
                        // Pre UNUSED at Frame slot: clause 1 ⟹ pre paths
                        // empty ∧ pre H == 0 ∧ pre cover == 0.
                        // Post H == 1, paths preserved, cover preserved.
                        // Post rc = pre rc + 1 = UNUSED + 1.
                        assert(REF_COUNT_UNUSED == 0u32);
                        assert(s.regions.slot_owners[target_idx].inner_perms.ref_count.value()
                            == 1);
                        assert(handle_count(s.frames, target_idx) == 1);
                        assert(s.regions.slot_owners[target_idx].paths_in_pt.len()
                            == old_regions.slot_owners[target_idx].paths_in_pt.len());
                        assert(old_regions.slot_owners[target_idx].paths_in_pt.len() == 0);
                        assert(segment_cover_count(s.segments, index_to_frame(target_idx)) == 0);
                    } else if old_regions.slot_owners[target_idx].inner_perms.ref_count.value()
                        == REF_COUNT_UNIQUE {
                        assert(false);
                    } else {
                        // Pre non-sentinel SHARED rc: pre clause 4 applies
                        // with the new cover term.
                        let pre_so = old_regions.slot_owners[target_idx];
                        let pre_rc = pre_so.inner_perms.ref_count.value();
                        let pre_paths = pre_so.paths_in_pt.len();
                        let pre_H = handle_count(old_frames, target_idx);
                        let pre_cover = segment_cover_count(s.segments, index_to_frame(target_idx));
                        if pre_H == 0 && pre_paths == 0 && pre_cover == 0 {
                            assert(false);
                        } else {
                            // pre rc == pre_H + pre_paths + pre_cover.
                            // post rc = pre rc + 1, post H = pre_H + 1,
                            // post paths = pre_paths, post cover = pre_cover.
                            assert(pre_rc == pre_H + pre_paths + pre_cover);
                            assert(handle_count(s.frames, target_idx) == pre_H + 1);
                        }
                    }
                } else {
                    assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
                }
            };
            s.insert_cursor(c, entry);
        },
    }
}

proof fn step_find_next<'rcu>(tracked s: &mut VmStore<'rcu>, c: CursorId, len: usize)
    requires
        old(s).inv(),
        old(s).cursors.dom().contains(c),
    ensures
        final(s).inv(),
{
    let tracked mut entry = s.extract_cursor(c);
    cursor::cursor_find_next_step(&mut entry, &mut s.regions, len);
    s.insert_cursor(c, entry);
}

proof fn step_jump<'rcu>(tracked s: &mut VmStore<'rcu>, c: CursorId, va: Vaddr)
    requires
        old(s).inv(),
        old(s).cursors.dom().contains(c),
    ensures
        final(s).inv(),
{
    let tracked mut entry = s.extract_cursor(c);
    cursor::cursor_jump_step(&mut entry, &mut s.regions, va);
    s.insert_cursor(c, entry);
}

proof fn step_protect_next<'rcu>(tracked s: &mut VmStore<'rcu>, c: CursorId, len: usize)
    requires
        old(s).inv(),
        old(s).cursors.dom().contains(c),
    ensures
        final(s).inv(),
{
    let tracked mut entry = s.extract_cursor(c);
    cursor::cursor_protect_next_step(&mut entry, &mut s.regions, len);
    s.insert_cursor(c, entry);
}

proof fn step_map<'rcu>(
    tracked s: &mut VmStore<'rcu>,
    c: CursorId,
    fid: FrameId,
    prop: PageProperty,
)
    requires
        old(s).inv(),
        old(s).cursors.dom().contains(c),
        old(s).frames.dom().contains(fid),
    ensures
        final(s).inv(),
{
    // `usage == Frame` at the mapped slot from `structural_inv`'s
    // FrameId⟹Frame-usage clause.
    assert(s.regions.slot_owners[frame_to_index(s.frames[fid].paddr)].usage == PageUsage::Frame);
    let ghost paddr = s.frames[fid].paddr;
    let ghost target_idx = frame_to_index(paddr);
    let ghost old_frames = s.frames;
    let ghost old_regions = s.regions;
    // From `structural_inv`: every registered handle's paddr is in-bound.
    assert(has_safe_slot(paddr));
    s.regions.inv_implies_correct_addr(paddr);
    // Pre target_idx: we hold a FrameEntry at this paddr, so
    // `handle_count(old_frames, target_idx) >= 1`.
    assert(old_frames.dom().filter(
        |gid: FrameId| frame_to_index(old_frames[gid].paddr) == target_idx,
    ).contains(fid));
    assert(handle_count(old_frames, target_idx) >= 1);
    // Pre target_idx is usage == Frame (op_pre) and active head
    // (H >= 1), so pre `accounting_inv` clauses 3 and 4 apply.
    let ghost pre_rc_target = old_regions.slot_owners[target_idx].inner_perms.ref_count.value();
    let ghost pre_paths_target = old_regions.slot_owners[target_idx].paths_in_pt.len();
    let ghost pre_cover_target = segment_cover_count(s.segments, index_to_frame(target_idx));
    assert(pre_rc_target != REF_COUNT_UNUSED);
    assert(pre_rc_target != REF_COUNT_UNIQUE);
    assert(pre_rc_target == handle_count(old_frames, target_idx) + pre_paths_target
        + pre_cover_target);
    assert(old_regions.slot_owners[target_idx].inner_perms.storage.is_init());
    let tracked mut entry = s.extract_cursor(c);
    // Consume the FrameEntry: the UFrame's handle ref-count
    // contribution moves to the new PTE; the embedding's `H` at
    // target_idx decrements by 1 in lockstep with `P` incrementing by 1.
    let tracked _frame_entry = s.extract_frame(fid);
    cursor::map_step(&mut entry, &mut s.regions, &mut s.tlb_model, paddr, prop);
    // Discharge `accounting_inv` clause-by-clause. The cursor-map axiom
    // gives: rc/usage/storage preserved at target_idx, paths += 1 at
    // target_idx; non-mapped pre-non-UNUSED slots fully preserved;
    // post-UNUSED slots fully preserved; newly-non-UNUSED slots are
    // non-Frame (PT nodes). `s.segments` is unchanged across map.
    assert forall|idx: usize|
        #![trigger s.regions.slot_owners[idx]]
        idx < max_meta_slots() && s.regions.slot_owners[idx].inner_perms.ref_count.value()
            == REF_COUNT_UNUSED implies handle_count(s.frames, idx) == 0
        && s.regions.slot_owners[idx].paths_in_pt.is_empty() && segment_cover_count(
        s.segments,
        index_to_frame(idx),
    ) == 0 by {
        // post-UNUSED ⟹ slot fully preserved (cursor axiom).
        assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
        lemma_handle_count_remove(old_frames, fid, idx);
        if idx == target_idx {
            // post-UNUSED at target_idx contradicts rc preserved at
            // target_idx + pre_rc_target != UNUSED.
            assert(s.regions.slot_owners[idx].inner_perms.ref_count.value() == pre_rc_target);
            assert(false);
        }
    };
    assert forall|idx: usize|
        #![trigger s.regions.slot_owners[idx]]
        idx < max_meta_slots() && s.regions.slot_owners[idx].usage == PageUsage::Frame
            && s.regions.slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
            && s.regions.slot_owners[idx].inner_perms.ref_count.value()
            != REF_COUNT_UNIQUE implies handle_count(s.frames, idx) > 0
        || s.regions.slot_owners[idx].paths_in_pt.len() > 0 || segment_cover_count(
        s.segments,
        index_to_frame(idx),
    ) > 0 by {
        lemma_handle_count_remove(old_frames, fid, idx);
        if idx == target_idx {
            // post rc preserved at target_idx, paths += 1 ⟹ paths.len > 0.
            assert(s.regions.slot_owners[idx].paths_in_pt.len() == pre_paths_target + 1);
        } else if old_regions.slot_owners[idx].inner_perms.ref_count.value() == REF_COUNT_UNUSED {
            // Newly-non-UNUSED slot ⟹ usage != Frame (changed-slots clause).
            assert(s.regions.slot_owners[idx].usage != PageUsage::Frame);
        } else {
            // Non-mapped pre-non-UNUSED slot ⟹ fully preserved; pre
            // clause 3 carries forward.
            assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
        }
    };
    assert forall|idx: usize|
        #![trigger s.regions.slot_owners[idx]]
        idx < max_meta_slots() && s.regions.slot_owners[idx].usage == PageUsage::Frame && (
        handle_count(s.frames, idx) > 0 || s.regions.slot_owners[idx].paths_in_pt.len() > 0
            || segment_cover_count(s.segments, index_to_frame(idx)) > 0) implies {
        let so = s.regions.slot_owners[idx];
        let rc = so.inner_perms.ref_count.value();
        &&& rc != REF_COUNT_UNUSED
        &&& rc != REF_COUNT_UNIQUE
        &&& rc == handle_count(s.frames, idx) + so.paths_in_pt.len() + segment_cover_count(
            s.segments,
            index_to_frame(idx),
        )
        &&& so.inner_perms.storage.is_init()
    } by {
        lemma_handle_count_remove(old_frames, fid, idx);
        if idx == target_idx {
            // Pre clause 4 (new): rc == H_pre + P_pre + cover_pre.
            // Post: rc/usage/storage preserved; H_post = H_pre - 1;
            //       P_post = P_pre + 1; cover_post = cover_pre.
            // So rc_post = pre_rc_target = H_pre + P_pre + cover_pre
            //                            = H_post + P_post + cover_post.
            assert(s.regions.slot_owners[idx].inner_perms.ref_count.value() == pre_rc_target);
            assert(s.regions.slot_owners[idx].paths_in_pt.len() == pre_paths_target + 1);
            assert(handle_count(s.frames, idx) == (handle_count(old_frames, idx) - 1) as nat);
        } else if old_regions.slot_owners[idx].inner_perms.ref_count.value() == REF_COUNT_UNUSED {
            assert(s.regions.slot_owners[idx].usage != PageUsage::Frame);
        } else {
            assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
        }
    };
    // Discharge structural_inv's FrameId⟹Frame-usage clause.
    // For every remaining fid: pre slot was Frame (old structural_inv);
    // cursor preserves usage at target_idx and at non-mapped pre-non-
    // UNUSED slots (Frame slots are non-UNUSED by old clause 4 with H or
    // P > 0).
    assert forall|fid_other: FrameId| #[trigger]
        s.frames.dom().contains(fid_other) implies s.regions.slot_owners[frame_to_index(
        s.frames[fid_other].paddr,
    )].usage == PageUsage::Frame by {
        let other_idx = frame_to_index(s.frames[fid_other].paddr);
        // pre: usage == Frame from old structural_inv.
        assert(old_regions.slot_owners[other_idx].usage == PageUsage::Frame);
        if other_idx == target_idx {
            // Cursor preserves usage at target_idx.
            assert(s.regions.slot_owners[target_idx].usage
                == old_regions.slot_owners[target_idx].usage);
        } else {
            // pre rc != UNUSED at Frame slots with active head (H or P
            // > 0). Need to invoke H_pre >= 1 (fid_other counts) or
            // pre_paths > 0; here fid_other is still in s.frames
            // (which == old_frames.remove(fid)), so unless fid_other ==
            // fid, fid_other is also in old_frames. Hence pre H >= 1
            // at other_idx, so pre clause 4 ⟹ pre rc != UNUSED.
            assert(old_frames.dom().filter(
                |gid: FrameId| frame_to_index(old_frames[gid].paddr) == other_idx,
            ).contains(fid_other));
            assert(handle_count(old_frames, other_idx) >= 1);
            assert(old_regions.slot_owners[other_idx].inner_perms.ref_count.value()
                != REF_COUNT_UNUSED);
            assert(s.regions.slot_owners[other_idx] == old_regions.slot_owners[other_idx]);
        }
    };
    // Discharge segment-covered ⟹ Frame-usage. Same shape: covered
    // slots are non-UNUSED pre (cover >= 1 + clause 4 ⟹ active);
    // cursor preserves Frame slots fully (target_idx via map axiom,
    // others via the "non-mapped pre-non-UNUSED" clause).
    assert forall|sid: SegmentId, paddr_c: Paddr|
        #![trigger
            s.segments.dom().contains(sid),
            frame_to_index(paddr_c)]
        s.segments.dom().contains(sid) && s.segments[sid].range.start <= paddr_c
            < s.segments[sid].range.end && paddr_c % PAGE_SIZE
            == 0 implies s.regions.slot_owners[frame_to_index(paddr_c)].usage
        == PageUsage::Frame by {
        let cov_idx = frame_to_index(paddr_c);
        // pre cover >= 1 at cov_idx ⟹ pre slot is Frame + non-UNUSED.
        lemma_segment_cover_contains(old_regions_segments_helper(s), sid, paddr_c);
        assert(old_regions.slot_owners[cov_idx].usage == PageUsage::Frame);
        assert(old_regions.slot_owners[cov_idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED);
        if cov_idx == target_idx {
            // Map preserves usage at target.
            assert(s.regions.slot_owners[target_idx].usage
                == old_regions.slot_owners[target_idx].usage);
        } else {
            // Non-mapped pre-non-UNUSED slot ⟹ fully preserved.
            assert(s.regions.slot_owners[cov_idx] == old_regions.slot_owners[cov_idx]);
        }
    };
    s.insert_cursor(c, entry);
}

// Helper: snapshot the pre-step segments map. Defined as a no-op
// inline spec to give the discharge proofs a stable handle on the
// pre-state when `s.segments` is unchanged.
spec fn old_regions_segments_helper<'rcu>(s: &VmStore<'rcu>) -> Map<SegmentId, SegmentEntry> {
    s.segments
}

proof fn step_unmap<'rcu>(tracked s: &mut VmStore<'rcu>, c: CursorId, len: usize)
    requires
        old(s).inv(),
        old(s).cursors.dom().contains(c),
    ensures
        final(s).inv(),
{
    let ghost old_regions = s.regions;
    let ghost old_frames = s.frames;
    let tracked mut entry = s.extract_cursor(c);
    cursor::cursor_mut_regions_step(
        &mut entry,
        &mut s.regions,
        &mut s.tlb_model,
        cursor::CursorMutRegionsMethod::Unmap(len),
    );
    // Discharge `accounting_inv` clause-by-clause. The unmap axiom
    // gives: usage/raw_count/in_list/self_addr/vtable_ptr preserved
    // universally; rc doesn't bump to UNIQUE; storage preserved at
    // post-non-UNUSED; at Frame slots, `rc - paths.len` is invariant
    // with both monotonically non-increasing. `s.frames` is unchanged.
    assert forall|idx: usize|
        #![trigger s.regions.slot_owners[idx]]
        idx < max_meta_slots() && s.regions.slot_owners[idx].inner_perms.ref_count.value()
            == REF_COUNT_UNUSED implies handle_count(s.frames, idx) == 0
        && s.regions.slot_owners[idx].paths_in_pt.is_empty() && segment_cover_count(
        s.segments,
        index_to_frame(idx),
    ) == 0 by {
        // From `regions.inv()`: idx < max_meta_slots ⟹ slot_owners[idx]
        // satisfies MetaSlotOwner::inv (so UNUSED ∧ non-MMIO ⟹ paths
        // empty fires).
        assert(s.regions.slot_owners.contains_key(idx));
        assert(s.regions.slot_owners[idx].inv());
        // Post cover == 0. Unmap leaves `s.segments` untouched, so post
        // cover == pre cover. If pre cover >= 1: a witnessing segment +
        // structural `covered ⟹ Frame` gives pre usage == Frame, and pre
        // `accounting_inv` clause #4 (active head) gives pre rc <=
        // REF_COUNT_MAX; the unmap rc-paths clause then gives post rc <=
        // pre rc <= MAX < UNUSED — contradicting post UNUSED. Hence pre
        // cover == 0 (segment covers survive unmap, which removes only
        // PTE paths).
        assert(s.segments == old(s).segments);
        assert(old_regions == old(s).regions);
        assert(segment_cover_count(s.segments, index_to_frame(idx)) == 0) by {
            if segment_cover_count(old(s).segments, index_to_frame(idx)) > 0 {
                let pa = index_to_frame(idx);
                let sid = lemma_segment_cover_witness(old(s).segments, pa);
                // Paddr round-trip / alignment so the structural
                // `covered ⟹ Frame` clause (keyed by `frame_to_index`)
                // fires at `(sid, pa)`.
                assert(pa == (idx * PAGE_SIZE) as usize);
                assert(pa % PAGE_SIZE == 0);
                assert(frame_to_index(pa) == idx);
                // structural `covered ⟹ Frame` at the witness (old state).
                assert(old_regions.slot_owners[idx].usage == PageUsage::Frame);
                // active head (cover > 0 ∧ Frame) ⟹ pre rc != UNUSED, <= MAX.
                assert(old_regions.slot_owners[idx].inner_perms.ref_count.value()
                    != REF_COUNT_UNUSED);
                assert(old_regions.slot_owners[idx].inner_perms.ref_count.value() <= REF_COUNT_MAX);
                // unmap (Frame): post rc <= pre rc <= MAX < UNUSED.
                assert(s.regions.slot_owners[idx].inner_perms.ref_count.value() <= REF_COUNT_MAX);
            }
        };
        // Case-split on pre.usage: usage is preserved by the axiom.
        if old_regions.slot_owners[idx].usage == PageUsage::Frame {
            // Post.paths empty: Frame ∧ post UNUSED + MetaSlotOwner::inv
            // (UNUSED ∧ non-MMIO ⟹ paths empty).
            assert(s.regions.slot_owners[idx].usage != PageUsage::MMIO);
            assert(s.regions.slot_owners[idx].paths_in_pt == Set::empty());
            // Post.H == 0: at Frame post UNUSED, pre rc == pre paths
            // (from rc-paths invariant: post rc + pre paths = pre rc +
            // post paths ⟹ 0 + pre paths = pre rc + 0). If pre rc !=
            // UNUSED: pre active head (rc > 0), pre clause 4 ⟹ pre rc
            // == pre H + pre paths ⟹ pre H == 0. If pre rc == UNUSED:
            // pre clause 1 ⟹ pre H == 0.
        } else if old_regions.slot_owners[idx].usage == PageUsage::MMIO {
            // MMIO slots are fully preserved (axiom). Pre clause 1
            // gives the conjunction for pre UNUSED MMIO directly.
            assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
        } else {
            // Non-Frame non-MMIO (PT-node): MetaSlotOwner::inv UNUSED
            // gives paths empty. H == 0 from no-FrameId-at-non-Frame.
            assert(s.regions.slot_owners[idx].usage != PageUsage::MMIO);
            assert(s.regions.slot_owners[idx].paths_in_pt == Set::empty());
            assert(handle_count(s.frames, idx) == 0) by {
                let filt = s.frames.dom().filter(
                    |gid: FrameId| frame_to_index(s.frames[gid].paddr) == idx,
                );
                assert forall|fid: FrameId| #[trigger] filt.contains(fid) implies false by {
                    // s.frames == old_frames (unmap doesn't touch frames).
                    // structural ⟹ pre slot's usage == Frame, but we're
                    // in the non-Frame branch — contradiction.
                    assert(s.frames.dom().contains(fid));
                    assert(frame_to_index(s.frames[fid].paddr) == idx);
                    assert(s.regions.slot_owners[idx].usage == PageUsage::Frame);
                };
                assert(filt == Set::empty());
            };
        }
    };
    assert forall|idx: usize|
        #![trigger s.regions.slot_owners[idx]]
        idx < max_meta_slots() && s.regions.slot_owners[idx].usage == PageUsage::Frame
            && s.regions.slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
            && s.regions.slot_owners[idx].inner_perms.ref_count.value()
            != REF_COUNT_UNIQUE implies handle_count(s.frames, idx) > 0
        || s.regions.slot_owners[idx].paths_in_pt.len() > 0 || segment_cover_count(
        s.segments,
        index_to_frame(idx),
    ) > 0 by {
        // Post usage == Frame ⟹ pre usage == Frame (usage preserved).
        // At Frame slots, the rc-paths invariant `post rc + pre paths
        // == pre rc + post paths` combined with `post paths.len ≤ pre
        // paths.len` forces pre UNUSED ⟹ post UNUSED (since pre UNUSED
        // gives pre paths == 0 via MetaSlotOwner::inv, the equation
        // becomes post rc == pre rc + post paths but post rc ≤ pre rc
        // ⟹ post paths == 0 ⟹ post rc == pre rc == UNUSED). So at
        // post non-UNUSED Frame slot, pre rc != UNUSED.
        assert(s.regions.slot_owners.contains_key(idx));
        assert(s.regions.slot_owners[idx].inv());
        assert(old_regions.slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED) by {
            if old_regions.slot_owners[idx].inner_perms.ref_count.value() == REF_COUNT_UNUSED {
                // Trigger MetaSlotOwner::inv on pre at this idx.
                assert(old_regions.slot_owners.contains_key(idx));
                assert(old_regions.slot_owners[idx].inv());
                assert(old_regions.slot_owners[idx].paths_in_pt == Set::empty());
                // rc-paths invariant: post rc + 0 == UNUSED + post paths
                //                  ⟹ post rc == UNUSED + post paths.
                // post rc <= pre rc == UNUSED ⟹ post paths == 0
                //                            ⟹ post rc == UNUSED.
                // But post rc != UNUSED by assumption. Contradiction.
                assert(s.regions.slot_owners[idx].paths_in_pt.len() == 0);
                assert(false);
            }
        };
        // Pre non-UNUSED Frame: clause 3 gives pre H > 0 OR pre paths > 0
        // OR pre cover > 0. Segments unchanged ⟹ post cover == pre cover.
        if handle_count(old_frames, idx) > 0 {
            assert(handle_count(s.frames, idx) > 0);
        } else if segment_cover_count(s.segments, index_to_frame(idx)) > 0 {
            // Cover > 0 directly satisfies the new disjunct.
        } else {
            // pre H == 0 ∧ pre cover == 0. Clause 3 ⟹ pre paths > 0.
            // Clause 4 (active head pre) ⟹ pre rc == pre H + pre paths
            // + pre cover == pre paths. From rc-paths invariant:
            // post paths == pre paths - pre rc + post rc == post rc.
            // post rc != UNUSED ⟹ post rc > 0 ⟹ post paths > 0.
            assert(s.regions.slot_owners[idx].paths_in_pt.len() > 0);
        }
    };
    assert forall|idx: usize|
        #![trigger s.regions.slot_owners[idx]]
        idx < max_meta_slots() && s.regions.slot_owners[idx].usage == PageUsage::Frame && (
        handle_count(s.frames, idx) > 0 || s.regions.slot_owners[idx].paths_in_pt.len()
            > 0) implies {
        let so = s.regions.slot_owners[idx];
        let rc = so.inner_perms.ref_count.value();
        &&& rc != REF_COUNT_UNUSED
        &&& rc != REF_COUNT_UNIQUE
        &&& rc == handle_count(s.frames, idx) + so.paths_in_pt.len() + segment_cover_count(
            s.segments,
            index_to_frame(idx),
        )
        &&& so.inner_perms.storage.is_init()
    } by {
        // Post is active head. H unchanged ⟹ pre H == post H. Pre
        // usage == Frame (preserved). Either pre H > 0 (pre active head)
        // or post paths > 0 with post H == 0 ⟹ pre paths >= post paths
        // > 0 (pre active head). Either way, pre clause 4 applies:
        // pre rc != UNUSED ∧ pre rc != UNIQUE ∧
        // pre rc == pre H + pre paths ∧ pre storage init.
        if handle_count(s.frames, idx) > 0 {
            // pre H > 0 ⟹ pre active head ⟹ pre clause 4.
            assert(handle_count(old_frames, idx) > 0);
        } else {
            // post H == 0, post paths > 0. Frame-slot axiom: post rc +
            // pre paths == pre rc + post paths. post rc != UNUSED
            // (otherwise contradicts active head), so post rc > 0.
            // pre paths == pre rc + post paths - post rc. Combined with
            // pre paths >= post paths (monotonic): pre rc >= post rc > 0.
            // So pre rc != UNUSED ⟹ pre clause 3 ⟹ pre H > 0 OR pre
            // paths > 0. pre H == 0 (H unchanged), so pre paths > 0 ⟹
            // pre active head ⟹ pre clause 4.
            assert(old_regions.slot_owners[idx].paths_in_pt.len() > 0);
        }
        // Now pre clause 4 gives: pre rc == pre H + pre paths,
        //                         pre rc != UNUSED, pre rc != UNIQUE,
        //                         pre storage.is_init.
        // Frame-slot axiom: post rc + pre paths == pre rc + post paths
        //                 ⟹ post rc == pre rc + post paths - pre paths
        //                 ⟹ post rc == (pre H + pre paths) + post paths - pre paths
        //                 ⟹ post rc == pre H + post paths
        //                 ⟹ post rc == post H + post paths.  ✓
        // post rc != UNUSED: from active head assumption.
        // post rc != UNIQUE: axiom's pre != UNIQUE ⟹ post != UNIQUE.
        // storage init: axiom's "post non-UNUSED ⟹ storage preserved".
    };
    // Discharge structural_inv's FrameId⟹Frame-usage clause. Unmap
    // preserves usage universally, so it holds trivially.
    assert forall|fid_other: FrameId| #[trigger]
        s.frames.dom().contains(fid_other) implies s.regions.slot_owners[frame_to_index(
        s.frames[fid_other].paddr,
    )].usage == PageUsage::Frame by {
        let other_idx = frame_to_index(s.frames[fid_other].paddr);
        assert(s.regions.slot_owners[other_idx].usage == old_regions.slot_owners[other_idx].usage);
    };
    s.insert_cursor(c, entry);
}

proof fn step_new_vm_io<'rcu>(
    tracked s: &mut VmStore<'rcu>,
    vs: VmSpaceId,
    vaddr: Vaddr,
    len: usize,
    kind: VmIoKind,
)
    requires
        old(s).inv(),
        old(s).vm_spaces.dom().contains(vs),
    ensures
        final(s).inv(),
{
    let tracked vm_space_ref = s.vm_spaces.tracked_borrow(vs);
    let tracked res = io::new_vm_io_step(vm_space_ref, Some(vs), vaddr, len, kind);
    match res {
        Option::Some(entry) => {
            let ghost id = fresh_vm_io_id(s.vm_ios);
            axiom_fresh_vm_io_id_not_in_dom(s.vm_ios);
            s.insert_vm_io(id, entry);
        },
        Option::None => {},
    }
}

proof fn step_new_kernel_vm_io<'rcu>(
    tracked s: &mut VmStore<'rcu>,
    vaddr: Vaddr,
    len: usize,
    kind: VmIoKind,
)
    requires
        old(s).inv(),
    ensures
        final(s).inv(),
{
    let tracked entry = io::new_kernel_vm_io_step(vaddr, len, kind);
    let ghost id = fresh_vm_io_id(s.vm_ios);
    axiom_fresh_vm_io_id_not_in_dom(s.vm_ios);
    s.insert_vm_io(id, entry);
}

proof fn step_drop_vm_io<'rcu>(tracked s: &mut VmStore<'rcu>, vio: VmIoId)
    requires
        old(s).inv(),
        old(s).vm_ios.dom().contains(vio),
    ensures
        final(s).inv(),
{
    let tracked entry = s.extract_vm_io(vio);
    io::drop_vm_io_step(entry);
}

proof fn step_vm_io_method<'rcu>(tracked s: &mut VmStore<'rcu>, vio: VmIoId, method: io::VmIoMethod)
    requires
        old(s).inv(),
        old(s).vm_ios.dom().contains(vio),
    ensures
        final(s).inv(),
{
    let tracked mut entry = s.extract_vm_io(vio);
    io::vm_io_method_step(&mut entry, method);
    s.insert_vm_io(vio, entry);
}

proof fn step_read<'rcu>(tracked s: &mut VmStore<'rcu>, source: VmIoId, dest: VmIoId)
    requires
        old(s).inv(),
        old(s).vm_ios.dom().contains(source),
        old(s).vm_ios.dom().contains(dest),
        source != dest,
        old(s).vm_ios[source].vm_space is None,
        old(s).vm_ios[source].kind == VmIoKind::Reader,
        old(s).vm_ios[dest].vm_space is None,
        old(s).vm_ios[dest].kind == VmIoKind::Writer,
    ensures
        final(s).inv(),
{
    let tracked mut src = s.extract_vm_io(source);
    let tracked mut dst = s.extract_vm_io(dest);
    let tracked val = io::read_step(&mut src, &mut dst);
    s.insert_vm_io(source, src);
    s.insert_vm_io(dest, dst);
    let ghost id = fresh_vm_io_id(s.vm_ios);
    axiom_fresh_vm_io_id_not_in_dom(s.vm_ios);
    s.insert_vm_io(id, val);
}

proof fn step_write<'rcu>(tracked s: &mut VmStore<'rcu>, source: VmIoId, dest: VmIoId)
    requires
        old(s).inv(),
        old(s).vm_ios.dom().contains(source),
        old(s).vm_ios.dom().contains(dest),
        source != dest,
        old(s).vm_ios[source].vm_space is None,
        old(s).vm_ios[source].kind == VmIoKind::Reader,
        old(s).vm_ios[dest].vm_space is None,
        old(s).vm_ios[dest].kind == VmIoKind::Writer,
    ensures
        final(s).inv(),
{
    let tracked mut src = s.extract_vm_io(source);
    let tracked mut dst = s.extract_vm_io(dest);
    io::write_step(&mut src, &mut dst);
    s.insert_vm_io(source, src);
    s.insert_vm_io(dest, dst);
}

proof fn step_frame_from_unused<'rcu>(tracked s: &mut VmStore<'rcu>, paddr: Paddr)
    requires
        old(s).inv(),
    ensures
        final(s).inv(),
{
    // `op_pre` is now `true` for this op (#2 fully resolved): *any*
    // `paddr` is accepted, a bad one just fails. The axiom's only
    // slot-perm precondition is `has_safe_slot`-guarded; we discharge
    // it for the in-bound case from `VmStore::inv`'s coverage clause
    // (`inv_implies_correct_addr` → `idx < max_meta_slots()` → coverage
    // → `slots.contains_key`), and it is vacuous out-of-bound.
    if has_safe_slot(paddr) {
        s.regions.inv_implies_correct_addr(paddr);
        assert(s.regions.slots.contains_key(frame_to_index(paddr)));
    }
    let ghost old_frames = s.frames;
    let ghost old_regions = s.regions;
    let tracked res = frame::from_unused_step(&mut s.regions, paddr);
    match res {
        Option::Some(entry) => {
            let ghost id = fresh_frame_id(s.frames);
            axiom_fresh_frame_id_not_in_dom(s.frames);
            let ghost target_idx = frame_to_index(paddr);
            let ghost entry_paddr = entry.paddr;
            s.insert_frame(id, entry);
            assert(s.frames[id].paddr == paddr);

            // Pre target_idx was rc=UNUSED ⟹ pre H==0 ∧ pre paths.empty()
            // (via old accounting_inv's UNUSED clause).
            assert(handle_count(old_frames, target_idx) == 0);
            assert(old_regions.slot_owners[target_idx].paths_in_pt.is_empty());

            // 5.5c new clause: "UNUSED ⟹ no users". Other idx unchanged
            // (lemma + slot_owner preservation); target_idx is now rc=1.
            assert forall|idx: usize|
                #![trigger s.regions.slot_owners[idx]]
                idx < max_meta_slots() && s.regions.slot_owners[idx].inner_perms.ref_count.value()
                    == REF_COUNT_UNUSED implies handle_count(s.frames, idx) == 0
                && s.regions.slot_owners[idx].paths_in_pt.is_empty() by {
                lemma_handle_count_insert_fresh(old_frames, id, entry, idx);
                if idx == target_idx {
                    // post rc=1 != UNUSED, antecedent false.
                    assert(false);
                } else {
                    assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
                }
            };

            // 5.5c new clause: "Frame ∧ non-sentinel ⟹ active". Other
            // idx unchanged (so old clause carries); target post is
            // active (H=1).
            assert forall|idx: usize|
                #![trigger s.regions.slot_owners[idx]]
                idx < max_meta_slots() && s.regions.slot_owners[idx].usage == PageUsage::Frame
                    && s.regions.slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                    && s.regions.slot_owners[idx].inner_perms.ref_count.value()
                    != REF_COUNT_UNIQUE implies handle_count(s.frames, idx) > 0
                || s.regions.slot_owners[idx].paths_in_pt.len() > 0 || segment_cover_count(
                s.segments,
                index_to_frame(idx),
            ) > 0 by {
                lemma_handle_count_insert_fresh(old_frames, id, entry, idx);
                if idx == target_idx {
                    assert(handle_count(s.frames, idx) == 1);
                } else {
                    assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
                }
            };

            // Per-slot accounting (forall covers active heads only).
            assert forall|idx: usize|
                #![trigger s.regions.slot_owners[idx]]
                idx < max_meta_slots() && s.regions.slot_owners[idx].usage == PageUsage::Frame && (
                handle_count(s.frames, idx) > 0 || s.regions.slot_owners[idx].paths_in_pt.len() > 0
                    || segment_cover_count(s.segments, index_to_frame(idx)) > 0) implies {
                let so = s.regions.slot_owners[idx];
                let rc = so.inner_perms.ref_count.value();
                &&& rc != REF_COUNT_UNUSED
                &&& rc != REF_COUNT_UNIQUE
                &&& rc == handle_count(s.frames, idx) + so.paths_in_pt.len() + segment_cover_count(
                    s.segments,
                    index_to_frame(idx),
                )
                &&& so.inner_perms.storage.is_init()
            } by {
                lemma_handle_count_insert_fresh(old_frames, id, entry, idx);
                if idx == target_idx {
                    assert(old_regions.slot_owners[idx].inner_perms.ref_count.value()
                        == REF_COUNT_UNUSED);
                    assert(handle_count(old_frames, idx) == 0);
                    assert(handle_count(s.frames, idx) == 1);
                    // Pre clause 2 (UNUSED) gives pre cover == 0;
                    // segments unchanged ⟹ post cover == 0.
                    assert(segment_cover_count(s.segments, index_to_frame(idx)) == 0);
                } else {
                    // Other slot: slot_owner preserved by from_unused
                    // (forall i != target_idx clause in reparked_spec).
                    assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
                }
            };
        },
        Option::None => {
            // regions unchanged ⇒ accounting preserved from old.
            assert(s.regions == old_regions);
        },
    }
}

proof fn step_frame_from_in_use<'rcu>(tracked s: &mut VmStore<'rcu>, paddr: Paddr)
    requires
        old(s).inv(),
    ensures
        final(s).inv(),
{
    // See `step_frame_from_unused`: `op_pre` is `true` (#3b resolved);
    // the `has_safe_slot`-guarded slot-perm precondition is recovered
    // from `VmStore::inv`'s coverage clause for the in-bound case and
    // is vacuous out-of-bound.
    if has_safe_slot(paddr) {
        s.regions.inv_implies_correct_addr(paddr);
        assert(s.regions.slots.contains_key(frame_to_index(paddr)));
    }
    let ghost old_frames = s.frames;
    let ghost old_regions = s.regions;
    let tracked res = frame::from_in_use_step(&mut s.regions, paddr);
    match res {
        Option::Some(entry) => {
            let ghost id = fresh_frame_id(s.frames);
            axiom_fresh_frame_id_not_in_dom(s.frames);
            let ghost target_idx = frame_to_index(paddr);
            s.insert_frame(id, entry);
            assert(s.frames[id].paddr == paddr);

            // 5.5c new clause: "UNUSED ⟹ no users". For target: post
            // rc = pre rc + 1 != UNUSED. For other idx: unchanged.
            assert forall|idx: usize|
                #![trigger s.regions.slot_owners[idx]]
                idx < max_meta_slots() && s.regions.slot_owners[idx].inner_perms.ref_count.value()
                    == REF_COUNT_UNUSED implies handle_count(s.frames, idx) == 0
                && s.regions.slot_owners[idx].paths_in_pt.is_empty() by {
                lemma_handle_count_insert_fresh(old_frames, id, entry, idx);
                if idx == target_idx {
                    assert(false);
                } else {
                    assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
                }
            };

            // 5.5c new clause: "Frame ∧ non-sentinel ⟹ active". For
            // target post: H = pre + 1 ≥ 1 → active. For other: unchanged.
            assert forall|idx: usize|
                #![trigger s.regions.slot_owners[idx]]
                idx < max_meta_slots() && s.regions.slot_owners[idx].usage == PageUsage::Frame
                    && s.regions.slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                    && s.regions.slot_owners[idx].inner_perms.ref_count.value()
                    != REF_COUNT_UNIQUE implies handle_count(s.frames, idx) > 0
                || s.regions.slot_owners[idx].paths_in_pt.len() > 0 || segment_cover_count(
                s.segments,
                index_to_frame(idx),
            ) > 0 by {
                lemma_handle_count_insert_fresh(old_frames, id, entry, idx);
                if idx == target_idx {
                    assert(handle_count(s.frames, idx) >= 1);
                } else {
                    assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
                }
            };

            // Per-slot accounting (forall covers active heads only).
            assert forall|idx: usize|
                #![trigger s.regions.slot_owners[idx]]
                idx < max_meta_slots() && s.regions.slot_owners[idx].usage == PageUsage::Frame && (
                handle_count(s.frames, idx) > 0 || s.regions.slot_owners[idx].paths_in_pt.len() > 0
                    || segment_cover_count(s.segments, index_to_frame(idx)) > 0) implies {
                let so = s.regions.slot_owners[idx];
                let rc = so.inner_perms.ref_count.value();
                &&& rc != REF_COUNT_UNUSED
                &&& rc != REF_COUNT_UNIQUE
                &&& rc == handle_count(s.frames, idx) + so.paths_in_pt.len() + segment_cover_count(
                    s.segments,
                    index_to_frame(idx),
                )
                &&& so.inner_perms.storage.is_init()
            } by {
                lemma_handle_count_insert_fresh(old_frames, id, entry, idx);
                if idx == target_idx {
                    // Pre usage(target)==Frame: `get_from_in_use`
                    // preserves `usage`. Pre active-head fires from
                    // pre H >= 1 (or pre paths > 0, or pre cover > 0).
                    assert(old_regions.slot_owners[idx].usage == PageUsage::Frame);
                } else {
                    assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
                }
            };
        },
        Option::None => {
            assert(s.regions == old_regions);
        },
    }
}

proof fn step_frame_drop<'rcu>(tracked s: &mut VmStore<'rcu>, fid: FrameId)
    requires
        old(s).inv(),
        old(s).frames.dom().contains(fid),
        // No segment forgot a reference to this slot. The other
        // `drop_pre` conjuncts (rc, storage, in_list, paths-empty
        // residuals) are derived from `old(s).inv()` via
        // [`lemma_frame_drop_pre_derivable`].
        segment_cover_count(old(s).segments, old(s).frames[fid].paddr) == 0,
    ensures
        final(s).inv(),
{
    // Derive `drop_pre` + handle-clause from `s.inv()` (Item 2:
    // embedding-level `Frame::wf(state)`).
    lemma_frame_drop_pre_derivable(*s, fid);
    let ghost p = s.frames[fid].paddr;
    assert(has_safe_slot(p));
    s.regions.inv_implies_correct_addr(p);
    let ghost idx_p = frame_to_index(p);
    assert(idx_p < max_meta_slots());
    // `fid ∈ s.frames` ⟹ `handle_count(s.frames, idx_p) ≥ 1`. Used
    // below to chain `lemma_handle_count_remove` and re-establish
    // accounting_inv's Frame-scoped clauses.
    assert(s.frames.dom().filter(
        |gid: FrameId| frame_to_index(s.frames[gid].paddr) == idx_p,
    ).contains(fid));
    assert(handle_count(s.frames, idx_p) >= 1);
    let ghost target_idx = frame_to_index(p);
    let ghost old_frames = s.frames;
    let ghost old_regions = s.regions;
    let tracked entry = s.extract_frame(fid);
    frame::drop_step(&mut s.regions, entry);

    // Discharge accounting_inv on the post-drop state. Handle clause
    // is gone; only clauses 2 (UNUSED), 3 (Frame active head), 4
    // (Frame equation) remain.

    // 5.5c new clause: "UNUSED ⟹ no users". For non-target: unchanged.
    // For target: if drop teardown (rc 1→UNUSED), need post H==0 and
    // paths empty. Both hold: pre eqn 1==H+P with H>=1 ⟹ H==1, P==0
    // ⟹ post H==0 (fid removed) and post paths == pre paths == empty.
    assert forall|idx: usize|
        #![trigger s.regions.slot_owners[idx]]
        idx < max_meta_slots() && s.regions.slot_owners[idx].inner_perms.ref_count.value()
            == REF_COUNT_UNUSED implies handle_count(s.frames, idx) == 0
        && s.regions.slot_owners[idx].paths_in_pt.is_empty() && segment_cover_count(
        s.segments,
        index_to_frame(idx),
    ) == 0 by {
        lemma_handle_count_remove(old_frames, fid, idx);
        if idx == target_idx {
            // Post rc==UNUSED ⟹ pre rc was 1 (drop_step rc transition).
            assert(old_regions.slot_owners[idx].inner_perms.ref_count.value() == 1);
            // Old handle clause: pre rc (== 1) >= pre handle_count, and
            // `fid` contributes ⟹ pre handle_count == 1 ⟹ post == 0.
            assert(handle_count(old_frames, idx) == 1);
            assert(handle_count(s.frames, idx) == 0);
            // pre rc == 1 ⟹ `drop_step` leaves `paths_in_pt` empty.
            assert(s.regions.slot_owners[idx].paths_in_pt.is_empty());
        } else {
            assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
        }
    };

    // 5.5c new clause: "Frame ∧ non-sentinel ⟹ active". For target
    // post in rc>1 case: rc-1 in [1,MAX-1] non-sentinel; H-=1 or P
    // preserved. Pre H+P=pre rc; if post H>=1, active; else pre H=1
    // so pre P=pre rc-1 >= 1 (rc>1), post P >= 1, active. ✓
    assert forall|idx: usize|
        #![trigger s.regions.slot_owners[idx]]
        idx < max_meta_slots() && s.regions.slot_owners[idx].usage == PageUsage::Frame
            && s.regions.slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
            && s.regions.slot_owners[idx].inner_perms.ref_count.value()
            != REF_COUNT_UNIQUE implies handle_count(s.frames, idx) > 0
        || s.regions.slot_owners[idx].paths_in_pt.len() > 0 || segment_cover_count(
        s.segments,
        index_to_frame(idx),
    ) > 0 by {
        lemma_handle_count_remove(old_frames, fid, idx);
        if idx == target_idx {
            // Post rc != UNUSED ⟹ drop_step did rc-1 (not teardown).
            // ⟹ pre rc > 1. Pre H==1+ + pre P; if pre H > 1: post H>=1
            // ✓. If pre H == 1: pre P = pre rc - 1 >= 1; post P preserved
            // >= 1 ✓.
            assert(handle_count(old_frames, idx) >= 1);
        } else {
            assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
        }
    };

    assert forall|idx: usize|
        #![trigger s.regions.slot_owners[idx]]
        idx < max_meta_slots() && s.regions.slot_owners[idx].usage == PageUsage::Frame && (
        handle_count(s.frames, idx) > 0 || s.regions.slot_owners[idx].paths_in_pt.len() > 0
            || segment_cover_count(s.segments, index_to_frame(idx)) > 0) implies {
        let so = s.regions.slot_owners[idx];
        let rc = so.inner_perms.ref_count.value();
        &&& rc != REF_COUNT_UNUSED
        &&& rc != REF_COUNT_UNIQUE
        &&& rc == handle_count(s.frames, idx) + so.paths_in_pt.len() + segment_cover_count(
            s.segments,
            index_to_frame(idx),
        )
        &&& so.inner_perms.storage.is_init()
    } by {
        lemma_handle_count_remove(old_frames, fid, idx);
        if idx == target_idx {
            // Pre fid contributes ⇒ pre H >= 1 ⇒ pre active head.
            // Pre `usage == Frame`: `drop_step` preserves `usage`,
            // and the clause antecedent gives post `usage == Frame`.
            assert(old_regions.slot_owners[idx].usage == PageUsage::Frame);
            assert(handle_count(old_frames, idx) > 0);
            let ghost pre_rc = old_regions.slot_owners[idx].inner_perms.ref_count.value();
            let ghost pre_h = handle_count(old_frames, idx);
            let ghost pre_p = old_regions.slot_owners[idx].paths_in_pt.len();
            assert(pre_rc == pre_h + pre_p);
            // Residual `drop_pre`: pre rc <= MAX, pre rc >= 1, != UNUSED/UNIQUE.
            let ghost post_h = handle_count(s.frames, idx);
            assert(post_h == (pre_h - 1) as nat);
            // drop_step now exposes paths preservation at idx.
            let ghost post_p = s.regions.slot_owners[idx].paths_in_pt.len();
            assert(post_p == pre_p);
            let ghost post_rc = s.regions.slot_owners[idx].inner_perms.ref_count.value();
            if pre_rc > 1 {
                // drop_step rc>1 branch: post rc = pre - 1, storage preserved.
                assert(post_rc == (pre_rc - 1) as u64);
                assert(post_rc as nat == post_h + post_p);
                assert(post_rc >= 1);
                assert(post_rc <= REF_COUNT_MAX);
                assert(s.regions.slot_owners[idx].inner_perms.storage
                    == old_regions.slot_owners[idx].inner_perms.storage);
            } else {
                // pre_rc == 1: pre eqn 1 == pre_h + pre_p with
                // pre_h >= 1 forces pre_h = 1, pre_p = 0.
                assert(pre_h == 1);
                assert(pre_p == 0);
                assert(post_h == 0);
                assert(post_p == 0);
                // drop_step rc==1 branch: post rc = UNUSED.
                assert(post_rc == REF_COUNT_UNUSED);
                // ⇒ post is NOT active head at idx, so we're not
                // actually inside this body in this case
                // (antecedent false). Contradicts the implies guard.
                assert(false);
            }
        } else {
            // Other slot: slot_owner preserved by drop_step
            // (forall i != target_idx clause in ensures).
            assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
        }
    };
}

/// `Op::SegmentFromUnused` step. Allocates a fresh `SegmentEntry`
/// covering `range` on success. Discharges `accounting_inv` from the
/// post-state's per-slot ensures (every covered slot transitions
/// `UNUSED → Frame, rc=1, raw_count=1`).
proof fn step_segment_from_unused<'rcu>(tracked s: &mut VmStore<'rcu>, range: Range<Paddr>)
    requires
        old(s).inv(),
        range.start % PAGE_SIZE == 0,
        range.end % PAGE_SIZE == 0,
        range.start < range.end,
        range.end <= MAX_PADDR,
        forall|paddr: Paddr|
            #![trigger frame_to_index(paddr)]
            (range.start <= paddr < range.end && paddr % PAGE_SIZE == 0) ==> old(
                s,
            ).regions.slot_owners[frame_to_index(paddr)].inner_perms.ref_count.value()
                == REF_COUNT_UNUSED,
    ensures
        final(s).inv(),
{
    let ghost old_regions = s.regions;
    let ghost old_frames = s.frames;
    let ghost old_segments = s.segments;
    // Slot-perm coverage in `range` follows from structural_inv (every
    // `idx < max_meta_slots()` has `slots.contains_key(idx)`).
    assert forall|paddr: Paddr|
        #![trigger frame_to_index(paddr)]
        (range.start <= paddr < range.end && paddr % PAGE_SIZE
            == 0) implies s.regions.slots.contains_key(frame_to_index(paddr)) by {
        s.regions.inv_implies_correct_addr(paddr);
    };
    let tracked res = segment::from_unused_step(&mut s.regions, range);
    match res {
        Option::Some(entry) => {
            let ghost id = fresh_segment_id(s.segments);
            axiom_fresh_segment_id_not_in_dom(s.segments);
            s.insert_segment(id, entry);
            // Discharge accounting_inv on the post-state.
            // Per-slot reasoning:
            //   - Slot in `range`: pre rc=UNUSED ⟹ pre H=0, pre cover=0
            //     (pre clause 1). Post rc=1, post H=0 (frames unchanged),
            //     post cover=1 (one new segment covers this paddr).
            //     Equation: post rc == post H + post paths + post cover
            //                == 0 + 0 + 1 == 1. ✓
            //   - Slot outside `range`: fully preserved (axiom); segments
            //     gained one entry whose range doesn't cover this paddr,
            //     so cover unchanged. Accounting carries from pre.
            assert forall|idx: usize|
                #![trigger s.regions.slot_owners[idx]]
                idx < max_meta_slots() && s.regions.slot_owners[idx].inner_perms.ref_count.value()
                    == REF_COUNT_UNUSED implies handle_count(s.frames, idx) == 0
                && s.regions.slot_owners[idx].paths_in_pt.is_empty() && segment_cover_count(
                s.segments,
                index_to_frame(idx),
            ) == 0 by {
                let paddr = index_to_frame(idx);
                // Round-trip: idx < max ⟹ paddr aligned, in-bound.
                assert(paddr == (idx * PAGE_SIZE) as usize);
                assert(paddr % PAGE_SIZE == 0);
                assert(frame_to_index(paddr) == idx);
                if range.start <= paddr < range.end {
                    // Slot in range: post rc=1 ≠ UNUSED — contradiction.
                    assert(false);
                } else {
                    // Slot outside range: fully preserved by axiom.
                    assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
                    // segments gained one entry; cover at this paddr is
                    // the same as before (entry's range doesn't cover paddr).
                    assert(!(entry.range.start <= paddr < entry.range.end));
                    lemma_segment_cover_insert_outside(old_segments, id, entry, paddr);
                }
            };
            assert forall|idx: usize|
                #![trigger s.regions.slot_owners[idx]]
                idx < max_meta_slots() && s.regions.slot_owners[idx].usage == PageUsage::Frame
                    && s.regions.slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                    && s.regions.slot_owners[idx].inner_perms.ref_count.value()
                    != REF_COUNT_UNIQUE implies handle_count(s.frames, idx) > 0
                || s.regions.slot_owners[idx].paths_in_pt.len() > 0 || segment_cover_count(
                s.segments,
                index_to_frame(idx),
            ) > 0 by {
                let paddr = index_to_frame(idx);
                assert(paddr == (idx * PAGE_SIZE) as usize);
                assert(paddr % PAGE_SIZE == 0);
                assert(frame_to_index(paddr) == idx);
                if range.start <= paddr < range.end {
                    assert(entry.range == range);
                    lemma_segment_cover_insert_inside(old_segments, id, entry, paddr);
                } else {
                    assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
                    assert(!(entry.range.start <= paddr < entry.range.end));
                    lemma_segment_cover_insert_outside(old_segments, id, entry, paddr);
                }
            };
            assert forall|idx: usize|
                #![trigger s.regions.slot_owners[idx]]
                idx < max_meta_slots() && s.regions.slot_owners[idx].usage == PageUsage::Frame && (
                handle_count(s.frames, idx) > 0 || s.regions.slot_owners[idx].paths_in_pt.len() > 0
                    || segment_cover_count(s.segments, index_to_frame(idx)) > 0) implies {
                let so = s.regions.slot_owners[idx];
                let rc = so.inner_perms.ref_count.value();
                &&& rc != REF_COUNT_UNUSED
                &&& rc != REF_COUNT_UNIQUE
                &&& rc == handle_count(s.frames, idx) + so.paths_in_pt.len() + segment_cover_count(
                    s.segments,
                    index_to_frame(idx),
                )
                &&& so.inner_perms.storage.is_init()
            } by {
                let paddr = index_to_frame(idx);
                assert(paddr == (idx * PAGE_SIZE) as usize);
                assert(paddr % PAGE_SIZE == 0);
                assert(frame_to_index(paddr) == idx);
                if range.start <= paddr < range.end {
                    assert(entry.range == range);
                    lemma_segment_cover_insert_inside(old_segments, id, entry, paddr);
                    // H == 0 at idx because pre UNUSED ⟹ pre H == 0
                    // (pre clause 1) and frames unchanged.
                    assert(handle_count(s.frames, idx) == 0);
                } else {
                    assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
                    assert(!(entry.range.start <= paddr < entry.range.end));
                    lemma_segment_cover_insert_outside(old_segments, id, entry, paddr);
                }
            };
            // Discharge structural_inv's `in_list == 0` clause.
            assert forall|idx: usize|
                idx
                    < max_meta_slots() implies #[trigger] s.regions.slot_owners[idx].inner_perms.in_list.value()
                == 0 by {
                let paddr = index_to_frame(idx);
                assert(paddr == (idx * PAGE_SIZE) as usize);
                assert(paddr % PAGE_SIZE == 0);
                assert(frame_to_index(paddr) == idx);
                if range.start <= paddr < range.end {
                    // Axiom: in_list == 0 post for in-range slots.
                } else {
                    // Outside: fully preserved.
                    assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
                }
            };
            // structural FrameId⟹Frame-usage: every existing fid's
            // slot's usage preserved. Frame-usage slots are non-UNUSED
            // pre (clause 4), so they're outside `range` (which is all
            // UNUSED pre). Axiom fully preserves outside-range slots.
            assert forall|fid_other: FrameId| #[trigger]
                s.frames.dom().contains(fid_other) implies s.regions.slot_owners[frame_to_index(
                s.frames[fid_other].paddr,
            )].usage == PageUsage::Frame by {
                let other_idx = frame_to_index(s.frames[fid_other].paddr);
                let other_paddr = index_to_frame(other_idx);
                // pre fid_other's slot usage == Frame from old structural.
                assert(old_regions.slot_owners[other_idx].usage == PageUsage::Frame);
                // pre rc != UNUSED at fid_other's slot (clause 4 + H>=1).
                assert(old_frames.dom().filter(
                    |gid: FrameId| frame_to_index(old_frames[gid].paddr) == other_idx,
                ).contains(fid_other));
                assert(handle_count(old_frames, other_idx) >= 1);
                assert(old_regions.slot_owners[other_idx].inner_perms.ref_count.value()
                    != REF_COUNT_UNUSED);
                // pre rc != UNUSED ⟹ paddr not in `range` (range slots are
                // all UNUSED).
                // ⟹ axiom preserves the slot fully.
                assert(s.regions.slot_owners[other_idx] == old_regions.slot_owners[other_idx]);
            };
        },
        Option::None => {
            assert(s.regions == old_regions);
            assert(s.segments == old_segments);
        },
    }
}

/// `Op::SegmentDrop` step. Removes the `SegmentEntry` at `sid` and
/// releases the segment's forgotten reference at each covered frame.
/// Frames whose `rc` reaches 1 transition to UNUSED.
proof fn step_segment_drop<'rcu>(tracked s: &mut VmStore<'rcu>, sid: SegmentId)
    requires
        old(s).inv(),
        old(s).segments.dom().contains(sid),
    ensures
        final(s).inv(),
{
    let ghost old_regions = s.regions;
    let ghost old_frames = s.frames;
    let ghost old_segments = s.segments;
    let ghost range = s.segments[sid].range;
    // Discharge segment::drop_step's preconditions from `s.inv()`
    // BEFORE extracting (we need old_regions and old_segments).
    assert forall|paddr: Paddr|
        #![trigger frame_to_index(paddr)]
        (range.start <= paddr < range.end && paddr % PAGE_SIZE == 0) implies {
        let so = old_regions.slot_owners[frame_to_index(paddr)];
        &&& so.inner_perms.ref_count.value() >= 1
        &&& so.inner_perms.ref_count.value() <= crate::specs::mm::frame::meta_owners::REF_COUNT_MAX
        &&& so.usage == PageUsage::Frame
        &&& so.inner_perms.ref_count.value() == 1 ==> so.paths_in_pt.is_empty()
    } by {
        let idx = frame_to_index(paddr);
        // Cover >= 1 at paddr (this segment covers it).
        lemma_segment_cover_contains(old_segments, sid, paddr);
        // Usage == Frame from structural segment-covered ⟹ Frame clause.
        assert(old_regions.slot_owners[idx].usage == PageUsage::Frame);
        // Accounting clause 4: active head (cover > 0) ⟹ rc != UNUSED,
        // rc != UNIQUE, rc == H + P + cover, storage init.
        let so = old_regions.slot_owners[idx];
        let rc = so.inner_perms.ref_count.value();
        assert(rc != REF_COUNT_UNUSED);
        assert(rc != REF_COUNT_UNIQUE);
        assert(rc == handle_count(old_frames, idx) + so.paths_in_pt.len() + segment_cover_count(
            old_segments,
            paddr,
        ));
        // rc >= 1 since cover >= 1 ⟹ H + P + cover >= 1.
        assert(rc >= 1);
        // Triggers MetaSlotOwner::inv's SHARED branch (Item 1): rc in
        // [1, MAX] ⟹ storage init, in_list == 0.
        assert(old_regions.slot_owners.contains_key(idx));
        assert(old_regions.slot_owners[idx].inv());
        assert(rc <= crate::specs::mm::frame::meta_owners::REF_COUNT_MAX);
        // rc == 1 case: rc = H + P + cover = 1, cover >= 1 ⟹ cover == 1
        // and H == 0 and P == 0 ⟹ paths empty.
        if rc == 1 {
            assert(handle_count(old_frames, idx) + so.paths_in_pt.len() + segment_cover_count(
                old_segments,
                paddr,
            ) == 1);
            assert(so.paths_in_pt.len() == 0);
            assert(so.paths_in_pt == Set::empty());
        }
    };
    let tracked entry = s.extract_segment(sid);
    segment::drop_step(&mut s.regions, entry);

    // Re-establish structural_inv + accounting_inv on the post-state.
    // Per-slot reasoning:
    //   - Slot in `range`: post raw_count = pre - 1; segments lost
    //     `sid` whose range covered this paddr, so post cover = pre - 1.
    //     ⟹ post raw_count == post cover. ✓
    //     For accounting: pre eq was `rc == H + P + cover`. Post rc:
    //       if pre rc > 1: post rc = pre rc - 1.
    //       if pre rc == 1: post rc = UNUSED (teardown).
    //     Post H = pre H, post P = pre P, post cover = pre cover - 1.
    //     If pre rc > 1: post rc = pre rc - 1 = H + P + (cover - 1) = post eq ✓.
    //     If pre rc == 1: pre H == 0 ∧ pre P == 0 ∧ pre cover == 1
    //       (from rc == 1). Post H = 0, post P = 0, post cover = 0,
    //       post rc = UNUSED. Clause 1 (UNUSED) fires; equation vacuous.
    //   - Slot outside `range`: fully preserved (axiom + segment removal
    //     leaves cover unchanged at outside paddrs).

    assert forall|idx: usize|
        idx
            < max_meta_slots() implies #[trigger] s.regions.slot_owners[idx].inner_perms.in_list.value()
        == 0 by {
        let paddr = index_to_frame(idx);
        assert(paddr == (idx * PAGE_SIZE) as usize);
        assert(paddr % PAGE_SIZE == 0);
        assert(frame_to_index(paddr) == idx);
        if range.start <= paddr < range.end {
            // Axiom preserves in_list at in-range slots.
        } else {
            assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
        }
    };
    // Discharge accounting_inv clauses.
    assert forall|idx: usize|
        #![trigger s.regions.slot_owners[idx]]
        idx < max_meta_slots() && s.regions.slot_owners[idx].inner_perms.ref_count.value()
            == REF_COUNT_UNUSED implies handle_count(s.frames, idx) == 0
        && s.regions.slot_owners[idx].paths_in_pt.is_empty() && segment_cover_count(
        s.segments,
        index_to_frame(idx),
    ) == 0 by {
        let paddr = index_to_frame(idx);
        assert(paddr == (idx * PAGE_SIZE) as usize);
        assert(paddr % PAGE_SIZE == 0);
        assert(frame_to_index(paddr) == idx);
        if range.start <= paddr < range.end {
            // Post UNUSED at in-range ⟹ pre rc == 1 (axiom transition).
            // Pre eq: 1 == H + P + cover, cover >= 1 ⟹ cover == 1,
            // H == 0, P == 0. Frames unchanged ⟹ post H == 0.
            // Paths preserved ⟹ post P == 0 ⟹ post paths empty.
            // Segments removed sid (whose range covered paddr) ⟹
            // post cover == 0.
            lemma_segment_cover_contains(old_segments, sid, paddr);
            lemma_segment_cover_remove_inside(old_segments, sid, paddr);
            assert(old_regions.slot_owners[idx].inner_perms.ref_count.value() == 1);
            assert(handle_count(old_frames, idx) == 0);
            assert(s.regions.slot_owners[idx].paths_in_pt == Set::empty());
        } else {
            // Outside: fully preserved; segments removal doesn't affect cover.
            assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
            assert(!(entry.range.start <= paddr < entry.range.end));
            lemma_segment_cover_remove_outside(old_segments, sid, paddr);
        }
    };
    assert forall|idx: usize|
        #![trigger s.regions.slot_owners[idx]]
        idx < max_meta_slots() && s.regions.slot_owners[idx].usage == PageUsage::Frame
            && s.regions.slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
            && s.regions.slot_owners[idx].inner_perms.ref_count.value()
            != REF_COUNT_UNIQUE implies handle_count(s.frames, idx) > 0
        || s.regions.slot_owners[idx].paths_in_pt.len() > 0 || segment_cover_count(
        s.segments,
        index_to_frame(idx),
    ) > 0 by {
        let paddr = index_to_frame(idx);
        assert(paddr == (idx * PAGE_SIZE) as usize);
        assert(paddr % PAGE_SIZE == 0);
        assert(frame_to_index(paddr) == idx);
        if range.start <= paddr < range.end {
            // Post non-UNUSED at in-range ⟹ pre rc > 1 (axiom).
            // Pre eq: pre rc == H + P + cover. Pre rc > 1 ⟹ at least
            // one of H, P, (cover-1) > 0. Post H == pre H, post P ==
            // pre P, post cover == pre cover - 1.
            lemma_segment_cover_contains(old_segments, sid, paddr);
            lemma_segment_cover_remove_inside(old_segments, sid, paddr);
        } else {
            assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
            assert(!(entry.range.start <= paddr < entry.range.end));
            lemma_segment_cover_remove_outside(old_segments, sid, paddr);
        }
    };
    assert forall|idx: usize|
        #![trigger s.regions.slot_owners[idx]]
        idx < max_meta_slots() && s.regions.slot_owners[idx].usage == PageUsage::Frame && (
        handle_count(s.frames, idx) > 0 || s.regions.slot_owners[idx].paths_in_pt.len() > 0
            || segment_cover_count(s.segments, index_to_frame(idx)) > 0) implies {
        let so = s.regions.slot_owners[idx];
        let rc = so.inner_perms.ref_count.value();
        &&& rc != REF_COUNT_UNUSED
        &&& rc != REF_COUNT_UNIQUE
        &&& rc == handle_count(s.frames, idx) + so.paths_in_pt.len() + segment_cover_count(
            s.segments,
            index_to_frame(idx),
        )
        &&& so.inner_perms.storage.is_init()
    } by {
        let paddr = index_to_frame(idx);
        assert(paddr == (idx * PAGE_SIZE) as usize);
        assert(paddr % PAGE_SIZE == 0);
        assert(frame_to_index(paddr) == idx);
        if range.start <= paddr < range.end {
            lemma_segment_cover_contains(old_segments, sid, paddr);
            lemma_segment_cover_remove_inside(old_segments, sid, paddr);
            // Pre eq: pre rc == pre H + pre P + pre cover.
            let pre_rc = old_regions.slot_owners[idx].inner_perms.ref_count.value();
            let pre_H = handle_count(old_frames, idx);
            let pre_P = old_regions.slot_owners[idx].paths_in_pt.len();
            let pre_cover = segment_cover_count(old_segments, paddr);
            assert(pre_rc == pre_H + pre_P + pre_cover);
            assert(pre_rc != REF_COUNT_UNIQUE);
            let post_rc = s.regions.slot_owners[idx].inner_perms.ref_count.value();
            assert(post_rc != REF_COUNT_UNUSED);
            assert(pre_rc > 1) by {
                if pre_rc == 1 {
                    assert(post_rc == REF_COUNT_UNUSED);
                }
            };
            assert(post_rc == (pre_rc - 1) as u64);
            assert(s.regions.slot_owners[idx].paths_in_pt
                == old_regions.slot_owners[idx].paths_in_pt);
            assert(handle_count(s.frames, idx) == pre_H);
            assert(segment_cover_count(s.segments, paddr) == (pre_cover - 1) as nat);
            // post rc <= MAX (pre rc was, post = pre - 1, still in range).
            assert(post_rc <= crate::specs::mm::frame::meta_owners::REF_COUNT_MAX);
            // storage.is_init at post: post rc ∈ SHARED (1 <= post rc <= MAX)
            // ⟹ MetaSlotOwner::inv SHARED branch ⟹ storage.is_init.
            assert(s.regions.slot_owners.contains_key(idx));
            assert(s.regions.slot_owners[idx].inv());
            assert(post_rc >= 1);
            assert(s.regions.slot_owners[idx].inner_perms.storage.is_init());
        } else {
            assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
            assert(!(entry.range.start <= paddr < entry.range.end));
            lemma_segment_cover_remove_outside(old_segments, sid, paddr);
        }
    };
    // Structural FrameId⟹Frame-usage: frames unchanged; for fid_other's
    // slot, usage preserved (covered slots remain Frame; in-range slots
    // either stay non-UNUSED (rc-1) or become UNUSED — UNUSED ones had
    // H == 0, so no fid points there).
    assert forall|fid_other: FrameId| #[trigger]
        s.frames.dom().contains(fid_other) implies s.regions.slot_owners[frame_to_index(
        s.frames[fid_other].paddr,
    )].usage == PageUsage::Frame by {
        let other_idx = frame_to_index(s.frames[fid_other].paddr);
        let other_paddr = index_to_frame(other_idx);
        // Pre fid_other's slot: usage == Frame (old structural).
        assert(old_regions.slot_owners[other_idx].usage == PageUsage::Frame);
        // Pre H >= 1 at other_idx (fid_other contributes).
        assert(old_frames.dom().filter(
            |gid: FrameId| frame_to_index(old_frames[gid].paddr) == other_idx,
        ).contains(fid_other));
        assert(handle_count(old_frames, other_idx) >= 1);
        // Pre clause 4: pre rc == H + P + cover ≥ 1 ⟹ rc != UNUSED.
        assert(old_regions.slot_owners[other_idx].inner_perms.ref_count.value() >= 1);
        // Axiom preserves usage (universal).
        if range.start <= other_paddr < range.end {
            // In-range: usage preserved by axiom.
        } else {
            // Outside: fully preserved.
            assert(s.regions.slot_owners[other_idx] == old_regions.slot_owners[other_idx]);
        }
    };
    // Structural segment-covered ⟹ Frame-usage: for any remaining
    // segment sid_other ≠ sid, usage at every covered paddr is
    // preserved (usage universally preserved by axiom).
    assert forall|sid_other: SegmentId, paddr_c: Paddr|
        #![trigger
            s.segments.dom().contains(sid_other),
            frame_to_index(paddr_c)]
        s.segments.dom().contains(sid_other) && s.segments[sid_other].range.start <= paddr_c
            < s.segments[sid_other].range.end && paddr_c % PAGE_SIZE
            == 0 implies s.regions.slot_owners[frame_to_index(paddr_c)].usage
        == PageUsage::Frame by {
        let cov_idx = frame_to_index(paddr_c);
        // sid_other != sid (since sid was removed from s.segments).
        assert(sid_other != sid);
        // sid_other was in old_segments too.
        assert(old_segments.dom().contains(sid_other));
        assert(old_segments[sid_other] == s.segments[sid_other]);
        // Pre covered ⟹ pre Frame from old structural.
        assert(old_regions.slot_owners[cov_idx].usage == PageUsage::Frame);
        // Axiom preserves usage universally.
    };
}

/// `Op::SegmentSplit` step. Replaces `sid` with two fresh segment
/// entries covering the disjoint halves; `regions` is unchanged.
/// `accounting_inv` chains because per-paddr `cover_count` is
/// invariant under the partition (see [`lemma_segment_cover_split`]).
proof fn step_segment_split<'rcu>(tracked s: &mut VmStore<'rcu>, sid: SegmentId, offset: usize)
    requires
        old(s).inv(),
        old(s).segments.dom().contains(sid),
        offset % PAGE_SIZE == 0,
        0 < offset,
        offset < (old(s).segments[sid].range.end - old(s).segments[sid].range.start),
    ensures
        final(s).inv(),
{
    let ghost old_regions = s.regions;
    let ghost old_frames = s.frames;
    let ghost old_segments = s.segments;
    let ghost range = s.segments[sid].range;
    let ghost mid = (range.start + offset) as Paddr;
    let ghost entry_left = SegmentEntry { range: range.start..mid };
    let ghost entry_right = SegmentEntry { range: mid..range.end };
    // Pick fresh ids BEFORE the extract so they are guaranteed
    // distinct from `sid` (which is still in `s.segments`). Choose
    // `id_left` first, then `id_right` from the
    // `s.segments.insert(id_left, _)`-extended domain so they are
    // distinct from each other and from `sid`.
    let ghost id_left = fresh_segment_id(s.segments);
    axiom_fresh_segment_id_not_in_dom(s.segments);
    assert(id_left != sid);
    let ghost stub_entry = SegmentEntry { range: range.start..mid };
    let ghost id_right = fresh_segment_id(s.segments.insert(id_left, stub_entry));
    axiom_fresh_segment_id_not_in_dom(s.segments.insert(id_left, stub_entry));
    assert(id_right != sid);
    assert(id_right != id_left);
    // Now extract and insert.
    let tracked _orig = s.extract_segment(sid);
    assert(!s.segments.dom().contains(id_left));
    let tracked entry_l = axiom_segment_entry_new(range.start..mid);
    s.insert_segment(id_left, entry_l);
    assert(!s.segments.dom().contains(id_right));
    let tracked entry_r = axiom_segment_entry_new(mid..range.end);
    s.insert_segment(id_right, entry_r);
    // Re-establish structural_inv + accounting_inv. Regions is
    // unchanged; the partition lemma gives per-paddr cover_count
    // preservation; so every invariant clause carries over from
    // `s_old`.
    assert(s.regions == old_regions);
    assert forall|paddr: Paddr| #[trigger]
        frame_to_index(paddr) < max_meta_slots() implies segment_cover_count(s.segments, paddr)
        == segment_cover_count(old_segments, paddr) by {
        lemma_segment_cover_split(
            old_segments,
            sid,
            id_left,
            id_right,
            entry_left,
            entry_right,
            paddr,
        );
    };
    // Each invariant clause that mentions `cover_count` chains via the
    // per-paddr equality above. `slot_owners` / `slots` / `frames` /
    // `tlb_model` / `vm_spaces` / `cursors` / `vm_ios` unchanged ⟹
    // their clauses carry verbatim from `old(s).inv()`.

    // Segment range well-formedness for the two new entries.
    assert(entry_left.range.start % PAGE_SIZE == 0);
    assert(entry_right.range.start % PAGE_SIZE == 0);
    assert(entry_left.range.end % PAGE_SIZE == 0);
    assert(entry_right.range.end % PAGE_SIZE == 0);
    // segment-covered ⟹ Frame-usage: covered paddrs by the new
    // entries are the same set as covered by the original ⟹ usage
    // was Frame pre, still Frame post (regions unchanged).
    assert forall|sid_other: SegmentId, paddr_c: Paddr|
        #![trigger
            s.segments.dom().contains(sid_other),
            frame_to_index(paddr_c)]
        s.segments.dom().contains(sid_other) && s.segments[sid_other].range.start <= paddr_c
            < s.segments[sid_other].range.end && paddr_c % PAGE_SIZE
            == 0 implies s.regions.slot_owners[frame_to_index(paddr_c)].usage
        == PageUsage::Frame by {
        if sid_other == id_left {
            assert(old_segments.dom().contains(sid));
            assert(old_segments[sid].range.start <= paddr_c < old_segments[sid].range.end);
        } else if sid_other == id_right {
            assert(old_segments.dom().contains(sid));
            assert(old_segments[sid].range.start <= paddr_c < old_segments[sid].range.end);
        } else {
            assert(old_segments.dom().contains(sid_other));
            assert(old_segments[sid_other] == s.segments[sid_other]);
        }
    };
    // Discharge accounting_inv's three clauses. Regions unchanged ⟹
    // every per-slot value (rc, paths, usage, etc.) preserved; frames
    // unchanged ⟹ handle_count preserved; cover_count preserved
    // per-paddr via lemma_segment_cover_split.
    assert forall|idx: usize|
        #![trigger s.regions.slot_owners[idx]]
        idx < max_meta_slots() && s.regions.slot_owners[idx].inner_perms.ref_count.value()
            == REF_COUNT_UNUSED implies handle_count(s.frames, idx) == 0
        && s.regions.slot_owners[idx].paths_in_pt.is_empty() && segment_cover_count(
        s.segments,
        index_to_frame(idx),
    ) == 0 by {
        let paddr = index_to_frame(idx);
        assert(paddr == (idx * PAGE_SIZE) as usize);
        assert(frame_to_index(paddr) == idx);
        lemma_segment_cover_split(
            old_segments,
            sid,
            id_left,
            id_right,
            entry_left,
            entry_right,
            paddr,
        );
    };
    assert forall|idx: usize|
        #![trigger s.regions.slot_owners[idx]]
        idx < max_meta_slots() && s.regions.slot_owners[idx].usage == PageUsage::Frame
            && s.regions.slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
            && s.regions.slot_owners[idx].inner_perms.ref_count.value()
            != REF_COUNT_UNIQUE implies handle_count(s.frames, idx) > 0
        || s.regions.slot_owners[idx].paths_in_pt.len() > 0 || segment_cover_count(
        s.segments,
        index_to_frame(idx),
    ) > 0 by {
        let paddr = index_to_frame(idx);
        assert(paddr == (idx * PAGE_SIZE) as usize);
        assert(frame_to_index(paddr) == idx);
        lemma_segment_cover_split(
            old_segments,
            sid,
            id_left,
            id_right,
            entry_left,
            entry_right,
            paddr,
        );
    };
    assert forall|idx: usize|
        #![trigger s.regions.slot_owners[idx]]
        idx < max_meta_slots() && s.regions.slot_owners[idx].usage == PageUsage::Frame && (
        handle_count(s.frames, idx) > 0 || s.regions.slot_owners[idx].paths_in_pt.len() > 0
            || segment_cover_count(s.segments, index_to_frame(idx)) > 0) implies {
        let so = s.regions.slot_owners[idx];
        let rc = so.inner_perms.ref_count.value();
        &&& rc != REF_COUNT_UNUSED
        &&& rc != REF_COUNT_UNIQUE
        &&& rc == handle_count(s.frames, idx) + so.paths_in_pt.len() + segment_cover_count(
            s.segments,
            index_to_frame(idx),
        )
        &&& so.inner_perms.storage.is_init()
    } by {
        let paddr = index_to_frame(idx);
        assert(paddr == (idx * PAGE_SIZE) as usize);
        assert(frame_to_index(paddr) == idx);
        lemma_segment_cover_split(
            old_segments,
            sid,
            id_left,
            id_right,
            entry_left,
            entry_right,
            paddr,
        );
    };
}

/// `Op::SegmentNext` step. Pops the front frame off `sid`'s range,
/// registering a fresh `FrameEntry` at `paddr = range.start`. The
/// segment's range shrinks by one page from the front; if it
/// becomes empty, `sid` is removed.
///
/// **The conversion bridge** between segment-held forgotten
/// references and user-held `Frame<M>` handles. Per-paddr at the
/// popped slot:
///   `raw_count: pre - 1`  (segment lost one forgotten ref via
///                          `Frame::from_raw`),
///   `cover_count: pre - 1` (segment's range shrunk past paddr),
///   `H: pre + 1`           (fresh `FrameEntry` registered),
///   `rc: pre`              (`from_raw` doesn't touch rc; the new
///                          `Frame` handle inherits the rc that
///                          the segment was holding).
///
/// Accounting equation `rc == H + P + cover_count`:
///   `pre rc == pre H + pre P + pre cover`
///   `post rc == pre rc
///            == (post H - 1) + post P + (post cover + 1)
///            == post H + post P + post cover`. ✓
///
/// Structural `raw_count == cover_count`:
///   pre: `pre raw == pre cover` at every idx.
///   post at popped: `(pre raw - 1) == (pre cover - 1)`. ✓
///   post elsewhere: unchanged.
proof fn step_segment_next<'rcu>(tracked s: &mut VmStore<'rcu>, sid: SegmentId)
    requires
        old(s).inv(),
        old(s).segments.dom().contains(sid),
    ensures
        final(s).inv(),
{
    let ghost old_regions = s.regions;
    let ghost old_frames = s.frames;
    let ghost old_segments = s.segments;
    let ghost range = s.segments[sid].range;
    let ghost paddr = range.start;
    let ghost target_idx = frame_to_index(paddr);
    let ghost new_range_start = (paddr + PAGE_SIZE) as Paddr;
    let ghost new_range_end = range.end;
    let ghost will_become_empty = new_range_start >= new_range_end;
    let ghost new_entry_ghost = SegmentEntry { range: new_range_start..new_range_end };

    // Establish facts about the popped slot from `s.inv()`.
    lemma_segment_cover_contains(old_segments, sid, paddr);
    assert(segment_cover_count(old_segments, paddr) >= 1);
    assert(old_regions.slot_owners[target_idx].usage == PageUsage::Frame);
    let ghost so_pre = old_regions.slot_owners[target_idx];
    let ghost pre_rc = so_pre.inner_perms.ref_count.value();
    let ghost pre_H = handle_count(old_frames, target_idx);
    let ghost pre_P = so_pre.paths_in_pt.len();
    let ghost pre_cover = segment_cover_count(old_segments, paddr);
    assert(pre_rc == pre_H + pre_P + pre_cover);
    assert(pre_rc != REF_COUNT_UNUSED);
    assert(pre_rc != REF_COUNT_UNIQUE);
    assert(pre_rc >= 1);
    assert(old_regions.slot_owners.contains_key(target_idx));
    assert(old_regions.slot_owners[target_idx].inv());
    assert(pre_rc <= crate::specs::mm::frame::meta_owners::REF_COUNT_MAX);
    assert(has_safe_slot(paddr));
    s.regions.inv_implies_correct_addr(paddr);
    assert(s.regions.slots.contains_key(target_idx));
    // page-alignment + bound for shrink_front lemma.
    assert(range.start % PAGE_SIZE == 0);
    assert(range.end <= MAX_PADDR);
    assert(range.start + PAGE_SIZE <= MAX_PADDR);

    // Register the new FrameEntry FIRST (s.inv() still holds).
    let ghost fid = fresh_frame_id(s.frames);
    axiom_fresh_frame_id_not_in_dom(s.frames);
    let tracked frame_entry = axiom_frame_entry_new(paddr);
    s.insert_frame(fid, frame_entry);
    // Now segment manipulation.
    let tracked _old_entry = s.extract_segment(sid);
    segment::segment_next_embedded(&mut s.regions, paddr);
    if !will_become_empty {
        let tracked new_entry = axiom_segment_entry_new(new_range_start..new_range_end);
        s.insert_segment(sid, new_entry);
        assert(new_entry == new_entry_ghost);
        assert(s.segments == old_segments.remove(sid).insert(sid, new_entry_ghost));
    } else {
        assert(s.segments == old_segments.remove(sid));
    }
    assert(s.frames == old_frames.insert(fid, frame_entry));

    // Per-paddr cover delta (from the shrink-front lemma): cover_post
    // == cover_pre - (1 at popped else 0).
    assert forall|paddr_c: Paddr| paddr_c % PAGE_SIZE == 0 implies #[trigger] segment_cover_count(
        s.segments,
        paddr_c,
    ) == (if paddr_c == paddr {
        1nat
    } else {
        0nat
    }) + 0nat
    // Workaround: we want
    //   cover_post == cover_pre - delta
    // Restated below as two separate forall conjuncts.
     || true by {
        lemma_segment_cover_shrink_front(old_segments, sid, new_entry_ghost, paddr_c);
    };
    // Cleaner per-paddr facts: at popped, cover decreased by 1; elsewhere unchanged.
    assert forall|paddr_c: Paddr|
        paddr_c % PAGE_SIZE == 0 && paddr_c == paddr implies #[trigger] segment_cover_count(
        s.segments,
        paddr_c,
    ) + 1 == segment_cover_count(old_segments, paddr_c) by {
        lemma_segment_cover_shrink_front(old_segments, sid, new_entry_ghost, paddr_c);
    };
    assert forall|paddr_c: Paddr|
        paddr_c % PAGE_SIZE == 0 && paddr_c != paddr implies #[trigger] segment_cover_count(
        s.segments,
        paddr_c,
    ) == segment_cover_count(old_segments, paddr_c) by {
        lemma_segment_cover_shrink_front(old_segments, sid, new_entry_ghost, paddr_c);
    };

    // Structural in_list == 0.
    assert forall|idx: usize|
        idx
            < max_meta_slots() implies #[trigger] s.regions.slot_owners[idx].inner_perms.in_list.value()
        == 0 by {
        let paddr_c = index_to_frame(idx);
        assert(paddr_c == (idx * PAGE_SIZE) as usize);
        if idx == target_idx {
            // Axiom preserves in_list at paddr.
        } else {
            assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
        }
    };
    // Structural FrameId⟹Frame-usage. New fid points at paddr whose
    // slot is Frame-usage (preserved by axiom); other fids' slots
    // preserved.
    assert forall|fid_other: FrameId| #[trigger]
        s.frames.dom().contains(fid_other) implies s.regions.slot_owners[frame_to_index(
        s.frames[fid_other].paddr,
    )].usage == PageUsage::Frame by {
        let other_idx = frame_to_index(s.frames[fid_other].paddr);
        if fid_other == fid {
            assert(s.frames[fid_other].paddr == paddr);
            assert(other_idx == target_idx);
        } else {
            assert(old_frames.dom().contains(fid_other));
            assert(s.frames[fid_other] == old_frames[fid_other]);
            assert(old_regions.slot_owners[other_idx].usage == PageUsage::Frame);
        }
    };
    // Structural segment-covered ⟹ Frame-usage.
    assert forall|sid_other: SegmentId, paddr_c: Paddr|
        #![trigger
            s.segments.dom().contains(sid_other),
            frame_to_index(paddr_c)]
        s.segments.dom().contains(sid_other) && s.segments[sid_other].range.start <= paddr_c
            < s.segments[sid_other].range.end && paddr_c % PAGE_SIZE
            == 0 implies s.regions.slot_owners[frame_to_index(paddr_c)].usage
        == PageUsage::Frame by {
        let cov_idx = frame_to_index(paddr_c);
        if !will_become_empty && sid_other == sid {
            // Covered paddr in new_range ⊆ original range.
            assert(old_segments.dom().contains(sid));
            assert(old_regions.slot_owners[cov_idx].usage == PageUsage::Frame);
        } else {
            assert(sid_other != sid);
            assert(old_segments.dom().contains(sid_other));
            assert(old_segments[sid_other] == s.segments[sid_other]);
            assert(old_regions.slot_owners[cov_idx].usage == PageUsage::Frame);
        }
    };
    // Segment range well-formedness for the re-inserted entry (if any).
    if !will_become_empty {
        assert(new_range_start % PAGE_SIZE == 0);
        assert(new_range_end % PAGE_SIZE == 0);
        assert(new_range_end <= MAX_PADDR);
    }
    // Accounting clauses.

    assert forall|idx: usize|
        #![trigger s.regions.slot_owners[idx]]
        idx < max_meta_slots() && s.regions.slot_owners[idx].inner_perms.ref_count.value()
            == REF_COUNT_UNUSED implies handle_count(s.frames, idx) == 0
        && s.regions.slot_owners[idx].paths_in_pt.is_empty() && segment_cover_count(
        s.segments,
        index_to_frame(idx),
    ) == 0 by {
        let paddr_c = index_to_frame(idx);
        assert(paddr_c == (idx * PAGE_SIZE) as usize);
        assert(frame_to_index(paddr_c) == idx);
        if idx == target_idx {
            // post rc at target == pre rc != UNUSED (axiom). Antecedent false.
            assert(false);
        } else {
            assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
            lemma_handle_count_insert_fresh(old_frames, fid, frame_entry, idx);
        }
    };
    assert forall|idx: usize|
        #![trigger s.regions.slot_owners[idx]]
        idx < max_meta_slots() && s.regions.slot_owners[idx].usage == PageUsage::Frame
            && s.regions.slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
            && s.regions.slot_owners[idx].inner_perms.ref_count.value()
            != REF_COUNT_UNIQUE implies handle_count(s.frames, idx) > 0
        || s.regions.slot_owners[idx].paths_in_pt.len() > 0 || segment_cover_count(
        s.segments,
        index_to_frame(idx),
    ) > 0 by {
        let paddr_c = index_to_frame(idx);
        assert(paddr_c == (idx * PAGE_SIZE) as usize);
        if idx == target_idx {
            // New fid gives H >= 1.
            lemma_handle_count_insert_fresh(old_frames, fid, frame_entry, idx);
            assert(handle_count(s.frames, target_idx) >= 1);
        } else {
            assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
            lemma_handle_count_insert_fresh(old_frames, fid, frame_entry, idx);
        }
    };
    assert forall|idx: usize|
        #![trigger s.regions.slot_owners[idx]]
        idx < max_meta_slots() && s.regions.slot_owners[idx].usage == PageUsage::Frame && (
        handle_count(s.frames, idx) > 0 || s.regions.slot_owners[idx].paths_in_pt.len() > 0
            || segment_cover_count(s.segments, index_to_frame(idx)) > 0) implies {
        let so = s.regions.slot_owners[idx];
        let rc = so.inner_perms.ref_count.value();
        &&& rc != REF_COUNT_UNUSED
        &&& rc != REF_COUNT_UNIQUE
        &&& rc == handle_count(s.frames, idx) + so.paths_in_pt.len() + segment_cover_count(
            s.segments,
            index_to_frame(idx),
        )
        &&& so.inner_perms.storage.is_init()
    } by {
        let paddr_c = index_to_frame(idx);
        assert(paddr_c == (idx * PAGE_SIZE) as usize);
        lemma_handle_count_insert_fresh(old_frames, fid, frame_entry, idx);
        if idx == target_idx {
            // post rc == pre rc; post H = pre H + 1; post P = pre P;
            // post cover = pre cover - 1.
            // post rc == pre H + pre P + pre cover
            //         == (post H - 1) + post P + (post cover + 1)
            //         == post H + post P + post cover.
        } else {
            assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
        }
    };
}

/// Inserting a fresh segment whose range DOES cover `paddr` bumps
/// `segment_cover_count` by 1.
pub proof fn lemma_segment_cover_insert_inside(
    segments: Map<SegmentId, SegmentEntry>,
    sid: SegmentId,
    entry: SegmentEntry,
    paddr: Paddr,
)
    requires
        !segments.dom().contains(sid),
        entry.range.start <= paddr < entry.range.end,
    ensures
        segment_cover_count(segments.insert(sid, entry), paddr) == segment_cover_count(
            segments,
            paddr,
        ) + 1,
{
    let segments2 = segments.insert(sid, entry);
    let pred = |s: SegmentId| segments[s].range.start <= paddr && paddr < segments[s].range.end;
    let pred2 = |s: SegmentId| segments2[s].range.start <= paddr && paddr < segments2[s].range.end;
    let old_filt = segments.dom().filter(pred);
    let new_filt = segments2.dom().filter(pred2);
    assert(segments2.dom() == segments.dom().insert(sid));
    assert(!old_filt.contains(sid));
    assert(new_filt == old_filt.insert(sid)) by {
        assert forall|s: SegmentId| #[trigger] new_filt.contains(s) implies old_filt.insert(
            sid,
        ).contains(s) by {
            if s == sid {
            } else {
                assert(segments2[s] == segments[s]);
            }
        };
        assert forall|s: SegmentId| #[trigger]
            old_filt.insert(sid).contains(s) implies new_filt.contains(s) by {
            if s == sid {
                assert(segments2[s].range == entry.range);
            } else {
                assert(segments2[s] == segments[s]);
            }
        };
    };
    assert(new_filt.len() == old_filt.len() + 1);
}

/// Inserting a fresh segment whose range DOES NOT cover `paddr`
/// leaves `segment_cover_count(_, paddr)` unchanged.
pub proof fn lemma_segment_cover_insert_outside(
    segments: Map<SegmentId, SegmentEntry>,
    sid: SegmentId,
    entry: SegmentEntry,
    paddr: Paddr,
)
    requires
        !segments.dom().contains(sid),
        !(entry.range.start <= paddr < entry.range.end),
    ensures
        segment_cover_count(segments.insert(sid, entry), paddr) == segment_cover_count(
            segments,
            paddr,
        ),
{
    let segments2 = segments.insert(sid, entry);
    let pred = |s: SegmentId| segments[s].range.start <= paddr && paddr < segments[s].range.end;
    let pred2 = |s: SegmentId| segments2[s].range.start <= paddr && paddr < segments2[s].range.end;
    let old_filt = segments.dom().filter(pred);
    let new_filt = segments2.dom().filter(pred2);
    assert(segments2.dom() == segments.dom().insert(sid));
    assert(new_filt == old_filt) by {
        assert forall|s: SegmentId| #[trigger] new_filt.contains(s) implies old_filt.contains(
            s,
        ) by {
            if s == sid {
                // entry's range doesn't cover paddr ⟹ pred2(sid) false.
                assert(false);
            } else {
                assert(segments2[s] == segments[s]);
            }
        };
        assert forall|s: SegmentId| #[trigger] old_filt.contains(s) implies new_filt.contains(
            s,
        ) by {
            assert(s != sid);
            assert(segments2[s] == segments[s]);
        };
    };
}

/// If `sid ∈ segments` and `segments[sid].range` covers `paddr`,
/// then `segment_cover_count >= 1` at `paddr`.
pub proof fn lemma_segment_cover_contains(
    segments: Map<SegmentId, SegmentEntry>,
    sid: SegmentId,
    paddr: Paddr,
)
    requires
        segments.dom().contains(sid),
        segments[sid].range.start <= paddr < segments[sid].range.end,
    ensures
        segment_cover_count(segments, paddr) >= 1,
{
    let filt = segments.dom().filter(
        |s: SegmentId| segments[s].range.start <= paddr && paddr < segments[s].range.end,
    );
    assert(filt.contains(sid));
}

/// Removing an existing segment whose range covers `paddr` decreases
/// `segment_cover_count` at `paddr` by exactly 1.
pub proof fn lemma_segment_cover_remove_inside(
    segments: Map<SegmentId, SegmentEntry>,
    sid: SegmentId,
    paddr: Paddr,
)
    requires
        segments.dom().contains(sid),
        segments[sid].range.start <= paddr < segments[sid].range.end,
    ensures
        segment_cover_count(segments.remove(sid), paddr) == (segment_cover_count(segments, paddr)
            - 1) as nat,
{
    let segments2 = segments.remove(sid);
    let pred = |s: SegmentId| segments[s].range.start <= paddr && paddr < segments[s].range.end;
    let pred2 = |s: SegmentId| segments2[s].range.start <= paddr && paddr < segments2[s].range.end;
    let old_filt = segments.dom().filter(pred);
    let new_filt = segments2.dom().filter(pred2);
    assert(segments2.dom() == segments.dom().remove(sid));
    assert(old_filt.contains(sid));
    assert(new_filt == old_filt.remove(sid)) by {
        assert forall|s: SegmentId| #[trigger] new_filt.contains(s) implies old_filt.remove(
            sid,
        ).contains(s) by {
            assert(s != sid);
            assert(segments2[s] == segments[s]);
        };
        assert forall|s: SegmentId| #[trigger]
            old_filt.remove(sid).contains(s) implies new_filt.contains(s) by {
            assert(s != sid);
            assert(segments2[s] == segments[s]);
        };
    };
}

/// **Next-pop helper.** `Segment::next` pops the front frame off
/// `sid`, shrinking its range from `[start, end)` to
/// `[start + PAGE_SIZE, end)`. The net effect on per-paddr
/// `segment_cover_count`: it decrements by 1 only at the popped
/// `paddr == start`; everywhere else it's invariant.
///
/// Models the two cases (segment becomes empty vs not) via the two
/// resulting map shapes: `remove(sid)` (when the new range is empty)
/// or `remove(sid).insert(sid, new_entry)` (when the new range still
/// has frames).
pub proof fn lemma_segment_cover_shrink_front(
    segments: Map<SegmentId, SegmentEntry>,
    sid: SegmentId,
    new_entry: SegmentEntry,
    paddr_check: Paddr,
)
    requires
        segments.dom().contains(sid),
        // Original segment is non-empty (the caller guarantees this
        // from structural_inv).
        segments[sid].range.start < segments[sid].range.end,
        // Page-aligned start (from structural_inv).
        segments[sid].range.start % PAGE_SIZE == 0,
        // No-overflow envelope for `start + PAGE_SIZE`.
        segments[sid].range.start + PAGE_SIZE <= MAX_PADDR,
        new_entry.range.start == (segments[sid].range.start + PAGE_SIZE) as Paddr,
        new_entry.range.end == segments[sid].range.end,
        new_entry.range.start <= new_entry.range.end,
        paddr_check % PAGE_SIZE == 0,
    ensures
// Non-empty new range case: cover at popped paddr drops by 1;
// elsewhere preserved.

        new_entry.range.start < new_entry.range.end ==> ({
            let new_segments = segments.remove(sid).insert(sid, new_entry);
            paddr_check == segments[sid].range.start ==> segment_cover_count(
                new_segments,
                paddr_check,
            ) + 1 == segment_cover_count(segments, paddr_check)
        }),
        new_entry.range.start < new_entry.range.end ==> ({
            let new_segments = segments.remove(sid).insert(sid, new_entry);
            paddr_check != segments[sid].range.start ==> segment_cover_count(
                new_segments,
                paddr_check,
            ) == segment_cover_count(segments, paddr_check)
        }),
        // Empty new range case (popped frame was the only one).
        new_entry.range.start >= new_entry.range.end ==> ({
            let new_segments = segments.remove(sid);
            paddr_check == segments[sid].range.start ==> segment_cover_count(
                new_segments,
                paddr_check,
            ) + 1 == segment_cover_count(segments, paddr_check)
        }),
        new_entry.range.start >= new_entry.range.end ==> ({
            let new_segments = segments.remove(sid);
            paddr_check != segments[sid].range.start ==> segment_cover_count(
                new_segments,
                paddr_check,
            ) == segment_cover_count(segments, paddr_check)
        }),
{
    let popped = segments[sid].range.start;
    let range = segments[sid].range;
    // PAGE_SIZE > 0 + the new_entry well-formedness ⟹ range.start
    // < range.end (so the original segment was non-empty).
    assert(range.start < range.end);
    let sid_pre_covers = range.start <= paddr_check < range.end;
    let new_covers = new_entry.range.start <= paddr_check < new_entry.range.end;
    // Cover transition after `remove(sid)`.
    if sid_pre_covers {
        lemma_segment_cover_remove_inside(segments, sid, paddr_check);
    } else {
        lemma_segment_cover_remove_outside(segments, sid, paddr_check);
    }
    if new_entry.range.start < new_entry.range.end {
        let new_segments = segments.remove(sid).insert(sid, new_entry);
        if paddr_check == popped {
            // new_entry.range.start == popped + PAGE_SIZE > popped ⟹
            // paddr_check < new_entry.range.start ⟹ !new_covers.
            assert(!new_covers);
            assert(sid_pre_covers);
            lemma_segment_cover_insert_outside(segments.remove(sid), sid, new_entry, paddr_check);
            lemma_segment_cover_contains(segments, sid, paddr_check);
            assert(segment_cover_count(new_segments, paddr_check) + 1 == segment_cover_count(
                segments,
                paddr_check,
            ));
        } else if sid_pre_covers {
            // paddr_check ∈ [popped, range.end), paddr_check != popped,
            // paddr_check page-aligned + popped page-aligned ⟹
            // paddr_check >= popped + PAGE_SIZE ⟹ in new_entry.range.
            assert(new_covers);
            lemma_segment_cover_contains(segments, sid, paddr_check);
            lemma_segment_cover_insert_inside(segments.remove(sid), sid, new_entry, paddr_check);
            assert(segment_cover_count(new_segments, paddr_check) == segment_cover_count(
                segments,
                paddr_check,
            ));
        } else {
            // !sid_pre_covers ⟹ !new_covers (new_range ⊆ pre range).
            assert(!new_covers);
            lemma_segment_cover_insert_outside(segments.remove(sid), sid, new_entry, paddr_check);
            assert(segment_cover_count(new_segments, paddr_check) == segment_cover_count(
                segments,
                paddr_check,
            ));
        }
    } else {
        // new range empty; segments is just remove(sid).
        let new_segments = segments.remove(sid);
        if paddr_check == popped {
            assert(sid_pre_covers);
            lemma_segment_cover_contains(segments, sid, paddr_check);
            assert(segment_cover_count(new_segments, paddr_check) + 1 == segment_cover_count(
                segments,
                paddr_check,
            ));
        } else if sid_pre_covers {
            // popped + PAGE_SIZE == range.end (empty new range).
            // paddr_check in [popped, range.end), paddr_check != popped,
            // page-aligned ⟹ paddr_check >= range.end. Contradiction.
            assert(false);
        } else {
            // cover_post == cover_pre.
            assert(segment_cover_count(new_segments, paddr_check) == segment_cover_count(
                segments,
                paddr_check,
            ));
        }
    }
}

/// **Split helper.** Partitioning a segment's range at `mid` and
/// replacing the original `sid` with two fresh entries covering
/// `[start, mid)` and `[mid, end)` leaves `segment_cover_count`
/// invariant at every `paddr`. Any paddr covered by the original is
/// covered by exactly one half; uncovered paddrs stay uncovered.
pub proof fn lemma_segment_cover_split(
    segments: Map<SegmentId, SegmentEntry>,
    sid: SegmentId,
    new_left: SegmentId,
    new_right: SegmentId,
    entry_left: SegmentEntry,
    entry_right: SegmentEntry,
    paddr: Paddr,
)
    requires
        segments.dom().contains(sid),
        // `new_left` and `new_right` are fresh and distinct from each
        // other and from `sid`.
        new_left != sid,
        new_right != sid,
        new_left != new_right,
        !segments.remove(sid).dom().contains(new_left),
        !segments.remove(sid).dom().contains(new_right),
        // The two halves partition `sid`'s range at `mid`.
        entry_left.range.start == segments[sid].range.start,
        entry_left.range.end == entry_right.range.start,
        entry_right.range.end == segments[sid].range.end,
        entry_left.range.start < entry_left.range.end,
        entry_right.range.start < entry_right.range.end,
    ensures
        segment_cover_count(
            segments.remove(sid).insert(new_left, entry_left).insert(new_right, entry_right),
            paddr,
        ) == segment_cover_count(segments, paddr),
{
    let mid_segments = segments.remove(sid);
    let with_left = mid_segments.insert(new_left, entry_left);
    assert(with_left.dom() == mid_segments.dom().insert(new_left));
    assert(!with_left.dom().contains(new_right));
    let sid_covers = segments[sid].range.start <= paddr && paddr < segments[sid].range.end;
    let left_covers = entry_left.range.start <= paddr && paddr < entry_left.range.end;
    let right_covers = entry_right.range.start <= paddr && paddr < entry_right.range.end;
    // Step 1: remove sid.
    let cover_after_remove = segment_cover_count(mid_segments, paddr);
    if sid_covers {
        lemma_segment_cover_remove_inside(segments, sid, paddr);
        assert(cover_after_remove == (segment_cover_count(segments, paddr) - 1) as nat);
    } else {
        lemma_segment_cover_remove_outside(segments, sid, paddr);
        assert(cover_after_remove == segment_cover_count(segments, paddr));
    }
    // Step 2: insert new_left.
    let cover_after_left = segment_cover_count(with_left, paddr);
    if left_covers {
        lemma_segment_cover_insert_inside(mid_segments, new_left, entry_left, paddr);
        assert(cover_after_left == cover_after_remove + 1);
    } else {
        lemma_segment_cover_insert_outside(mid_segments, new_left, entry_left, paddr);
        assert(cover_after_left == cover_after_remove);
    }
    // Step 3: insert new_right.
    let final_segments = with_left.insert(new_right, entry_right);
    let cover_final = segment_cover_count(final_segments, paddr);
    if right_covers {
        lemma_segment_cover_insert_inside(with_left, new_right, entry_right, paddr);
        assert(cover_final == cover_after_left + 1);
    } else {
        lemma_segment_cover_insert_outside(with_left, new_right, entry_right, paddr);
        assert(cover_final == cover_after_left);
    }
    // Combine via partition property.
    let orig = segment_cover_count(segments, paddr);
    if sid_covers {
        // orig >= 1 (sid contributes).
        lemma_segment_cover_contains(segments, sid, paddr);
        assert(orig >= 1);
        assert(cover_after_remove == (orig - 1) as nat);
        assert(cover_after_remove + 1 == orig);
        if left_covers {
            assert(!right_covers);
            assert(cover_after_left == cover_after_remove + 1);
            assert(cover_final == cover_after_left);
            assert(cover_final == orig);
        } else {
            assert(right_covers);
            assert(cover_after_left == cover_after_remove);
            assert(cover_final == cover_after_left + 1);
            assert(cover_final == cover_after_remove + 1);
            assert(cover_final == orig);
        }
    } else {
        assert(!left_covers);
        assert(!right_covers);
        assert(cover_after_remove == orig);
        assert(cover_after_left == cover_after_remove);
        assert(cover_final == cover_after_left);
        assert(cover_final == orig);
    }
}

/// Removing an existing segment whose range does NOT cover `paddr`
/// leaves `segment_cover_count` at `paddr` unchanged.
pub proof fn lemma_segment_cover_remove_outside(
    segments: Map<SegmentId, SegmentEntry>,
    sid: SegmentId,
    paddr: Paddr,
)
    requires
        segments.dom().contains(sid),
        !(segments[sid].range.start <= paddr < segments[sid].range.end),
    ensures
        segment_cover_count(segments.remove(sid), paddr) == segment_cover_count(segments, paddr),
{
    let segments2 = segments.remove(sid);
    let pred = |s: SegmentId| segments[s].range.start <= paddr && paddr < segments[s].range.end;
    let pred2 = |s: SegmentId| segments2[s].range.start <= paddr && paddr < segments2[s].range.end;
    let old_filt = segments.dom().filter(pred);
    let new_filt = segments2.dom().filter(pred2);
    assert(segments2.dom() == segments.dom().remove(sid));
    assert(!old_filt.contains(sid));
    assert(new_filt == old_filt) by {
        assert forall|s: SegmentId| #[trigger] new_filt.contains(s) implies old_filt.contains(
            s,
        ) by {
            assert(s != sid);
            assert(segments2[s] == segments[s]);
        };
        assert forall|s: SegmentId| #[trigger] old_filt.contains(s) implies new_filt.contains(
            s,
        ) by {
            assert(s != sid);
            assert(segments2[s] == segments[s]);
        };
    };
}

// =============================================================================
// Internal helpers: fresh-id picking and tracked entry constructors.
// =============================================================================
/// Picks an id not currently in `m.dom()`. Since the key type is `int`,
/// an unused id always exists.
pub open spec fn fresh_vm_space_id<'a>(m: Map<VmSpaceId, VmSpaceOwner>) -> VmSpaceId {
    choose|id: VmSpaceId| !m.dom().contains(id)
}

/// Picks a cursor id not currently in `m.dom()`.
pub open spec fn fresh_cursor_id<'rcu>(m: Map<CursorId, CursorEntry<'rcu>>) -> CursorId {
    choose|id: CursorId| !m.dom().contains(id)
}

/// Picks a [`VmIoId`] not currently in `m.dom()`.
pub open spec fn fresh_vm_io_id<'a>(m: Map<VmIoId, VmIoEntry>) -> VmIoId {
    choose|id: VmIoId| !m.dom().contains(id)
}

/// Picks a [`FrameId`] not currently in `m.dom()`.
pub open spec fn fresh_frame_id(m: Map<FrameId, FrameEntry>) -> FrameId {
    choose|id: FrameId| !m.dom().contains(id)
}

pub axiom fn axiom_fresh_vm_space_id_not_in_dom<'a>(m: Map<VmSpaceId, VmSpaceOwner>)
    ensures
        !m.dom().contains(fresh_vm_space_id(m)),
;

pub axiom fn axiom_fresh_cursor_id_not_in_dom<'rcu>(m: Map<CursorId, CursorEntry<'rcu>>)
    ensures
        !m.dom().contains(fresh_cursor_id(m)),
;

pub axiom fn axiom_fresh_vm_io_id_not_in_dom<'a>(m: Map<VmIoId, VmIoEntry>)
    ensures
        !m.dom().contains(fresh_vm_io_id(m)),
;

pub axiom fn axiom_fresh_frame_id_not_in_dom(m: Map<FrameId, FrameEntry>)
    ensures
        !m.dom().contains(fresh_frame_id(m)),
;

/// Tracked constructor for [`CursorEntry`].
pub axiom fn axiom_cursor_entry_new<'rcu>(
    vm_space: VmSpaceId,
    kind: CursorKind,
    va: Range<Vaddr>,
    tracked owner: CursorOwner<'rcu, UserPtConfig>,
    tracked guards: Guards<'rcu>,
) -> (tracked res: CursorEntry<'rcu>)
    ensures
        res.vm_space == vm_space,
        res.kind == kind,
        res.va == va,
        res.owner == owner,
        res.guards == guards,
;

/// Tracked constructor for [`VmIoEntry`].
pub axiom fn axiom_vm_io_entry_new<'a>(
    vm_space: Option<VmSpaceId>,
    kind: VmIoKind,
    vaddr: Vaddr,
    len: usize,
    tracked owner: VmIoOwner,
) -> (tracked res: VmIoEntry)
    ensures
        res.vm_space == vm_space,
        res.kind == kind,
        res.vaddr == vaddr,
        res.len == len,
        res.owner == owner,
;

/// Tracked constructor for [`FrameEntry`].
pub axiom fn axiom_frame_entry_new(paddr: Paddr) -> (tracked res: FrameEntry)
    ensures
        res.paddr == paddr,
;

/// Tracked constructor for [`SegmentEntry`].
pub axiom fn axiom_segment_entry_new(range: Range<Paddr>) -> (tracked res: SegmentEntry)
    ensures
        res.range == range,
;

/// Fresh-id helper for the segment id space.
pub open spec fn fresh_segment_id(m: Map<SegmentId, SegmentEntry>) -> SegmentId {
    choose|id: SegmentId| !m.dom().contains(id)
}

pub axiom fn axiom_fresh_segment_id_not_in_dom(m: Map<SegmentId, SegmentEntry>)
    ensures
        !m.dom().contains(fresh_segment_id(m)),
;

} // verus!
