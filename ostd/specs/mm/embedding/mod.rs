//! Deep embedding of the `VmSpace` and `VmReader`/`VmWriter` API.
//!
//! `VmStore` is the abstract state of a caller of these APIs: it holds
//! the [`MetaRegionOwners`] plus a registry of every owner object the
//! caller currently has access to.
//!
//! [`Op`] is an ADT enumerating the public exec API. [`lemma_step`] is the
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
pub mod cursor;
pub mod frame;
pub mod io;
pub mod kvirt_store;
pub mod list_store;
pub mod segment;
pub mod trace;
pub mod unique;
pub mod vm_space;

use core::ops::Range;

use vstd::prelude::*;
use vstd_extra::{ownership::*, set_extra::*};

use crate::specs::{
    arch::*,
    mm::{
        frame::{
            mapping::{frame_to_index, index_to_frame, index_to_meta, max_meta_slots},
            meta_owners::{MetaSlotOwner, PageUsage},
            meta_region_owners::MetaRegionOwners,
        },
        io::VmIoOwner,
        page_table::{cursor::owners::CursorOwner, node::Guards},
        tlb::TlbModel,
    },
};

use crate::mm::{
    MAX_USERSPACE_VADDR, Paddr, Vaddr,
    frame::{
        MetaSlot, UFrame,
        meta::{REF_COUNT_MAX, REF_COUNT_UNIQUE, REF_COUNT_UNUSED},
    },
    page_prop::PageProperty,
    vm_space::{UserPtConfig, vm_space_specs::VmSpaceOwner},
};

verus! {

broadcast use crate::specs::mm::frame::mapping::lemma_index_to_frame_biinjective;
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

/// Logical identifier for a held [`crate::mm::frame::UniqueFrame`]
/// handle in the store.
pub type UniqueId = int;

/// Per-Frame entry in the store. Represents one outstanding handle to
/// the slot at `paddr` — i.e., one unit of refcount in
/// `regions.slot_owner(paddr)`.
///
/// Multiple `FrameEntry`s may share the same `paddr`; each contributes
/// `+1` to that slot's `ref_count`.
pub tracked struct FrameEntry {
    pub ghost paddr: Paddr,
}

/// Per-Segment entry in the store. Represents one outstanding
/// `Segment<M>` covering the contiguous physical range `range`.
///
/// Multiple `SegmentEntry`s may overlap (e.g. after `clone`); each
/// independently contributes `+1` to every covered slot's obligation
/// count and ref_count`.
///
/// [`Segment::relate_regions`]: crate::mm::frame::Segment::relate_regions
pub tracked struct SegmentEntry {
    pub ghost range: Range<Paddr>,
}

/// Per-`UniqueFrame` entry in the store.
pub tracked struct UniqueEntry {
    pub ghost paddr: Paddr,
}

/// Number of outstanding `Segment` handles covering the frame slot
/// at `paddr`.
pub open spec fn segment_cover_count(segments: Map<SegmentId, SegmentEntry>, paddr: Paddr) -> nat {
    segments.dom().filter(
        |sid: SegmentId| segments[sid].range.start <= paddr && paddr < segments[sid].range.end,
    ).len()
}

/// A positive segment-cover count exhibits a witnessing segment id whose
/// range covers `paddr`.
pub proof fn lemma_segment_cover_witness(
    segments: Map<SegmentId, SegmentEntry>,
    paddr: Paddr,
) -> (sid: SegmentId)
    requires
        segment_cover_count(segments, paddr) > 0,
    ensures
        segments.contains_key(sid),
        segments[sid].range.start <= paddr < segments[sid].range.end,
{
    let covering = segments.dom().filter(
        |sid: SegmentId| segments[sid].range.start <= paddr && paddr < segments[sid].range.end,
    );
    let sid = covering.choose();
    assert(covering.contains(sid));
    sid
}

/// Number of outstanding `Frame` handles whose paddr maps to slot
/// `idx`.
pub open spec fn handle_count(frames: Map<FrameId, FrameEntry>, idx: int) -> nat {
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
    idx: int,
)
    requires
        !frames.contains_key(id),
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
pub proof fn lemma_handle_count_remove(frames: Map<FrameId, FrameEntry>, fid: FrameId, idx: int)
    requires
        frames.contains_key(fid),
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

pub proof fn lemma_frame_drop_pre_derivable<'rcu>(s: VmStore<'rcu>, fid: FrameId)
    requires
        s.inv(),
        s.frames.contains_key(fid),
        segment_cover_count(s.segments, s.frames[fid].paddr) == 0,
    ensures
        frame::drop_pre(s.regions, s.frames[fid].paddr),
        s.regions.slot_owner(s.frames[fid].paddr).ref_count() == 1 ==> handle_count(
            s.frames,
            frame_to_index(s.frames[fid].paddr),
        ) == 1,
{
    reveal(VmStore::structural_inv);
    reveal(VmStore::accounting_inv);
    let paddr = s.frames[fid].paddr;
    let idx = frame_to_index(paddr);
    assert(s.regions.ref_count(idx) == s.regions.slot_owners[idx].ref_count_perm.value());

    assert(s.frames.dom().filter(
        |gid: FrameId| frame_to_index(s.frames[gid].paddr) == idx,
    ).contains(fid));
}

/// Whether a [`VmIoOwner`] backs a `VmReader` or a `VmWriter`.
pub enum VmIoKind {
    Reader,
    Writer,
}

/// Per-VmIo entry in the store.
pub tracked struct VmIoEntry {
    pub ghost vm_space: Option<VmSpaceId>,
    pub ghost kind: VmIoKind,
    pub ghost vaddr: Vaddr,
    pub ghost len: usize,
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
pub ghost enum CursorKind {
    ReadOnly,
    Mutable,
}

/// Per-cursor entry in the store.
///
/// `guards` is the lock-protocol state for the page-table nodes the
/// cursor holds locked; mirrors what the exec `Cursor` carries via
/// `path: [Option<PageTableGuard<'rcu, C>>; NR_LEVELS]`.
pub tracked struct CursorEntry<'rcu> {
    pub ghost vm_space: VmSpaceId,
    pub ghost kind: CursorKind,
    pub ghost va: Range<Vaddr>,
    pub owner: CursorOwner<'rcu, UserPtConfig>,
    pub guards: Guards,
}

impl<'rcu> CursorEntry<'rcu> {
    pub open spec fn inv(self) -> bool {
        &&& self.owner.inv()
        &&& self.owner.children_not_locked(self.guards)
        &&& self.owner.nodes_locked(self.guards)
        &&& !self.owner.popped_too_high
    }
}

/// Resource store: the abstract state visible to a caller of the
/// VmSpace + VmReader/VmWriter API.
pub tracked struct VmStore<'rcu> {
    pub regions: MetaRegionOwners,
    pub tlb_model: TlbModel,
    pub vm_spaces: Map<VmSpaceId, VmSpaceOwner>,
    pub cursors: Map<CursorId, CursorEntry<'rcu>>,
    pub vm_ios: Map<VmIoId, VmIoEntry>,
    pub frames: Map<FrameId, FrameEntry>,
    pub segments: Map<SegmentId, SegmentEntry>,
    pub unique_frames: Map<UniqueId, UniqueEntry>,
}

impl<'a, 'rcu> VmStore<'rcu> {
    /// The store's top-level invariant.
    pub open spec fn inv(self) -> bool {
        self.structural_inv() && self.accounting_inv() && self.regions.inv()
    }

    /// Everything in [`inv`] **except** the accounting equation.
    /// Preserved by any helper that touches at most one of `frames` /
    /// `regions.slot_owners`, since the accounting equation is the only
    /// clause that mentions both. Frame-only helpers
    /// ([`tracked_extract_frame`] / [`lemma_insert_frame`]) require / ensure this.
    #[verifier::opaque]
    pub open spec fn structural_inv(self) -> bool {
        &&& forall|idx: int|
            0 <= idx < max_meta_slots() ==> #[trigger] self.regions.slots.contains_key(idx) || (
            self.regions.slot_owners[idx].usage is PageTable && self.regions.ref_count(idx)
                != REF_COUNT_UNUSED)
        &&& forall|idx: int|
            0 <= idx < max_meta_slots()
                ==> #[trigger] self.regions.slot_owners[idx].in_list_perm.value() == 0
        &&& self.tlb_model.inv()
        &&& forall|id: VmSpaceId| #[trigger]
            self.vm_spaces.contains_key(id) ==> self.vm_spaces[id].inv()
        &&& forall|id: CursorId| #[trigger] self.cursors.contains_key(id) ==> self.cursors[id].inv()
        &&& forall|id: CursorId| #[trigger]
            self.cursors.contains_key(id) ==> self.cursors[id].owner.metaregion_sound(self.regions)
        &&& forall|id: CursorId| #[trigger]
            self.cursors.contains_key(id) ==> self.vm_spaces.contains_key(self.cursors[id].vm_space)
        &&& forall|id: VmIoId| #[trigger] self.vm_ios.contains_key(id) ==> self.vm_ios[id].inv()
        &&& forall|id: VmIoId| #[trigger]
            self.vm_ios.contains_key(id) ==> (self.vm_ios[id].vm_space matches Some(vs)
                ==> self.vm_spaces.contains_key(vs))
        &&& forall|id: VmIoId| #[trigger]
            self.vm_ios.contains_key(id) ==> self.vm_ios[id].vm_space is Some ==> (
            self.vm_ios[id].vaddr as nat) + (self.vm_ios[id].len as nat)
                <= MAX_USERSPACE_VADDR as nat
        &&& forall|fid: FrameId| #[trigger]
            self.frames.contains_key(fid) ==> valid_frame_paddr(self.frames[fid].paddr)
        &&& forall|fid: FrameId| #[trigger]
            self.frames.contains_key(fid) ==> self.regions.slot_owner(
                self.frames[fid].paddr,
            ).usage is Frame
        &&& forall|sid: SegmentId| #[trigger]
            self.segments.contains_key(sid) ==> {
                let r = self.segments[sid].range;
                &&& r.start % PAGE_SIZE == 0
                &&& r.end % PAGE_SIZE == 0
                &&& r.start < r.end
                &&& r.end <= MAX_PADDR
            }
        &&& forall|sid: SegmentId, paddr: Paddr|
            #![trigger
                    self.segments.contains_key(sid),
                    frame_to_index(paddr)]
            self.segments.contains_key(sid) && self.segments[sid].range.start <= paddr
                < self.segments[sid].range.end && paddr % PAGE_SIZE == 0
                ==> self.regions.slot_owner(paddr).usage is Frame
        &&& forall|uid: UniqueId| #[trigger]
            self.unique_frames.contains_key(uid) ==> valid_frame_paddr(
                self.unique_frames[uid].paddr,
            )
        &&& forall|uid: UniqueId| #[trigger]
            self.unique_frames.contains_key(uid) ==> {
                let so = self.regions.slot_owner(self.unique_frames[uid].paddr);
                &&& so.usage is Frame
                &&& so.ref_count() == REF_COUNT_UNIQUE
                &&& so.in_list_perm.value() == 0
                &&& so.paths_in_pt.is_empty()
            }
        &&& forall|uid1: UniqueId, uid2: UniqueId|
            #![trigger
                self.unique_frames.contains_key(uid1),
                self.unique_frames.contains_key(uid2)]
            self.unique_frames.contains_key(uid1) && self.unique_frames.contains_key(uid2)
                && self.unique_frames[uid1].paddr == self.unique_frames[uid2].paddr ==> uid1 == uid2
    }

    #[verifier::opaque]
    pub open spec fn accounting_inv(self) -> bool {
        &&& forall|idx: int|
            #![trigger self.regions.slot_owners[idx]]
            0 <= idx < max_meta_slots() && self.regions.ref_count(idx) == REF_COUNT_UNUSED
                ==> handle_count(self.frames, idx) == 0
                && self.regions.slot_owners[idx].paths_in_pt.is_empty() && segment_cover_count(
                self.segments,
                index_to_frame(idx),
            ) == 0
        &&& forall|idx: int|
            #![trigger self.regions.slot_owners[idx]]
            0 <= idx < max_meta_slots() && self.regions.slot_owners[idx].usage is Frame
                && self.regions.ref_count(idx) != REF_COUNT_UNUSED && self.regions.ref_count(idx)
                != REF_COUNT_UNIQUE ==> handle_count(self.frames, idx) > 0
                || self.regions.slot_owners[idx].paths_in_pt.len() > 0 || segment_cover_count(
                self.segments,
                index_to_frame(idx),
            ) > 0
        &&& forall|idx: int|
            #![trigger self.regions.slot_owners[idx]]
            0 <= idx < max_meta_slots() && self.regions.slot_owners[idx].usage is Frame && (
            handle_count(self.frames, idx) > 0 || self.regions.slot_owners[idx].paths_in_pt.len()
                > 0 || segment_cover_count(self.segments, index_to_frame(idx)) > 0) ==> {
                let so = self.regions.slot_owners[idx];
                let rc = so.ref_count();
                &&& rc != REF_COUNT_UNUSED
                &&& rc != REF_COUNT_UNIQUE
                &&& rc == handle_count(self.frames, idx) + so.paths_in_pt.len()
                    + segment_cover_count(self.segments, index_to_frame(idx))
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
    /// Fallible `VmReader::read_val<T>`.
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
    /// Infallible `VmWriter::write`.
    Write { source: VmIoId, dest: VmIoId },
    /// `Frame::from_unused`: try to allocate a fresh handle on a
    /// previously-unused slot.
    FrameFromUnused { paddr: Paddr },
    /// `Frame::from_in_use`: try to acquire a new handle on an
    /// in-use slot.
    FrameFromInUse { paddr: Paddr },
    /// Drop one outstanding `Frame` handle.
    FrameDrop { fid: FrameId },
    /// `Segment::from_unused`: allocate a fresh segment over a range
    /// of previously-unused slots.
    SegmentFromUnused { range: Range<Paddr> },
    /// Drop a `Segment` handle.
    SegmentDrop { sid: SegmentId },
    /// `Segment::split`: split a segment at a page-aligned byte
    /// `offset` from its start, producing two segments covering the
    /// disjoint halves.
    SegmentSplit { sid: SegmentId, offset: usize },
    /// `Segment::next`: pop the front frame off `sid`'s range,
    /// producing a fresh `Frame<M>` handle.
    SegmentNext { sid: SegmentId },
    /// `Segment::clone`: produce a second handle covering the *same*
    /// range as `sid`.
    SegmentClone { sid: SegmentId },
    /// `Segment::slice`: produce a handle covering the sub-range
    /// `sub_range`.
    SegmentSlice { sid: SegmentId, sub_range: Range<Paddr> },
    /// `UniqueFrame::from_unused`: allocate a fresh *exclusive* handle on
    /// a previously-unused slot.
    UniqueFromUnused { paddr: Paddr },
    /// Drop a `UniqueFrame` handle.
    UniqueDrop { uid: UniqueId },
    /// `Frame::from_unique`: convert the exclusive handle `uid` into a
    /// shared `Frame`.
    FromUnique { uid: UniqueId },
    /// `UniqueFrame::try_from_shared`: try to convert the shared handle
    /// `fid` back into an exclusive one.
    TryFromShared { fid: FrameId },
}

/// Per-op precondition — the conjunction of facts about the store that
/// must hold for an `Op` to be applied.
///
/// [`lemma_step`] requires `op_pre(*old(s), op)`. Callers must establish the
/// precondition for the specific Op variant they're about to apply.
///
/// SOUNDNESS: when we're done building this model, `op_pre` must be
/// permissive enough to permit every possible call trace. That means
/// that these conditions should reduce to
/// "the relevant objects exist in the store".
pub open spec fn op_pre<'rcu>(s: VmStore<'rcu>, op: Op) -> bool {
    match op {
        Op::NewVmSpace => true,
        Op::DropVmSpace { vs } => s.vm_spaces.contains_key(vs) && (forall|c: CursorId| #[trigger]
            s.cursors.contains_key(c) ==> s.cursors[c].vm_space != vs) && (forall|v: VmIoId|
         #[trigger]
            s.vm_ios.contains_key(v) ==> s.vm_ios[v].vm_space != Some(vs)),
        Op::OpenCursor { vs, va: _ } => s.vm_spaces.contains_key(vs),
        Op::OpenCursorMut { vs, va: _ } => s.vm_spaces.contains_key(vs),
        Op::DropCursor { c } => s.cursors.contains_key(c),
        Op::Query { c } => s.cursors.contains_key(c),
        Op::FindNext { c, len: _ } => s.cursors.contains_key(c),
        Op::Jump { c, va: _ } => s.cursors.contains_key(c),
        Op::VirtAddr { c } => s.cursors.contains_key(c),
        Op::Map { c, fid, prop: _ } => s.cursors.contains_key(c) && s.frames.contains_key(fid),
        Op::Unmap { c, len: _ } => s.cursors.contains_key(c),
        Op::ProtectNext { c, len: _ } => s.cursors.contains_key(c),
        Op::NewReader { vs, vaddr: _, len: _ } => s.vm_spaces.contains_key(vs),
        Op::NewWriter { vs, vaddr: _, len: _ } => s.vm_spaces.contains_key(vs),
        Op::NewKernelReader { vaddr: _, len: _ } => true,
        Op::NewKernelWriter { vaddr: _, len: _ } => true,
        Op::DropReader { vio } => s.vm_ios.contains_key(vio),
        Op::DropWriter { vio } => s.vm_ios.contains_key(vio),
        Op::ReaderReadVal { source } => s.vm_ios.contains_key(source),
        Op::ReaderCollect { source } => s.vm_ios.contains_key(source),
        Op::ReaderLimit { vio, max: _ } => s.vm_ios.contains_key(vio),
        Op::ReaderSkip { vio, n: _ } => s.vm_ios.contains_key(vio),
        Op::ReaderQuery { vio } => s.vm_ios.contains_key(vio),
        Op::WriterWriteVal { writer } => s.vm_ios.contains_key(writer),
        Op::WriterFillZeros { vio, len: _ } => s.vm_ios.contains_key(vio),
        Op::WriterLimit { vio, max: _ } => s.vm_ios.contains_key(vio),
        Op::WriterSkip { vio, n: _ } => s.vm_ios.contains_key(vio),
        Op::WriterQuery { vio } => s.vm_ios.contains_key(vio),
        Op::Read { source, dest } => s.vm_ios.contains_key(source) && s.vm_ios.contains_key(dest)
            && source != dest && s.vm_ios[source].is_kernel_reader()
            && s.vm_ios[dest].is_kernel_writer(),
        Op::Write { source, dest } => s.vm_ios.contains_key(source) && s.vm_ios.contains_key(dest)
            && source != dest && s.vm_ios[source].is_kernel_reader()
            && s.vm_ios[dest].is_kernel_writer(),
        Op::FrameFromUnused { paddr: _ } => true,
        Op::FrameFromInUse { paddr: _ } => true,
        Op::FrameDrop { fid } => s.frames.contains_key(fid) && segment_cover_count(
            s.segments,
            s.frames[fid].paddr,
        ) == 0,
        Op::SegmentFromUnused { range: _ } => true,
        Op::SegmentDrop { sid } => s.segments.contains_key(sid),
        Op::SegmentSplit { sid, offset } => s.segments.contains_key(sid) && offset % PAGE_SIZE == 0
            && 0 < offset && offset < (s.segments[sid].range.end - s.segments[sid].range.start),
        Op::SegmentNext { sid } => s.segments.contains_key(sid),
        Op::SegmentClone { sid } => s.segments.contains_key(sid) && forall|paddr: Paddr|
            #![trigger frame_to_index(paddr)]
            (s.segments[sid].range.start <= paddr < s.segments[sid].range.end && paddr % PAGE_SIZE
                == 0) ==> s.regions.slot_owner(paddr).ref_count() + 1 <= REF_COUNT_MAX,
        Op::SegmentSlice { sid, sub_range } => s.segments.contains_key(sid) && sub_range.start
            % PAGE_SIZE == 0 && sub_range.end % PAGE_SIZE == 0 && s.segments[sid].range.start
            <= sub_range.start && sub_range.start < sub_range.end && sub_range.end
            <= s.segments[sid].range.end && forall|paddr: Paddr|
            #![trigger frame_to_index(paddr)]
            (sub_range.start <= paddr < sub_range.end && paddr % PAGE_SIZE == 0)
                ==> s.regions.slot_owner(paddr).ref_count() + 1 <= REF_COUNT_MAX,
        Op::UniqueFromUnused { paddr: _ } => true,
        Op::UniqueDrop { uid } => s.unique_frames.contains_key(uid),
        Op::FromUnique { uid } => s.unique_frames.contains_key(uid),
        Op::TryFromShared { fid } => s.frames.contains_key(fid),
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
    pub proof fn tracked_extract_vm_space(tracked &mut self, vs: VmSpaceId) -> (tracked res:
        VmSpaceOwner)
        requires
            old(self).inv(),
            old(self).vm_spaces.contains_key(vs),
            forall|c: CursorId| #[trigger]
                old(self).cursors.contains_key(c) ==> old(self).cursors[c].vm_space != vs,
            forall|v: VmIoId| #[trigger]
                old(self).vm_ios.contains_key(v) ==> old(self).vm_ios[v].vm_space != Some(vs),
        ensures
            final(self).regions == old(self).regions,
            final(self).tlb_model == old(self).tlb_model,
            final(self).vm_spaces == old(self).vm_spaces.remove(vs),
            final(self).cursors == old(self).cursors,
            final(self).vm_ios == old(self).vm_ios,
            final(self).frames == old(self).frames,
            final(self).segments == old(self).segments,
            final(self).unique_frames == old(self).unique_frames,
            res == old(self).vm_spaces[vs],
            final(self).inv(),
    {
        reveal(VmStore::structural_inv);
        reveal(VmStore::accounting_inv);
        self.vm_spaces.tracked_remove(vs)
    }

    /// Inserts a VmSpaceOwner at the given fresh id. Requires the id is
    /// not already used and the owner satisfies its invariant.
    pub proof fn lemma_insert_vm_space(
        tracked &mut self,
        vs: VmSpaceId,
        tracked owner: VmSpaceOwner,
    )
        requires
            old(self).inv(),
            !old(self).vm_spaces.contains_key(vs),
            owner.inv(),
        ensures
            final(self).regions == old(self).regions,
            final(self).tlb_model == old(self).tlb_model,
            final(self).vm_spaces == old(self).vm_spaces.insert(vs, owner),
            final(self).cursors == old(self).cursors,
            final(self).vm_ios == old(self).vm_ios,
            final(self).frames == old(self).frames,
            final(self).segments == old(self).segments,
            final(self).unique_frames == old(self).unique_frames,
            final(self).inv(),
    {
        reveal(VmStore::structural_inv);
        reveal(VmStore::accounting_inv);
        self.vm_spaces.tracked_insert(vs, owner);
    }

    /// Removes the cursor entry at `c` from the store and returns it.
    pub proof fn tracked_extract_cursor(tracked &mut self, c: CursorId) -> (tracked res:
        CursorEntry<'rcu>)
        requires
            old(self).inv(),
            old(self).cursors.contains_key(c),
        ensures
            final(self).regions == old(self).regions,
            final(self).tlb_model == old(self).tlb_model,
            final(self).vm_spaces == old(self).vm_spaces,
            final(self).cursors == old(self).cursors.remove(c),
            final(self).vm_ios == old(self).vm_ios,
            final(self).frames == old(self).frames,
            final(self).segments == old(self).segments,
            final(self).unique_frames == old(self).unique_frames,
            res == old(self).cursors[c],
            final(self).inv(),
    {
        reveal(VmStore::structural_inv);
        reveal(VmStore::accounting_inv);
        self.cursors.tracked_remove(c)
    }

    /// Inserts a cursor entry at the given fresh id. Requires the id is
    /// not already used, the entry satisfies its inv, the entry's
    /// `vm_space` is in the store, and the entry's owner is sound w.r.t.
    /// the store's regions.
    pub proof fn lemma_insert_cursor(
        tracked &mut self,
        c: CursorId,
        tracked entry: CursorEntry<'rcu>,
    )
        requires
            old(self).inv(),
            !old(self).cursors.contains_key(c),
            entry.inv(),
            entry.owner.metaregion_sound(old(self).regions),
            old(self).vm_spaces.contains_key(entry.vm_space),
        ensures
            final(self).regions == old(self).regions,
            final(self).tlb_model == old(self).tlb_model,
            final(self).vm_spaces == old(self).vm_spaces,
            final(self).cursors == old(self).cursors.insert(c, entry),
            final(self).vm_ios == old(self).vm_ios,
            final(self).frames == old(self).frames,
            final(self).segments == old(self).segments,
            final(self).unique_frames == old(self).unique_frames,
            final(self).inv(),
    {
        reveal(VmStore::structural_inv);
        reveal(VmStore::accounting_inv);
        self.cursors.tracked_insert(c, entry);
    }

    /// Removes the VmIo entry at `vio` from the store and returns it.
    pub proof fn tracked_extract_vm_io(tracked &mut self, vio: VmIoId) -> (tracked res: VmIoEntry)
        requires
            old(self).inv(),
            old(self).vm_ios.contains_key(vio),
        ensures
            final(self).regions == old(self).regions,
            final(self).tlb_model == old(self).tlb_model,
            final(self).vm_spaces == old(self).vm_spaces,
            final(self).cursors == old(self).cursors,
            final(self).vm_ios == old(self).vm_ios.remove(vio),
            final(self).frames == old(self).frames,
            final(self).segments == old(self).segments,
            final(self).unique_frames == old(self).unique_frames,
            res == old(self).vm_ios[vio],
            final(self).inv(),
    {
        reveal(VmStore::structural_inv);
        reveal(VmStore::accounting_inv);
        self.vm_ios.tracked_remove(vio)
    }

    /// Inserts a VmIo entry at the given fresh id.
    pub proof fn lemma_insert_vm_io(tracked &mut self, vio: VmIoId, tracked entry: VmIoEntry)
        requires
            old(self).inv(),
            !old(self).vm_ios.contains_key(vio),
            entry.inv(),
            entry.vm_space matches Some(vs) ==> old(self).vm_spaces.contains_key(vs),
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
            final(self).unique_frames == old(self).unique_frames,
            final(self).inv(),
    {
        reveal(VmStore::structural_inv);
        reveal(VmStore::accounting_inv);
        self.vm_ios.tracked_insert(vio, entry);
    }

    /// Removes the FrameEntry at `fid` from the store.
    pub proof fn tracked_extract_frame(tracked &mut self, fid: FrameId) -> (tracked res: FrameEntry)
        requires
            old(self).structural_inv(),
            old(self).frames.contains_key(fid),
        ensures
            final(self).regions == old(self).regions,
            final(self).tlb_model == old(self).tlb_model,
            final(self).vm_spaces == old(self).vm_spaces,
            final(self).cursors == old(self).cursors,
            final(self).vm_ios == old(self).vm_ios,
            final(self).frames == old(self).frames.remove(fid),
            final(self).segments == old(self).segments,
            final(self).unique_frames == old(self).unique_frames,
            res == old(self).frames[fid],
            final(self).structural_inv(),
    {
        reveal(VmStore::structural_inv);
        self.frames.tracked_remove(fid)
    }

    /// Inserts a FrameEntry at the given fresh id.
    pub proof fn lemma_insert_frame(tracked &mut self, fid: FrameId, tracked entry: FrameEntry)
        requires
            old(self).structural_inv(),
            !old(self).frames.contains_key(fid),
            valid_frame_paddr(entry.paddr),
            old(self).regions.slot_owner(entry.paddr).usage is Frame,
        ensures
            final(self).regions == old(self).regions,
            final(self).tlb_model == old(self).tlb_model,
            final(self).vm_spaces == old(self).vm_spaces,
            final(self).cursors == old(self).cursors,
            final(self).vm_ios == old(self).vm_ios,
            final(self).frames == old(self).frames.insert(fid, entry),
            final(self).segments == old(self).segments,
            final(self).unique_frames == old(self).unique_frames,
            final(self).structural_inv(),
    {
        reveal(VmStore::structural_inv);
        self.frames.tracked_insert(fid, entry);
    }

    /// Removes the UniqueEntry at `uid` from the store.
    pub proof fn tracked_extract_unique(tracked &mut self, uid: UniqueId) -> (tracked res:
        UniqueEntry)
        requires
            old(self).unique_frames.contains_key(uid),
        ensures
            final(self).regions == old(self).regions,
            final(self).tlb_model == old(self).tlb_model,
            final(self).vm_spaces == old(self).vm_spaces,
            final(self).cursors == old(self).cursors,
            final(self).vm_ios == old(self).vm_ios,
            final(self).frames == old(self).frames,
            final(self).segments == old(self).segments,
            final(self).unique_frames == old(self).unique_frames.remove(uid),
            res == old(self).unique_frames[uid],
    {
        self.unique_frames.tracked_remove(uid)
    }

    /// Inserts a UniqueEntry at a fresh id.
    pub proof fn lemma_insert_unique(tracked &mut self, uid: UniqueId, tracked entry: UniqueEntry)
        requires
            !old(self).unique_frames.contains_key(uid),
        ensures
            final(self).regions == old(self).regions,
            final(self).tlb_model == old(self).tlb_model,
            final(self).vm_spaces == old(self).vm_spaces,
            final(self).cursors == old(self).cursors,
            final(self).vm_ios == old(self).vm_ios,
            final(self).frames == old(self).frames,
            final(self).segments == old(self).segments,
            final(self).unique_frames == old(self).unique_frames.insert(uid, entry),
    {
        self.unique_frames.tracked_insert(uid, entry);
    }

    /// Removes the SegmentEntry at `sid` from the store.
    pub proof fn tracked_extract_segment(tracked &mut self, sid: SegmentId) -> (tracked res:
        SegmentEntry)
        requires
            old(self).segments.contains_key(sid),
        ensures
            final(self).regions == old(self).regions,
            final(self).tlb_model == old(self).tlb_model,
            final(self).vm_spaces == old(self).vm_spaces,
            final(self).cursors == old(self).cursors,
            final(self).vm_ios == old(self).vm_ios,
            final(self).frames == old(self).frames,
            final(self).segments == old(self).segments.remove(sid),
            final(self).unique_frames == old(self).unique_frames,
            res == old(self).segments[sid],
    {
        self.segments.tracked_remove(sid)
    }

    /// Inserts a SegmentEntry at a fresh id.
    pub proof fn lemma_insert_segment(
        tracked &mut self,
        sid: SegmentId,
        tracked entry: SegmentEntry,
    )
        requires
            !old(self).segments.contains_key(sid),
        ensures
            final(self).regions == old(self).regions,
            final(self).tlb_model == old(self).tlb_model,
            final(self).vm_spaces == old(self).vm_spaces,
            final(self).cursors == old(self).cursors,
            final(self).vm_ios == old(self).vm_ios,
            final(self).frames == old(self).frames,
            final(self).segments == old(self).segments.insert(sid, entry),
            final(self).unique_frames == old(self).unique_frames,
    {
        self.segments.tracked_insert(sid, entry);
    }
}

// Narrow elimination lemmas keep opaque store invariants out of large step contexts.
proof fn lemma_structural_inv_cursor_frame<'rcu>(s: VmStore<'rcu>, c: CursorId, fid: FrameId)
    requires
        s.structural_inv(),
        s.cursors.contains_key(c),
        s.frames.contains_key(fid),
    ensures
        s.tlb_model.inv(),
        s.cursors[c].inv(),
        s.cursors[c].owner.metaregion_sound(s.regions),
        s.vm_spaces.contains_key(s.cursors[c].vm_space),
        valid_frame_paddr(s.frames[fid].paddr),
        s.regions.slot_owner(s.frames[fid].paddr).usage is Frame,
{
    reveal(VmStore::structural_inv);
}

proof fn lemma_structural_inv_frame<'rcu>(s: VmStore<'rcu>, fid: FrameId)
    requires
        s.structural_inv(),
        s.frames.contains_key(fid),
    ensures
        valid_frame_paddr(s.frames[fid].paddr),
        s.regions.slot_owner(s.frames[fid].paddr).usage is Frame,
{
    reveal(VmStore::structural_inv);
}

proof fn lemma_structural_inv_segment<'rcu>(s: VmStore<'rcu>, sid: SegmentId, paddr: Paddr)
    requires
        s.structural_inv(),
        s.segments.contains_key(sid),
        s.segments[sid].range.start <= paddr < s.segments[sid].range.end,
        paddr % PAGE_SIZE == 0,
    ensures
        valid_frame_paddr(paddr),
        s.regions.slot_owner(paddr).usage is Frame,
{
    reveal(VmStore::structural_inv);
}

proof fn lemma_accounting_inv_at<'rcu>(s: VmStore<'rcu>, idx: int)
    requires
        s.accounting_inv(),
        0 <= idx < max_meta_slots(),
    ensures
        s.regions.ref_count(idx) == REF_COUNT_UNUSED ==> handle_count(s.frames, idx) == 0
            && s.regions.slot_owners[idx].paths_in_pt.is_empty() && segment_cover_count(
            s.segments,
            index_to_frame(idx),
        ) == 0,
        s.regions.slot_owners[idx].usage is Frame && s.regions.ref_count(idx) != REF_COUNT_UNUSED
            && s.regions.ref_count(idx) != REF_COUNT_UNIQUE ==> handle_count(s.frames, idx) > 0
            || s.regions.slot_owners[idx].paths_in_pt.len() > 0 || segment_cover_count(
            s.segments,
            index_to_frame(idx),
        ) > 0,
        s.regions.slot_owners[idx].usage is Frame && (handle_count(s.frames, idx) > 0
            || s.regions.slot_owners[idx].paths_in_pt.len() > 0 || segment_cover_count(
            s.segments,
            index_to_frame(idx),
        ) > 0) ==> {
            let so = s.regions.slot_owners[idx];
            let rc = so.ref_count();
            &&& rc != REF_COUNT_UNUSED
            &&& rc != REF_COUNT_UNIQUE
            &&& rc == handle_count(s.frames, idx) + so.paths_in_pt.len() + segment_cover_count(
                s.segments,
                index_to_frame(idx),
            )
        },
{
    reveal(VmStore::accounting_inv);
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
pub proof fn lemma_step<'rcu>(tracked s: &mut VmStore<'rcu>, op: Op)
    requires
        old(s).inv(),
        op_pre(*old(s), op),
    ensures
        final(s).inv(),
{
    match op {
        Op::NewVmSpace => lemma_step_new_vm_space(s),
        Op::DropVmSpace { vs } => lemma_step_drop_vm_space(s, vs),
        Op::OpenCursor { vs, va } => lemma_step_open_cursor(s, vs, va),
        Op::OpenCursorMut { vs, va } => lemma_step_open_cursor_mut(s, vs, va),
        Op::DropCursor { c } => lemma_step_drop_cursor(s, c),
        Op::Query { c } => lemma_step_query(s, c),
        Op::FindNext { c, len } => lemma_step_find_next(s, c, len),
        Op::Jump { c, va } => lemma_step_jump(s, c, va),
        Op::VirtAddr { c: _ } => {},
        Op::Map { c, fid, prop } => lemma_step_map(s, c, fid, prop),
        Op::Unmap { c, len } => lemma_step_unmap(s, c, len),
        Op::ProtectNext { c, len } => lemma_step_protect_next(s, c, len),
        Op::NewReader { vs, vaddr, len } => lemma_step_new_vm_io(
            s,
            vs,
            vaddr,
            len,
            VmIoKind::Reader,
        ),
        Op::NewWriter { vs, vaddr, len } => lemma_step_new_vm_io(
            s,
            vs,
            vaddr,
            len,
            VmIoKind::Writer,
        ),
        Op::NewKernelReader { vaddr, len } => lemma_step_new_kernel_vm_io(
            s,
            vaddr,
            len,
            VmIoKind::Reader,
        ),
        Op::NewKernelWriter { vaddr, len } => lemma_step_new_kernel_vm_io(
            s,
            vaddr,
            len,
            VmIoKind::Writer,
        ),
        Op::DropReader { vio } => lemma_step_drop_vm_io(s, vio),
        Op::DropWriter { vio } => lemma_step_drop_vm_io(s, vio),
        // Fallible variants: handle-only, no embedding state changes.
        Op::ReaderReadVal { source: _ } => {},
        Op::ReaderCollect { source: _ } => {},
        Op::WriterWriteVal { writer: _ } => {},
        Op::ReaderLimit { vio, max } => lemma_step_vm_io_method(
            s,
            vio,
            io::VmIoMethod::ReaderLimit(max),
        ),
        Op::ReaderSkip { vio, n } => lemma_step_vm_io_method(s, vio, io::VmIoMethod::ReaderSkip(n)),
        Op::ReaderQuery { vio: _ } => {},
        Op::WriterFillZeros { vio, len } => lemma_step_vm_io_method(
            s,
            vio,
            io::VmIoMethod::WriterFillZeros(len),
        ),
        Op::WriterLimit { vio, max } => lemma_step_vm_io_method(
            s,
            vio,
            io::VmIoMethod::WriterLimit(max),
        ),
        Op::WriterSkip { vio, n } => lemma_step_vm_io_method(s, vio, io::VmIoMethod::WriterSkip(n)),
        Op::WriterQuery { vio: _ } => {},
        // Infallible `read`: produces a fresh activated-Writer val_owner.
        Op::Read { source, dest } => lemma_step_read(s, source, dest),
        // Infallible `write`: no longer surfaces consumed_w; just
        // mutates source/dest owners.
        Op::Write { source, dest } => lemma_step_write(s, source, dest),
        Op::FrameFromUnused { paddr } => lemma_step_frame_from_unused(s, paddr),
        Op::FrameFromInUse { paddr } => lemma_step_frame_from_in_use(s, paddr),
        Op::FrameDrop { fid } => lemma_step_frame_drop(s, fid),
        Op::SegmentFromUnused { range } => lemma_step_segment_from_unused(s, range),
        Op::SegmentDrop { sid } => lemma_step_segment_drop(s, sid),
        Op::SegmentSplit { sid, offset } => lemma_step_segment_split(s, sid, offset),
        Op::SegmentNext { sid } => lemma_step_segment_next(s, sid),
        Op::SegmentClone { sid } => lemma_step_segment_clone(s, sid),
        Op::SegmentSlice { sid, sub_range } => lemma_step_segment_slice(s, sid, sub_range),
        Op::UniqueFromUnused { paddr } => lemma_step_unique_from_unused(s, paddr),
        Op::UniqueDrop { uid } => lemma_step_unique_drop(s, uid),
        Op::FromUnique { uid } => lemma_step_from_unique(s, uid),
        Op::TryFromShared { fid } => lemma_step_try_from_shared(s, fid),
    }
}

proof fn lemma_accounting_preserved_by_pt_alloc<'rcu>(s_old: VmStore<'rcu>, s_new: VmStore<'rcu>)
    requires
        s_old.inv(),
        s_new.frames == s_old.frames,
        // Segments unchanged ⟹ `segment_cover_count` unchanged.
        s_new.segments == s_old.segments,
        forall|i: int|
            #![trigger s_new.regions.slot_owners[i]]
            s_new.regions.slot_owners[i] != s_old.regions.slot_owners[i] ==> {
                &&& s_old.regions.ref_count(i) == REF_COUNT_UNUSED
                &&& s_new.regions.ref_count(i) != REF_COUNT_UNUSED
                &&& s_new.regions.slot_owners[i].usage !is Frame
            },
    ensures
        s_new.accounting_inv(),
        forall|fid: FrameId| #[trigger]
            s_new.frames.contains_key(fid) ==> s_new.regions.slot_owner(
                s_new.frames[fid].paddr,
            ).usage is Frame,
        forall|sid: SegmentId, paddr: Paddr|
            #![trigger
                s_new.segments.contains_key(sid),
                frame_to_index(paddr)]
            s_new.segments.contains_key(sid) && s_new.segments[sid].range.start <= paddr
                < s_new.segments[sid].range.end && paddr % PAGE_SIZE == 0
                ==> s_new.regions.slot_owner(paddr).usage is Frame,
{
    reveal(VmStore::structural_inv);
    reveal(VmStore::accounting_inv);
    assert forall|idx: int|
        #![trigger s_new.regions.slot_owners[idx]]
        0 <= idx < max_meta_slots() && s_new.regions.ref_count(idx)
            == REF_COUNT_UNUSED implies handle_count(s_new.frames, idx) == 0
        && s_new.regions.slot_owners[idx].paths_in_pt.is_empty() && segment_cover_count(
        s_new.segments,
        index_to_frame(idx),
    ) == 0 by {
        assert(s_new.regions.slot_owners[idx] == s_old.regions.slot_owners[idx]);
    };
    assert forall|idx: int|
        #![trigger s_new.regions.slot_owners[idx]]
        0 <= idx < max_meta_slots() && s_new.regions.slot_owners[idx].usage is Frame
            && s_new.regions.ref_count(idx) != REF_COUNT_UNUSED && s_new.regions.ref_count(idx)
            != REF_COUNT_UNIQUE implies handle_count(s_new.frames, idx) > 0
        || s_new.regions.slot_owners[idx].paths_in_pt.len() > 0 || segment_cover_count(
        s_new.segments,
        index_to_frame(idx),
    ) > 0 by {
        assert(s_new.regions.slot_owners[idx] == s_old.regions.slot_owners[idx]);
    };
    assert forall|idx: int|
        #![trigger s_new.regions.slot_owners[idx]]
        0 <= idx < max_meta_slots() && s_new.regions.slot_owners[idx].usage is Frame && (
        handle_count(s_new.frames, idx) > 0 || s_new.regions.slot_owners[idx].paths_in_pt.len() > 0
            || segment_cover_count(s_new.segments, index_to_frame(idx)) > 0) implies {
        let so = s_new.regions.slot_owners[idx];
        let rc = so.ref_count();
        &&& rc != REF_COUNT_UNUSED
        &&& rc != REF_COUNT_UNIQUE
        &&& rc == handle_count(s_new.frames, idx) + so.paths_in_pt.len() + segment_cover_count(
            s_new.segments,
            index_to_frame(idx),
        )
    } by {
        assert(s_new.regions.slot_owners[idx] == s_old.regions.slot_owners[idx]);
    };
    assert forall|sid: SegmentId, paddr: Paddr|
        #![trigger
            s_new.segments.contains_key(sid),
            frame_to_index(paddr)]
        s_new.segments.contains_key(sid) && s_new.segments[sid].range.start <= paddr
            < s_new.segments[sid].range.end && paddr % PAGE_SIZE
            == 0 implies s_new.regions.slot_owner(paddr).usage is Frame by {
        let idx = frame_to_index(paddr);
        assert(s_old.regions.slot_owners[idx].usage is Frame);
        lemma_segment_cover_contains(s_old.segments, sid, paddr);
        assert(s_old.regions.ref_count(idx) != REF_COUNT_UNUSED);
        assert(s_new.regions.slot_owners[idx] == s_old.regions.slot_owners[idx]);
    };
    assert forall|fid: FrameId| #[trigger]
        s_new.frames.contains_key(fid) implies s_new.regions.slot_owner(
        s_new.frames[fid].paddr,
    ).usage is Frame by {
        let idx = frame_to_index(s_new.frames[fid].paddr);
        assert(s_old.frames.dom().filter(
            |gid: FrameId| frame_to_index(s_old.frames[gid].paddr) == idx,
        ).contains(fid));
        assert(handle_count(s_old.frames, idx) >= 1);
        assert(s_old.regions.slot_owners[idx].usage is Frame);
        assert(s_old.regions.ref_count(idx) != REF_COUNT_UNUSED);
        assert(s_new.regions.slot_owners[idx] == s_old.regions.slot_owners[idx]);
    };
}

/// Re-establish `structural_inv`'s slot-perm coverage exception for an op
/// that preserves the `slots` map (`slots == old slots`) and leaves every
/// UNPARKED slot's `slot_owner` untouched.
proof fn lemma_coverage_preserved_slots_eq<'rcu>(s_old: VmStore<'rcu>, s_new: VmStore<'rcu>)
    requires
        s_old.structural_inv(),
        s_new.regions.slots == s_old.regions.slots,
        forall|idx: int|
            #![trigger s_new.regions.slot_owners[idx]]
            !s_old.regions.slots.contains_key(idx) ==> s_new.regions.slot_owners[idx]
                == s_old.regions.slot_owners[idx],
    ensures
        forall|idx: int|
            0 <= idx < max_meta_slots() ==> #[trigger] s_new.regions.slots.contains_key(idx) || (
            s_new.regions.slot_owners[idx].usage is PageTable && s_new.regions.ref_count(idx)
                != REF_COUNT_UNUSED),
{
    reveal(VmStore::structural_inv);
    assert forall|idx: int|
        0 <= idx < max_meta_slots() implies #[trigger] s_new.regions.slots.contains_key(idx) || (
    s_new.regions.slot_owners[idx].usage is PageTable && s_new.regions.ref_count(idx)
        != REF_COUNT_UNUSED) by {
        if !s_new.regions.slots.contains_key(idx) {
            assert(!s_old.regions.slots.contains_key(idx));
            assert(s_new.regions.slot_owners[idx] == s_old.regions.slot_owners[idx]);
        }
    };
}

proof fn lemma_step_new_vm_space<'rcu>(tracked s: &mut VmStore<'rcu>)
    requires
        old(s).inv(),
    ensures
        final(s).inv(),
{
    reveal(VmStore::structural_inv);
    let ghost s_before = *s;
    let tracked owner = vm_space::new_vm_space_step(&mut s.regions);
    let ghost id = fresh_vm_space_id(s.vm_spaces);
    lemma_fresh_vm_space_id_not_in_dom(s.vm_spaces);
    lemma_accounting_preserved_by_pt_alloc(s_before, *s);
    let ghost root_idx = vm_space::vm_space_root_idx(owner);
    assert forall|idx: int|
        0 <= idx < max_meta_slots() implies #[trigger] s.regions.slots.contains_key(idx) || (
    s.regions.slot_owners[idx].usage is PageTable && s.regions.ref_count(idx)
        != REF_COUNT_UNUSED) by {
        if idx == root_idx {
        } else {
            assert(s.regions.slots.contains_key(idx) == s_before.regions.slots.contains_key(idx));
            if s.regions.slot_owners[idx] != s_before.regions.slot_owners[idx] {
                assert(s_before.regions.ref_count(idx) == REF_COUNT_UNUSED);
                assert(s_before.regions.slots.contains_key(idx));
            }
        }
    };
    s.lemma_insert_vm_space(id, owner);
}

proof fn lemma_step_drop_vm_space<'rcu>(tracked s: &mut VmStore<'rcu>, vs: VmSpaceId)
    requires
        old(s).inv(),
        old(s).vm_spaces.contains_key(vs),
        forall|c: CursorId| #[trigger]
            old(s).cursors.contains_key(c) ==> old(s).cursors[c].vm_space != vs,
        forall|v: VmIoId| #[trigger]
            old(s).vm_ios.contains_key(v) ==> old(s).vm_ios[v].vm_space != Some(vs),
    ensures
        final(s).inv(),
{
    let tracked owner = s.tracked_extract_vm_space(vs);
    vm_space::drop_vm_space_step(owner);
}

proof fn lemma_step_open_cursor<'rcu>(
    tracked s: &mut VmStore<'rcu>,
    vs: VmSpaceId,
    va: Range<Vaddr>,
)
    requires
        old(s).inv(),
        old(s).vm_spaces.contains_key(vs),
    ensures
        final(s).inv(),
{
    reveal(VmStore::structural_inv);
    let ghost s_before = *s;
    let tracked vm_space_ref = s.vm_spaces.tracked_borrow(vs);
    let tracked res = cursor::open_cursor_step(vm_space_ref, &mut s.regions, vs, va);
    // `VmSpace::cursor` only allocates fresh PT nodes; accounting
    // carries (every changed slot went UNUSED → non-UNUSED PT node).
    lemma_accounting_preserved_by_pt_alloc(s_before, *s);
    match res {
        Option::Some(entry) => {
            let ghost id = fresh_cursor_id(s.cursors);
            lemma_fresh_cursor_id_not_in_dom(s.cursors);
            s.lemma_insert_cursor(id, entry);
        },
        Option::None => {},
    }
}

proof fn lemma_step_open_cursor_mut<'rcu>(
    tracked s: &mut VmStore<'rcu>,
    vs: VmSpaceId,
    va: Range<Vaddr>,
)
    requires
        old(s).inv(),
        old(s).vm_spaces.contains_key(vs),
    ensures
        final(s).inv(),
{
    reveal(VmStore::structural_inv);
    let ghost s_before = *s;
    let tracked vm_space_ref = s.vm_spaces.tracked_borrow(vs);
    let tracked res = cursor::open_cursor_mut_step(vm_space_ref, &mut s.regions, vs, va);
    // `VmSpace::cursor_mut` only allocates fresh PT nodes; accounting
    // carries (every changed slot went UNUSED → non-UNUSED PT node).
    lemma_accounting_preserved_by_pt_alloc(s_before, *s);
    match res {
        Option::Some(entry) => {
            let ghost id = fresh_cursor_id(s.cursors);
            lemma_fresh_cursor_id_not_in_dom(s.cursors);
            s.lemma_insert_cursor(id, entry);
        },
        Option::None => {},
    }
}

proof fn lemma_step_drop_cursor<'rcu>(tracked s: &mut VmStore<'rcu>, c: CursorId)
    requires
        old(s).inv(),
        old(s).cursors.contains_key(c),
    ensures
        final(s).inv(),
{
    let tracked entry = s.tracked_extract_cursor(c);
    cursor::drop_cursor_step(entry);
}

proof fn lemma_step_query<'rcu>(tracked s: &mut VmStore<'rcu>, c: CursorId)
    requires
        old(s).inv(),
        old(s).cursors.contains_key(c),
    ensures
        final(s).inv(),
{
    reveal(VmStore::structural_inv);
    reveal(VmStore::accounting_inv);
    let ghost old_frames = s.frames;
    let ghost old_regions = s.regions;
    let tracked mut entry = s.tracked_extract_cursor(c);
    let ghost res = cursor::cursor_query_step(&mut entry, &mut s.regions);
    match res {
        Option::None => {
            s.lemma_insert_cursor(c, entry);
        },
        Option::Some(paddr) => {
            let ghost target_idx = frame_to_index(paddr);
            s.regions.lemma_contains_valid_frame_paddr(paddr);
            let ghost id = fresh_frame_id(s.frames);
            lemma_fresh_frame_id_not_in_dom(s.frames);
            let tracked frame_entry = tracked_frame_entry_new(paddr);
            s.lemma_insert_frame(id, frame_entry);
            assert(s.regions.slot_owners[target_idx].usage is Frame);
            assert forall|idx: int|
                #![trigger s.regions.slot_owners[idx]]
                0 <= idx < max_meta_slots() && s.regions.ref_count(idx)
                    == REF_COUNT_UNUSED implies handle_count(s.frames, idx) == 0
                && s.regions.slot_owners[idx].paths_in_pt.is_empty() && segment_cover_count(
                s.segments,
                index_to_frame(idx),
            ) == 0 by {
                lemma_handle_count_insert_fresh(old_frames, id, frame_entry, idx);
                if idx == target_idx {
                    assert(false);
                } else {
                    assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
                }
            };
            assert forall|idx: int|
                #![trigger s.regions.slot_owners[idx]]
                0 <= idx < max_meta_slots() && s.regions.slot_owners[idx].usage is Frame
                    && s.regions.ref_count(idx) != REF_COUNT_UNUSED && s.regions.ref_count(idx)
                    != REF_COUNT_UNIQUE implies handle_count(s.frames, idx) > 0
                || s.regions.slot_owners[idx].paths_in_pt.len() > 0 || segment_cover_count(
                s.segments,
                index_to_frame(idx),
            ) > 0 by {
                lemma_handle_count_insert_fresh(old_frames, id, frame_entry, idx);
                if idx == target_idx {
                    assert(handle_count(s.frames, target_idx) >= 1);
                } else {
                    assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
                }
            };
            assert forall|idx: int|
                #![trigger s.regions.slot_owners[idx]]
                0 <= idx < max_meta_slots() && s.regions.slot_owners[idx].usage is Frame && (
                handle_count(s.frames, idx) > 0 || s.regions.slot_owners[idx].paths_in_pt.len() > 0
                    || segment_cover_count(s.segments, index_to_frame(idx)) > 0) implies {
                let so = s.regions.slot_owners[idx];
                let rc = so.ref_count();
                &&& rc != REF_COUNT_UNUSED
                &&& rc != REF_COUNT_UNIQUE
                &&& rc == handle_count(s.frames, idx) + so.paths_in_pt.len() + segment_cover_count(
                    s.segments,
                    index_to_frame(idx),
                )
            } by {
                lemma_handle_count_insert_fresh(old_frames, id, frame_entry, idx);
                if idx == target_idx {
                    if old_regions.slot_owners[target_idx].ref_count() == REF_COUNT_UNUSED {
                        assert(REF_COUNT_UNUSED == 0u32);
                        assert(s.regions.slot_owners[target_idx].ref_count() == 1);
                        assert(handle_count(s.frames, target_idx) == 1);
                        assert(s.regions.slot_owners[target_idx].paths_in_pt.len()
                            == old_regions.slot_owners[target_idx].paths_in_pt.len());
                        assert(old_regions.slot_owners[target_idx].paths_in_pt.len() == 0);
                        assert(segment_cover_count(s.segments, index_to_frame(target_idx)) == 0);
                    } else if old_regions.slot_owners[target_idx].ref_count() == REF_COUNT_UNIQUE {
                        assert(false);
                    } else {
                        let pre_so = old_regions.slot_owners[target_idx];
                        let pre_rc = pre_so.ref_count();
                        let pre_paths = pre_so.paths_in_pt.len();
                        let pre_H = handle_count(old_frames, target_idx);
                        let pre_cover = segment_cover_count(s.segments, index_to_frame(target_idx));
                        if pre_H == 0 && pre_paths == 0 && pre_cover == 0 {
                            assert(false);
                        } else {
                            assert(pre_rc == pre_H + pre_paths + pre_cover);
                            assert(handle_count(s.frames, target_idx) == pre_H + 1);
                        }
                    }
                } else {
                    assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
                }
            };
            s.lemma_insert_cursor(c, entry);
        },
    }
}

proof fn lemma_step_find_next<'rcu>(tracked s: &mut VmStore<'rcu>, c: CursorId, len: usize)
    requires
        old(s).inv(),
        old(s).cursors.contains_key(c),
    ensures
        final(s).inv(),
{
    reveal(VmStore::structural_inv);
    reveal(VmStore::accounting_inv);
    let tracked mut entry = s.tracked_extract_cursor(c);
    cursor::cursor_find_next_step(&mut entry, &mut s.regions, len);
    s.lemma_insert_cursor(c, entry);
}

proof fn lemma_step_jump<'rcu>(tracked s: &mut VmStore<'rcu>, c: CursorId, va: Vaddr)
    requires
        old(s).inv(),
        old(s).cursors.contains_key(c),
    ensures
        final(s).inv(),
{
    reveal(VmStore::structural_inv);
    reveal(VmStore::accounting_inv);
    let tracked mut entry = s.tracked_extract_cursor(c);
    cursor::cursor_jump_step(&mut entry, &mut s.regions, va);
    s.lemma_insert_cursor(c, entry);
}

proof fn lemma_step_protect_next<'rcu>(tracked s: &mut VmStore<'rcu>, c: CursorId, len: usize)
    requires
        old(s).inv(),
        old(s).cursors.contains_key(c),
    ensures
        final(s).inv(),
{
    reveal(VmStore::structural_inv);
    reveal(VmStore::accounting_inv);
    let tracked mut entry = s.tracked_extract_cursor(c);
    cursor::cursor_protect_next_step(&mut entry, &mut s.regions, len);
    s.lemma_insert_cursor(c, entry);
}

#[verifier::spinoff_prover]
proof fn lemma_step_map<'rcu>(
    tracked s: &mut VmStore<'rcu>,
    c: CursorId,
    fid: FrameId,
    prop: PageProperty,
)
    requires
        old(s).inv(),
        old(s).cursors.contains_key(c),
        old(s).frames.contains_key(fid),
    ensures
        final(s).inv(),
{
    let ghost s_before = *s;
    lemma_structural_inv_cursor_frame(*s, c, fid);
    assert(s.regions.inv() && s.tlb_model.inv() && s.cursors[c].inv()
        && s.cursors[c].owner.metaregion_sound(s.regions) && s.vm_spaces.contains_key(
        s.cursors[c].vm_space,
    ));
    // `usage == Frame` at the mapped slot from `structural_inv`'s
    // FrameId⟹Frame-usage clause.
    assert(s.regions.slot_owner(s.frames[fid].paddr).usage is Frame);
    let ghost paddr = s.frames[fid].paddr;
    let ghost target_idx = frame_to_index(paddr);
    let ghost old_frames = s.frames;
    let ghost old_regions = s.regions;
    assert(valid_frame_paddr(paddr));
    s.regions.lemma_contains_valid_frame_paddr(paddr);
    assert(s.regions.contains(target_idx));
    assert(s.regions.slots[target_idx].addr() == index_to_meta(target_idx));
    assert(old_frames.dom().filter(
        |gid: FrameId| frame_to_index(old_frames[gid].paddr) == target_idx,
    ).contains(fid));
    assert(handle_count(old_frames, target_idx) >= 1);
    let ghost pre_rc_target = old_regions.slot_owners[target_idx].ref_count();
    let ghost pre_paths_target = old_regions.slot_owners[target_idx].paths_in_pt.len();
    let ghost pre_cover_target = segment_cover_count(s.segments, index_to_frame(target_idx));
    lemma_accounting_inv_at(*s, target_idx);
    assert(pre_rc_target != REF_COUNT_UNUSED && pre_rc_target != REF_COUNT_UNIQUE && pre_rc_target
        == handle_count(old_frames, target_idx) + pre_paths_target + pre_cover_target);
    let tracked mut entry = s.tracked_extract_cursor(c);
    let tracked _frame_entry = s.tracked_extract_frame(fid);
    assert(entry.inv());
    assert(entry.owner.metaregion_sound(s.regions));
    assert(s.regions.inv());
    assert(s.tlb_model.inv());
    cursor::map_step(&mut entry, &mut s.regions, &mut s.tlb_model, paddr, prop);
    assert forall|idx: int|
        #![trigger s.regions.slot_owners[idx]]
        0 <= idx < max_meta_slots() && s.regions.ref_count(idx)
            == REF_COUNT_UNUSED implies handle_count(s.frames, idx) == 0
        && s.regions.slot_owners[idx].paths_in_pt.is_empty() && segment_cover_count(
        s.segments,
        index_to_frame(idx),
    ) == 0 by {
        lemma_accounting_inv_at(s_before, idx);
        // post-UNUSED ⟹ slot fully preserved (cursor axiom).
        assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
        lemma_handle_count_remove(old_frames, fid, idx);
        if idx == target_idx {
            // post-UNUSED at target_idx contradicts rc preserved at
            // target_idx + pre_rc_target != UNUSED.
            assert(s.regions.ref_count(idx) == pre_rc_target);
            assert(false);
        }
    };
    assert forall|idx: int|
        #![trigger s.regions.slot_owners[idx]]
        0 <= idx < max_meta_slots() && s.regions.slot_owners[idx].usage is Frame
            && s.regions.ref_count(idx) != REF_COUNT_UNUSED && s.regions.ref_count(idx)
            != REF_COUNT_UNIQUE implies handle_count(s.frames, idx) > 0
        || s.regions.slot_owners[idx].paths_in_pt.len() > 0 || segment_cover_count(
        s.segments,
        index_to_frame(idx),
    ) > 0 by {
        lemma_accounting_inv_at(s_before, idx);
        lemma_handle_count_remove(old_frames, fid, idx);
        if idx == target_idx {
            assert(s.regions.slot_owners[idx].paths_in_pt.len() == pre_paths_target + 1);
        } else if old_regions.ref_count(idx) == REF_COUNT_UNUSED {
            assert(s.regions.slot_owners[idx].usage !is Frame);
        } else {
            assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
        }
    };
    assert forall|idx: int|
        #![trigger s.regions.slot_owners[idx]]
        0 <= idx < max_meta_slots() && s.regions.slot_owners[idx].usage is Frame && (handle_count(
            s.frames,
            idx,
        ) > 0 || s.regions.slot_owners[idx].paths_in_pt.len() > 0 || segment_cover_count(
            s.segments,
            index_to_frame(idx),
        ) > 0) implies {
        let so = s.regions.slot_owners[idx];
        let rc = so.ref_count();
        &&& rc != REF_COUNT_UNUSED
        &&& rc != REF_COUNT_UNIQUE
        &&& rc == handle_count(s.frames, idx) + so.paths_in_pt.len() + segment_cover_count(
            s.segments,
            index_to_frame(idx),
        )
    } by {
        lemma_accounting_inv_at(s_before, idx);
        lemma_handle_count_remove(old_frames, fid, idx);
        if idx == target_idx {
            assert(s.regions.ref_count(idx) == pre_rc_target);
            assert(s.regions.slot_owners[idx].paths_in_pt.len() == pre_paths_target + 1);
            assert(handle_count(s.frames, idx) == (handle_count(old_frames, idx) - 1) as nat);
        } else if old_regions.ref_count(idx) == REF_COUNT_UNUSED {
            assert(s.regions.slot_owners[idx].usage !is Frame);
        } else {
            assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
        }
    };
    assert forall|fid_other: FrameId| #[trigger]
        s.frames.contains_key(fid_other) implies s.regions.slot_owner(
        s.frames[fid_other].paddr,
    ).usage is Frame by {
        let other_idx = frame_to_index(s.frames[fid_other].paddr);
        lemma_structural_inv_frame(s_before, fid_other);
        lemma_accounting_inv_at(s_before, other_idx);
        assert(old_regions.slot_owners[other_idx].usage is Frame);
        if other_idx == target_idx {
            assert(s.regions.slot_owners[target_idx].usage
                == old_regions.slot_owners[target_idx].usage);
        } else {
            assert(old_frames.dom().filter(
                |gid: FrameId| frame_to_index(old_frames[gid].paddr) == other_idx,
            ).contains(fid_other));
            assert(handle_count(old_frames, other_idx) >= 1);
            assert(old_regions.slot_owners[other_idx].ref_count() != REF_COUNT_UNUSED);
            assert(s.regions.slot_owners[other_idx] == old_regions.slot_owners[other_idx]);
        }
    };
    assert forall|sid: SegmentId, paddr_c: Paddr|
        #![trigger
            s.segments.contains_key(sid),
            frame_to_index(paddr_c)]
        s.segments.contains_key(sid) && s.segments[sid].range.start <= paddr_c
            < s.segments[sid].range.end && paddr_c % PAGE_SIZE == 0 implies s.regions.slot_owner(
        paddr_c,
    ).usage is Frame by {
        let cov_idx = frame_to_index(paddr_c);
        lemma_structural_inv_segment(s_before, sid, paddr_c);
        s_before.regions.lemma_contains_valid_frame_paddr(paddr_c);
        lemma_accounting_inv_at(s_before, cov_idx);
        // pre cover >= 1 at cov_idx ⟹ pre slot is Frame + non-UNUSED.
        lemma_segment_cover_contains(old_regions_segments_helper(s), sid, paddr_c);
        assert(old_regions.slot_owners[cov_idx].usage is Frame);
        assert(old_regions.slot_owners[cov_idx].ref_count() != REF_COUNT_UNUSED);
        if cov_idx == target_idx {
            // Map preserves usage at target.
            assert(s.regions.slot_owners[target_idx].usage
                == old_regions.slot_owners[target_idx].usage);
        } else {
            // Non-mapped pre-non-UNUSED slot ⟹ fully preserved.
            assert(s.regions.slot_owners[cov_idx] == old_regions.slot_owners[cov_idx]);
        }
    };
    lemma_accounting_inv_intro(*s);
    assert(s.structural_inv()) by {
        reveal(VmStore::structural_inv);
    };
    assert(s.vm_spaces.contains_key(entry.vm_space));
    s.lemma_insert_cursor(c, entry);
}

// Helper: snapshot the pre-step segments map. Defined as a no-op
// inline spec to give the discharge proofs a stable handle on the
// pre-state when `s.segments` is unchanged.
spec fn old_regions_segments_helper<'rcu>(s: &VmStore<'rcu>) -> Map<SegmentId, SegmentEntry> {
    s.segments
}

proof fn lemma_step_unmap<'rcu>(tracked s: &mut VmStore<'rcu>, c: CursorId, len: usize)
    requires
        old(s).inv(),
        old(s).cursors.contains_key(c),
    ensures
        final(s).inv(),
{
    reveal(VmStore::structural_inv);
    reveal(VmStore::accounting_inv);
    let ghost s_before = *s;
    let ghost old_regions = s.regions;
    let ghost old_frames = s.frames;
    let tracked mut entry = s.tracked_extract_cursor(c);
    cursor::cursor_mut_regions_step(
        &mut entry,
        &mut s.regions,
        &mut s.tlb_model,
        cursor::CursorMutRegionsMethod::Unmap(len),
    );
    lemma_coverage_preserved_slots_eq(s_before, *s);
    assert forall|idx: int|
        #![trigger s.regions.slot_owners[idx]]
        0 <= idx < max_meta_slots() && s.regions.ref_count(idx)
            == REF_COUNT_UNUSED implies handle_count(s.frames, idx) == 0
        && s.regions.slot_owners[idx].paths_in_pt.is_empty() && segment_cover_count(
        s.segments,
        index_to_frame(idx),
    ) == 0 by {
        assert(s.regions.contains(idx));
        assert(segment_cover_count(s.segments, index_to_frame(idx)) == 0) by {
            if segment_cover_count(old(s).segments, index_to_frame(idx)) > 0 {
                let pa = index_to_frame(idx);
                let sid = lemma_segment_cover_witness(old(s).segments, pa);
                assert(pa == (idx * PAGE_SIZE) as usize);
                assert(pa % PAGE_SIZE == 0);
                assert(frame_to_index(pa) == idx);
                assert(old_regions.slot_owners[idx].usage is Frame);
                assert(old_regions.ref_count(idx) != REF_COUNT_UNUSED);
                assert(old_regions.ref_count(idx) <= REF_COUNT_MAX);
                assert(s.regions.ref_count(idx) <= REF_COUNT_MAX);
            }
        };
        // Case-split on pre.usage: usage is preserved by the axiom.
        if old_regions.slot_owners[idx].usage is Frame {
            assert(s.regions.slot_owners[idx].usage != PageUsage::MMIO);
            assert(s.regions.slot_owners[idx].paths_in_pt == Set::empty());
        } else if old_regions.slot_owners[idx].usage == PageUsage::MMIO {
            assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
        } else {
            assert(s.regions.slot_owners[idx].usage != PageUsage::MMIO);
            assert(s.regions.slot_owners[idx].paths_in_pt == Set::empty());
            assert(handle_count(s.frames, idx) == 0) by {
                let filt = s.frames.dom().filter(
                    |gid: FrameId| frame_to_index(s.frames[gid].paddr) == idx,
                );
                assert forall|fid: FrameId| #[trigger] filt.contains(fid) implies false by {
                    assert(s.frames.contains_key(fid));
                    assert(frame_to_index(s.frames[fid].paddr) == idx);
                    assert(s.regions.slot_owners[idx].usage is Frame);
                };
                assert(filt == Set::empty());
            };
        }
    };
    assert forall|idx: int|
        #![trigger s.regions.slot_owners[idx]]
        0 <= idx < max_meta_slots() && s.regions.slot_owners[idx].usage is Frame
            && s.regions.ref_count(idx) != REF_COUNT_UNUSED && s.regions.ref_count(idx)
            != REF_COUNT_UNIQUE implies handle_count(s.frames, idx) > 0
        || s.regions.slot_owners[idx].paths_in_pt.len() > 0 || segment_cover_count(
        s.segments,
        index_to_frame(idx),
    ) > 0 by {
        assert(s.regions.contains(idx));
        assert(old_regions.ref_count(idx) != REF_COUNT_UNUSED) by {
            if old_regions.ref_count(idx) == REF_COUNT_UNUSED {
                assert(old_regions.contains(idx));
                assert(old_regions.slot_owners[idx].paths_in_pt == Set::empty());
                assert(s.regions.slot_owners[idx].paths_in_pt.len() == 0);
                assert(false);
            }
        };
        if handle_count(old_frames, idx) > 0 {
            assert(handle_count(s.frames, idx) > 0);
        } else if segment_cover_count(s.segments, index_to_frame(idx)) > 0 {
        } else {
            assert(s.regions.slot_owners[idx].paths_in_pt.len() > 0);
        }
    };
    assert forall|idx: int|
        #![trigger s.regions.slot_owners[idx]]
        0 <= idx < max_meta_slots() && s.regions.slot_owners[idx].usage is Frame && (handle_count(
            s.frames,
            idx,
        ) > 0 || s.regions.slot_owners[idx].paths_in_pt.len() > 0) implies {
        let so = s.regions.slot_owners[idx];
        let rc = so.ref_count();
        &&& rc != REF_COUNT_UNUSED
        &&& rc != REF_COUNT_UNIQUE
        &&& rc == handle_count(s.frames, idx) + so.paths_in_pt.len() + segment_cover_count(
            s.segments,
            index_to_frame(idx),
        )
    } by {
        if handle_count(s.frames, idx) > 0 {
            assert(handle_count(old_frames, idx) > 0);
        } else {
            assert(old_regions.slot_owners[idx].paths_in_pt.len() > 0);
        }
    };
    assert forall|fid_other: FrameId| #[trigger]
        s.frames.contains_key(fid_other) implies s.regions.slot_owner(
        s.frames[fid_other].paddr,
    ).usage is Frame by {
        let other_idx = frame_to_index(s.frames[fid_other].paddr);
        assert(s.regions.slot_owners[other_idx].usage == old_regions.slot_owners[other_idx].usage);
    };
    assert forall|u: UniqueId| #[trigger] s.unique_frames.contains_key(u) implies {
        let so = s.regions.slot_owner(s.unique_frames[u].paddr);
        &&& so.usage is Frame
        &&& so.ref_count() == REF_COUNT_UNIQUE
        &&& so.in_list_perm.value() == 0
        &&& so.paths_in_pt.is_empty()
    } by {
        let u_idx = frame_to_index(s.unique_frames[u].paddr);
        assert(old(s).unique_frames.contains_key(u));
        // Old validity at `u`.
        assert(old_regions.slot_owners[u_idx].usage is Frame);
        assert(old_regions.slot_owners[u_idx].ref_count() == REF_COUNT_UNIQUE);
        assert(old_regions.slot_owners[u_idx].paths_in_pt.is_empty());
        assert(old_regions.slot_owners[u_idx].in_list_perm.value() == 0);
        // `u_idx` is a managed slot.
        s.regions.lemma_contains_valid_frame_paddr(s.unique_frames[u].paddr);
        assert(s.regions.contains(u_idx));
        // usage / in_list preserved universally by the unmap axiom.
        assert(s.regions.slot_owners[u_idx].usage == old_regions.slot_owners[u_idx].usage);
        assert(s.regions.slot_owners[u_idx].in_list_perm
            == old_regions.slot_owners[u_idx].in_list_perm);
        // Frame rc-paths invariant: pre paths empty ⟹ post paths empty,
        // post rc == pre rc == UNIQUE.
        assert(s.regions.slot_owners[u_idx].paths_in_pt.len()
            <= old_regions.slot_owners[u_idx].paths_in_pt.len());
        assert(old_regions.slot_owners[u_idx].paths_in_pt.len() == 0);
        assert(s.regions.slot_owners[u_idx].paths_in_pt =~= Set::empty());
        assert(s.regions.slot_owners[u_idx].ref_count() == REF_COUNT_UNIQUE);
    };
    s.lemma_insert_cursor(c, entry);
}

proof fn lemma_step_new_vm_io<'rcu>(
    tracked s: &mut VmStore<'rcu>,
    vs: VmSpaceId,
    vaddr: Vaddr,
    len: usize,
    kind: VmIoKind,
)
    requires
        old(s).inv(),
        old(s).vm_spaces.contains_key(vs),
    ensures
        final(s).inv(),
{
    reveal(VmStore::structural_inv);
    let tracked vm_space_ref = s.vm_spaces.tracked_borrow(vs);
    let tracked res = io::new_vm_io_step(vm_space_ref, Some(vs), vaddr, len, kind);
    match res {
        Option::Some(entry) => {
            let ghost id = fresh_vm_io_id(s.vm_ios);
            lemma_fresh_vm_io_id_not_in_dom(s.vm_ios);
            s.lemma_insert_vm_io(id, entry);
        },
        Option::None => {},
    }
}

proof fn lemma_step_new_kernel_vm_io<'rcu>(
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
    lemma_fresh_vm_io_id_not_in_dom(s.vm_ios);
    s.lemma_insert_vm_io(id, entry);
}

proof fn lemma_step_drop_vm_io<'rcu>(tracked s: &mut VmStore<'rcu>, vio: VmIoId)
    requires
        old(s).inv(),
        old(s).vm_ios.contains_key(vio),
    ensures
        final(s).inv(),
{
    let tracked entry = s.tracked_extract_vm_io(vio);
    io::drop_vm_io_step(entry);
}

proof fn lemma_step_vm_io_method<'rcu>(
    tracked s: &mut VmStore<'rcu>,
    vio: VmIoId,
    method: io::VmIoMethod,
)
    requires
        old(s).inv(),
        old(s).vm_ios.contains_key(vio),
    ensures
        final(s).inv(),
{
    reveal(VmStore::structural_inv);
    let tracked mut entry = s.tracked_extract_vm_io(vio);
    io::vm_io_method_step(&mut entry, method);
    s.lemma_insert_vm_io(vio, entry);
}

proof fn lemma_step_read<'rcu>(tracked s: &mut VmStore<'rcu>, source: VmIoId, dest: VmIoId)
    requires
        old(s).inv(),
        old(s).vm_ios.contains_key(source),
        old(s).vm_ios.contains_key(dest),
        source != dest,
        old(s).vm_ios[source].vm_space is None,
        old(s).vm_ios[source].kind == VmIoKind::Reader,
        old(s).vm_ios[dest].vm_space is None,
        old(s).vm_ios[dest].kind == VmIoKind::Writer,
    ensures
        final(s).inv(),
{
    reveal(VmStore::structural_inv);
    let tracked mut src = s.tracked_extract_vm_io(source);
    let tracked mut dst = s.tracked_extract_vm_io(dest);
    let tracked val = io::read_step(&mut src, &mut dst);
    s.lemma_insert_vm_io(source, src);
    s.lemma_insert_vm_io(dest, dst);
    let ghost id = fresh_vm_io_id(s.vm_ios);
    lemma_fresh_vm_io_id_not_in_dom(s.vm_ios);
    s.lemma_insert_vm_io(id, val);
}

proof fn lemma_step_write<'rcu>(tracked s: &mut VmStore<'rcu>, source: VmIoId, dest: VmIoId)
    requires
        old(s).inv(),
        old(s).vm_ios.contains_key(source),
        old(s).vm_ios.contains_key(dest),
        source != dest,
        old(s).vm_ios[source].vm_space is None,
        old(s).vm_ios[source].kind == VmIoKind::Reader,
        old(s).vm_ios[dest].vm_space is None,
        old(s).vm_ios[dest].kind == VmIoKind::Writer,
    ensures
        final(s).inv(),
{
    reveal(VmStore::structural_inv);
    let tracked mut src = s.tracked_extract_vm_io(source);
    let tracked mut dst = s.tracked_extract_vm_io(dest);
    s.lemma_insert_vm_io(source, src);
    s.lemma_insert_vm_io(dest, dst);
}

proof fn lemma_step_frame_from_unused<'rcu>(tracked s: &mut VmStore<'rcu>, paddr: Paddr)
    requires
        old(s).inv(),
    ensures
        final(s).inv(),
{
    reveal(VmStore::structural_inv);
    reveal(VmStore::accounting_inv);
    let ghost old_frames = s.frames;
    let ghost old_regions = s.regions;
    if !valid_frame_paddr(paddr) || s.regions.slots.contains_key(frame_to_index(paddr)) {
        let tracked res = frame::from_unused_step(&mut s.regions, paddr);
        match res {
            Option::Some(entry) => {
                let ghost id = fresh_frame_id(s.frames);
                lemma_fresh_frame_id_not_in_dom(s.frames);
                let ghost target_idx = frame_to_index(paddr);
                let ghost entry_paddr = entry.paddr;
                s.lemma_insert_frame(id, entry);
                assert(s.frames[id].paddr == paddr);

                assert(handle_count(old_frames, target_idx) == 0);
                assert(old_regions.slot_owners[target_idx].paths_in_pt.is_empty());

                assert forall|idx: int|
                    #![trigger s.regions.slot_owners[idx]]
                    0 <= idx < max_meta_slots() && s.regions.ref_count(idx)
                        == REF_COUNT_UNUSED implies handle_count(s.frames, idx) == 0
                    && s.regions.slot_owners[idx].paths_in_pt.is_empty() by {
                    lemma_handle_count_insert_fresh(old_frames, id, entry, idx);
                    if idx == target_idx {
                        assert(false);
                    } else {
                        assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
                    }
                };
                assert forall|idx: int|
                    #![trigger s.regions.slot_owners[idx]]
                    0 <= idx < max_meta_slots() && s.regions.slot_owners[idx].usage is Frame
                        && s.regions.ref_count(idx) != REF_COUNT_UNUSED && s.regions.ref_count(idx)
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
                assert forall|idx: int|
                    #![trigger s.regions.slot_owners[idx]]
                    0 <= idx < max_meta_slots() && s.regions.slot_owners[idx].usage is Frame && (
                    handle_count(s.frames, idx) > 0 || s.regions.slot_owners[idx].paths_in_pt.len()
                        > 0 || segment_cover_count(s.segments, index_to_frame(idx)) > 0) implies {
                    let so = s.regions.slot_owners[idx];
                    let rc = so.ref_count();
                    &&& rc != REF_COUNT_UNUSED
                    &&& rc != REF_COUNT_UNIQUE
                    &&& rc == handle_count(s.frames, idx) + so.paths_in_pt.len()
                        + segment_cover_count(s.segments, index_to_frame(idx))
                } by {
                    lemma_handle_count_insert_fresh(old_frames, id, entry, idx);
                    if idx == target_idx {
                        assert(old_regions.ref_count(idx) == REF_COUNT_UNUSED);
                        assert(handle_count(old_frames, idx) == 0);
                        assert(handle_count(s.frames, idx) == 1);
                        assert(segment_cover_count(s.segments, index_to_frame(idx)) == 0);
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
}

proof fn lemma_step_frame_from_in_use<'rcu>(tracked s: &mut VmStore<'rcu>, paddr: Paddr)
    requires
        old(s).inv(),
    ensures
        final(s).inv(),
{
    reveal(VmStore::structural_inv);
    reveal(VmStore::accounting_inv);
    let ghost old_frames = s.frames;
    let ghost old_regions = s.regions;
    if !valid_frame_paddr(paddr) || s.regions.slots.contains_key(frame_to_index(paddr)) {
        let tracked res = frame::from_in_use_step(&mut s.regions, paddr);
        match res {
            Option::Some(entry) => {
                let ghost id = fresh_frame_id(s.frames);
                lemma_fresh_frame_id_not_in_dom(s.frames);
                let ghost target_idx = frame_to_index(paddr);
                s.lemma_insert_frame(id, entry);
                assert(s.frames[id].paddr == paddr);

                assert forall|idx: int|
                    #![trigger s.regions.slot_owners[idx]]
                    0 <= idx < max_meta_slots() && s.regions.ref_count(idx)
                        == REF_COUNT_UNUSED implies handle_count(s.frames, idx) == 0
                    && s.regions.slot_owners[idx].paths_in_pt.is_empty() by {
                    lemma_handle_count_insert_fresh(old_frames, id, entry, idx);
                    if idx == target_idx {
                        assert(false);
                    } else {
                        assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
                    }
                };

                assert forall|idx: int|
                    #![trigger s.regions.slot_owners[idx]]
                    0 <= idx < max_meta_slots() && s.regions.slot_owners[idx].usage is Frame
                        && s.regions.ref_count(idx) != REF_COUNT_UNUSED && s.regions.ref_count(idx)
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

                assert forall|idx: int|
                    #![trigger s.regions.slot_owners[idx]]
                    0 <= idx < max_meta_slots() && s.regions.slot_owners[idx].usage is Frame && (
                    handle_count(s.frames, idx) > 0 || s.regions.slot_owners[idx].paths_in_pt.len()
                        > 0 || segment_cover_count(s.segments, index_to_frame(idx)) > 0) implies {
                    let so = s.regions.slot_owners[idx];
                    let rc = so.ref_count();
                    &&& rc != REF_COUNT_UNUSED
                    &&& rc != REF_COUNT_UNIQUE
                    &&& rc == handle_count(s.frames, idx) + so.paths_in_pt.len()
                        + segment_cover_count(s.segments, index_to_frame(idx))
                } by {
                    lemma_handle_count_insert_fresh(old_frames, id, entry, idx);
                    if idx == target_idx {
                        assert(old_regions.slot_owners[idx].usage is Frame);
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
}

proof fn lemma_step_frame_drop<'rcu>(tracked s: &mut VmStore<'rcu>, fid: FrameId)
    requires
        old(s).inv(),
        old(s).frames.contains_key(fid),
        segment_cover_count(old(s).segments, old(s).frames[fid].paddr) == 0,
    ensures
        final(s).inv(),
{
    reveal(VmStore::structural_inv);
    reveal(VmStore::accounting_inv);
    lemma_frame_drop_pre_derivable(*s, fid);
    let ghost p = s.frames[fid].paddr;
    s.regions.lemma_contains_valid_frame_paddr(p);
    let ghost idx_p = frame_to_index(p);
    assert(s.frames.dom().filter(
        |gid: FrameId| frame_to_index(s.frames[gid].paddr) == idx_p,
    ).contains(fid));
    assert(handle_count(s.frames, idx_p) >= 1);
    let ghost target_idx = frame_to_index(p);
    let ghost old_frames = s.frames;
    let ghost old_regions = s.regions;
    let tracked entry = s.tracked_extract_frame(fid);
    frame::drop_step(&mut s.regions, entry);
    assert forall|idx: int|
        #![trigger s.regions.slot_owners[idx]]
        0 <= idx < max_meta_slots() && s.regions.ref_count(idx)
            == REF_COUNT_UNUSED implies handle_count(s.frames, idx) == 0
        && s.regions.slot_owners[idx].paths_in_pt.is_empty() && segment_cover_count(
        s.segments,
        index_to_frame(idx),
    ) == 0 by {
        lemma_handle_count_remove(old_frames, fid, idx);
        if idx == target_idx {
            assert(old_regions.ref_count(idx) == 1);
            assert(handle_count(old_frames, idx) == 1);
            assert(handle_count(s.frames, idx) == 0);
            assert(s.regions.slot_owners[idx].paths_in_pt.is_empty());
        } else {
            assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
        }
    };

    assert forall|idx: int|
        #![trigger s.regions.slot_owners[idx]]
        0 <= idx < max_meta_slots() && s.regions.slot_owners[idx].usage is Frame
            && s.regions.ref_count(idx) != REF_COUNT_UNUSED && s.regions.ref_count(idx)
            != REF_COUNT_UNIQUE implies handle_count(s.frames, idx) > 0
        || s.regions.slot_owners[idx].paths_in_pt.len() > 0 || segment_cover_count(
        s.segments,
        index_to_frame(idx),
    ) > 0 by {
        lemma_handle_count_remove(old_frames, fid, idx);
        if idx == target_idx {
            assert(handle_count(old_frames, idx) >= 1);
        } else {
            assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
        }
    };

    assert forall|idx: int|
        #![trigger s.regions.slot_owners[idx]]
        0 <= idx < max_meta_slots() && s.regions.slot_owners[idx].usage is Frame && (handle_count(
            s.frames,
            idx,
        ) > 0 || s.regions.slot_owners[idx].paths_in_pt.len() > 0 || segment_cover_count(
            s.segments,
            index_to_frame(idx),
        ) > 0) implies {
        let so = s.regions.slot_owners[idx];
        let rc = so.ref_count();
        &&& rc != REF_COUNT_UNUSED
        &&& rc != REF_COUNT_UNIQUE
        &&& rc == handle_count(s.frames, idx) + so.paths_in_pt.len() + segment_cover_count(
            s.segments,
            index_to_frame(idx),
        )
    } by {
        lemma_handle_count_remove(old_frames, fid, idx);
        if idx == target_idx {
            assert(old_regions.slot_owners[idx].usage is Frame);
            assert(handle_count(old_frames, idx) > 0);
            let ghost pre_rc = old_regions.ref_count(idx);
            let ghost pre_h = handle_count(old_frames, idx);
            let ghost pre_p = old_regions.slot_owners[idx].paths_in_pt.len();
            assert(pre_rc == pre_h + pre_p);
            let ghost post_h = handle_count(s.frames, idx);
            assert(post_h == (pre_h - 1) as nat);
            let ghost post_p = s.regions.slot_owners[idx].paths_in_pt.len();
            assert(post_p == pre_p);
            let ghost post_rc = s.regions.ref_count(idx);
            if pre_rc > 1 {
                assert(post_rc == (pre_rc - 1) as u64);
                assert(post_rc as nat == post_h + post_p);
                assert(s.regions.slot_owners[idx].storage_perm()
                    == old_regions.slot_owners[idx].storage_perm());
            } else {
                assert(pre_h == 1);
                assert(pre_p == 0);
                assert(post_h == 0);
                assert(post_p == 0);
                assert(post_rc == REF_COUNT_UNUSED);
                assert(false);
            }
        } else {
            assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
        }
    };
}

/// Discharges the post-state `accounting_inv` for `lemma_step_segment_from_unused`.
#[verifier::spinoff_prover]
proof fn lemma_step_segment_from_unused_accounting<'rcu>(
    s_after: VmStore<'rcu>,
    old_store: VmStore<'rcu>,
    range: Range<Paddr>,
    id: SegmentId,
    entry: SegmentEntry,
)
    requires
        s_after.regions.inv(),
        s_after.frames == old_store.frames,
        !old_store.segments.contains_key(id),
        s_after.segments == old_store.segments.insert(id, entry),
        entry.range == range,
        range.start % PAGE_SIZE == 0,
        range.end % PAGE_SIZE == 0,
        range.start < range.end,
        range.end <= MAX_PADDR,
        old_store.accounting_inv(),
        old_store.regions.inv(),
        forall|paddr: Paddr|
            #![trigger frame_to_index(paddr)]
            (range.start <= paddr < range.end && paddr % PAGE_SIZE == 0) ==> {
                let idx = frame_to_index(paddr);
                let so = s_after.regions.slot_owners[idx];
                &&& so.usage is Frame
                &&& so.ref_count() == 1
                &&& so.paths_in_pt.is_empty()
                &&& so.storage_perm().is_init()
            },
        forall|i: int|
            #![trigger s_after.regions.slot_owners[i]]
            i < max_meta_slots() && !(range.start <= index_to_frame(i) < range.end)
                ==> s_after.regions.slot_owners[i] == old_store.regions.slot_owners[i],
        forall|paddr: Paddr|
            #![trigger frame_to_index(paddr)]
            (range.start <= paddr < range.end && paddr % PAGE_SIZE == 0)
                ==> old_store.regions.slot_owner(paddr).ref_count() == REF_COUNT_UNUSED,
    ensures
        s_after.accounting_inv(),
{
    reveal(VmStore::accounting_inv);
    let old_regions = old_store.regions;
    let old_frames = old_store.frames;
    let old_segments = old_store.segments;
    assert forall|idx: int|
        #![trigger s_after.regions.slot_owners[idx]]
        0 <= idx < max_meta_slots() && s_after.regions.ref_count(idx)
            == REF_COUNT_UNUSED implies handle_count(s_after.frames, idx) == 0
        && s_after.regions.slot_owners[idx].paths_in_pt.is_empty() && segment_cover_count(
        s_after.segments,
        index_to_frame(idx),
    ) == 0 by {
        let paddr = index_to_frame(idx);
        if range.start <= paddr < range.end {
            assert(false);
        } else {
            lemma_segment_cover_insert_outside(old_segments, id, entry, paddr);
        }
    };
    assert forall|idx: int|
        #![trigger s_after.regions.slot_owners[idx]]
        0 <= idx < max_meta_slots() && s_after.regions.slot_owners[idx].usage is Frame
            && s_after.regions.ref_count(idx) != REF_COUNT_UNUSED && s_after.regions.ref_count(idx)
            != REF_COUNT_UNIQUE implies handle_count(s_after.frames, idx) > 0
        || s_after.regions.slot_owners[idx].paths_in_pt.len() > 0 || segment_cover_count(
        s_after.segments,
        index_to_frame(idx),
    ) > 0 by {
        let paddr = index_to_frame(idx);
        if range.start <= paddr < range.end {
            lemma_segment_cover_insert_inside(old_segments, id, entry, paddr);
        } else {
            lemma_segment_cover_insert_outside(old_segments, id, entry, paddr);
        }
    };
    assert forall|idx: int|
        #![trigger s_after.regions.slot_owners[idx]]
        0 <= idx < max_meta_slots() && s_after.regions.slot_owners[idx].usage is Frame && (
        handle_count(s_after.frames, idx) > 0 || s_after.regions.slot_owners[idx].paths_in_pt.len()
            > 0 || segment_cover_count(s_after.segments, index_to_frame(idx)) > 0) implies {
        let so = s_after.regions.slot_owners[idx];
        let rc = so.ref_count();
        &&& rc != REF_COUNT_UNUSED
        &&& rc != REF_COUNT_UNIQUE
        &&& rc == handle_count(s_after.frames, idx) + so.paths_in_pt.len() + segment_cover_count(
            s_after.segments,
            index_to_frame(idx),
        )
    } by {
        let paddr = index_to_frame(idx);
        if range.start <= paddr < range.end {
            lemma_segment_cover_insert_inside(old_segments, id, entry, paddr);
        } else {
            lemma_segment_cover_insert_outside(old_segments, id, entry, paddr);
        }
    };
}

/// `Op::SegmentFromUnused` step.
#[verifier::spinoff_prover]
proof fn lemma_step_segment_from_unused<'rcu>(tracked s: &mut VmStore<'rcu>, range: Range<Paddr>)
    requires
        old(s).inv(),
    ensures
        final(s).inv(),
{
    reveal(VmStore::structural_inv);
    reveal(VmStore::accounting_inv);
    if range.start % PAGE_SIZE == 0 && range.end % PAGE_SIZE == 0 && range.start < range.end
        && range.end <= MAX_PADDR && (forall|paddr: Paddr|
        #![trigger frame_to_index(paddr)]
        (range.start <= paddr < range.end && paddr % PAGE_SIZE == 0) ==> s.regions.slot_owner(
            paddr,
        ).ref_count() == REF_COUNT_UNUSED) {
        let ghost s_before = *s;
        let ghost old_regions = s.regions;
        let ghost old_frames = s.frames;
        let ghost old_segments = s.segments;
        let tracked res = segment::from_unused_step(&mut s.regions, range);
        match res {
            Option::Some(entry) => {
                let ghost id = fresh_segment_id(s.segments);
                lemma_fresh_segment_id_not_in_dom(s.segments);
                s.lemma_insert_segment(id, entry);
                lemma_step_segment_from_unused_accounting(*s, s_before, range, id, entry);
            },
            Option::None => {},
        }
    }
}

proof fn lemma_accounting_inv_intro<'rcu>(store: VmStore<'rcu>)
    requires
        forall|idx: int|
            #![trigger store.regions.slot_owners[idx]]
            0 <= idx < max_meta_slots() && store.regions.ref_count(idx) == REF_COUNT_UNUSED
                ==> handle_count(store.frames, idx) == 0
                && store.regions.slot_owners[idx].paths_in_pt.is_empty() && segment_cover_count(
                store.segments,
                index_to_frame(idx),
            ) == 0,
        forall|idx: int|
            #![trigger store.regions.slot_owners[idx]]
            0 <= idx < max_meta_slots() && store.regions.slot_owners[idx].usage is Frame
                && store.regions.ref_count(idx) != REF_COUNT_UNUSED && store.regions.ref_count(idx)
                != REF_COUNT_UNIQUE ==> handle_count(store.frames, idx) > 0
                || store.regions.slot_owners[idx].paths_in_pt.len() > 0 || segment_cover_count(
                store.segments,
                index_to_frame(idx),
            ) > 0,
        forall|idx: int|
            #![trigger store.regions.slot_owners[idx]]
            0 <= idx < max_meta_slots() && store.regions.slot_owners[idx].usage is Frame && (
            handle_count(store.frames, idx) > 0 || store.regions.slot_owners[idx].paths_in_pt.len()
                > 0 || segment_cover_count(store.segments, index_to_frame(idx)) > 0) ==> {
                let so = store.regions.slot_owners[idx];
                let rc = so.ref_count();
                &&& rc != REF_COUNT_UNUSED
                &&& rc != REF_COUNT_UNIQUE
                &&& rc == handle_count(store.frames, idx) + so.paths_in_pt.len()
                    + segment_cover_count(store.segments, index_to_frame(idx))
            },
    ensures
        store.accounting_inv(),
{
    reveal(VmStore::accounting_inv);
}

#[verifier::spinoff_prover]
proof fn lemma_drop_segment_with_store_inv<'rcu>(
    tracked regions: &mut MetaRegionOwners,
    tracked entry: SegmentEntry,
    store: VmStore<'rcu>,
    sid: SegmentId,
)
    requires
        store.inv(),
        store.segments.contains_key(sid),
        entry == store.segments[sid],
        *old(regions) == store.regions,
    ensures
        final(regions).inv(),
        final(regions).slots == old(regions).slots,
        forall|paddr: Paddr|
            #![trigger frame_to_index(paddr)]
            (entry.range.start <= paddr < entry.range.end && paddr % PAGE_SIZE == 0) ==> {
                let idx = frame_to_index(paddr);
                let so_old = old(regions).slot_owners[idx];
                let so_new = final(regions).slot_owners[idx];
                &&& so_old.ref_count() >= 1
                &&& so_old.ref_count() <= REF_COUNT_MAX
                &&& so_old.usage is Frame
                &&& so_old.ref_count() == 1 ==> so_old.paths_in_pt.is_empty()
                &&& so_new.usage == so_old.usage
                &&& so_new.paths_in_pt == so_old.paths_in_pt
                &&& so_new.slot_vaddr == so_old.slot_vaddr
                &&& so_new.in_list_perm == so_old.in_list_perm
                &&& so_old.ref_count() == 1 ==> so_new.ref_count() == REF_COUNT_UNUSED
                &&& so_old.ref_count() > 1 ==> so_new.ref_count() == (so_old.ref_count() - 1) as u64
            },
        forall|i: int|
            #![trigger final(regions).slot_owners[i]]
            i < max_meta_slots() && !(entry.range.start <= index_to_frame(i) < entry.range.end)
                ==> final(regions).slot_owners[i] == old(regions).slot_owners[i],
        forall|i: int|
            #![trigger final(regions).slot_owners[i]]
            !old(regions).slots.contains_key(i) ==> final(regions).slot_owners[i] == old(
                regions,
            ).slot_owners[i],
        forall|c: CursorOwner<'_, UserPtConfig>|
            #![auto]
            c.metaregion_sound(*old(regions)) ==> c.metaregion_sound(*final(regions)),
{
    reveal(VmStore::structural_inv);
    reveal(VmStore::accounting_inv);
    assert forall|paddr: Paddr|
        #![trigger store.regions.slot_owner(paddr)]
        (entry.range.start <= paddr < entry.range.end && paddr % PAGE_SIZE == 0) implies {
        let so = store.regions.slot_owner(paddr);
        &&& so.ref_count() >= 1
        &&& so.ref_count() <= REF_COUNT_MAX
        &&& so.usage is Frame
        &&& so.ref_count() == 1 ==> so.paths_in_pt.is_empty()
    } by {
        let idx = frame_to_index(paddr);
        lemma_segment_cover_contains(store.segments, sid, paddr);
        let so = store.regions.slot_owners[idx];
        let rc = so.ref_count();
        assert(store.regions.contains(idx));
        if rc == 1 {
        }
    };
    segment::drop_step(regions, entry);
}

/// `Op::SegmentDrop` step.
#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
proof fn lemma_step_segment_drop<'rcu>(tracked s: &mut VmStore<'rcu>, sid: SegmentId)
    requires
        old(s).inv(),
        old(s).segments.contains_key(sid),
    ensures
        final(s).inv(),
{
    reveal(VmStore::structural_inv);
    reveal(VmStore::accounting_inv);
    let ghost s_before = *s;
    let ghost old_regions = s.regions;
    let ghost old_frames = s.frames;
    let ghost old_segments = s.segments;
    let ghost range = s.segments[sid].range;
    let tracked entry = s.tracked_extract_segment(sid);
    assert(entry.range == range);
    lemma_drop_segment_with_store_inv(&mut s.regions, entry, s_before, sid);
    lemma_coverage_preserved_slots_eq(s_before, *s);

    assert forall|idx: int|
        0 <= idx
            < max_meta_slots() implies #[trigger] s.regions.slot_owners[idx].in_list_perm.value()
        == 0 by {
        reveal(VmStore::structural_inv);
        let paddr = index_to_frame(idx);
        assert(paddr == (idx * PAGE_SIZE) as usize);
        assert(paddr % PAGE_SIZE == 0);
        assert(frame_to_index(paddr) == idx);
        if range.start <= paddr < range.end {
        } else {
            assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
        }
    };
    assert forall|idx: int|
        #![trigger s.regions.slot_owners[idx]]
        0 <= idx < max_meta_slots() && s.regions.ref_count(idx)
            == REF_COUNT_UNUSED implies handle_count(s.frames, idx) == 0
        && s.regions.slot_owners[idx].paths_in_pt.is_empty() && segment_cover_count(
        s.segments,
        index_to_frame(idx),
    ) == 0 by {
        reveal(VmStore::accounting_inv);
        let paddr = index_to_frame(idx);
        assert(paddr == (idx * PAGE_SIZE) as usize);
        assert(paddr % PAGE_SIZE == 0);
        assert(frame_to_index(paddr) == idx);
        if range.start <= paddr < range.end {
            lemma_segment_cover_contains(old_segments, sid, paddr);
            lemma_segment_cover_remove_inside(old_segments, sid, paddr);
            assert(old_regions.ref_count(idx) == 1);
            assert(handle_count(old_frames, idx) == 0);
            assert(s.regions.slot_owners[idx].paths_in_pt == Set::empty());
        } else {
            assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
            assert(!(entry.range.start <= paddr < entry.range.end));
            lemma_segment_cover_remove_outside(old_segments, sid, paddr);
        }
    };
    assert forall|idx: int|
        #![trigger s.regions.slot_owners[idx]]
        0 <= idx < max_meta_slots() && s.regions.slot_owners[idx].usage is Frame
            && s.regions.ref_count(idx) != REF_COUNT_UNUSED && s.regions.ref_count(idx)
            != REF_COUNT_UNIQUE implies handle_count(s.frames, idx) > 0
        || s.regions.slot_owners[idx].paths_in_pt.len() > 0 || segment_cover_count(
        s.segments,
        index_to_frame(idx),
    ) > 0 by {
        reveal(VmStore::accounting_inv);
        let paddr = index_to_frame(idx);
        assert(paddr == (idx * PAGE_SIZE) as usize);
        assert(paddr % PAGE_SIZE == 0);
        assert(frame_to_index(paddr) == idx);
        if range.start <= paddr < range.end {
            lemma_segment_cover_contains(old_segments, sid, paddr);
            lemma_segment_cover_remove_inside(old_segments, sid, paddr);
        } else {
            assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
            assert(!(entry.range.start <= paddr < entry.range.end));
            lemma_segment_cover_remove_outside(old_segments, sid, paddr);
        }
    };
    assert forall|idx: int|
        #![trigger s.regions.slot_owners[idx]]
        0 <= idx < max_meta_slots() && s.regions.slot_owners[idx].usage is Frame && (handle_count(
            s.frames,
            idx,
        ) > 0 || s.regions.slot_owners[idx].paths_in_pt.len() > 0 || segment_cover_count(
            s.segments,
            index_to_frame(idx),
        ) > 0) implies {
        let so = s.regions.slot_owners[idx];
        let rc = so.ref_count();
        &&& rc != REF_COUNT_UNUSED
        &&& rc != REF_COUNT_UNIQUE
        &&& rc == handle_count(s.frames, idx) + so.paths_in_pt.len() + segment_cover_count(
            s.segments,
            index_to_frame(idx),
        )
    } by {
        reveal(VmStore::accounting_inv);
        let paddr = index_to_frame(idx);
        assert(paddr == (idx * PAGE_SIZE) as usize);
        assert(paddr % PAGE_SIZE == 0);
        assert(frame_to_index(paddr) == idx);
        if range.start <= paddr < range.end {
            lemma_segment_cover_contains(old_segments, sid, paddr);
            lemma_segment_cover_remove_inside(old_segments, sid, paddr);
            // Pre eq: pre rc == pre H + pre P + pre cover.
            let pre_rc = old_regions.ref_count(idx);
            let pre_H = handle_count(old_frames, idx);
            let pre_P = old_regions.slot_owners[idx].paths_in_pt.len();
            let pre_cover = segment_cover_count(old_segments, paddr);
            assert(pre_rc == pre_H + pre_P + pre_cover);
            assert(pre_rc != REF_COUNT_UNIQUE);
            let post_rc = s.regions.ref_count(idx);
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
            assert(s.regions.contains(idx));
            assert(s.regions.slot_owners[idx].metadata_perm.not_empty()
                ==> s.regions.slot_owners[idx].storage_perm().is_init());
        } else {
            assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
            assert(!(entry.range.start <= paddr < entry.range.end));
            lemma_segment_cover_remove_outside(old_segments, sid, paddr);
        }
    };
    assert forall|fid_other: FrameId| #[trigger]
        s.frames.contains_key(fid_other) implies s.regions.slot_owner(
        s.frames[fid_other].paddr,
    ).usage is Frame by {
        reveal(VmStore::structural_inv);
        reveal(VmStore::accounting_inv);
        let other_idx = frame_to_index(s.frames[fid_other].paddr);
        let other_paddr = index_to_frame(other_idx);
        assert(old_regions.slot_owners[other_idx].usage is Frame);
        assert(old_frames.dom().filter(
            |gid: FrameId| frame_to_index(old_frames[gid].paddr) == other_idx,
        ).contains(fid_other));
        assert(handle_count(old_frames, other_idx) >= 1);
        assert(old_regions.slot_owners[other_idx].ref_count() >= 1);
        if range.start <= other_paddr < range.end {
        } else {
            assert(s.regions.slot_owners[other_idx] == old_regions.slot_owners[other_idx]);
        }
    };
    assert forall|sid_other: SegmentId, paddr_c: Paddr|
        #![trigger
            s.segments.contains_key(sid_other),
            frame_to_index(paddr_c)]
        s.segments.contains_key(sid_other) && s.segments[sid_other].range.start <= paddr_c
            < s.segments[sid_other].range.end && paddr_c % PAGE_SIZE
            == 0 implies s.regions.slot_owner(paddr_c).usage is Frame by {
        reveal(VmStore::structural_inv);
        let cov_idx = frame_to_index(paddr_c);
        assert(sid_other != sid);
        assert(old_segments.contains_key(sid_other));
        assert(old_segments[sid_other] == s.segments[sid_other]);
        assert(old_regions.slot_owners[cov_idx].usage is Frame);
    };
    assert forall|u: UniqueId| #[trigger] s.unique_frames.contains_key(u) implies {
        let so = s.regions.slot_owner(s.unique_frames[u].paddr);
        &&& so.usage is Frame
        &&& so.ref_count() == REF_COUNT_UNIQUE
        &&& so.in_list_perm.value() == 0
        &&& so.paths_in_pt.is_empty()
    } by {
        reveal(VmStore::structural_inv);
        reveal(VmStore::accounting_inv);
        let u_paddr = s.unique_frames[u].paddr;
        let u_idx = frame_to_index(u_paddr);
        assert(old(s).unique_frames.contains_key(u));
        assert(valid_frame_paddr(u_paddr));
        s.regions.lemma_contains_valid_frame_paddr(u_paddr);
        // Old UNIQUE validity at `u`.
        assert(old_regions.slot_owners[u_idx].ref_count() == REF_COUNT_UNIQUE);
        assert(old_regions.slot_owners[u_idx].usage is Frame);
        // UNIQUE ⟹ uncovered ⟹ not in the dropped segment's range.
        assert(!(range.start <= u_paddr < range.end)) by {
            if range.start <= u_paddr < range.end {
                lemma_segment_cover_contains(old_segments, sid, u_paddr);
            }
        };
        // Outside range ⟹ teardown axiom preserves the slot fully.
        assert(s.regions.slot_owners[u_idx] == old_regions.slot_owners[u_idx]);
    };
    lemma_accounting_inv_intro(*s);
    assert(s.structural_inv()) by {
        reveal(VmStore::structural_inv);
    };
}

/// `Op::SegmentSplit` step.
proof fn lemma_step_segment_split<'rcu>(
    tracked s: &mut VmStore<'rcu>,
    sid: SegmentId,
    offset: usize,
)
    requires
        old(s).inv(),
        old(s).segments.contains_key(sid),
        offset % PAGE_SIZE == 0,
        0 < offset,
        offset < (old(s).segments[sid].range.end - old(s).segments[sid].range.start),
    ensures
        final(s).inv(),
{
    reveal(VmStore::structural_inv);
    reveal(VmStore::accounting_inv);
    let ghost old_regions = s.regions;
    let ghost old_frames = s.frames;
    let ghost old_segments = s.segments;
    let ghost range = s.segments[sid].range;
    let ghost mid = (range.start + offset) as Paddr;
    let ghost entry_left = SegmentEntry { range: range.start..mid };
    let ghost entry_right = SegmentEntry { range: mid..range.end };
    let ghost id_left = fresh_segment_id(s.segments);
    lemma_fresh_segment_id_not_in_dom(s.segments);
    assert(id_left != sid);
    let ghost stub_entry = SegmentEntry { range: range.start..mid };
    let ghost id_right = fresh_segment_id(s.segments.insert(id_left, stub_entry));
    lemma_fresh_segment_id_not_in_dom(s.segments.insert(id_left, stub_entry));
    assert(id_right != sid);
    assert(id_right != id_left);
    // Now extract and insert.
    let tracked _orig = s.tracked_extract_segment(sid);
    assert(!s.segments.contains_key(id_left));
    let tracked entry_l = tracked_segment_entry_new(range.start..mid);
    s.lemma_insert_segment(id_left, entry_l);
    assert(!s.segments.contains_key(id_right));
    let tracked entry_r = tracked_segment_entry_new(mid..range.end);
    s.lemma_insert_segment(id_right, entry_r);
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
    assert(entry_left.range.start % PAGE_SIZE == 0);
    assert(entry_right.range.start % PAGE_SIZE == 0);
    assert(entry_left.range.end % PAGE_SIZE == 0);
    assert(entry_right.range.end % PAGE_SIZE == 0);
    assert forall|sid_other: SegmentId, paddr_c: Paddr|
        #![trigger
            s.segments.contains_key(sid_other),
            frame_to_index(paddr_c)]
        s.segments.contains_key(sid_other) && s.segments[sid_other].range.start <= paddr_c
            < s.segments[sid_other].range.end && paddr_c % PAGE_SIZE
            == 0 implies s.regions.slot_owner(paddr_c).usage is Frame by {
        if sid_other == id_left {
            assert(old_segments.contains_key(sid));
            assert(old_segments[sid].range.start <= paddr_c < old_segments[sid].range.end);
        } else if sid_other == id_right {
            assert(old_segments.contains_key(sid));
            assert(old_segments[sid].range.start <= paddr_c < old_segments[sid].range.end);
        } else {
            assert(old_segments.contains_key(sid_other));
            assert(old_segments[sid_other] == s.segments[sid_other]);
        }
    };
    assert forall|idx: int|
        #![trigger s.regions.slot_owners[idx]]
        0 <= idx < max_meta_slots() && s.regions.ref_count(idx)
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
    assert forall|idx: int|
        #![trigger s.regions.slot_owners[idx]]
        0 <= idx < max_meta_slots() && s.regions.slot_owners[idx].usage is Frame
            && s.regions.ref_count(idx) != REF_COUNT_UNUSED && s.regions.ref_count(idx)
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
    assert forall|idx: int|
        #![trigger s.regions.slot_owners[idx]]
        0 <= idx < max_meta_slots() && s.regions.slot_owners[idx].usage is Frame && (handle_count(
            s.frames,
            idx,
        ) > 0 || s.regions.slot_owners[idx].paths_in_pt.len() > 0 || segment_cover_count(
            s.segments,
            index_to_frame(idx),
        ) > 0) implies {
        let so = s.regions.slot_owners[idx];
        let rc = so.ref_count();
        &&& rc != REF_COUNT_UNUSED
        &&& rc != REF_COUNT_UNIQUE
        &&& rc == handle_count(s.frames, idx) + so.paths_in_pt.len() + segment_cover_count(
            s.segments,
            index_to_frame(idx),
        )
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

/// `Op::SegmentNext` step.
#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
proof fn lemma_step_segment_next<'rcu>(tracked s: &mut VmStore<'rcu>, sid: SegmentId)
    requires
        old(s).inv(),
        old(s).segments.contains_key(sid),
    ensures
        final(s).inv(),
{
    reveal(VmStore::structural_inv);
    reveal(VmStore::accounting_inv);
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
    let ghost so_pre = old_regions.slot_owners[target_idx];
    let ghost pre_rc = so_pre.ref_count();
    let ghost pre_H = handle_count(old_frames, target_idx);
    let ghost pre_P = so_pre.paths_in_pt.len();
    let ghost pre_cover = segment_cover_count(old_segments, paddr);
    s.regions.lemma_contains_valid_frame_paddr(paddr);

    // Register the new FrameEntry FIRST (s.inv() still holds).
    let ghost fid = fresh_frame_id(s.frames);
    lemma_fresh_frame_id_not_in_dom(s.frames);
    let tracked frame_entry = tracked_frame_entry_new(paddr);
    s.lemma_insert_frame(fid, frame_entry);
    // Now segment manipulation.
    let tracked _old_entry = s.tracked_extract_segment(sid);
    if !will_become_empty {
        let tracked new_entry = tracked_segment_entry_new(new_range_start..new_range_end);
        s.lemma_insert_segment(sid, new_entry);
    } else {
    }
    assert(s.frames == old_frames.insert(fid, frame_entry));

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

    if !will_become_empty {
    }
    assert forall|idx: int|
        #![trigger s.regions.slot_owners[idx]]
        0 <= idx < max_meta_slots() && s.regions.ref_count(idx)
            == REF_COUNT_UNUSED implies handle_count(s.frames, idx) == 0
        && s.regions.slot_owners[idx].paths_in_pt.is_empty() && segment_cover_count(
        s.segments,
        index_to_frame(idx),
    ) == 0 by {
        let paddr_c = index_to_frame(idx);
        if idx == target_idx {
            lemma_segment_cover_contains(old_segments, sid, paddr);
            assert(false);
        } else {
            lemma_handle_count_insert_fresh(old_frames, fid, frame_entry, idx);
        }
    };
    assert forall|idx: int|
        #![trigger s.regions.slot_owners[idx]]
        0 <= idx < max_meta_slots() && s.regions.slot_owners[idx].usage is Frame
            && s.regions.ref_count(idx) != REF_COUNT_UNUSED && s.regions.ref_count(idx)
            != REF_COUNT_UNIQUE implies handle_count(s.frames, idx) > 0
        || s.regions.slot_owners[idx].paths_in_pt.len() > 0 || segment_cover_count(
        s.segments,
        index_to_frame(idx),
    ) > 0 by {
        let paddr_c = index_to_frame(idx);
        if idx == target_idx {
            // New fid gives H >= 1.
            lemma_handle_count_insert_fresh(old_frames, fid, frame_entry, idx);
        } else {
            lemma_handle_count_insert_fresh(old_frames, fid, frame_entry, idx);
        }
    };
    assert forall|idx: int|
        #![trigger s.regions.slot_owners[idx]]
        0 <= idx < max_meta_slots() && s.regions.slot_owners[idx].usage is Frame && (handle_count(
            s.frames,
            idx,
        ) > 0 || s.regions.slot_owners[idx].paths_in_pt.len() > 0 || segment_cover_count(
            s.segments,
            index_to_frame(idx),
        ) > 0) implies {
        let so = s.regions.slot_owners[idx];
        let rc = so.ref_count();
        &&& rc != REF_COUNT_UNUSED
        &&& rc != REF_COUNT_UNIQUE
        &&& rc == handle_count(s.frames, idx) + so.paths_in_pt.len() + segment_cover_count(
            s.segments,
            index_to_frame(idx),
        )
    } by {
        let paddr_c = index_to_frame(idx);
        lemma_handle_count_insert_fresh(old_frames, fid, frame_entry, idx);
        if idx == target_idx {
        } else {
        }
    };
    assert forall|u: UniqueId| #[trigger] s.unique_frames.contains_key(u) implies {
        let so = s.regions.slot_owner(s.unique_frames[u].paddr);
        &&& so.usage is Frame
        &&& so.ref_count() == REF_COUNT_UNIQUE
        &&& so.in_list_perm.value() == 0
        &&& so.paths_in_pt.is_empty()
    } by {};
}

#[verifier::spinoff_prover]
proof fn lemma_step_segment_clone_range<'rcu>(
    tracked s: &mut VmStore<'rcu>,
    sid: SegmentId,
    sub_range: Range<Paddr>,
)
    requires
        old(s).inv(),
        old(s).segments.contains_key(sid),
        sub_range.start % PAGE_SIZE == 0,
        sub_range.end % PAGE_SIZE == 0,
        old(s).segments[sid].range.start <= sub_range.start,
        sub_range.start < sub_range.end,
        sub_range.end <= old(s).segments[sid].range.end,
        forall|paddr: Paddr|
            #![trigger frame_to_index(paddr)]
            (sub_range.start <= paddr < sub_range.end && paddr % PAGE_SIZE == 0) ==> old(
                s,
            ).regions.slot_owner(paddr).ref_count() + 1 <= REF_COUNT_MAX,
    ensures
        final(s).inv(),
{
    // Keep the opaque pre-state invariants pointwise throughout this proof.
    let ghost s_before = *s;
    assert(s.regions.inv());
    let ghost old_regions = s.regions;
    let ghost old_frames = s.frames;
    let ghost old_segments = s.segments;
    let ghost sid_range = s.segments[sid].range;
    let ghost new_entry_ghost = SegmentEntry { range: sub_range };

    assert(sid_range.end <= MAX_PADDR) by {
        reveal(VmStore::structural_inv);
    };
    assert(sub_range.end <= MAX_PADDR);

    assert forall|paddr: Paddr|
        #![trigger frame_to_index(paddr)]
        (sub_range.start <= paddr < sub_range.end && paddr % PAGE_SIZE == 0) implies {
        let so = old_regions.slot_owner(paddr);
        &&& so.usage is Frame
        &&& so.ref_count() >= 1
        &&& so.ref_count() + 1 <= REF_COUNT_MAX
    } by {
        // `paddr` is covered by `sid` (sub_range ⊆ sid's range).
        assert(old_segments.contains_key(sid));
        assert(sid_range.start <= paddr < sid_range.end);
        lemma_structural_inv_segment(s_before, sid, paddr);
        s_before.regions.lemma_contains_valid_frame_paddr(paddr);
        let idx = frame_to_index(paddr);
        lemma_accounting_inv_at(s_before, idx);
        lemma_segment_cover_contains(old_segments, sid, paddr);
        assert(segment_cover_count(old_segments, paddr) >= 1);
        // Active head (cover > 0) ⟹ accounting equation gives rc >= cover >= 1.
    };

    // Bump `rc` at every frame in `sub_range`.
    segment::segment_clone_embedded(&mut s.regions, sub_range);

    // Insert the fresh covering entry at a fresh id.
    let ghost sid2 = fresh_segment_id(s.segments);
    lemma_fresh_segment_id_not_in_dom(s.segments);
    assert(sid2 != sid);
    let tracked new_entry = tracked_segment_entry_new(sub_range);
    s.lemma_insert_segment(sid2, new_entry);
    assert(new_entry =~= new_entry_ghost);
    assert(s.segments =~= old_segments.insert(sid2, new_entry_ghost));
    assert(s.frames == old_frames);

    // --- per-paddr cover delta: +1 inside sub_range, unchanged outside ---
    assert forall|paddr_c: Paddr|
        paddr_c % PAGE_SIZE == 0 && sub_range.start <= paddr_c
            < sub_range.end implies #[trigger] segment_cover_count(s.segments, paddr_c)
        == segment_cover_count(old_segments, paddr_c) + 1 by {
        lemma_segment_cover_insert_inside(old_segments, sid2, new_entry_ghost, paddr_c);
    };
    assert forall|paddr_c: Paddr|
        paddr_c % PAGE_SIZE == 0 && !(sub_range.start <= paddr_c
            < sub_range.end) implies #[trigger] segment_cover_count(s.segments, paddr_c)
        == segment_cover_count(old_segments, paddr_c) by {
        lemma_segment_cover_insert_outside(old_segments, sid2, new_entry_ghost, paddr_c);
    };

    // --- per-slot regions delta: usage / in_list preserved everywhere ---
    // `usage` is preserved at every slot (inside: usage clause of the
    // axiom; outside: full slot preservation).
    assert forall|idx: int|
        0 <= idx < max_meta_slots() implies #[trigger] s.regions.slot_owners[idx].usage
        == old_regions.slot_owners[idx].usage by {
        let aligned = index_to_frame(idx);
        assert(aligned == (idx * PAGE_SIZE) as usize);
        assert(frame_to_index(aligned) == idx);
        if sub_range.start <= aligned < sub_range.end {
            // inside: axiom preserves usage at `aligned`.
        } else {
            assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
        }
    };
    // `in_list == 0` at every slot (preserved by the axiom both ways).
    assert forall|idx: int|
        0 <= idx
            < max_meta_slots() implies #[trigger] s.regions.slot_owners[idx].in_list_perm.value()
        == 0 by {
        assert(old_regions.slot_owners[idx].in_list_perm.value() == 0) by {
            reveal(VmStore::structural_inv);
        };
        let aligned = index_to_frame(idx);
        assert(aligned == (idx * PAGE_SIZE) as usize);
        assert(frame_to_index(aligned) == idx);
        if sub_range.start <= aligned < sub_range.end {
            // inside: axiom preserves in_list at `aligned`.
        } else {
            assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
        }
    };

    // --- structural: segment-covered ⟹ Frame-usage ---
    assert forall|sid_other: SegmentId, paddr_c: Paddr|
        #![trigger
            s.segments.contains_key(sid_other),
            frame_to_index(paddr_c)]
        s.segments.contains_key(sid_other) && s.segments[sid_other].range.start <= paddr_c
            < s.segments[sid_other].range.end && paddr_c % PAGE_SIZE
            == 0 implies s.regions.slot_owner(paddr_c).usage is Frame by {
        let cov_idx = frame_to_index(paddr_c);
        if sid_other == sid2 {
            // Covered by the new entry ⟹ in sub_range ⊆ sid's range.
            assert(s.segments[sid2].range == sub_range);
            assert(old_segments.contains_key(sid));
            assert(sid_range.start <= paddr_c < sid_range.end);
            lemma_structural_inv_segment(s_before, sid, paddr_c);
        } else {
            assert(old_segments.contains_key(sid_other));
            assert(old_segments[sid_other] == s.segments[sid_other]);
            lemma_structural_inv_segment(s_before, sid_other, paddr_c);
        }
        assert(valid_frame_paddr(paddr_c));
        s.regions.lemma_contains_valid_frame_paddr(paddr_c);
        assert(s.regions.contains(cov_idx));
    };

    // --- structural: FrameId ⟹ Frame-usage (frames unchanged) ---
    assert forall|fid_other: FrameId| #[trigger]
        s.frames.contains_key(fid_other) implies s.regions.slot_owner(
        s.frames[fid_other].paddr,
    ).usage is Frame by {
        let other_idx = frame_to_index(s.frames[fid_other].paddr);
        lemma_structural_inv_frame(s_before, fid_other);
        s.regions.lemma_contains_valid_frame_paddr(s.frames[fid_other].paddr);
        assert(s.regions.contains(other_idx));
    };

    // --- accounting clause 1: UNUSED ⟹ no users ---
    assert forall|idx: int|
        #![trigger s.regions.slot_owners[idx]]
        0 <= idx < max_meta_slots() && s.regions.ref_count(idx)
            == REF_COUNT_UNUSED implies handle_count(s.frames, idx) == 0
        && s.regions.slot_owners[idx].paths_in_pt.is_empty() && segment_cover_count(
        s.segments,
        index_to_frame(idx),
    ) == 0 by {
        lemma_accounting_inv_at(s_before, idx);
        let aligned = index_to_frame(idx);
        assert(aligned == (idx * PAGE_SIZE) as usize);
        assert(frame_to_index(aligned) == idx);
        if sub_range.start <= aligned < sub_range.end {
            // post rc == pre rc + 1 <= REF_COUNT_MAX < UNUSED. Antecedent false.
            assert(false);
        } else {
            assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
        }
    };
    // --- accounting clause 2: valid rc ⟹ active head ---
    assert forall|idx: int|
        #![trigger s.regions.slot_owners[idx]]
        0 <= idx < max_meta_slots() && s.regions.slot_owners[idx].usage is Frame
            && s.regions.ref_count(idx) != REF_COUNT_UNUSED && s.regions.ref_count(idx)
            != REF_COUNT_UNIQUE implies handle_count(s.frames, idx) > 0
        || s.regions.slot_owners[idx].paths_in_pt.len() > 0 || segment_cover_count(
        s.segments,
        index_to_frame(idx),
    ) > 0 by {
        lemma_accounting_inv_at(s_before, idx);
        let aligned = index_to_frame(idx);
        assert(aligned == (idx * PAGE_SIZE) as usize);
        assert(frame_to_index(aligned) == idx);
        if sub_range.start <= aligned < sub_range.end {
            // cover_post >= cover_pre + 1 >= 1 > 0 ⟹ third disjunct.
        } else {
            assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
        }
    };
    // --- accounting clause 3: the rc equation ---
    assert forall|idx: int|
        #![trigger s.regions.slot_owners[idx]]
        0 <= idx < max_meta_slots() && s.regions.slot_owners[idx].usage is Frame && (handle_count(
            s.frames,
            idx,
        ) > 0 || s.regions.slot_owners[idx].paths_in_pt.len() > 0 || segment_cover_count(
            s.segments,
            index_to_frame(idx),
        ) > 0) implies {
        let so = s.regions.slot_owners[idx];
        let rc = so.ref_count();
        &&& rc != REF_COUNT_UNUSED
        &&& rc != REF_COUNT_UNIQUE
        &&& rc == handle_count(s.frames, idx) + so.paths_in_pt.len() + segment_cover_count(
            s.segments,
            index_to_frame(idx),
        )
    } by {
        lemma_accounting_inv_at(s_before, idx);
        let aligned = index_to_frame(idx);
        assert(aligned == (idx * PAGE_SIZE) as usize);
        assert(frame_to_index(aligned) == idx);
        assert(s.regions.slot_owners.contains_key(idx));
        assert(s.regions.slots.contains_key(idx));
        assert(s.regions.slot_owners[idx].inv());
        if sub_range.start <= aligned < sub_range.end {
            assert(0 < s.regions.ref_count(idx) <= REF_COUNT_MAX);
        } else {
            assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
        }
        let so = s.regions.slot_owners[idx];
        let rc = so.ref_count();
        assert(rc == handle_count(s.frames, idx) + so.paths_in_pt.len() + segment_cover_count(
            s.segments,
            aligned,
        ));
        assert(0 < rc <= REF_COUNT_MAX);
    };
    assert forall|u: UniqueId| #[trigger] s.unique_frames.contains_key(u) implies {
        let so = s.regions.slot_owner(s.unique_frames[u].paddr);
        &&& so.usage is Frame
        &&& so.ref_count() == REF_COUNT_UNIQUE
        &&& so.in_list_perm.value() == 0
        &&& so.paths_in_pt.is_empty()
    } by {
        let u_paddr = s.unique_frames[u].paddr;
        let u_idx = frame_to_index(u_paddr);
        assert(s_before.unique_frames.contains_key(u));
        assert(valid_frame_paddr(u_paddr) && old_regions.slot_owners[u_idx].ref_count()
            == REF_COUNT_UNIQUE && old_regions.slot_owners[u_idx].usage is Frame
            && old_regions.slot_owners[u_idx].in_list_perm.value() == 0
            && old_regions.slot_owners[u_idx].paths_in_pt.is_empty()) by {
            reveal(VmStore::structural_inv);
        };
        s.regions.lemma_contains_valid_frame_paddr(u_paddr);
        assert(!(sub_range.start <= u_paddr < sub_range.end)) by {
            if sub_range.start <= u_paddr < sub_range.end {
                // u_paddr ∈ sub_range ⊆ sid_range ⟹ sid covers u_paddr.
                assert(sid_range.start <= u_paddr < sid_range.end);
                lemma_segment_cover_contains(old_segments, sid, u_paddr);
            }
        };
        assert(s.regions.slot_owners[u_idx] == old_regions.slot_owners[u_idx]);
    };
    lemma_accounting_inv_intro(*s);
    assert(s.structural_inv()) by {
        reveal(VmStore::structural_inv);
    };
}

/// `Op::SegmentClone` step.
proof fn lemma_step_segment_clone<'rcu>(tracked s: &mut VmStore<'rcu>, sid: SegmentId)
    requires
        old(s).inv(),
        old(s).segments.contains_key(sid),
        forall|paddr: Paddr|
            #![trigger frame_to_index(paddr)]
            (old(s).segments[sid].range.start <= paddr < old(s).segments[sid].range.end && paddr
                % PAGE_SIZE == 0) ==> old(s).regions.slot_owner(paddr).ref_count() + 1
                <= REF_COUNT_MAX,
    ensures
        final(s).inv(),
{
    reveal(VmStore::structural_inv);
    let ghost r = s.segments[sid].range;
    assert(r.start % PAGE_SIZE == 0);
    assert(r.end % PAGE_SIZE == 0);
    assert(r.start < r.end);
    assert(r.end <= MAX_PADDR);
    lemma_step_segment_clone_range(s, sid, r);
}

/// `Op::SegmentSlice` step.
proof fn lemma_step_segment_slice<'rcu>(
    tracked s: &mut VmStore<'rcu>,
    sid: SegmentId,
    sub_range: Range<Paddr>,
)
    requires
        old(s).inv(),
        old(s).segments.contains_key(sid),
        sub_range.start % PAGE_SIZE == 0,
        sub_range.end % PAGE_SIZE == 0,
        old(s).segments[sid].range.start <= sub_range.start,
        sub_range.start < sub_range.end,
        sub_range.end <= old(s).segments[sid].range.end,
        forall|paddr: Paddr|
            #![trigger frame_to_index(paddr)]
            (sub_range.start <= paddr < sub_range.end && paddr % PAGE_SIZE == 0) ==> old(
                s,
            ).regions.slot_owner(paddr).ref_count() + 1 <= REF_COUNT_MAX,
    ensures
        final(s).inv(),
{
    lemma_step_segment_clone_range(s, sid, sub_range);
}

proof fn lemma_step_unique_from_unused<'rcu>(tracked s: &mut VmStore<'rcu>, paddr: Paddr)
    requires
        old(s).inv(),
    ensures
        final(s).inv(),
{
    reveal(VmStore::structural_inv);
    reveal(VmStore::accounting_inv);
    if valid_frame_paddr(paddr) && s.regions.slots.contains_key(frame_to_index(paddr))
        && s.regions.slot_owner(paddr).usage is Unused && s.regions.slot_owner(paddr).ref_count()
        == REF_COUNT_UNUSED {
        let ghost old_regions = s.regions;
        let ghost old_frames = s.frames;
        let ghost old_segments = s.segments;
        let ghost old_unique = s.unique_frames;
        let ghost idx = frame_to_index(paddr);

        // `idx` in range; `paddr` is its page base.
        s.regions.lemma_contains_valid_frame_paddr(paddr);
        assert(s.regions.contains(idx));
        assert(index_to_frame(idx) == paddr);

        // Pre "no users" facts at the UNUSED slot (accounting clause 1).
        assert(handle_count(old_frames, idx) == 0);
        assert(old_regions.slot_owners[idx].paths_in_pt.is_empty());
        assert(segment_cover_count(old_segments, index_to_frame(idx)) == 0);

        // Transition the slot UNUSED → UNIQUE.
        unique::unique_from_unused_embedded(&mut s.regions, paddr);

        // Register the fresh UniqueEntry at a fresh id.
        let ghost uid = fresh_unique_id(s.unique_frames);
        lemma_fresh_unique_id_not_in_dom(s.unique_frames);
        let tracked entry = tracked_unique_entry_new(paddr);
        s.lemma_insert_unique(uid, entry);
        assert(s.unique_frames =~= old_unique.insert(uid, UniqueEntry { paddr }));
        assert(s.frames == old_frames);
        assert(s.segments == old_segments);

        // --- structural: in_list == 0 everywhere ---
        assert forall|i: int|
            0 <= i
                < max_meta_slots() implies #[trigger] s.regions.slot_owners[i].in_list_perm.value()
            == 0 by {
            if i != idx {
                assert(s.regions.slot_owners[i] == old_regions.slot_owners[i]);
            }
        };
        // --- structural: FrameId ⟹ Frame-usage ---
        assert forall|fid: FrameId| #[trigger]
            s.frames.contains_key(fid) implies s.regions.slot_owner(
            s.frames[fid].paddr,
        ).usage is Frame by {
            let other_idx = frame_to_index(s.frames[fid].paddr);
            assert(old_frames.contains_key(fid));
            assert(old_regions.slot_owners[other_idx].usage is Frame);
            if other_idx == idx {
                // Pre `idx` was `Unused`-usage — no `FrameEntry` maps there.
                assert(false);
            }
        };
        // --- structural: segment-covered ⟹ Frame-usage ---
        assert forall|sid: SegmentId, paddr_c: Paddr|
            #![trigger s.segments.contains_key(sid), frame_to_index(paddr_c)]
            s.segments.contains_key(sid) && s.segments[sid].range.start <= paddr_c
                < s.segments[sid].range.end && paddr_c % PAGE_SIZE
                == 0 implies s.regions.slot_owner(paddr_c).usage is Frame by {
            let cov_idx = frame_to_index(paddr_c);
            assert(old_segments.contains_key(sid));
            assert(old_regions.slot_owners[cov_idx].usage is Frame);
            if cov_idx == idx {
                assert(false);
            }
        };
        // --- structural: unique-entry validity ---
        assert forall|u: UniqueId| #[trigger] s.unique_frames.contains_key(u) implies {
            let so = s.regions.slot_owner(s.unique_frames[u].paddr);
            &&& so.usage is Frame
            &&& so.ref_count() == REF_COUNT_UNIQUE
            &&& so.in_list_perm.value() == 0
            &&& so.paths_in_pt.is_empty()
        } by {
            let u_idx = frame_to_index(s.unique_frames[u].paddr);
            if u == uid {
                assert(s.unique_frames[u].paddr == paddr);
                assert(u_idx == idx);
            } else {
                assert(old_unique.contains_key(u));
                assert(s.unique_frames[u] == old_unique[u]);
                assert(old_regions.slot_owners[u_idx].ref_count() == REF_COUNT_UNIQUE);
                assert(u_idx != idx);
                assert(s.regions.slot_owners[u_idx] == old_regions.slot_owners[u_idx]);
            }
        };
        // --- structural: unique valid_frame_paddr ---
        assert forall|u: UniqueId| #[trigger]
            s.unique_frames.contains_key(u) implies valid_frame_paddr(s.unique_frames[u].paddr) by {
            if u != uid {
                assert(old_unique.contains_key(u));
            }
        };
        // --- structural: unique injectivity ---
        assert forall|u1: UniqueId, u2: UniqueId|
            #![trigger s.unique_frames.contains_key(u1), s.unique_frames.contains_key(u2)]
            s.unique_frames.contains_key(u1) && s.unique_frames.contains_key(u2)
                && s.unique_frames[u1].paddr == s.unique_frames[u2].paddr implies u1 == u2 by {
            if u1 == uid && u2 != uid {
                assert(old_unique.contains_key(u2));
                assert(s.unique_frames[u2].paddr == paddr);
                assert(frame_to_index(s.unique_frames[u2].paddr) == idx);
                assert(old_regions.ref_count(idx) == REF_COUNT_UNIQUE);
                assert(false);
            } else if u2 == uid && u1 != uid {
                assert(old_unique.contains_key(u1));
                assert(s.unique_frames[u1].paddr == paddr);
                assert(frame_to_index(s.unique_frames[u1].paddr) == idx);
                assert(old_regions.ref_count(idx) == REF_COUNT_UNIQUE);
                assert(false);
            } else if u1 != uid && u2 != uid {
                assert(old_unique.contains_key(u1));
                assert(old_unique.contains_key(u2));
            }
        };

        // --- accounting clause 1: UNUSED ⟹ no users ---
        assert forall|i: int|
            #![trigger s.regions.slot_owners[i]]
            0 <= i < max_meta_slots() && s.regions.ref_count(i)
                == REF_COUNT_UNUSED implies handle_count(s.frames, i) == 0
            && s.regions.slot_owners[i].paths_in_pt.is_empty() && segment_cover_count(
            s.segments,
            index_to_frame(i),
        ) == 0 by {
            if i == idx {
                // post rc at `idx` is UNIQUE, not UNUSED — antecedent false.
                assert(false);
            } else {
                assert(s.regions.slot_owners[i] == old_regions.slot_owners[i]);
            }
        };
        // --- accounting clause 2: valid rc ⟹ active head ---
        assert forall|i: int|
            #![trigger s.regions.slot_owners[i]]
            0 <= i < max_meta_slots() && s.regions.slot_owners[i].usage is Frame
                && s.regions.ref_count(i) != REF_COUNT_UNUSED && s.regions.ref_count(i)
                != REF_COUNT_UNIQUE implies handle_count(s.frames, i) > 0
            || s.regions.slot_owners[i].paths_in_pt.len() > 0 || segment_cover_count(
            s.segments,
            index_to_frame(i),
        ) > 0 by {
            if i == idx {
                assert(false);
            } else {
                assert(s.regions.slot_owners[i] == old_regions.slot_owners[i]);
            }
        };
        assert forall|i: int|
            #![trigger s.regions.slot_owners[i]]
            0 <= i < max_meta_slots() && s.regions.slot_owners[i].usage is Frame && (handle_count(
                s.frames,
                i,
            ) > 0 || s.regions.slot_owners[i].paths_in_pt.len() > 0 || segment_cover_count(
                s.segments,
                index_to_frame(i),
            ) > 0) implies {
            let so = s.regions.slot_owners[i];
            let rc = so.ref_count();
            &&& rc != REF_COUNT_UNUSED
            &&& rc != REF_COUNT_UNIQUE
            &&& rc == handle_count(s.frames, i) + so.paths_in_pt.len() + segment_cover_count(
                s.segments,
                index_to_frame(i),
            )
        } by {
            if i == idx {
                // `idx` is now UNIQUE with no users (H=P=cover=0) — the
                // active-head antecedent is false, so this is vacuous.
                assert(handle_count(s.frames, idx) == 0);
                assert(s.regions.slot_owners[idx].paths_in_pt.is_empty());
                assert(segment_cover_count(s.segments, index_to_frame(idx)) == 0);
            } else {
                assert(s.regions.slot_owners[i] == old_regions.slot_owners[i]);
            }
        };
    }
}

/// `Op::UniqueDrop` step. Tears down the exclusive handle `uid`: the
/// slot transitions `UNIQUE → UNUSED` (uninitialising storage), with
/// `usage` (Frame) / `paths_in_pt` (empty) / `in_list` (0) preserved.
/// `frames` / `segments` untouched.
proof fn lemma_step_unique_drop<'rcu>(tracked s: &mut VmStore<'rcu>, uid: UniqueId)
    requires
        old(s).inv(),
        old(s).unique_frames.contains_key(uid),
    ensures
        final(s).inv(),
{
    reveal(VmStore::structural_inv);
    reveal(VmStore::accounting_inv);
    let ghost old_regions = s.regions;
    let ghost old_frames = s.frames;
    let ghost old_segments = s.segments;
    let ghost old_unique = s.unique_frames;
    let ghost paddr = s.unique_frames[uid].paddr;
    let ghost idx = frame_to_index(paddr);

    // Slot facts from the structural unique-entry clause + the UNIQUE
    // branch of `MetaSlotOwner::inv`.
    s.regions.lemma_contains_valid_frame_paddr(paddr);
    assert(s.regions.contains(idx));
    assert(index_to_frame(idx) == paddr);
    assert(s.regions.slot_owners[idx].usage is Frame);
    assert(s.regions.ref_count(idx) == REF_COUNT_UNIQUE);
    assert(s.regions.slot_owners[idx].in_list_perm.value() == 0);
    assert(s.regions.slot_owners[idx].paths_in_pt.is_empty());

    assert(handle_count(old_frames, idx) == 0) by {
        if handle_count(old_frames, idx) > 0 {
            assert(old_regions.ref_count(idx) != REF_COUNT_UNIQUE);
            assert(false);
        }
    };
    assert(segment_cover_count(old_segments, index_to_frame(idx)) == 0) by {
        if segment_cover_count(old_segments, index_to_frame(idx)) > 0 {
            assert(old_regions.ref_count(idx) != REF_COUNT_UNIQUE);
            assert(false);
        }
    };

    let tracked _entry = s.tracked_extract_unique(uid);
    unique::unique_drop_embedded(&mut s.regions, paddr);
    assert(s.unique_frames =~= old_unique.remove(uid));
    assert(s.frames == old_frames);
    assert(s.segments == old_segments);

    assert forall|i: int|
        0 <= i < max_meta_slots() implies #[trigger] s.regions.slot_owners[i].in_list_perm.value()
        == 0 by {
        if i != idx {
            assert(s.regions.slot_owners[i] == old_regions.slot_owners[i]);
        }
    };
    assert forall|fid: FrameId| #[trigger] s.frames.contains_key(fid) implies s.regions.slot_owner(
        s.frames[fid].paddr,
    ).usage is Frame by {
        let other_idx = frame_to_index(s.frames[fid].paddr);
        assert(old_frames.contains_key(fid));
        assert(old_regions.slot_owners[other_idx].usage is Frame);
        if other_idx != idx {
            assert(s.regions.slot_owners[other_idx] == old_regions.slot_owners[other_idx]);
        }
    };
    assert forall|sid: SegmentId, paddr_c: Paddr|
        #![trigger s.segments.contains_key(sid), frame_to_index(paddr_c)]
        s.segments.contains_key(sid) && s.segments[sid].range.start <= paddr_c
            < s.segments[sid].range.end && paddr_c % PAGE_SIZE == 0 implies s.regions.slot_owner(
        paddr_c,
    ).usage is Frame by {
        let cov_idx = frame_to_index(paddr_c);
        assert(old_segments.contains_key(sid));
        assert(old_regions.slot_owners[cov_idx].usage is Frame);
        if cov_idx != idx {
            assert(s.regions.slot_owners[cov_idx] == old_regions.slot_owners[cov_idx]);
        }
    };
    // --- structural: unique-entry validity (remaining entries) ---
    assert forall|u: UniqueId| #[trigger] s.unique_frames.contains_key(u) implies {
        let so = s.regions.slot_owner(s.unique_frames[u].paddr);
        &&& so.usage is Frame
        &&& so.ref_count() == REF_COUNT_UNIQUE
        &&& so.in_list_perm.value() == 0
        &&& so.paths_in_pt.is_empty()
    } by {
        let u_idx = frame_to_index(s.unique_frames[u].paddr);
        assert(old_unique.contains_key(u));
        assert(u != uid);
        // Injectivity (old): only `uid` sat at `paddr`/`idx`, so u_idx != idx.
        if u_idx == idx {
            assert(s.unique_frames[u].paddr == paddr) by {
                assert(old_unique[u].paddr == s.unique_frames[u].paddr);
            };
            assert(u == uid);
            assert(false);
        }
        assert(s.regions.slot_owners[u_idx] == old_regions.slot_owners[u_idx]);
    };
    // --- structural: unique valid_frame_paddr / injectivity (subset of old) ---
    assert forall|u: UniqueId| #[trigger] s.unique_frames.contains_key(u) implies valid_frame_paddr(
        s.unique_frames[u].paddr,
    ) by {
        assert(old_unique.contains_key(u));
    };
    assert forall|u1: UniqueId, u2: UniqueId|
        #![trigger s.unique_frames.contains_key(u1), s.unique_frames.contains_key(u2)]
        s.unique_frames.contains_key(u1) && s.unique_frames.contains_key(u2)
            && s.unique_frames[u1].paddr == s.unique_frames[u2].paddr implies u1 == u2 by {
        assert(old_unique.contains_key(u1));
        assert(old_unique.contains_key(u2));
    };

    // --- accounting clause 1: UNUSED ⟹ no users ---
    assert forall|i: int|
        #![trigger s.regions.slot_owners[i]]
        0 <= i < max_meta_slots() && s.regions.ref_count(i)
            == REF_COUNT_UNUSED implies handle_count(s.frames, i) == 0
        && s.regions.slot_owners[i].paths_in_pt.is_empty() && segment_cover_count(
        s.segments,
        index_to_frame(i),
    ) == 0 by {
        if i == idx {
            // post: H(idx)==0 (frames fixed; derived pre), paths empty
            // (preserved), cover==0 (segments fixed; derived pre).
            assert(handle_count(s.frames, idx) == 0);
            assert(s.regions.slot_owners[idx].paths_in_pt.is_empty());
            assert(segment_cover_count(s.segments, index_to_frame(idx)) == 0);
        } else {
            assert(s.regions.slot_owners[i] == old_regions.slot_owners[i]);
        }
    };
    // --- accounting clause 2: valid rc ⟹ active head ---
    assert forall|i: int|
        #![trigger s.regions.slot_owners[i]]
        0 <= i < max_meta_slots() && s.regions.slot_owners[i].usage is Frame && s.regions.ref_count(
            i,
        ) != REF_COUNT_UNUSED && s.regions.ref_count(i) != REF_COUNT_UNIQUE implies handle_count(
        s.frames,
        i,
    ) > 0 || s.regions.slot_owners[i].paths_in_pt.len() > 0 || segment_cover_count(
        s.segments,
        index_to_frame(i),
    ) > 0 by {
        if i == idx {
            // post rc at `idx` is UNUSED — antecedent false.
            assert(false);
        } else {
            assert(s.regions.slot_owners[i] == old_regions.slot_owners[i]);
        }
    };
    // --- accounting clause 3: the rc equation ---
    assert forall|i: int|
        #![trigger s.regions.slot_owners[i]]
        0 <= i < max_meta_slots() && s.regions.slot_owners[i].usage is Frame && (handle_count(
            s.frames,
            i,
        ) > 0 || s.regions.slot_owners[i].paths_in_pt.len() > 0 || segment_cover_count(
            s.segments,
            index_to_frame(i),
        ) > 0) implies {
        let so = s.regions.slot_owners[i];
        let rc = so.ref_count();
        &&& rc != REF_COUNT_UNUSED
        &&& rc != REF_COUNT_UNIQUE
        &&& rc == handle_count(s.frames, i) + so.paths_in_pt.len() + segment_cover_count(
            s.segments,
            index_to_frame(i),
        )
    } by {
        if i == idx {
            // `idx` is now UNUSED with no users — antecedent false.
            assert(handle_count(s.frames, idx) == 0);
            assert(s.regions.slot_owners[idx].paths_in_pt.is_empty());
            assert(segment_cover_count(s.segments, index_to_frame(idx)) == 0);
        } else {
            assert(s.regions.slot_owners[i] == old_regions.slot_owners[i]);
        }
    };
}

/// `Op::FromUnique` step.
proof fn lemma_step_from_unique<'rcu>(tracked s: &mut VmStore<'rcu>, uid: UniqueId)
    requires
        old(s).inv(),
        old(s).unique_frames.contains_key(uid),
    ensures
        final(s).inv(),
{
    reveal(VmStore::structural_inv);
    reveal(VmStore::accounting_inv);
    let ghost old_regions = s.regions;
    let ghost old_frames = s.frames;
    let ghost old_segments = s.segments;
    let ghost old_unique = s.unique_frames;
    let ghost paddr = s.unique_frames[uid].paddr;
    let ghost idx = frame_to_index(paddr);

    // Slot facts from the structural unique-entry clause + UNIQUE branch.
    s.regions.lemma_contains_valid_frame_paddr(paddr);
    assert(s.regions.contains(idx));
    assert(index_to_frame(idx) == paddr);
    assert(s.regions.slot_owners[idx].usage is Frame);
    assert(s.regions.ref_count(idx) == REF_COUNT_UNIQUE);
    assert(s.regions.slot_owners[idx].paths_in_pt.is_empty());

    // Pre "no users" at the UNIQUE slot (a user forces rc != UNIQUE).
    assert(handle_count(old_frames, idx) == 0) by {
        if handle_count(old_frames, idx) > 0 {
            assert(old_regions.ref_count(idx) != REF_COUNT_UNIQUE);
            assert(false);
        }
    };
    assert(segment_cover_count(old_segments, index_to_frame(idx)) == 0) by {
        if segment_cover_count(old_segments, index_to_frame(idx)) > 0 {
            assert(old_regions.ref_count(idx) != REF_COUNT_UNIQUE);
            assert(false);
        }
    };

    // Consume the unique handle, transition rc UNIQUE → 1.
    let tracked _ue = s.tracked_extract_unique(uid);
    unique::from_unique_embedded(&mut s.regions, paddr);

    // Register the fresh shared FrameEntry.
    let ghost fid = fresh_frame_id(s.frames);
    lemma_fresh_frame_id_not_in_dom(s.frames);
    let tracked fe = tracked_frame_entry_new(paddr);
    s.lemma_insert_frame(fid, fe);
    assert(s.frames =~= old_frames.insert(fid, FrameEntry { paddr }));
    assert(s.unique_frames =~= old_unique.remove(uid));
    assert(s.segments == old_segments);
    assert(s.frames[fid].paddr == paddr);

    // --- structural: in_list == 0 everywhere ---
    assert forall|i: int|
        0 <= i < max_meta_slots() implies #[trigger] s.regions.slot_owners[i].in_list_perm.value()
        == 0 by {
        if i != idx {
            assert(s.regions.slot_owners[i] == old_regions.slot_owners[i]);
        }
    };
    // --- structural: FrameId ⟹ Frame-usage ---
    assert forall|fid_other: FrameId| #[trigger]
        s.frames.contains_key(fid_other) implies s.regions.slot_owner(
        s.frames[fid_other].paddr,
    ).usage is Frame by {
        let other_idx = frame_to_index(s.frames[fid_other].paddr);
        if fid_other == fid {
            assert(s.frames[fid_other].paddr == paddr);
            assert(other_idx == idx);
        } else {
            assert(old_frames.contains_key(fid_other));
            assert(s.frames[fid_other] == old_frames[fid_other]);
            assert(old_regions.slot_owners[other_idx].usage is Frame);
            if other_idx != idx {
                assert(s.regions.slot_owners[other_idx] == old_regions.slot_owners[other_idx]);
            }
        }
    };
    // --- structural: segment-covered ⟹ Frame-usage ---
    assert forall|sid: SegmentId, paddr_c: Paddr|
        #![trigger s.segments.contains_key(sid), frame_to_index(paddr_c)]
        s.segments.contains_key(sid) && s.segments[sid].range.start <= paddr_c
            < s.segments[sid].range.end && paddr_c % PAGE_SIZE == 0 implies s.regions.slot_owner(
        paddr_c,
    ).usage is Frame by {
        let cov_idx = frame_to_index(paddr_c);
        assert(old_segments.contains_key(sid));
        assert(old_regions.slot_owners[cov_idx].usage is Frame);
        if cov_idx != idx {
            assert(s.regions.slot_owners[cov_idx] == old_regions.slot_owners[cov_idx]);
        }
    };
    // --- structural: unique-entry validity (remaining entries) ---
    assert forall|u: UniqueId| #[trigger] s.unique_frames.contains_key(u) implies {
        let so = s.regions.slot_owner(s.unique_frames[u].paddr);
        &&& so.usage is Frame
        &&& so.ref_count() == REF_COUNT_UNIQUE
        &&& so.in_list_perm.value() == 0
        &&& so.paths_in_pt.is_empty()
    } by {
        let u_idx = frame_to_index(s.unique_frames[u].paddr);
        assert(old_unique.contains_key(u));
        assert(u != uid);
        if u_idx == idx {
            assert(old_unique[u].paddr == s.unique_frames[u].paddr);
            assert(u == uid);
            assert(false);
        }
        assert(s.regions.slot_owners[u_idx] == old_regions.slot_owners[u_idx]);
    };
    assert forall|u: UniqueId| #[trigger] s.unique_frames.contains_key(u) implies valid_frame_paddr(
        s.unique_frames[u].paddr,
    ) by {
        assert(old_unique.contains_key(u));
    };
    assert forall|u1: UniqueId, u2: UniqueId|
        #![trigger s.unique_frames.contains_key(u1), s.unique_frames.contains_key(u2)]
        s.unique_frames.contains_key(u1) && s.unique_frames.contains_key(u2)
            && s.unique_frames[u1].paddr == s.unique_frames[u2].paddr implies u1 == u2 by {
        assert(old_unique.contains_key(u1));
        assert(old_unique.contains_key(u2));
    };

    // --- accounting clause 1: UNUSED ⟹ no users ---
    assert forall|i: int|
        #![trigger s.regions.slot_owners[i]]
        0 <= i < max_meta_slots() && s.regions.ref_count(i)
            == REF_COUNT_UNUSED implies handle_count(s.frames, i) == 0
        && s.regions.slot_owners[i].paths_in_pt.is_empty() && segment_cover_count(
        s.segments,
        index_to_frame(i),
    ) == 0 by {
        lemma_handle_count_insert_fresh(old_frames, fid, fe, i);
        if i == idx {
            assert(false);
        } else {
            assert(s.regions.slot_owners[i] == old_regions.slot_owners[i]);
        }
    };
    // --- accounting clause 2: valid rc ⟹ active head ---
    assert forall|i: int|
        #![trigger s.regions.slot_owners[i]]
        0 <= i < max_meta_slots() && s.regions.slot_owners[i].usage is Frame && s.regions.ref_count(
            i,
        ) != REF_COUNT_UNUSED && s.regions.ref_count(i) != REF_COUNT_UNIQUE implies handle_count(
        s.frames,
        i,
    ) > 0 || s.regions.slot_owners[i].paths_in_pt.len() > 0 || segment_cover_count(
        s.segments,
        index_to_frame(i),
    ) > 0 by {
        lemma_handle_count_insert_fresh(old_frames, fid, fe, i);
        if i == idx {
            assert(handle_count(s.frames, idx) == 1);
        } else {
            assert(s.regions.slot_owners[i] == old_regions.slot_owners[i]);
        }
    };
    // --- accounting clause 3: the rc equation ---
    assert forall|i: int|
        #![trigger s.regions.slot_owners[i]]
        0 <= i < max_meta_slots() && s.regions.slot_owners[i].usage is Frame && (handle_count(
            s.frames,
            i,
        ) > 0 || s.regions.slot_owners[i].paths_in_pt.len() > 0 || segment_cover_count(
            s.segments,
            index_to_frame(i),
        ) > 0) implies {
        let so = s.regions.slot_owners[i];
        let rc = so.ref_count();
        &&& rc != REF_COUNT_UNUSED
        &&& rc != REF_COUNT_UNIQUE
        &&& rc == handle_count(s.frames, i) + so.paths_in_pt.len() + segment_cover_count(
            s.segments,
            index_to_frame(i),
        )
    } by {
        lemma_handle_count_insert_fresh(old_frames, fid, fe, i);
        if i == idx {
            // post rc==1, H==1, P==0 (paths empty preserved), cover==0;
            // storage preserved (was init at the UNIQUE slot).
            assert(handle_count(s.frames, idx) == 1);
            assert(s.regions.slot_owners[idx].paths_in_pt.is_empty());
            assert(segment_cover_count(s.segments, index_to_frame(idx)) == 0);
        } else {
            assert(s.regions.slot_owners[i] == old_regions.slot_owners[i]);
        }
    };
}

/// `Op::TryFromShared` step. Tries to convert the shared handle `fid`
/// back into an exclusive one. The CAS succeeds only when `fid` is the
/// *sole* reference (`rc == 1`, hence `H == 1 ∧ P == 0 ∧ cover == 0`):
/// then the slot rises `1 → UNIQUE`, the `FrameEntry` is consumed and a
/// fresh `UniqueEntry` registered. Otherwise the CAS fails and the
/// store is unchanged.
proof fn lemma_step_try_from_shared<'rcu>(tracked s: &mut VmStore<'rcu>, fid: FrameId)
    requires
        old(s).inv(),
        old(s).frames.contains_key(fid),
    ensures
        final(s).inv(),
{
    reveal(VmStore::structural_inv);
    reveal(VmStore::accounting_inv);
    let ghost paddr = s.frames[fid].paddr;
    let ghost idx = frame_to_index(paddr);
    // `fid` registered ⟹ in-bound, `usage == Frame`, and it contributes
    // to `handle_count` (so the slot is an active head).
    s.regions.lemma_contains_valid_frame_paddr(paddr);
    assert(s.regions.contains(idx));
    assert(index_to_frame(idx) == paddr);
    assert(s.regions.slot_owners[idx].usage is Frame);
    assert(s.frames.dom().filter(
        |gid: FrameId| frame_to_index(s.frames[gid].paddr) == idx,
    ).contains(fid));
    assert(handle_count(s.frames, idx) >= 1);

    if s.regions.ref_count(idx) == 1 {
        let ghost old_regions = s.regions;
        let ghost old_frames = s.frames;
        let ghost old_segments = s.segments;
        let ghost old_unique = s.unique_frames;

        // rc==1 ∧ active head ⟹ equation: rc == H + P + cover == 1, and
        // H >= 1, so H == 1, P == 0, cover == 0 (sole reference).
        assert(handle_count(old_frames, idx) == 1);
        assert(s.regions.slot_owners[idx].paths_in_pt.len() == 0);
        assert(segment_cover_count(old_segments, index_to_frame(idx)) == 0);
        assert(s.regions.slot_owners[idx].paths_in_pt =~= Set::empty());

        // Consume the sole FrameEntry, transition rc 1 → UNIQUE.
        let tracked _fe = s.tracked_extract_frame(fid);
        assert(s.frames =~= old_frames.remove(fid));
        unique::try_from_shared_embedded(&mut s.regions, paddr);

        // Register the fresh exclusive UniqueEntry.
        let ghost uid = fresh_unique_id(s.unique_frames);
        lemma_fresh_unique_id_not_in_dom(s.unique_frames);
        let tracked ue = tracked_unique_entry_new(paddr);
        s.lemma_insert_unique(uid, ue);
        assert(s.unique_frames =~= old_unique.insert(uid, UniqueEntry { paddr }));
        assert(s.segments == old_segments);
        // `idx` now has no shared handle (the sole `fid` was removed).
        assert(handle_count(s.frames, idx) == 0) by {
            lemma_handle_count_remove(old_frames, fid, idx);
        };

        // --- structural: in_list == 0 everywhere ---
        assert forall|i: int|
            0 <= i
                < max_meta_slots() implies #[trigger] s.regions.slot_owners[i].in_list_perm.value()
            == 0 by {
            if i != idx {
                assert(s.regions.slot_owners[i] == old_regions.slot_owners[i]);
            }
        };
        // --- structural: FrameId ⟹ Frame-usage ---
        // The converted slot keeps `usage == Frame`; all other slots are
        // unchanged. (No remaining `FrameEntry` sits at `idx`: `H == 0`.)
        assert forall|fid_other: FrameId| #[trigger]
            s.frames.contains_key(fid_other) implies s.regions.slot_owner(
            s.frames[fid_other].paddr,
        ).usage is Frame by {
            let other_idx = frame_to_index(s.frames[fid_other].paddr);
            assert(old_frames.contains_key(fid_other));
            assert(old_regions.slot_owners[other_idx].usage is Frame);
            if other_idx != idx {
                assert(s.regions.slot_owners[other_idx] == old_regions.slot_owners[other_idx]);
            }
        };
        // --- structural: segment-covered ⟹ Frame-usage ---
        assert forall|sid: SegmentId, paddr_c: Paddr|
            #![trigger s.segments.contains_key(sid), frame_to_index(paddr_c)]
            s.segments.contains_key(sid) && s.segments[sid].range.start <= paddr_c
                < s.segments[sid].range.end && paddr_c % PAGE_SIZE
                == 0 implies s.regions.slot_owner(paddr_c).usage is Frame by {
            let cov_idx = frame_to_index(paddr_c);
            assert(old_segments.contains_key(sid));
            assert(old_regions.slot_owners[cov_idx].usage is Frame);
            if cov_idx != idx {
                assert(s.regions.slot_owners[cov_idx] == old_regions.slot_owners[cov_idx]);
            }
        };
        // --- structural: unique-entry validity ---
        assert forall|u: UniqueId| #[trigger] s.unique_frames.contains_key(u) implies {
            let so = s.regions.slot_owner(s.unique_frames[u].paddr);
            &&& so.usage is Frame
            &&& so.ref_count() == REF_COUNT_UNIQUE
            &&& so.in_list_perm.value() == 0
            &&& so.paths_in_pt.is_empty()
        } by {
            let u_idx = frame_to_index(s.unique_frames[u].paddr);
            if u == uid {
                assert(s.unique_frames[u].paddr == paddr);
                assert(u_idx == idx);
            } else {
                assert(old_unique.contains_key(u));
                assert(s.unique_frames[u] == old_unique[u]);
                // old entry's slot was UNIQUE (≠ idx, which was rc==1).
                assert(old_regions.slot_owners[u_idx].ref_count() == REF_COUNT_UNIQUE);
                assert(u_idx != idx);
                assert(s.regions.slot_owners[u_idx] == old_regions.slot_owners[u_idx]);
            }
        };
        assert forall|u: UniqueId| #[trigger]
            s.unique_frames.contains_key(u) implies valid_frame_paddr(s.unique_frames[u].paddr) by {
            if u != uid {
                assert(old_unique.contains_key(u));
            }
        };
        assert forall|u1: UniqueId, u2: UniqueId|
            #![trigger s.unique_frames.contains_key(u1), s.unique_frames.contains_key(u2)]
            s.unique_frames.contains_key(u1) && s.unique_frames.contains_key(u2)
                && s.unique_frames[u1].paddr == s.unique_frames[u2].paddr implies u1 == u2 by {
            if u1 == uid && u2 != uid {
                assert(old_unique.contains_key(u2));
                assert(s.unique_frames[u2].paddr == paddr);
                assert(frame_to_index(s.unique_frames[u2].paddr) == idx);
                assert(old_regions.ref_count(idx) == REF_COUNT_UNIQUE);
                assert(false);
            } else if u2 == uid && u1 != uid {
                assert(old_unique.contains_key(u1));
                assert(s.unique_frames[u1].paddr == paddr);
                assert(frame_to_index(s.unique_frames[u1].paddr) == idx);
                assert(old_regions.ref_count(idx) == REF_COUNT_UNIQUE);
                assert(false);
            } else if u1 != uid && u2 != uid {
                assert(old_unique.contains_key(u1));
                assert(old_unique.contains_key(u2));
            }
        };

        // --- accounting clause 1: UNUSED ⟹ no users ---
        assert forall|i: int|
            #![trigger s.regions.slot_owners[i]]
            0 <= i < max_meta_slots() && s.regions.ref_count(i)
                == REF_COUNT_UNUSED implies handle_count(s.frames, i) == 0
            && s.regions.slot_owners[i].paths_in_pt.is_empty() && segment_cover_count(
            s.segments,
            index_to_frame(i),
        ) == 0 by {
            lemma_handle_count_remove(old_frames, fid, i);
            if i == idx {
                // post `idx` is UNIQUE, not UNUSED — antecedent false.
                assert(false);
            } else {
                assert(s.regions.slot_owners[i] == old_regions.slot_owners[i]);
            }
        };
        // --- accounting clause 2: valid rc ⟹ active head ---
        assert forall|i: int|
            #![trigger s.regions.slot_owners[i]]
            0 <= i < max_meta_slots() && s.regions.slot_owners[i].usage is Frame
                && s.regions.ref_count(i) != REF_COUNT_UNUSED && s.regions.ref_count(i)
                != REF_COUNT_UNIQUE implies handle_count(s.frames, i) > 0
            || s.regions.slot_owners[i].paths_in_pt.len() > 0 || segment_cover_count(
            s.segments,
            index_to_frame(i),
        ) > 0 by {
            lemma_handle_count_remove(old_frames, fid, i);
            if i == idx {
                // post `idx` is UNIQUE — antecedent false.
                assert(false);
            } else {
                assert(s.regions.slot_owners[i] == old_regions.slot_owners[i]);
            }
        };
        // --- accounting clause 3: the rc equation ---
        assert forall|i: int|
            #![trigger s.regions.slot_owners[i]]
            0 <= i < max_meta_slots() && s.regions.slot_owners[i].usage is Frame && (handle_count(
                s.frames,
                i,
            ) > 0 || s.regions.slot_owners[i].paths_in_pt.len() > 0 || segment_cover_count(
                s.segments,
                index_to_frame(i),
            ) > 0) implies {
            let so = s.regions.slot_owners[i];
            let rc = so.ref_count();
            &&& rc != REF_COUNT_UNUSED
            &&& rc != REF_COUNT_UNIQUE
            &&& rc == handle_count(s.frames, i) + so.paths_in_pt.len() + segment_cover_count(
                s.segments,
                index_to_frame(i),
            )
        } by {
            lemma_handle_count_remove(old_frames, fid, i);
            if i == idx {
                // post `idx` is UNIQUE with no users (H=P=cover=0) — the
                // active-head antecedent is false, so this is vacuous.
                assert(handle_count(s.frames, idx) == 0);
                assert(s.regions.slot_owners[idx].paths_in_pt.is_empty());
                assert(segment_cover_count(s.segments, index_to_frame(idx)) == 0);
            } else {
                assert(s.regions.slot_owners[i] == old_regions.slot_owners[i]);
            }
        };
    }
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
        !segments.contains_key(sid),
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
            if s != sid {
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
        !segments.contains_key(sid),
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
        segments.contains_key(sid),
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
        segments.contains_key(sid),
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
        segments.contains_key(sid),
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
            assert(new_covers);
            lemma_segment_cover_contains(segments, sid, paddr_check);
            lemma_segment_cover_insert_inside(segments.remove(sid), sid, new_entry, paddr_check);
            assert(segment_cover_count(new_segments, paddr_check) == segment_cover_count(
                segments,
                paddr_check,
            ));
        } else {
            assert(!new_covers);
            lemma_segment_cover_insert_outside(segments.remove(sid), sid, new_entry, paddr_check);
            assert(segment_cover_count(new_segments, paddr_check) == segment_cover_count(
                segments,
                paddr_check,
            ));
        }
    } else {
        let new_segments = segments.remove(sid);
        if paddr_check == popped {
            assert(sid_pre_covers);
            lemma_segment_cover_contains(segments, sid, paddr_check);
            assert(segment_cover_count(new_segments, paddr_check) + 1 == segment_cover_count(
                segments,
                paddr_check,
            ));
        } else if sid_pre_covers {
            assert(false);
        } else {
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
        segments.contains_key(sid),
        // `new_left` and `new_right` are fresh and distinct from each
        // other and from `sid`.
        new_left != sid,
        new_right != sid,
        new_left != new_right,
        !segments.remove(sid).contains_key(new_left),
        !segments.remove(sid).contains_key(new_right),
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
    assert(!with_left.contains_key(new_right));
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
        segments.contains_key(sid),
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
    choose|id: VmSpaceId| !m.contains_key(id)
}

/// Picks a cursor id not currently in `m.dom()`.
pub open spec fn fresh_cursor_id<'rcu>(m: Map<CursorId, CursorEntry<'rcu>>) -> CursorId {
    choose|id: CursorId| !m.contains_key(id)
}

/// Picks a [`VmIoId`] not currently in `m.dom()`.
pub open spec fn fresh_vm_io_id<'a>(m: Map<VmIoId, VmIoEntry>) -> VmIoId {
    choose|id: VmIoId| !m.contains_key(id)
}

/// Picks a [`FrameId`] not currently in `m.dom()`.
pub open spec fn fresh_frame_id(m: Map<FrameId, FrameEntry>) -> FrameId {
    choose|id: FrameId| !m.contains_key(id)
}

pub proof fn lemma_fresh_vm_space_id_not_in_dom<'a>(m: Map<VmSpaceId, VmSpaceOwner>)
    ensures
        !m.contains_key(fresh_vm_space_id(m)),
{
    lemma_finite_int_set_has_unused(m.dom());
}

pub proof fn lemma_fresh_cursor_id_not_in_dom<'rcu>(m: Map<CursorId, CursorEntry<'rcu>>)
    ensures
        !m.contains_key(fresh_cursor_id(m)),
{
    lemma_finite_int_set_has_unused(m.dom());
}

pub proof fn lemma_fresh_vm_io_id_not_in_dom<'a>(m: Map<VmIoId, VmIoEntry>)
    ensures
        !m.contains_key(fresh_vm_io_id(m)),
{
    lemma_finite_int_set_has_unused(m.dom());
}

pub proof fn lemma_fresh_frame_id_not_in_dom(m: Map<FrameId, FrameEntry>)
    ensures
        !m.contains_key(fresh_frame_id(m)),
{
    lemma_finite_int_set_has_unused(m.dom());
}

/// Tracked constructor for [`CursorEntry`].
pub proof fn tracked_cursor_entry_new<'rcu>(
    vm_space: VmSpaceId,
    kind: CursorKind,
    va: Range<Vaddr>,
    tracked owner: CursorOwner<'rcu, UserPtConfig>,
    tracked guards: Guards,
) -> (tracked res: CursorEntry<'rcu>)
    ensures
        res.vm_space == vm_space,
        res.kind == kind,
        res.va == va,
        res.owner == owner,
        res.guards == guards,
{
    let tracked res = CursorEntry { vm_space, kind, va, owner, guards };
    res
}

/// Tracked constructor for [`VmIoEntry`].
pub proof fn tracked_vm_io_entry_new<'a>(
    vm_space: Option<VmSpaceId>,
    kind: VmIoKind,
    vaddr: Vaddr,
    len: usize,
    tracked owner: VmIoOwner,
) -> tracked VmIoEntry
    returns
        (VmIoEntry { vm_space, kind, vaddr, len, owner }),
{
    let tracked res = VmIoEntry { vm_space, kind, vaddr, len, owner };
    res
}

/// Tracked constructor for [`FrameEntry`].
pub proof fn tracked_frame_entry_new(paddr: Paddr) -> tracked FrameEntry
    returns
        (FrameEntry { paddr }),
{
    let tracked res = FrameEntry { paddr };
    res
}

/// Tracked constructor for [`SegmentEntry`].
pub proof fn tracked_segment_entry_new(range: Range<Paddr>) -> tracked SegmentEntry
    returns
        (SegmentEntry { range }),
{
    let tracked res = SegmentEntry { range };
    res
}

/// Fresh-id helper for the segment id space.
pub open spec fn fresh_segment_id(m: Map<SegmentId, SegmentEntry>) -> SegmentId {
    choose|id: SegmentId| !m.contains_key(id)
}

pub proof fn lemma_fresh_segment_id_not_in_dom(m: Map<SegmentId, SegmentEntry>)
    ensures
        !m.contains_key(fresh_segment_id(m)),
{
    lemma_finite_int_set_has_unused(m.dom());
}

/// Tracked constructor for [`UniqueEntry`].
pub proof fn tracked_unique_entry_new(paddr: Paddr) -> tracked UniqueEntry
    returns
        (UniqueEntry { paddr }),
{
    let tracked res = UniqueEntry { paddr };
    res
}

/// Picks a [`UniqueId`] not currently in `m.dom()`.
pub open spec fn fresh_unique_id(m: Map<UniqueId, UniqueEntry>) -> UniqueId {
    choose|id: UniqueId| !m.contains_key(id)
}

pub proof fn lemma_fresh_unique_id_not_in_dom(m: Map<UniqueId, UniqueEntry>)
    ensures
        !m.contains_key(fresh_unique_id(m)),
{
    lemma_finite_int_set_has_unused(m.dom());
}

} // verus!
