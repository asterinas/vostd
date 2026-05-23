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

pub mod cursor;
pub mod frame;
pub mod io;
pub mod trace;
pub mod vm_space;

use core::ops::Range;

use vstd::prelude::*;
use vstd_extra::ownership::*;

use crate::mm::frame::{has_safe_slot, MetaSlot, UFrame};
use crate::mm::page_prop::PageProperty;
use crate::mm::vm_space::vm_space_specs::VmSpaceOwner;
use crate::mm::vm_space::UserPtConfig;
use crate::mm::{Paddr, Vaddr, MAX_USERSPACE_VADDR};
use crate::specs::mm::frame::mapping::{frame_to_index_spec, max_meta_slots};
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

/// Per-Frame entry in the store. Represents one outstanding handle to
/// the slot at `paddr` — i.e., one unit of refcount in
/// `regions.slot_owners[frame_to_index_spec(paddr)]`.
///
/// Multiple `FrameEntry`s may share the same `paddr`; each contributes
/// `+1` to that slot's `inner_perms.ref_count`.
pub tracked struct FrameEntry {
    pub paddr: Paddr,
}

/// Number of outstanding `Frame` handles whose paddr maps to slot
/// `idx` — i.e. the `#handles(idx)` term of the exact reference-count
/// accounting `ref_count(idx) == #handles(idx) + paths_in_pt(idx).len()`
/// (Stage 5 / full #4). Well-defined as a `nat` only when
/// `frames.dom()` is finite, which [`VmStore::inv`] maintains.
pub open spec fn handle_count(frames: Map<FrameId, FrameEntry>, idx: usize) -> nat {
    frames.dom().filter(
        |fid: FrameId| frame_to_index_spec(frames[fid].paddr) == idx,
    ).len()
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
        frames.dom().finite(),
    ensures
        handle_count(frames.insert(id, entry), idx) == handle_count(frames, idx)
            + (if frame_to_index_spec(entry.paddr) == idx { 1nat } else { 0nat }),
{
    let frames2 = frames.insert(id, entry);
    let new_filt = frames2.dom().filter(
        |fid: FrameId| frame_to_index_spec(frames2[fid].paddr) == idx);
    let old_filt = frames.dom().filter(
        |fid: FrameId| frame_to_index_spec(frames[fid].paddr) == idx);
    assert(frames2.dom() =~= frames.dom().insert(id));
    if frame_to_index_spec(entry.paddr) == idx {
        assert(new_filt =~= old_filt.insert(id)) by {
            assert forall|fid: FrameId|
                #[trigger] new_filt.contains(fid)
                implies old_filt.insert(id).contains(fid) by {
                    if fid != id {
                        assert(frames2[fid] == frames[fid]);
                    }
                };
            assert forall|fid: FrameId|
                #[trigger] old_filt.insert(id).contains(fid)
                implies new_filt.contains(fid) by {
                    if fid != id {
                        assert(frames2[fid] == frames[fid]);
                    } else {
                        assert(frames2[id] == entry);
                    }
                };
        };
        assert(!old_filt.contains(id));
        assert(old_filt.finite());
        assert(new_filt.len() == old_filt.len() + 1);
    } else {
        assert(new_filt =~= old_filt) by {
            assert forall|fid: FrameId|
                #[trigger] new_filt.contains(fid) implies old_filt.contains(fid) by {
                    if fid != id {
                        assert(frames2[fid] == frames[fid]);
                    } else {
                        assert(frames2[id] == entry);
                    }
                };
            assert forall|fid: FrameId|
                #[trigger] old_filt.contains(fid) implies new_filt.contains(fid) by {
                    assert(fid != id);
                    assert(frames2[fid] == frames[fid]);
                };
        };
    }
}

/// Handle-count delta under [`Map::remove`]: -1 at the removed entry's
/// slot if it was the only one present (or generally `-1` if the entry
/// at `fid` mapped to `idx`), unchanged elsewhere.
pub proof fn lemma_handle_count_remove(
    frames: Map<FrameId, FrameEntry>,
    fid: FrameId,
    idx: usize,
)
    requires
        frames.dom().contains(fid),
        frames.dom().finite(),
    ensures
        handle_count(frames.remove(fid), idx)
            == handle_count(frames, idx)
                - (if frame_to_index_spec(frames[fid].paddr) == idx { 1nat } else { 0nat }),
{
    let frames2 = frames.remove(fid);
    let new_filt = frames2.dom().filter(
        |gid: FrameId| frame_to_index_spec(frames2[gid].paddr) == idx);
    let old_filt = frames.dom().filter(
        |gid: FrameId| frame_to_index_spec(frames[gid].paddr) == idx);
    assert(frames2.dom() =~= frames.dom().remove(fid));
    if frame_to_index_spec(frames[fid].paddr) == idx {
        assert(old_filt.contains(fid));
        assert(new_filt =~= old_filt.remove(fid)) by {
            assert forall|gid: FrameId|
                #[trigger] new_filt.contains(gid)
                implies old_filt.remove(fid).contains(gid) by {
                    assert(gid != fid);
                    assert(frames2[gid] == frames[gid]);
                };
            assert forall|gid: FrameId|
                #[trigger] old_filt.remove(fid).contains(gid)
                implies new_filt.contains(gid) by {
                    assert(gid != fid);
                    assert(frames2[gid] == frames[gid]);
                };
        };
        assert(old_filt.finite());
        assert(new_filt.len() == (old_filt.len() - 1) as nat);
    } else {
        assert(!old_filt.contains(fid));
        assert(new_filt =~= old_filt) by {
            assert forall|gid: FrameId|
                #[trigger] new_filt.contains(gid) implies old_filt.contains(gid) by {
                    assert(gid != fid);
                    assert(frames2[gid] == frames[gid]);
                };
            assert forall|gid: FrameId|
                #[trigger] old_filt.contains(gid) implies new_filt.contains(gid) by {
                    assert(gid != fid);
                    assert(frames2[gid] == frames[gid]);
                };
        };
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
    pub guards: Guards<'rcu, UserPtConfig>,
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
                idx < max_meta_slots() ==> #[trigger] self.regions.slots.contains_key(idx)
        // `raw_count` / `in_list` coverage (Design B, #4 partial). Same
        // soundness shape as the slot-perm coverage above: NOT globally
        // true, but true *here* because the embedding's `Op` surface has
        // no `into_raw`/`from_raw`/`ManuallyDrop` op (so `raw_count`
        // never leaves 0) and no allocator/free-list op (so `in_list`
        // never leaves 0). Internalising these discharges `drop_pre`'s
        // `raw_count == 0` and the `in_list == 0` half of its last-ref
        // teardown conjunct, so `op_pre[FrameDrop]` keeps only the
        // genuine refcount residual (see [`op_pre`] / [`step_frame_drop`]).
        &&& forall|idx: usize|
                idx < max_meta_slots()
                    ==> #[trigger] self.regions.slot_owners[idx].raw_count == 0
        &&& forall|idx: usize|
                idx < max_meta_slots()
                    ==> #[trigger] self.regions.slot_owners[idx].inner_perms.in_list.value() == 0
        &&& self.tlb_model.inv()
        &&& forall|id: VmSpaceId|
                #[trigger] self.vm_spaces.dom().contains(id)
                    ==> self.vm_spaces[id].inv()
        &&& forall|id: CursorId|
                #[trigger] self.cursors.dom().contains(id)
                    ==> self.cursors[id].inv()
        &&& forall|id: CursorId|
                #[trigger] self.cursors.dom().contains(id)
                    ==> self.cursors[id].owner.metaregion_sound(self.regions)
        &&& forall|id: CursorId|
                #[trigger] self.cursors.dom().contains(id)
                    ==> self.vm_spaces.dom().contains(self.cursors[id].vm_space)
        &&& forall|id: VmIoId|
                #[trigger] self.vm_ios.dom().contains(id)
                    ==> self.vm_ios[id].inv()
        &&& forall|id: VmIoId|
                #[trigger] self.vm_ios.dom().contains(id)
                    ==> (self.vm_ios[id].vm_space matches Some(vs)
                            ==> self.vm_spaces.dom().contains(vs))
        &&& forall|id: VmIoId|
                #[trigger] self.vm_ios.dom().contains(id)
                    ==> self.vm_ios[id].vm_space is Some
                            ==> (self.vm_ios[id].vaddr as nat)
                                + (self.vm_ios[id].len as nat)
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
        &&& forall|fid: FrameId|
                #[trigger] self.frames.dom().contains(fid)
                    ==> has_safe_slot(self.frames[fid].paddr)
        // `frames.dom()` is finite (built by finitely many `insert_frame`
        // from an empty map; never an infinite `choose`). Needed for
        // [`handle_count`] (`Set::len`) to be a well-defined `nat` in the
        // Stage-5 accounting clause.
        &&& self.frames.dom().finite()
        // `paths_in_pt.finite()` is now a per-slot fact in
        // `MetaSlotOwner::inv` (main verification), implied here via
        // `regions.inv() → slot_owners[i].inv()` for any `i <
        // max_meta_slots()`.
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
    /// The exact equation is *Frame-scoped*. The residual refcount
    /// obligation of `drop_pre` (`rc>0`, `rc<=MAX`,
    /// `rc==1 ==> storage.is_init()`) is instead discharged for *any*
    /// `FrameEntry` — regardless of slot `usage` — by the separate,
    /// usage-independent **handle clause** (`handle_count > 0 ⟹` live
    /// non-sentinel `rc ≥ #handles` with initialised storage).
    /// `from_in_use` can legitimately hand out a handle on a non-Frame
    /// slot, so this is what keeps `op_pre[FrameDrop]` collapsed to
    /// mere id-existence (full #4).
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
        // Stage 5.5c absorption clauses (couple `frames` + `regions`,
        // so they belong in `accounting_inv` not `structural_inv` —
        // preserving the 5.5a split).
        //
        // **Handle ⟹ live, initialised slot** (usage-independent;
        // Stage 5 / 2b). Every outstanding `Frame` handle is a genuine
        // reference, so a slot with `handle_count > 0` has a live,
        // non-sentinel `ref_count` of at least that many, and
        // initialised metadata storage. This holds for *any* `usage`:
        // `from_in_use` can legitimately acquire a handle on a
        // page-table / MMIO slot — upstream `from_in_use` lives on
        // `Frame<dyn AnyFrameMeta>` and never inspects `usage` — which
        // is why the old "handles imply Frame usage" clause was
        // dropped.
        &&& forall|idx: usize|
                #![trigger self.regions.slot_owners[idx]]
                idx < max_meta_slots()
                && handle_count(self.frames, idx) > 0
                    ==> {
                    let so = self.regions.slot_owners[idx];
                    let rc = so.inner_perms.ref_count.value();
                    &&& rc != REF_COUNT_UNUSED
                    &&& rc != REF_COUNT_UNIQUE
                    &&& rc >= handle_count(self.frames, idx)
                    &&& so.inner_perms.storage.is_init()
                }
        // **UNUSED ⟹ no users.** A live PTE bumps `rc`, so reaching
        // `UNUSED` requires `paths_in_pt.is_empty()`.
        &&& forall|idx: usize|
                #![trigger self.regions.slot_owners[idx]]
                idx < max_meta_slots()
                && self.regions.slot_owners[idx].inner_perms.ref_count.value()
                        == REF_COUNT_UNUSED
                    ==> handle_count(self.frames, idx) == 0
                        && self.regions.slot_owners[idx].paths_in_pt.is_empty()
        // **Frame in valid rc range ⟹ active head.** Inverse of the
        // active-head guard below — absorbs the pre-active-head assume
        // in `step_frame_from_in_use`.
        &&& forall|idx: usize|
                #![trigger self.regions.slot_owners[idx]]
                idx < max_meta_slots()
                && self.regions.slot_owners[idx].usage == PageUsage::Frame
                && self.regions.slot_owners[idx].inner_perms.ref_count.value()
                        != REF_COUNT_UNUSED
                && self.regions.slot_owners[idx].inner_perms.ref_count.value()
                        != REF_COUNT_UNIQUE
                    ==> handle_count(self.frames, idx) > 0
                        || self.regions.slot_owners[idx].paths_in_pt.len() > 0
        &&& forall|idx: usize|
            #![trigger self.regions.slot_owners[idx]]
            idx < max_meta_slots()
            && self.regions.slot_owners[idx].usage == PageUsage::Frame
            && (handle_count(self.frames, idx) > 0
                || self.regions.slot_owners[idx].paths_in_pt.len() > 0)
                ==> {
                let so = self.regions.slot_owners[idx];
                let rc = so.inner_perms.ref_count.value();
                &&& rc != REF_COUNT_UNUSED
                &&& rc != REF_COUNT_UNIQUE
                &&& rc == handle_count(self.frames, idx) + so.paths_in_pt.len()
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
    Map { c: CursorId, frame: UFrame, prop: PageProperty },
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
        Op::DropVmSpace { vs } =>
            s.vm_spaces.dom().contains(vs)
            && (forall|c: CursorId|
                #[trigger] s.cursors.dom().contains(c)
                    ==> s.cursors[c].vm_space != vs)
            && (forall|v: VmIoId|
                #[trigger] s.vm_ios.dom().contains(v)
                    ==> s.vm_ios[v].vm_space != Some(vs)),
        Op::OpenCursor { vs, va: _ } => s.vm_spaces.dom().contains(vs),
        Op::OpenCursorMut { vs, va: _ } => s.vm_spaces.dom().contains(vs),
        Op::DropCursor { c } => s.cursors.dom().contains(c),
        Op::Query { c } => s.cursors.dom().contains(c),
        Op::FindNext { c, len: _ } => s.cursors.dom().contains(c),
        Op::Jump { c, va: _ } => s.cursors.dom().contains(c),
        Op::VirtAddr { c } => s.cursors.dom().contains(c),
        Op::Map { c, frame: _, prop: _ } => s.cursors.dom().contains(c),
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
        Op::Read { source, dest } =>
            s.vm_ios.dom().contains(source)
            && s.vm_ios.dom().contains(dest)
            && source != dest
            && s.vm_ios[source].is_kernel_reader()
            && s.vm_ios[dest].is_kernel_writer(),
        // exec Infallible `write`: same operand typing as `read`.
        Op::Write { source, dest } =>
            s.vm_ios.dom().contains(source)
            && s.vm_ios.dom().contains(dest)
            && source != dest
            && s.vm_ios[source].is_kernel_reader()
            && s.vm_ios[dest].is_kernel_writer(),
        Op::FrameFromUnused { paddr: _ } => true,
        Op::FrameFromInUse { paddr: _ } => true,
        // The bulk of `frame::drop_pre` is recovered from `VmStore::inv`
        // — structural coverage gives `slots.contains_key`,
        // `raw_count == 0`, `in_list == 0`; the handle clause of
        // `accounting_inv` gives the refcount bounds, non-sentinel
        // status, and `storage.is_init`. The one residual is the
        // FUTURE-plan strengthening of exec `Frame::drop_requires`:
        // `rc == 1 ⟹ paths_in_pt.is_empty()`. For a Frame-usage slot
        // this is derivable from clause 4 (`rc == H + P` for active
        // heads), but the embedding's accounting is Frame-scoped while
        // 2b allows `FrameEntry`s on non-Frame slots, so the conjunct
        // is carried in `op_pre` rather than re-derived universally.
        // Callers discharge it trivially for Frame entries (clause 4)
        // and via real-world refcount reasoning for non-Frame ones.
        Op::FrameDrop { fid } =>
            s.frames.dom().contains(fid)
            && (s.regions.slot_owners[frame_to_index_spec(s.frames[fid].paddr)]
                    .inner_perms.ref_count.value() == 1
                ==> s.regions.slot_owners[frame_to_index_spec(s.frames[fid].paddr)]
                        .paths_in_pt.is_empty()),
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
            forall|c: CursorId|
                #[trigger] old(self).cursors.dom().contains(c)
                    ==> old(self).cursors[c].vm_space != vs,
            forall|v: VmIoId|
                #[trigger] old(self).vm_ios.dom().contains(v)
                    ==> old(self).vm_ios[v].vm_space != Some(vs),
        ensures
            final(self).regions == old(self).regions,
            final(self).tlb_model == old(self).tlb_model,
            final(self).vm_spaces == old(self).vm_spaces.remove(vs),
            final(self).cursors == old(self).cursors,
            final(self).vm_ios == old(self).vm_ios,
            res == old(self).vm_spaces[vs],
            final(self).inv(),
    {
        self.vm_spaces.tracked_remove(vs)
    }

    /// Inserts a VmSpaceOwner at the given fresh id. Requires the id is
    /// not already used and the owner satisfies its invariant.
    pub proof fn insert_vm_space(
        tracked &mut self,
        vs: VmSpaceId,
        tracked owner: VmSpaceOwner,
    )
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
            final(self).inv(),
    {
        self.vm_spaces.tracked_insert(vs, owner);
    }

    /// Removes the cursor entry at `c` from the store and returns it.
    pub proof fn extract_cursor(tracked &mut self, c: CursorId)
        -> (tracked res: CursorEntry<'rcu>)
        requires
            old(self).inv(),
            old(self).cursors.dom().contains(c),
        ensures
            final(self).regions == old(self).regions,
            final(self).tlb_model == old(self).tlb_model,
            final(self).vm_spaces == old(self).vm_spaces,
            final(self).cursors == old(self).cursors.remove(c),
            final(self).vm_ios == old(self).vm_ios,
            res == old(self).cursors[c],
            final(self).inv(),
    {
        self.cursors.tracked_remove(c)
    }

    /// Inserts a cursor entry at the given fresh id. Requires the id is
    /// not already used, the entry satisfies its inv, the entry's
    /// `vm_space` is in the store, and the entry's owner is sound w.r.t.
    /// the store's regions.
    pub proof fn insert_cursor(
        tracked &mut self,
        c: CursorId,
        tracked entry: CursorEntry<'rcu>,
    )
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
            final(self).inv(),
    {
        self.cursors.tracked_insert(c, entry);
    }

    /// Removes the VmIo entry at `vio` from the store and returns it.
    pub proof fn extract_vm_io(tracked &mut self, vio: VmIoId)
        -> (tracked res: VmIoEntry)
        requires
            old(self).inv(),
            old(self).vm_ios.dom().contains(vio),
        ensures
            final(self).regions == old(self).regions,
            final(self).tlb_model == old(self).tlb_model,
            final(self).vm_spaces == old(self).vm_spaces,
            final(self).cursors == old(self).cursors,
            final(self).vm_ios == old(self).vm_ios.remove(vio),
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
    pub proof fn insert_vm_io(
        tracked &mut self,
        vio: VmIoId,
        tracked entry: VmIoEntry,
    )
        requires
            old(self).inv(),
            !old(self).vm_ios.dom().contains(vio),
            entry.inv(),
            entry.vm_space matches Some(vs)
                ==> old(self).vm_spaces.dom().contains(vs),
            entry.vm_space is Some
                ==> (entry.vaddr as nat) + (entry.len as nat)
                        <= MAX_USERSPACE_VADDR as nat,
        ensures
            final(self).regions == old(self).regions,
            final(self).tlb_model == old(self).tlb_model,
            final(self).vm_spaces == old(self).vm_spaces,
            final(self).cursors == old(self).cursors,
            final(self).vm_ios == old(self).vm_ios.insert(vio, entry),
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
    pub proof fn extract_frame(tracked &mut self, fid: FrameId)
        -> (tracked res: FrameEntry)
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
    pub proof fn insert_frame(
        tracked &mut self,
        fid: FrameId,
        tracked entry: FrameEntry,
    )
        requires
            old(self).structural_inv(),
            !old(self).frames.dom().contains(fid),
            has_safe_slot(entry.paddr),
        ensures
            final(self).regions == old(self).regions,
            final(self).tlb_model == old(self).tlb_model,
            final(self).vm_spaces == old(self).vm_spaces,
            final(self).cursors == old(self).cursors,
            final(self).vm_ios == old(self).vm_ios,
            final(self).frames == old(self).frames.insert(fid, entry),
            final(self).structural_inv(),
    {
        self.frames.tracked_insert(fid, entry);
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
        Op::Query { c } => step_cursor_method(s, c, cursor::CursorMethod::Query),
        Op::FindNext { c, len } => step_cursor_method(s, c, cursor::CursorMethod::FindNext(len)),
        Op::Jump { c, va } => step_cursor_method(s, c, cursor::CursorMethod::Jump(va)),
        Op::VirtAddr { c: _ } => {},
        Op::Map { c, frame, prop } => step_map(s, c, frame, prop),
        Op::Unmap { c, len } => step_unmap(s, c, len),
        Op::ProtectNext { c, len } =>
            step_cursor_method(s, c, cursor::CursorMethod::ProtectNext(len)),
        Op::NewReader { vs, vaddr, len } => step_new_vm_io(s, vs, vaddr, len, VmIoKind::Reader),
        Op::NewWriter { vs, vaddr, len } => step_new_vm_io(s, vs, vaddr, len, VmIoKind::Writer),
        Op::NewKernelReader { vaddr, len } => step_new_kernel_vm_io(s, vaddr, len, VmIoKind::Reader),
        Op::NewKernelWriter { vaddr, len } => step_new_kernel_vm_io(s, vaddr, len, VmIoKind::Writer),
        Op::DropReader { vio } => step_drop_vm_io(s, vio),
        Op::DropWriter { vio } => step_drop_vm_io(s, vio),
        // Fallible variants: handle-only, no embedding state changes.
        Op::ReaderReadVal { source: _ } => {},
        Op::ReaderCollect { source: _ } => {},
        Op::WriterWriteVal { writer: _ } => {},
        Op::ReaderLimit { vio, max } =>
            step_vm_io_method(s, vio, io::VmIoMethod::ReaderLimit(max)),
        Op::ReaderSkip { vio, n } =>
            step_vm_io_method(s, vio, io::VmIoMethod::ReaderSkip(n)),
        Op::ReaderQuery { vio: _ } => {},
        Op::WriterFillZeros { vio, len } =>
            step_vm_io_method(s, vio, io::VmIoMethod::WriterFillZeros(len)),
        Op::WriterLimit { vio, max } =>
            step_vm_io_method(s, vio, io::VmIoMethod::WriterLimit(max)),
        Op::WriterSkip { vio, n } =>
            step_vm_io_method(s, vio, io::VmIoMethod::WriterSkip(n)),
        Op::WriterQuery { vio: _ } => {},
        // Infallible `read`: produces a fresh activated-Writer val_owner.
        Op::Read { source, dest } => step_read(s, source, dest),
        // Infallible `write`: no longer surfaces consumed_w; just
        // mutates source/dest owners.
        Op::Write { source, dest } => step_write(s, source, dest),
        Op::FrameFromUnused { paddr } => step_frame_from_unused(s, paddr),
        Op::FrameFromInUse { paddr } => step_frame_from_in_use(s, paddr),
        Op::FrameDrop { fid } => step_frame_drop(s, fid),
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
proof fn lemma_accounting_preserved_by_pt_alloc<'rcu>(
    s_old: VmStore<'rcu>,
    s_new: VmStore<'rcu>,
)
    requires
        s_old.inv(),
        s_new.frames == s_old.frames,
        forall|i: usize| #![trigger s_new.regions.slot_owners[i]]
            s_new.regions.slot_owners[i] != s_old.regions.slot_owners[i] ==> {
                &&& s_old.regions.slot_owners[i].inner_perms.ref_count.value()
                        == REF_COUNT_UNUSED
                &&& s_new.regions.slot_owners[i].inner_perms.ref_count.value()
                        != REF_COUNT_UNUSED
                &&& s_new.regions.slot_owners[i].usage != PageUsage::Frame
            },
    ensures
        s_new.accounting_inv(),
{
    // Handle clause — handle ⟹ live, initialised slot. A slot carrying
    // a handle in `s_new` cannot have transitioned: a transitioned slot
    // was pre-UNUSED, but a pre-UNUSED slot has `handle_count == 0`
    // (old clause 2). So the slot is unchanged and the old handle
    // clause carries.
    assert forall|idx: usize|
        #![trigger s_new.regions.slot_owners[idx]]
        idx < max_meta_slots()
        && handle_count(s_new.frames, idx) > 0
            implies {
                let so = s_new.regions.slot_owners[idx];
                let rc = so.inner_perms.ref_count.value();
                &&& rc != REF_COUNT_UNUSED
                &&& rc != REF_COUNT_UNIQUE
                &&& rc >= handle_count(s_new.frames, idx)
                &&& so.inner_perms.storage.is_init()
            } by {
        if s_new.regions.slot_owners[idx] != s_old.regions.slot_owners[idx] {
            // changed ⟹ pre-UNUSED ⟹ (old clause 2) handle_count == 0.
            assert(s_old.regions.slot_owners[idx].inner_perms.ref_count.value()
                == REF_COUNT_UNUSED);
            assert(handle_count(s_old.frames, idx) == 0);
            assert(false);
        }
        assert(s_new.regions.slot_owners[idx] == s_old.regions.slot_owners[idx]);
    };
    // Clause 2 — UNUSED ⟹ no users. An UNUSED slot in `s_new` is
    // unchanged (a transitioned slot is non-UNUSED in `s_new`).
    assert forall|idx: usize|
        #![trigger s_new.regions.slot_owners[idx]]
        idx < max_meta_slots()
        && s_new.regions.slot_owners[idx].inner_perms.ref_count.value()
                == REF_COUNT_UNUSED
            implies handle_count(s_new.frames, idx) == 0
                && s_new.regions.slot_owners[idx].paths_in_pt.is_empty() by {
        assert(s_new.regions.slot_owners[idx] == s_old.regions.slot_owners[idx]);
    };
    // Clause 3 — Frame ∧ non-sentinel ⟹ active head. A Frame-usage slot
    // in `s_new` is unchanged (a transitioned slot is non-Frame).
    assert forall|idx: usize|
        #![trigger s_new.regions.slot_owners[idx]]
        idx < max_meta_slots()
        && s_new.regions.slot_owners[idx].usage == PageUsage::Frame
        && s_new.regions.slot_owners[idx].inner_perms.ref_count.value()
                != REF_COUNT_UNUSED
        && s_new.regions.slot_owners[idx].inner_perms.ref_count.value()
                != REF_COUNT_UNIQUE
            implies handle_count(s_new.frames, idx) > 0
                || s_new.regions.slot_owners[idx].paths_in_pt.len() > 0 by {
        assert(s_new.regions.slot_owners[idx] == s_old.regions.slot_owners[idx]);
    };
    // Clause 4 — the accounting equation. Same: a Frame-usage slot in
    // `s_new` is unchanged, so the old equation carries.
    assert forall|idx: usize|
        #![trigger s_new.regions.slot_owners[idx]]
        idx < max_meta_slots()
        && s_new.regions.slot_owners[idx].usage == PageUsage::Frame
        && (handle_count(s_new.frames, idx) > 0
            || s_new.regions.slot_owners[idx].paths_in_pt.len() > 0)
            implies {
                let so = s_new.regions.slot_owners[idx];
                let rc = so.inner_perms.ref_count.value();
                &&& rc != REF_COUNT_UNUSED
                &&& rc != REF_COUNT_UNIQUE
                &&& rc == handle_count(s_new.frames, idx) + so.paths_in_pt.len()
                &&& so.inner_perms.storage.is_init()
            } by {
        assert(s_new.regions.slot_owners[idx] == s_old.regions.slot_owners[idx]);
    };
}

proof fn step_new_vm_space<'rcu>(tracked s: &mut VmStore<'rcu>)
    requires old(s).inv()
    ensures final(s).inv()
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
        forall|c: CursorId|
            #[trigger] old(s).cursors.dom().contains(c)
                ==> old(s).cursors[c].vm_space != vs,
        forall|v: VmIoId|
            #[trigger] old(s).vm_ios.dom().contains(v)
                ==> old(s).vm_ios[v].vm_space != Some(vs),
    ensures final(s).inv()
{
    let tracked owner = s.extract_vm_space(vs);
    vm_space::drop_vm_space_step(owner);
}

proof fn step_open_cursor<'rcu>(
    tracked s: &mut VmStore<'rcu>,
    vs: VmSpaceId,
    va: Range<Vaddr>,
)
    requires
        old(s).inv(),
        old(s).vm_spaces.dom().contains(vs),
    ensures final(s).inv()
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

proof fn step_open_cursor_mut<'rcu>(
    tracked s: &mut VmStore<'rcu>,
    vs: VmSpaceId,
    va: Range<Vaddr>,
)
    requires
        old(s).inv(),
        old(s).vm_spaces.dom().contains(vs),
    ensures final(s).inv()
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
    ensures final(s).inv()
{
    let tracked entry = s.extract_cursor(c);
    cursor::drop_cursor_step(entry);
}

proof fn step_cursor_method<'rcu>(
    tracked s: &mut VmStore<'rcu>,
    c: CursorId,
    method: cursor::CursorMethod,
)
    requires
        old(s).inv(),
        old(s).cursors.dom().contains(c),
    ensures final(s).inv()
{
    let tracked mut entry = s.extract_cursor(c);
    cursor::cursor_method_step(&mut entry, &mut s.regions, method);
    s.insert_cursor(c, entry);
}

proof fn step_map<'rcu>(
    tracked s: &mut VmStore<'rcu>,
    c: CursorId,
    frame: UFrame,
    prop: PageProperty,
)
    requires
        old(s).inv(),
        old(s).cursors.dom().contains(c),
    ensures final(s).inv()
{
    let tracked mut entry = s.extract_cursor(c);
    cursor::map_step(&mut entry, &mut s.regions, &mut s.tlb_model, frame, prop);
    s.insert_cursor(c, entry);
}

proof fn step_unmap<'rcu>(tracked s: &mut VmStore<'rcu>, c: CursorId, len: usize)
    requires
        old(s).inv(),
        old(s).cursors.dom().contains(c),
    ensures final(s).inv()
{
    let tracked mut entry = s.extract_cursor(c);
    cursor::cursor_mut_regions_step(
        &mut entry,
        &mut s.regions,
        &mut s.tlb_model,
        cursor::CursorMutRegionsMethod::Unmap(len),
    );
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
    ensures final(s).inv()
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
    requires old(s).inv()
    ensures final(s).inv()
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
    ensures final(s).inv()
{
    let tracked entry = s.extract_vm_io(vio);
    io::drop_vm_io_step(entry);
}

proof fn step_vm_io_method<'rcu>(
    tracked s: &mut VmStore<'rcu>,
    vio: VmIoId,
    method: io::VmIoMethod,
)
    requires
        old(s).inv(),
        old(s).vm_ios.dom().contains(vio),
    ensures final(s).inv()
{
    let tracked mut entry = s.extract_vm_io(vio);
    io::vm_io_method_step(&mut entry, method);
    s.insert_vm_io(vio, entry);
}

proof fn step_read<'rcu>(
    tracked s: &mut VmStore<'rcu>,
    source: VmIoId,
    dest: VmIoId,
)
    requires
        old(s).inv(),
        old(s).vm_ios.dom().contains(source),
        old(s).vm_ios.dom().contains(dest),
        source != dest,
        old(s).vm_ios[source].vm_space is None,
        old(s).vm_ios[source].kind == VmIoKind::Reader,
        old(s).vm_ios[dest].vm_space is None,
        old(s).vm_ios[dest].kind == VmIoKind::Writer,
    ensures final(s).inv()
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

proof fn step_write<'rcu>(
    tracked s: &mut VmStore<'rcu>,
    source: VmIoId,
    dest: VmIoId,
)
    requires
        old(s).inv(),
        old(s).vm_ios.dom().contains(source),
        old(s).vm_ios.dom().contains(dest),
        source != dest,
        old(s).vm_ios[source].vm_space is None,
        old(s).vm_ios[source].kind == VmIoKind::Reader,
        old(s).vm_ios[dest].vm_space is None,
        old(s).vm_ios[dest].kind == VmIoKind::Writer,
    ensures final(s).inv()
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
    ensures final(s).inv()
{
    // `op_pre` is now `true` for this op (#2 fully resolved): *any*
    // `paddr` is accepted, a bad one just fails. The axiom's only
    // slot-perm precondition is `has_safe_slot`-guarded; we discharge
    // it for the in-bound case from `VmStore::inv`'s coverage clause
    // (`inv_implies_correct_addr` → `idx < max_meta_slots()` → coverage
    // → `slots.contains_key`), and it is vacuous out-of-bound.
    if has_safe_slot(paddr) {
        s.regions.inv_implies_correct_addr(paddr);
        assert(s.regions.slots.contains_key(frame_to_index_spec(paddr)));
    }
    let ghost old_frames = s.frames;
    let ghost old_regions = s.regions;
    let tracked res = frame::from_unused_step(&mut s.regions, paddr);
    match res {
        Option::Some(entry) => {
            let ghost id = fresh_frame_id(s.frames);
            axiom_fresh_frame_id_not_in_dom(s.frames);
            let ghost target_idx = frame_to_index_spec(paddr);
            let ghost entry_paddr = entry.paddr;
            s.insert_frame(id, entry);
            assert(s.frames[id].paddr == paddr);

            // Pre target_idx was rc=UNUSED ⟹ pre H==0 ∧ pre paths.empty()
            // (via old accounting_inv's UNUSED clause).
            assert(handle_count(old_frames, target_idx) == 0);
            assert(old_regions.slot_owners[target_idx].paths_in_pt.is_empty());

            // Handle clause: handle ⟹ live, initialised slot. The new
            // handle `id` lands on `target_idx` — post `rc == 1`,
            // `storage.is_init` (`get_from_unused_inner_perms_spec`,
            // `as_unique == false`), and pre `handle_count == 0` so
            // post `handle_count == 1`. Every other slot and its
            // handle-count are unchanged, so the old handle clause
            // carries.
            assert forall|idx: usize|
                #![trigger s.regions.slot_owners[idx]]
                idx < max_meta_slots()
                && handle_count(s.frames, idx) > 0
                    implies {
                        let so = s.regions.slot_owners[idx];
                        let rc = so.inner_perms.ref_count.value();
                        &&& rc != REF_COUNT_UNUSED
                        &&& rc != REF_COUNT_UNIQUE
                        &&& rc >= handle_count(s.frames, idx)
                        &&& so.inner_perms.storage.is_init()
                    } by {
                lemma_handle_count_insert_fresh(old_frames, id, entry, idx);
                if idx == target_idx {
                    assert(old_regions.slot_owners[idx].inner_perms.ref_count.value()
                        == REF_COUNT_UNUSED);
                    assert(handle_count(old_frames, idx) == 0);
                    assert(handle_count(s.frames, idx) == 1);
                } else {
                    assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
                }
            };

            // 5.5c new clause: "UNUSED ⟹ no users". Other idx unchanged
            // (lemma + slot_owner preservation); target_idx is now rc=1.
            assert forall|idx: usize|
                #![trigger s.regions.slot_owners[idx]]
                idx < max_meta_slots()
                && s.regions.slot_owners[idx].inner_perms.ref_count.value()
                        == REF_COUNT_UNUSED
                    implies handle_count(s.frames, idx) == 0
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
                idx < max_meta_slots()
                && s.regions.slot_owners[idx].usage == PageUsage::Frame
                && s.regions.slot_owners[idx].inner_perms.ref_count.value()
                        != REF_COUNT_UNUSED
                && s.regions.slot_owners[idx].inner_perms.ref_count.value()
                        != REF_COUNT_UNIQUE
                    implies handle_count(s.frames, idx) > 0
                        || s.regions.slot_owners[idx].paths_in_pt.len() > 0 by {
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
                idx < max_meta_slots()
                && s.regions.slot_owners[idx].usage == PageUsage::Frame
                && (handle_count(s.frames, idx) > 0
                    || s.regions.slot_owners[idx].paths_in_pt.len() > 0)
                implies {
                    let so = s.regions.slot_owners[idx];
                    let rc = so.inner_perms.ref_count.value();
                    &&& rc != REF_COUNT_UNUSED
                    &&& rc != REF_COUNT_UNIQUE
                    &&& rc == handle_count(s.frames, idx) + so.paths_in_pt.len()
                    &&& so.inner_perms.storage.is_init()
                } by {
                    lemma_handle_count_insert_fresh(old_frames, id, entry, idx);
                    if idx == target_idx {
                        // Pre rc=UNUSED (reparked_spec recommends);
                        // Stage 5.5c accounting_inv UNUSED clause gives
                        // pre H==0 ∧ pre paths.empty() directly.
                        assert(old_regions.slot_owners[idx].inner_perms.ref_count.value()
                            == REF_COUNT_UNUSED);
                        assert(handle_count(old_frames, idx) == 0);
                        assert(handle_count(s.frames, idx) == 1);
                    } else {
                        // Other slot: slot_owner preserved by from_unused
                        // (forall i != target_idx clause in reparked_spec).
                        assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
                    }
            };
        },
        Option::None => {
            // regions unchanged ⇒ accounting preserved from old.
            assert(s.regions =~= old_regions);
        },
    }
}

proof fn step_frame_from_in_use<'rcu>(tracked s: &mut VmStore<'rcu>, paddr: Paddr)
    requires old(s).inv()
    ensures final(s).inv()
{
    // See `step_frame_from_unused`: `op_pre` is `true` (#3b resolved);
    // the `has_safe_slot`-guarded slot-perm precondition is recovered
    // from `VmStore::inv`'s coverage clause for the in-bound case and
    // is vacuous out-of-bound.
    if has_safe_slot(paddr) {
        s.regions.inv_implies_correct_addr(paddr);
        assert(s.regions.slots.contains_key(frame_to_index_spec(paddr)));
    }
    let ghost old_frames = s.frames;
    let ghost old_regions = s.regions;
    let tracked res = frame::from_in_use_step(&mut s.regions, paddr);
    match res {
        Option::Some(entry) => {
            let ghost id = fresh_frame_id(s.frames);
            axiom_fresh_frame_id_not_in_dom(s.frames);
            let ghost target_idx = frame_to_index_spec(paddr);
            s.insert_frame(id, entry);
            assert(s.frames[id].paddr == paddr);

            // Handle clause: handle ⟹ live, initialised slot. The new
            // handle `id` lands on `target_idx`; the strengthened
            // `from_in_use` axiom surfaces post `rc ∉ {UNUSED, UNIQUE}`
            // and `storage.is_init` there, and `rc >= handle_count`
            // carries because `rc` and `handle_count` both step by +1.
            // Every other slot and its handle-count are unchanged.
            assert forall|idx: usize|
                #![trigger s.regions.slot_owners[idx]]
                idx < max_meta_slots()
                && handle_count(s.frames, idx) > 0
                    implies {
                        let so = s.regions.slot_owners[idx];
                        let rc = so.inner_perms.ref_count.value();
                        &&& rc != REF_COUNT_UNUSED
                        &&& rc != REF_COUNT_UNIQUE
                        &&& rc >= handle_count(s.frames, idx)
                        &&& so.inner_perms.storage.is_init()
                    } by {
                lemma_handle_count_insert_fresh(old_frames, id, entry, idx);
                if idx == target_idx {
                    // pre `rc >= handle_count` (old handle clause, or
                    // vacuous when pre `handle_count == 0`); `rc` and
                    // `handle_count` then both step by +1.
                    if handle_count(old_frames, idx) > 0 {
                        assert(old_regions.slot_owners[idx].inner_perms.ref_count.value()
                            >= handle_count(old_frames, idx));
                    }
                } else {
                    assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
                }
            };

            // 5.5c new clause: "UNUSED ⟹ no users". For target: post
            // rc = pre rc + 1 != UNUSED. For other idx: unchanged.
            assert forall|idx: usize|
                #![trigger s.regions.slot_owners[idx]]
                idx < max_meta_slots()
                && s.regions.slot_owners[idx].inner_perms.ref_count.value()
                        == REF_COUNT_UNUSED
                    implies handle_count(s.frames, idx) == 0
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
                idx < max_meta_slots()
                && s.regions.slot_owners[idx].usage == PageUsage::Frame
                && s.regions.slot_owners[idx].inner_perms.ref_count.value()
                        != REF_COUNT_UNUSED
                && s.regions.slot_owners[idx].inner_perms.ref_count.value()
                        != REF_COUNT_UNIQUE
                    implies handle_count(s.frames, idx) > 0
                        || s.regions.slot_owners[idx].paths_in_pt.len() > 0 by {
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
                idx < max_meta_slots()
                && s.regions.slot_owners[idx].usage == PageUsage::Frame
                && (handle_count(s.frames, idx) > 0
                    || s.regions.slot_owners[idx].paths_in_pt.len() > 0)
                implies {
                    let so = s.regions.slot_owners[idx];
                    let rc = so.inner_perms.ref_count.value();
                    &&& rc != REF_COUNT_UNUSED
                    &&& rc != REF_COUNT_UNIQUE
                    &&& rc == handle_count(s.frames, idx) + so.paths_in_pt.len()
                    &&& so.inner_perms.storage.is_init()
                } by {
                    lemma_handle_count_insert_fresh(old_frames, id, entry, idx);
                    if idx == target_idx {
                        // Pre usage(target)==Frame: `get_from_in_use`
                        // preserves `usage`, and the clause antecedent
                        // gives post `usage == Frame`. Old clause 3
                        // then fires ⟹ pre active head ⟹ old accounting
                        // equation fires.
                        assert(old_regions.slot_owners[idx].usage == PageUsage::Frame);
                    } else {
                        assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
                    }
            };
        },
        Option::None => {
            assert(s.regions =~= old_regions);
        },
    }
}

proof fn step_frame_drop<'rcu>(tracked s: &mut VmStore<'rcu>, fid: FrameId)
    requires
        old(s).inv(),
        old(s).frames.dom().contains(fid),
        // Mirrors the residual conjunct of `op_pre[FrameDrop]`: the
        // exec `Frame::drop_requires` strengthening (`rc == 1 ⟹
        // paths_in_pt.is_empty()`) is not universally derivable from
        // the embedding's Frame-scoped accounting, so it travels in via
        // the dispatcher's `op_pre` and into the step.
        old(s).regions.slot_owners[frame_to_index_spec(old(s).frames[fid].paddr)]
                .inner_perms.ref_count.value() == 1
            ==> old(s).regions.slot_owners[frame_to_index_spec(old(s).frames[fid].paddr)]
                    .paths_in_pt.is_empty(),
    ensures final(s).inv()
{
    // Derive the full `frame::drop_pre` from `VmStore::inv` alone (#4
    // fully resolved). The structural coverage clauses give
    // `slots.contains_key`, `raw_count == 0`, `in_list == 0`. The
    // usage-independent **handle clause** of `accounting_inv` fires at
    // `idx_p` (fid ∈ frames ⟹ handle_count ≥ 1): it gives
    // `rc ∉ {UNUSED, UNIQUE}`, `rc ≥ handle_count ≥ 1`, and
    // `storage.is_init`; `rc <= MAX` then follows from the
    // forbidden-zone exclusion in `MetaSlotOwner::inv`. No `usage`
    // assumption is needed — the handle clause holds for any slot.
    let ghost p = s.frames[fid].paddr;
    assert(has_safe_slot(p));
    s.regions.inv_implies_correct_addr(p);
    let ghost idx_p = frame_to_index_spec(p);
    assert(idx_p < max_meta_slots());
    // fid ∈ frames ⟹ handle_count(s.frames, idx_p) ≥ 1: filter
    // applied to s.frames.dom().contains(fid) with predicate true.
    assert(s.frames.dom().filter(
        |gid: FrameId| frame_to_index_spec(s.frames[gid].paddr) == idx_p)
        .contains(fid));
    assert(handle_count(s.frames, idx_p) >= 1);
    // Handle clause ⇒ drop_pre.
    assert(frame::drop_pre(s.regions, p));
    let ghost target_idx = frame_to_index_spec(p);
    let ghost old_frames = s.frames;
    let ghost old_regions = s.regions;
    let tracked entry = s.extract_frame(fid);
    frame::drop_step(&mut s.regions, entry);

    // Discharge accounting_inv on the post-drop state.

    // Handle clause: handle ⟹ live, initialised slot. For idx ≠ target,
    // slot and handle-count are unchanged. For target: a *remaining*
    // handle (post `handle_count > 0`) means pre `handle_count >= 2`,
    // so pre `rc >= 2 > 1` (old handle clause) and `drop_step` took the
    // decrement branch — post `rc = pre rc - 1` stays non-sentinel,
    // `>= post handle_count`, with storage preserved.
    assert forall|idx: usize|
        #![trigger s.regions.slot_owners[idx]]
        idx < max_meta_slots()
        && handle_count(s.frames, idx) > 0
            implies {
                let so = s.regions.slot_owners[idx];
                let rc = so.inner_perms.ref_count.value();
                &&& rc != REF_COUNT_UNUSED
                &&& rc != REF_COUNT_UNIQUE
                &&& rc >= handle_count(s.frames, idx)
                &&& so.inner_perms.storage.is_init()
            } by {
        lemma_handle_count_remove(old_frames, fid, idx);
        if idx == target_idx {
            // post handle_count > 0 ⟹ pre handle_count >= 2.
            assert(handle_count(old_frames, idx) >= 2);
            // old handle clause ⟹ pre rc >= pre handle_count >= 2 > 1.
            assert(old_regions.slot_owners[idx].inner_perms.ref_count.value()
                >= handle_count(old_frames, idx));
        } else {
            assert(s.regions.slot_owners[idx] == old_regions.slot_owners[idx]);
        }
    };

    // 5.5c new clause: "UNUSED ⟹ no users". For non-target: unchanged.
    // For target: if drop teardown (rc 1→UNUSED), need post H==0 and
    // paths empty. Both hold: pre eqn 1==H+P with H>=1 ⟹ H==1, P==0
    // ⟹ post H==0 (fid removed) and post paths == pre paths == empty.
    assert forall|idx: usize|
        #![trigger s.regions.slot_owners[idx]]
        idx < max_meta_slots()
        && s.regions.slot_owners[idx].inner_perms.ref_count.value()
                == REF_COUNT_UNUSED
            implies handle_count(s.frames, idx) == 0
                && s.regions.slot_owners[idx].paths_in_pt.is_empty() by {
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
        idx < max_meta_slots()
        && s.regions.slot_owners[idx].usage == PageUsage::Frame
        && s.regions.slot_owners[idx].inner_perms.ref_count.value()
                != REF_COUNT_UNUSED
        && s.regions.slot_owners[idx].inner_perms.ref_count.value()
                != REF_COUNT_UNIQUE
            implies handle_count(s.frames, idx) > 0
                || s.regions.slot_owners[idx].paths_in_pt.len() > 0 by {
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
        idx < max_meta_slots()
        && s.regions.slot_owners[idx].usage == PageUsage::Frame
        && (handle_count(s.frames, idx) > 0
            || s.regions.slot_owners[idx].paths_in_pt.len() > 0)
        implies {
            let so = s.regions.slot_owners[idx];
            let rc = so.inner_perms.ref_count.value();
            &&& rc != REF_COUNT_UNUSED
            &&& rc != REF_COUNT_UNIQUE
            &&& rc == handle_count(s.frames, idx) + so.paths_in_pt.len()
            &&& so.inner_perms.storage.is_init()
        } by {
            lemma_handle_count_remove(old_frames, fid, idx);
            if idx == target_idx {
                // Pre fid contributes ⇒ pre H >= 1 ⇒ pre active head.
                // Pre `usage == Frame`: `drop_step` preserves `usage`,
                // and the clause antecedent gives post `usage == Frame`.
                assert(old_regions.slot_owners[idx].usage == PageUsage::Frame);
                assert(handle_count(old_frames, idx) > 0);
                let ghost pre_rc = old_regions.slot_owners[idx]
                    .inner_perms.ref_count.value();
                let ghost pre_h = handle_count(old_frames, idx);
                let ghost pre_p = old_regions.slot_owners[idx].paths_in_pt.len();
                assert(pre_rc == pre_h + pre_p);
                // Residual `drop_pre`: pre rc <= MAX, pre rc >= 1, != UNUSED/UNIQUE.
                let ghost post_h = handle_count(s.frames, idx);
                assert(post_h == (pre_h - 1) as nat);
                // drop_step now exposes paths preservation at idx.
                let ghost post_p = s.regions.slot_owners[idx].paths_in_pt.len();
                assert(post_p == pre_p);
                let ghost post_rc = s.regions.slot_owners[idx]
                    .inner_perms.ref_count.value();
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

pub axiom fn axiom_fresh_vm_space_id_not_in_dom<'a>(
    m: Map<VmSpaceId, VmSpaceOwner>,
)
    ensures
        !m.dom().contains(fresh_vm_space_id(m)),
;

pub axiom fn axiom_fresh_cursor_id_not_in_dom<'rcu>(
    m: Map<CursorId, CursorEntry<'rcu>>,
)
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
    tracked guards: Guards<'rcu, UserPtConfig>,
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

} // verus!
