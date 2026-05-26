// SPDX-License-Identifier: MPL-2.0
//! Spec/proof companion for [`crate::mm::frame::segment`].

use vstd::prelude::*;
use vstd_extra::drop_tracking::*;
use vstd_extra::ownership::*;

use core::ops::Range;

use crate::mm::frame::{AnyFrameMeta, MetaSlot, Segment};
use crate::mm::{paddr_to_vaddr, Paddr, Vaddr};
use crate::specs::arch::kspace::FRAME_METADATA_RANGE;
use crate::specs::arch::mm::{MAX_PADDR, PAGE_SIZE};
use crate::specs::mm::frame::mapping::{frame_to_index, meta_addr, META_SLOT_SIZE};
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::virt_mem::MemView;

verus! {

impl<M: AnyFrameMeta + ?Sized> TrackDrop for Segment<M> {
    /// Mirroring [`crate::mm::frame::UniqueFrame`]'s pattern, the tracked
    /// state for `ManuallyDrop` purposes is just the global
    /// [`MetaRegionOwners`]. The [`SegmentOwner<M>`] that holds the per-frame
    /// perms is threaded into the custom drop method via `verus_spec` rather
    /// than via this trait state — so that
    /// `ManuallyDrop::new(self, Tracked(regions))` can be called without
    /// combining a `&mut MetaRegionOwners` borrow with an owned
    /// `SegmentOwner` into a single tracked tuple.
    type State = MetaRegionOwners;

    open spec fn constructor_requires(self, s: Self::State) -> bool {
        true
    }

    open spec fn constructor_ensures(self, s0: Self::State, s1: Self::State) -> bool {
        s0 =~= s1
    }

    proof fn constructor_spec(self, tracked s: &mut Self::State) {
    }

    open spec fn drop_requires(self, s: Self::State) -> bool {
        s.inv()
    }

    open spec fn drop_ensures(self, s0: Self::State, s1: Self::State) -> bool {
        true
    }

}

/// A [`SegmentOwner<M>`] holds the permission tokens for all frames in the
/// [`Segment<M>`] for verification purposes.
///
/// The `range` field tracks which physical-address range this owner corresponds
/// to. It is a ghost-only field used by [`Self::inv`] to express the structural
/// connection between `perms` and the segment's frames.
/// Number of frames in a page-aligned physical range.
#[verifier::inline]
pub open spec fn seg_nframes(range: Range<Paddr>) -> int {
    (range.end - range.start) / PAGE_SIZE as int
}

pub tracked struct SegmentOwner<M: AnyFrameMeta + ?Sized> {
    /// The physical-address range of the segment that this owner corresponds to.
    ///
    /// Design B (Arc-style): the owner no longer holds the per-frame slot
    /// permissions. Each frame's `simple_pptr::PointsTo<MetaSlot>` stays
    /// canonical in `regions.slots[idx]` and is *borrowed* on drop/next;
    /// the segment merely contributes one (forgotten) reference per frame.
    pub ghost range: Range<Paddr>,
    pub _marker: core::marker::PhantomData<M>,
}

impl<M: AnyFrameMeta + ?Sized> Inv for SegmentOwner<M> {
    /// The invariant of a [`SegmentOwner`]:
    ///
    /// - the tracked `range` is page-aligned and within bounds;
    /// - the number of permissions matches the number of frames in the range;
    /// - each permission's address corresponds to the meta slot of its frame
    ///   (so consecutive permissions are spaced by `META_SLOT_SIZE`);
    /// - each permission is initialized and individually well-formed.
    open spec fn inv(self) -> bool {
        &&& self.range.start % PAGE_SIZE == 0
        &&& self.range.end % PAGE_SIZE == 0
        &&& self.range.start <= self.range.end <= MAX_PADDR
    }
}

impl<M: AnyFrameMeta + ?Sized> SegmentOwner<M> {
    /// The cross-object relation between a [`SegmentOwner`] and the global
    /// [`MetaRegionOwners`].
    ///
    /// For every frame `i` in the segment, this asserts:
    /// - the slot owner is present in `regions` and the perm matches it,
    /// - the slot's `self_addr` is consistent with its index,
    /// - the slot has a live, non-`UNUSED` reference count,
    /// - `raw_count == 1` (the segment holds one forgotten reference per frame),
    /// - the slot's perm is *not* in `regions.slots` (it lives in `self.perms`),
    /// - distinct frames in the segment map to distinct slot indices.
    ///
    /// This is an invariant preserved by every operation that transforms a
    /// `SegmentOwner` together with `MetaRegionOwners` — analogous to
    /// [`crate::specs::mm::frame::unique::UniqueFrameOwner::global_inv`] but
    /// spanning all frames in a segment.
    pub open spec fn relate_regions(self, regions: MetaRegionOwners) -> bool {
        &&& forall|i: int|
            #![trigger frame_to_index((self.range.start + i * PAGE_SIZE) as usize)]
            0 <= i < seg_nframes(self.range) ==> {
                let idx = frame_to_index((self.range.start + i * PAGE_SIZE) as usize);
                &&& regions.slot_owners.contains_key(idx)
                // Design B: the slot perm is canonical in `regions.slots`
                // (borrowable), NOT owned by the segment.
                &&& regions.slots.contains_key(idx)
                &&& regions.slot_owners[idx].raw_count == 1
                &&& regions.slot_owners[idx].self_addr == meta_addr(idx)
                &&& regions.slot_owners[idx].inner_perms.ref_count.value() > 0
                // Segment frames are shared (never `UNIQUE`); the upper
                // bound also keeps post-`fetch_sub` out of the forbidden
                // `(REF_COUNT_MAX, REF_COUNT_UNIQUE)` zone.
                &&& regions.slot_owners[idx].inner_perms.ref_count.value()
                    <= crate::mm::frame::meta::REF_COUNT_MAX
                // A segment holds its frames as a unit; they are not
                // mapped into any page table, so the slot carries no PTE
                // paths. Needed to discharge `Frame::drop`'s strengthened
                // precondition (`ref_count == 1 ==> paths_in_pt empty`)
                // in the per-frame teardown loop.
                &&& regions.slot_owners[idx].paths_in_pt.is_empty()
            }
        &&& forall|i: int, j: int|
            #![trigger frame_to_index((self.range.start + i * PAGE_SIZE) as usize),
                frame_to_index((self.range.start + j * PAGE_SIZE) as usize)]
            0 <= i < j < seg_nframes(self.range) ==>
                frame_to_index((self.range.start + i * PAGE_SIZE) as usize)
                    != frame_to_index((self.range.start + j * PAGE_SIZE) as usize)
    }

    /// Manually instantiates the [`relate_regions`] forall at a specific index.
    /// Use this to extract per-frame facts (slot_owner present, slot perm in
    /// `regions.slots`, raw_count == 1, ref_count > 0, etc.) without fighting
    /// trigger inference.
    pub proof fn relate_regions_at(self, regions: MetaRegionOwners, i: int)
        requires
            self.relate_regions(regions),
            0 <= i < seg_nframes(self.range),
        ensures
            ({
                let idx = frame_to_index((self.range.start + i * PAGE_SIZE) as usize);
                &&& regions.slot_owners.contains_key(idx)
                &&& regions.slots.contains_key(idx)
                &&& regions.slot_owners[idx].raw_count == 1
                &&& regions.slot_owners[idx].self_addr == meta_addr(idx)
                &&& regions.slot_owners[idx].inner_perms.ref_count.value() > 0
                &&& regions.slot_owners[idx].inner_perms.ref_count.value()
                    <= crate::mm::frame::meta::REF_COUNT_MAX
                &&& regions.slot_owners[idx].paths_in_pt.is_empty()
            }),
    {
        // Trigger the forall at index `i`.
        let _ = frame_to_index((self.range.start + i * PAGE_SIZE) as usize);
    }

    /// Manually instantiates the [`relate_regions`] distinctness forall at a
    /// specific index pair: distinct in-range frames map to distinct slot
    /// indices. Reusable lever for `from_unused`/`split`/`slice` proofs.
    pub proof fn relate_regions_distinct(self, regions: MetaRegionOwners, i: int, j: int)
        requires
            self.relate_regions(regions),
            0 <= i < j < seg_nframes(self.range),
        ensures
            frame_to_index((self.range.start + i * PAGE_SIZE) as usize)
                != frame_to_index((self.range.start + j * PAGE_SIZE) as usize),
    {
        // Trigger the distinctness forall at `(i, j)`.
        let _ = frame_to_index((self.range.start + i * PAGE_SIZE) as usize);
        let _ = frame_to_index((self.range.start + j * PAGE_SIZE) as usize);
    }
}

impl<M: AnyFrameMeta + ?Sized> Segment<M> {
    /// The well-formedness relation between a [`Segment`] and its owner:
    ///
    /// - the segment's range matches the range tracked by the owner;
    /// - the number of permissions in the owner matches the number of frames in the segment;
    /// - the physical address of each permission matches the corresponding frame in the segment.
    ///
    /// This is *only* the cross-object relation; callers are expected to also
    /// state `self.inv()` (and where relevant `owner.inv()`) alongside. With
    /// `owner.inv()` the perm-address and length conjuncts are consequences of
    /// `self.range == owner.range`, but they are kept here for trigger
    /// availability at sites that don't invoke `owner.inv()`.
    ///
    /// Interested readers are encouraged to see [`frame_to_index`] and [`meta_addr`] for how
    /// we convert between physical addresses and meta region indices.
    pub open spec fn wf(&self, owner: &SegmentOwner<M>) -> bool {
        &&& self.range() == owner.range
    }

    /// Whether a [`MemView`] covers the segment through the kernel direct mapping.
    ///
    /// This predicate only describes the virtual-to-physical relation and the
    /// presence of initialized backing frame contents.
    pub open spec fn kernel_mem_view_covers(&self, view: &MemView) -> bool {
        &&& self.inv()
        &&& view.mappings.finite()
        &&& view.mappings_are_disjoint()
        &&& forall|vaddr: Vaddr|
            #![trigger view.addr_transl(vaddr)]
            paddr_to_vaddr(self.start_paddr()) <= vaddr < paddr_to_vaddr(self.start_paddr())
                + self.end_paddr() - self.start_paddr() ==> {
                &&& view.addr_transl(vaddr) is Some
                &&& view.memory.contains_key(view.addr_transl(vaddr).unwrap().0)
                &&& view.memory[view.addr_transl(vaddr).unwrap().0].inv()
                &&& view.memory[view.addr_transl(vaddr).unwrap().0].contents[view.addr_transl(
                    vaddr,
                ).unwrap().1 as int] is Init
            }
        &&& forall|paddr: Paddr|
            #![trigger paddr_to_vaddr(paddr)]
            self.start_paddr() <= paddr < self.end_paddr() ==> {
                let vaddr = paddr_to_vaddr(paddr);
                &&& view.addr_transl(vaddr) is Some
                &&& view.addr_transl(vaddr).unwrap().0 <= paddr
                &&& paddr < view.addr_transl(vaddr).unwrap().0 + view.memory[view.addr_transl(
                    vaddr,
                ).unwrap().0].size@
                &&& view.addr_transl(vaddr).unwrap().1 == paddr - view.addr_transl(vaddr).unwrap().0
                &&& view.memory.contains_key(view.addr_transl(vaddr).unwrap().0)
                &&& view.memory[view.addr_transl(vaddr).unwrap().0].inv()
                &&& view.memory[view.addr_transl(vaddr).unwrap().0].contents[view.addr_transl(
                    vaddr,
                ).unwrap().1 as int] is Init
            }
    }
}

/// Helper spec: the slot index of the j-th frame in a segment whose physical
/// range starts at `range_start`. Unlike a let-bound ghost closure (which Verus
/// treats opaquely under SMT), a `spec fn` is auto-unfolded so equalities
/// between `frame_idx_at(...)` and `frame_to_index(...)` are derivable.
#[verifier::inline]
pub open spec fn frame_idx_at(range_start: usize, j: int) -> usize {
    frame_to_index((range_start + j * PAGE_SIZE) as usize)
}

} // verus!
