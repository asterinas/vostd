// SPDX-License-Identifier: MPL-2.0
//! Spec/proof companion for [`crate::mm::frame::segment`].
use core::ops::Range;

use vstd::prelude::*;

use vstd_extra::{drop_tracking::TrackDrop, ownership::*};

use crate::specs::{
    arch::PAGE_SIZE,
    mm::{
        frame::{
            mapping::{frame_to_index, index_to_meta},
            meta_region_owners::MetaRegionOwners,
        },
        virt_mem::MemView,
    },
};

use crate::mm::{
    Paddr, Vaddr,
    frame::{AnyFrameMeta, Frame, Segment},
    paddr_to_vaddr,
};

verus! {

impl<M: AnyFrameMeta + ?Sized> TrackDrop for Segment<M> {
    /// The segment carries its frame fractions directly; `ManuallyDrop`
    /// therefore only needs a unit token after those fractions move out.
    type State = MetaRegionOwners;

    type Obligation = ();

    open spec fn tracked_redeem_requires(self, s: Self::State) -> bool {
        true
    }

    open spec fn tracked_redeem_ensures(
        self,
        s0: Self::State,
        s1: Self::State,
        obl: Self::Obligation,
    ) -> bool {
        s0 == s1
    }

    proof fn tracked_redeem(self, tracked s: &mut Self::State) -> (tracked obl: Self::Obligation) {
        ()
    }

    open spec fn drop_requires(self, s: Self::State, obl: Self::Obligation) -> bool {
        s.inv()
    }

    open spec fn drop_ensures(
        self,
        s0: Self::State,
        s1: Self::State,
        obl: Self::Obligation,
    ) -> bool {
        true
    }
}

/// Number of frames in a page-aligned physical range.
#[verifier::inline]
pub open spec fn seg_nframes(range: Range<Paddr>) -> int {
    (range.end - range.start) / PAGE_SIZE as int
}

impl<M: AnyFrameMeta + ?Sized> Segment<M> {
    /// The cross-object relation between a [`Segment`] and the global
    /// [`MetaRegionOwners`].
    ///
    /// For every frame `i` in the segment, this asserts:
    /// - the slot owner and canonical slot permission are present in `regions`,
    /// - the slot's `slot_vaddr` is consistent with its index,
    /// - the slot has a live, non-`UNUSED` reference count,
    /// - the segment carries the matching metadata fraction,
    /// - the slot is a data-frame slot with no page-table paths,
    /// - distinct frames in the segment map to distinct slot indices.
    ///
    /// This is an invariant preserved by operations that transform a
    /// `Segment` together with `MetaRegionOwners`. The segment's own `range`
    /// is the only identity source; there is no separate segment owner token.
    pub open spec fn relate_regions(&self, regions: MetaRegionOwners) -> bool {
        &&& self.permissions().len() == seg_nframes(self.range())
        &&& forall|i: int|
            #![trigger frame_to_index((self.range().start + i * PAGE_SIZE) as usize)]
            0 <= i < seg_nframes(self.range()) ==> {
                let idx = frame_to_index((self.range().start + i * PAGE_SIZE) as usize);
                &&& Frame::<M>::frame_permission_wf(
                    regions,
                    (self.range().start + i * PAGE_SIZE) as usize,
                    self.permissions()[i],
                )
                &&& regions.contains(idx)
                &&& regions.slot_owners[idx].slot_vaddr == index_to_meta(idx)
                &&& regions.slot_owners[idx].ref_count()
                    > 0
                // Segment frames are shared (never `UNIQUE`).
                &&& regions.slot_owners[idx].ref_count()
                    <= crate::mm::frame::meta::REF_COUNT_MAX
                // A segment holds its frames as a unit; they are not
                // mapped into any page table, so the slot carries no PTE
                // paths. Needed to discharge `Frame::drop`'s strengthened
                // precondition (ref_count == 1 ==> paths_in_pt empty`)
                // in the per-frame teardown loop.
                &&& regions.slot_owners[idx].paths_in_pt.is_empty()
                &&& regions.slot_owners[idx].usage is Frame
            }
        &&& forall|i: int, j: int|
            #![trigger frame_to_index((self.range().start + i * PAGE_SIZE) as usize),
                frame_to_index((self.range().start + j * PAGE_SIZE) as usize)]
            0 <= i < j < seg_nframes(self.range()) ==> frame_to_index(
                (self.range().start + i * PAGE_SIZE) as usize,
            ) != frame_to_index((self.range().start + j * PAGE_SIZE) as usize)
    }

    /// Manually instantiates the [`relate_regions`] forall at a specific index.
    /// Use this to extract per-frame facts without fighting trigger inference.
    pub proof fn relate_regions_at(&self, regions: MetaRegionOwners, i: int)
        requires
            self.relate_regions(regions),
            0 <= i < seg_nframes(self.range()),
        ensures
            ({
                let idx = frame_to_index((self.range().start + i * PAGE_SIZE) as usize);
                &&& Frame::<M>::frame_permission_wf(
                    regions,
                    (self.range().start + i * PAGE_SIZE) as usize,
                    self.permissions()[i],
                )
                &&& regions.contains(
                    idx,
                )
                // Borrow-protocol transition: `raw_count` is dormant.
                &&& regions.slot_owners[idx].slot_vaddr == index_to_meta(idx)
                &&& regions.slot_owners[idx].ref_count() > 0
                &&& regions.slot_owners[idx].ref_count() <= crate::mm::frame::meta::REF_COUNT_MAX
                &&& regions.slot_owners[idx].paths_in_pt.is_empty()
                &&& regions.slot_owners[idx].usage is Frame
            }),
    {
        // Trigger the forall at index `i`.
        let _ = frame_to_index((self.range().start + i * PAGE_SIZE) as usize);
    }

    /// Manually instantiates the [`relate_regions`] distinctness forall at a
    /// specific index pair: distinct in-range frames map to distinct slot
    /// indices. Reusable lever for `from_unused`/`split`/`slice` proofs.
    pub proof fn relate_regions_distinct(&self, regions: MetaRegionOwners, i: int, j: int)
        requires
            self.relate_regions(regions),
            0 <= i < j < seg_nframes(self.range()),
        ensures
            frame_to_index((self.range().start + i * PAGE_SIZE) as usize) != frame_to_index(
                (self.range().start + j * PAGE_SIZE) as usize,
            ),
    {
        // Trigger the distinctness forall at `(i, j)`.
        let _ = frame_to_index((self.range().start + i * PAGE_SIZE) as usize);
        let _ = frame_to_index((self.range().start + j * PAGE_SIZE) as usize);
    }

    /// The bundled invariant for [`Segment`] operations that thread the global
    /// `regions`: the segment's own invariant, the region invariant, and the
    /// cross-object relation tying this segment's range to `regions`.
    ///
    /// Mirrors the `invariants` bundles used throughout the page-table / cursor
    /// code — it collapses the clauses repeated across `split`, `slice`,
    /// `into_raw`, `next`, and `drop` into one predicate.
    pub open spec fn invariants(&self, regions: MetaRegionOwners) -> bool {
        &&& self.inv()
        &&& regions.inv()
        &&& self.relate_regions(regions)
    }

    /// Whether a [`MemView`] covers the segment through the kernel direct mapping.
    ///
    /// This predicate only describes the virtual-to-physical relation and the
    /// presence of initialized backing frame contents.
    pub open spec fn kernel_mem_view_covers(&self, view: &MemView) -> bool {
        &&& self.inv()
        &&& view.mappings_are_disjoint()
        &&& forall|vaddr: Vaddr|
            #![trigger view.addr_transl(vaddr)]
            paddr_to_vaddr(self.start_paddr()) <= vaddr < paddr_to_vaddr(self.start_paddr())
                + self.end_paddr() - self.start_paddr() ==> {
                &&& view.addr_transl(vaddr) is Some
                &&& view.memory.contains_key((view.addr_transl(vaddr)->0).0)
                &&& view.memory[(view.addr_transl(vaddr)->0).0].inv()
                &&& view.memory[(view.addr_transl(vaddr)->0).0].contents[(view.addr_transl(
                    vaddr,
                )->0).1 as int] is Init
            }
        &&& forall|paddr: Paddr|
            #![trigger paddr_to_vaddr(paddr)]
            self.start_paddr() <= paddr < self.end_paddr() ==> {
                let vaddr = paddr_to_vaddr(paddr);
                &&& view.addr_transl(vaddr) is Some
                &&& (view.addr_transl(vaddr)->0).0 <= paddr
                &&& paddr < (view.addr_transl(vaddr)->0).0 + view.memory[(view.addr_transl(
                    vaddr,
                )->0).0].size@
                &&& (view.addr_transl(vaddr)->0).1 == paddr - (view.addr_transl(vaddr)->0).0
                &&& view.memory.contains_key((view.addr_transl(vaddr)->0).0)
                &&& view.memory[(view.addr_transl(vaddr)->0).0].inv()
                &&& view.memory[(view.addr_transl(vaddr)->0).0].contents[(view.addr_transl(
                    vaddr,
                )->0).1 as int] is Init
            }
    }
}

/// Helper spec: the slot index of the j-th frame in a segment whose physical
/// range starts at `range_start`. Unlike a let-bound ghost closure (which Verus
/// treats opaquely under SMT), a `spec fn` is auto-unfolded so equalities
/// between `frame_idx_at(...)` and `frame_to_index(...)` are derivable.
#[verifier::inline]
pub open spec fn frame_idx_at(range_start: usize, j: int) -> int {
    frame_to_index((range_start + j * PAGE_SIZE) as usize)
}

} // verus!
