use vstd::prelude::*;

use vstd_extra::cast_ptr::*;
use vstd_extra::ownership::*;

use crate::mm::frame::meta::{get_slot_spec, mapping::frame_to_index, REF_COUNT_UNUSED};
use crate::mm::frame::*;
use crate::mm::{Paddr, PagingLevel, Vaddr};
use crate::specs::arch::mm::{MAX_NR_PAGES, MAX_PADDR, PAGE_SIZE};
use crate::specs::mm::frame::meta_owners::{MetaPerm, MetaSlotStorage};
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;

use core::marker::PhantomData;

verus! {

impl<'a, M: AnyFrameMeta> Frame<M> {
    /// # Internal Safety Spec
    /// This is a condition that supports unsafe Rust encapsulation. It should never be exposed to
    /// the API client.
    pub open spec fn from_raw_requires(regions: MetaRegionOwners, paddr: Paddr) -> bool {
        &&& regions.slot_owners.contains_key(frame_to_index(paddr))
        &&& regions.slot_owners[frame_to_index(paddr)].raw_count == 1
        &&& regions.slot_owners[frame_to_index(paddr)].self_addr == frame_to_meta(paddr)
        &&& has_safe_slot(paddr) // TODO: this should actually imply the first condition
        &&& !regions.slots.contains_key(frame_to_index(paddr)) // Whomever called `into_raw` should hold the permission.
        &&& regions.inv()
    }

    pub open spec fn from_raw_ensures(
        old_regions: MetaRegionOwners,
        new_regions: MetaRegionOwners,
        paddr: Paddr,
        r: Self,
    ) -> bool {
        &&& new_regions.inv()
        &&& new_regions.slots.contains_key(frame_to_index(paddr))
        &&& new_regions.slot_owners[frame_to_index(paddr)].raw_count == 0
        &&& new_regions.slot_owners[frame_to_index(paddr)].inner_perms ==
            old_regions.slot_owners[frame_to_index(paddr)].inner_perms
        &&& new_regions.slot_owners[frame_to_index(paddr)].usage ==
            old_regions.slot_owners[frame_to_index(paddr)].usage
        &&& new_regions.slot_owners[frame_to_index(paddr)].path_if_in_pt ==
            old_regions.slot_owners[frame_to_index(paddr)].path_if_in_pt
        &&& new_regions.slot_owners[frame_to_index(paddr)].self_addr == r.ptr.addr()
        &&& forall|i: usize|
            #![trigger new_regions.slot_owners[i], old_regions.slot_owners[i]]
            i != frame_to_index(paddr) ==> new_regions.slot_owners[i] == old_regions.slot_owners[i]
        &&& r.ptr.addr() == frame_to_meta(paddr)
        &&& r.paddr() == paddr
    }


    // ── into_raw precondition predicates ──

    /// **Safety Invariant**: The frame's structural invariant must hold.
    pub open spec fn into_raw_pre_frame_inv(self) -> bool {
        self.inv()
    }

    /// **Bookkeeping**: The frame must be in use (not unused).
    pub open spec fn into_raw_pre_not_unused(self, regions: MetaRegionOwners) -> bool {
        regions.slot_owners[self.index()].inner_perms.ref_count.value() != REF_COUNT_UNUSED
    }

    // ── into_raw postcondition predicates ──

    /// **Correctness**: The frame's raw count is incremented.
    pub open spec fn into_raw_post_raw_count_incremented(
        self,
        old_regions: MetaRegionOwners,
        new_regions: MetaRegionOwners,
    ) -> bool {
        &&& new_regions.slot_owners.contains_key(self.index())
        &&& new_regions.slot_owners[self.index()].raw_count
            == (old_regions.slot_owners[self.index()].raw_count + 1) as usize
    }

    /// **Safety**: Frames other than this one are not affected by the call.
    pub open spec fn into_raw_post_noninterference(
        self,
        old_regions: MetaRegionOwners,
        new_regions: MetaRegionOwners,
    ) -> bool {
        &&& forall|i: usize|
            #![trigger new_regions.slots[i], old_regions.slots[i]]
            i != self.index() && old_regions.slots.contains_key(i)
                ==> new_regions.slots.contains_key(i)
                    && new_regions.slots[i] == old_regions.slots[i]
        &&& forall|i: usize|
            #![trigger new_regions.slot_owners[i], old_regions.slot_owners[i]]
            i != self.index() ==> new_regions.slot_owners[i] == old_regions.slot_owners[i]
        &&& new_regions.slot_owners.dom() =~= old_regions.slot_owners.dom()
    }
}

} // verus!
