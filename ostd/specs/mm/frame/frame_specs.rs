use vstd::prelude::*;

use vstd_extra::cast_ptr::*;
use vstd_extra::ownership::*;

use crate::mm::frame::meta::{mapping::frame_to_index, REF_COUNT_UNUSED};
use crate::mm::frame::*;
use crate::mm::{Paddr, PagingLevel, Vaddr};
use crate::specs::arch::mm::{MAX_NR_PAGES, MAX_PADDR, PAGE_SIZE};
use crate::specs::mm::frame::meta_owners::MetaSlotStorage;
use crate::specs::mm::frame::meta_region_owners::MetaRegionModel;

use core::marker::PhantomData;

verus! {

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> UniqueFrame<M> {

    pub open spec fn from_unused_spec(paddr: Paddr, metadata: M, pre: MetaRegionModel)
        -> (Self, MetaRegionModel)
        recommends
            paddr % PAGE_SIZE == 0,
            paddr < MAX_PADDR,
            pre.inv(),
            pre.slots[frame_to_index(paddr)].ref_count == REF_COUNT_UNUSED,
    {
        let (ptr, post) = MetaSlot::get_from_unused_spec(paddr, metadata, true, pre);
        (UniqueFrame { ptr, _marker: PhantomData }, post)
    }

    pub proof fn from_unused_properties(paddr: Paddr, metadata: M, pre: MetaRegionModel)
        requires
            paddr % 4096 == 0,
            paddr < MAX_PADDR,
            pre.inv(),
            pre.slots[paddr / 4096].ref_count == REF_COUNT_UNUSED,
        ensures
            UniqueFrame::from_unused_spec(paddr, metadata, pre).1.inv(),
    { }
}

} // verus!
