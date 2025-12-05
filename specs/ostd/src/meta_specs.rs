use vstd::cell;
use vstd::prelude::*;
use vstd::simple_pptr::{self, PPtr};

use vstd_extra::cast_ptr::*;
use vstd_extra::ownership::*;

use aster_common::prelude::frame::*;
use aster_common::prelude::*;

use std::marker::PhantomData;

verus! {

impl MetaSlot {
    #[rustc_allow_incoherent_impl]
    pub open spec fn from_unused_slot_spec<M: AnyFrameMeta>(
        paddr: Paddr,
        metadata: M,
        as_unique_ptr: bool,
    ) -> MetaSlotModel {
        let (rc, status) = if as_unique_ptr {
            (REF_COUNT_UNIQUE, MetaSlotStatus::UNIQUE)
        } else {
            (1, MetaSlotStatus::SHARED)
        };
        MetaSlotModel {
            status,
            storage: cell::MemContents::Uninit,  //TODO: fix this cell::MemContents::Init(metadata.to_repr()),
            ref_count: rc,
            vtable_ptr: simple_pptr::MemContents::Init(metadata.vtable_ptr()),
            in_list: 0,
            self_addr: frame_to_meta(paddr),
            usage: PageUsage::Frame,
        }
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn get_from_unused_spec<M: AnyFrameMeta>(
        paddr: Paddr,
        metadata: M,
        as_unique_ptr: bool,
        // -- ghost parameters --
        pre: MetaRegionModel,
    ) -> (PPtr<MetaSlot>, MetaRegionModel)
        recommends
            paddr % 4096 == 0,
            paddr < MAX_PADDR(),
            pre.inv(),
            pre.slots[frame_to_index(paddr)].ref_count == REF_COUNT_UNUSED,
    {
        let ptr = get_slot_spec(paddr);
        let idx = frame_to_index(paddr);

        let post = MetaRegionModel {
            slots: pre.slots.insert(
                idx,
                Self::from_unused_slot_spec(paddr, metadata, as_unique_ptr),
            ),
        };
        (ptr, post)
    }

    /// All other slots remain unchanged.
    #[rustc_allow_incoherent_impl]
    pub open spec fn update_index_tracked(
        idx: usize,
        pre: MetaRegionOwners,
        post: MetaRegionOwners,
    ) -> bool
        recommends
            pre.slots.contains_key(idx),
    {
        &&& pre.slots.dom() == post.slots.dom()
        &&& pre.dropped_slots.dom() == post.dropped_slots.dom()
        &&& pre.slot_owners.dom() == post.slot_owners.dom()
        &&& forall|i: usize| #[trigger]
            pre.slots.contains_key(i) && i != idx ==> pre.slots[i] == post.slots[i]
        &&& forall|i: usize| #[trigger]
            pre.dropped_slots.contains_key(i) && i != idx ==> pre.dropped_slots[i]
                == post.dropped_slots[i]
        &&& forall|i: usize| #[trigger]
            pre.slot_owners.contains_key(i) && i != idx ==> pre.slot_owners[i]
                == post.slot_owners[i]
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn get_from_unused_tracked<M: AnyFrameMeta>(
        paddr: Paddr,
        metadata: M,
        as_unique_ptr: bool,
        // -- ghost parameters --
        pre: MetaRegionOwners,
        post: MetaRegionOwners,
    ) -> bool
        recommends
            paddr % 4096 == 0,
            paddr < MAX_PADDR(),
            pre.inv(),
            pre.view().slots[paddr / 4096].ref_count == REF_COUNT_UNUSED,
    {
        let idx = paddr / 4096;
        {
            &&& Self::update_index_tracked(idx, pre, post)
            &&& Self::get_from_unused_spec(paddr, metadata, as_unique_ptr, pre.view()).1
                == post.view()
        }
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn get_from_in_use_spec(paddr: Paddr, pre: MetaRegionModel) -> (
        PPtr<MetaSlot>,
        MetaRegionModel,
    )
        recommends
            paddr % 4096 == 0,
            paddr < MAX_PADDR(),
            pre.inv(),
            0 <= pre.slots[paddr / 4096].ref_count < REF_COUNT_MAX,
    {
        let ptr = get_slot_spec(paddr);
        let idx = paddr / 4096;
        let pre_slot = pre.slots[idx];
        let post = MetaRegionModel {
            slots: pre.slots.insert(
                idx,
                MetaSlotModel { ref_count: (pre_slot.ref_count + 1) as u64, ..pre_slot },
            ),
        };
        (ptr, post)
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn get_from_in_use_tracked(
        paddr: Paddr,
        // -- ghost parameters --
        pre: MetaRegionOwners,
        post: MetaRegionOwners,
    ) -> bool
        recommends
            paddr % 4096 == 0,
            paddr < MAX_PADDR(),
            pre.inv(),
            0 <= pre.view().slots[paddr / 4096].ref_count < REF_COUNT_MAX,
    {
        let idx = paddr / 4096;
        {
            &&& Self::update_index_tracked(idx, pre, post)
            &&& Self::get_from_in_use_spec(paddr, pre.view()).1 == post.view()
        }
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn inc_ref_count_spec(&self, pre: MetaSlotModel) -> (MetaSlotModel)
        recommends
            pre.inv(),
            pre.status == MetaSlotStatus::SHARED,
    {
        MetaSlotModel { ref_count: (pre.ref_count + 1) as u64, ..pre }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlot> + OwnerOf> UniqueFrame<M> {
    #[rustc_allow_incoherent_impl]
    pub open spec fn from_unused_spec(paddr: Paddr, metadata: M, pre: MetaRegionModel) -> (
        Self,
        MetaRegionModel,
    )
        recommends
            paddr % PAGE_SIZE() == 0,
            paddr < MAX_PADDR(),
            pre.inv(),
            pre.slots[frame_to_index(paddr)].ref_count == REF_COUNT_UNUSED,
    {
        let (ptr, post) = MetaSlot::get_from_unused_spec(paddr, metadata, true, pre);
        (UniqueFrame { ptr, _marker: PhantomData }, post)
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn from_unused_properties(paddr: Paddr, metadata: M, pre: MetaRegionModel)
        requires
            paddr % 4096 == 0,
            paddr < MAX_PADDR(),
            pre.inv(),
            pre.slots[paddr / 4096].ref_count == REF_COUNT_UNUSED,
        ensures
            UniqueFrame::from_unused_spec(paddr, metadata, pre).1.inv(),
    {
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlot> + OwnerOf> Frame<M> {
    #[rustc_allow_incoherent_impl]
    pub open spec fn from_raw_spec(paddr: Paddr) -> Self {
        Frame::<M> {
            ptr: PPtr::<MetaSlot>(frame_to_meta(paddr), PhantomData),
            _marker: PhantomData,
        }
    }
}

} // verus!
