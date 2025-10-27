use vstd::atomic::*;
use vstd::cell;
use vstd::prelude::*;
use vstd::simple_pptr::{self, *};

use vstd_extra::ownership::*;

use super::*;

verus! {

/// Represents the meta-frame memory region. Can be viewed as a collection of
/// Cell<MetaSlot> at a fixed address range.
pub struct MetaRegion;

pub tracked struct MetaRegionOwners {
    pub slots: Map<usize, Tracked<simple_pptr::PointsTo<MetaSlot>>>,
    pub dropped_slots: Map<usize, Tracked<simple_pptr::PointsTo<MetaSlot>>>,
    pub slot_owners: Map<usize, MetaSlotOwner>,
}

pub ghost struct MetaRegionModel {
    pub slots: Map<usize, MetaSlotModel>,
}

impl Inv for MetaRegionOwners {
    open spec fn inv(self) -> bool {
        &&& self.slots.dom().finite()
        &&& {
            // All accessible slots are within the valid address range.
            forall|i: usize| i < max_meta_slots() <==> #[trigger] self.slot_owners.contains_key(i)
        }
        &&& { forall|i: usize| #[trigger] self.slots.contains_key(i) ==> i < max_meta_slots() }
        &&& {
            forall|i: usize| #[trigger] self.dropped_slots.contains_key(i) ==> i < max_meta_slots()
        }
        &&& {
            // Invariant for each slot holds.
            forall|i: usize| #[trigger]
                self.slot_owners.contains_key(i) ==> self.slot_owners[i].inv()
        }
        &&& {
            forall|i: usize| #[trigger]
                self.slots.contains_key(i) ==> {
                    &&& self.slots[i]@.is_init()
                    &&& self.slots[i]@.addr() == meta_addr(i)
                    &&& self.slots[i]@.value().wf(self.slot_owners[i])
                    &&& self.slot_owners[i].self_addr == self.slots[i]@.addr()
                    &&& !self.dropped_slots.contains_key(i)
                }
        }
        &&& {
            forall|i: usize| #[trigger]
                self.dropped_slots.contains_key(i) ==> {
                    &&& self.dropped_slots[i]@.is_init()
                    &&& self.dropped_slots[i]@.addr() == meta_addr(i)
                    &&& self.dropped_slots[i]@.value().wf(self.slot_owners[i])
                    &&& self.slot_owners[i].self_addr == self.dropped_slots[i]@.addr()
                    &&& !self.slots.contains_key(i)
                }
        }
    }
}

impl Inv for MetaRegionModel {
    open spec fn inv(self) -> bool {
        &&& self.slots.dom().finite()
        &&& forall|i: usize| i < max_meta_slots() <==> #[trigger] self.slots.contains_key(i)
        &&& forall|i: usize| #[trigger] self.slots.contains_key(i) ==> self.slots[i].inv()
    }
}

impl InvView for MetaRegionOwners {
    type V = MetaRegionModel;

    open spec fn view(self) -> Self::V {
        let slots = self.slot_owners.map_values(|s: MetaSlotOwner| s.view());
        MetaRegionModel { slots }
    }

    // XXX: verus `map_values` does not preserves the `finite()` attribute.
    axiom fn view_preserves_inv(self);
}

impl OwnerOf for MetaRegion {
    type Owner = MetaRegionOwners;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        true
    }
}

impl ModelOf for MetaRegion {

}

impl MetaRegionOwners {
    pub open spec fn ref_count(self, i: usize) -> (res: u64)
        recommends
            self.inv(),
            i < max_meta_slots() as usize,
    {
        self.slot_owners[i].ref_count@.value()
    }

    pub proof fn inv_implies_correct_addr(self, paddr: usize)
        requires
            paddr < MAX_PADDR(),
            paddr % PAGE_SIZE() == 0,
            self.inv(),
        ensures
            self.slot_owners.contains_key(frame_to_index_spec(paddr) as usize),
    {
        assert((frame_to_index_spec(paddr)) < max_meta_slots() as usize);
    }
}

} // verus!
