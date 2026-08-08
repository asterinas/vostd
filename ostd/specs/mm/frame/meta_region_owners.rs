use core::ops::Range;

use vstd::prelude::*;

use vstd::{
    atomic::*,
    simple_pptr::{self, *},
};
use vstd_extra::{cast_ptr::Repr, ownership::*};

use crate::specs::arch::valid_frame_paddr;
use crate::specs::{
    arch::{MAX_PADDR, PAGE_SIZE},
    mm::frame::mapping::{frame_to_index, index_to_meta, max_meta_slots},
};

use crate::mm::{
    Paddr,
    frame::{
        Link,
        meta::{AnyFrameMeta, META_SLOT_SIZE, MetaSlot, REF_COUNT_MAX, mapping::frame_to_meta},
    },
    kspace::FRAME_METADATA_RANGE,
};

use super::{
    meta_owners::{MetaSlotModel, MetaSlotOwner},
    *,
};

verus! {

/// Represents the ownership of the meta-frame memory region.
/// # Verification Design
/// ## Slot owners and permissions
/// Every metadata slot has its owner ([`MetaSlotOwner`]) tracked by the `slot_owners` map at all times.
/// This makes the `MetaRegionOwners` the one place that tracks every frame, whether or not it is
/// in use. Likewise, every slot has an permission stored in `slots`.
#[verifier::ext_equal]
pub tracked struct MetaRegionOwners {
    pub slots: Map<int, &'static simple_pptr::PointsTo<MetaSlot>>,
    pub slot_owners: Map<int, MetaSlotOwner>,
}

pub ghost struct MetaRegionModel {
    pub slots: Map<int, MetaSlotModel>,
}

impl Inv for MetaRegionOwners {
    open spec fn inv(self) -> bool {
        &&& {
            // Keep the map-membership trigger: callers frequently expose a
            // slot-owner lookup without mentioning the `contains` wrapper.
            forall|i: int|
                0 <= i < max_meta_slots() <==> #[trigger] self.slot_owners.contains_key(i)
        }
        &&& {
            forall|i: int| #[trigger]
                self.slot_owners.contains_key(i) ==> self.slots.contains_key(i)
        }
        &&& { forall|i: int| #[trigger] self.slots.contains_key(i) ==> 0 <= i < max_meta_slots() }
        &&& {
            forall|i: int| #[trigger]
                self.slots.contains_key(i) ==> {
                    &&& self.slot_owners[i].inv()
                    &&& self.slots[i].is_init()
                    &&& self.slots[i].addr() == index_to_meta(i)
                    &&& self.slots[i].value().wf(self.slot_owners[i])
                    &&& self.slot_owners[i].slot_vaddr == self.slots[i].addr()
                }
        }
    }
}

impl MetaRegionModel {
    pub open spec fn contains(self, index: int) -> bool {
        self.slots.contains_key(index)
    }
}

impl Inv for MetaRegionModel {
    open spec fn inv(self) -> bool {
        &&& forall|i: int| 0 <= i < max_meta_slots() <==> #[trigger] self.slots.contains_key(i)
        &&& forall|i: int| #[trigger] self.slots.contains_key(i) ==> self.slots[i].inv()
    }
}

impl View for MetaRegionOwners {
    type V = MetaRegionModel;

    open spec fn view(&self) -> <Self as View>::V {
        let slots = self.slot_owners.map_values(|s: MetaSlotOwner| s@);
        MetaRegionModel { slots }
    }
}

impl InvView for MetaRegionOwners {
    proof fn view_preserves_inv(self) {
    }
}

impl MetaRegionOwners {
    /// Returns whether the slot permission and its corresponding owner are both present.
    pub open spec fn contains(self, index: int) -> bool {
        &&& self.slot_owners.contains_key(index)
        &&& self.slots.contains_key(index)
    }

    pub open spec fn insert_slot_owner(self, paddr: Paddr, owner: MetaSlotOwner) -> Self {
        let index = frame_to_index(paddr);
        Self { slot_owners: self.slot_owners.insert(index, owner), ..self }
    }

    pub open spec fn ref_count(self, i: int) -> (res: u64)
        recommends
            0 <= i < max_meta_slots(),
    {
        self.slot_owners[i].ref_count()
    }

    /// `other` agrees with `self` on every slot owner except the one at index
    /// `idx`: a single-slot operation leaves all other slots' owners untouched.
    pub open spec fn slot_owners_agree_except(self, other: MetaRegionOwners, idx: int) -> bool {
        forall|i: int|
            #![trigger other.slot_owners[i]]
            i != idx ==> other.slot_owners[i] == self.slot_owners[i]
    }

    pub open spec fn paddr_range_not_mapped(self, range: Range<Paddr>) -> bool
        recommends
            range.start < range.end < MAX_PADDR,
    {
        forall|paddr: Paddr|
            #![trigger frame_to_index(paddr)]
            (range.start <= paddr < range.end && paddr % PAGE_SIZE == 0) ==> self.slot_owner(
                paddr,
            ).paths_in_pt.is_empty()
    }

    pub proof fn lemma_contains_valid_frame_paddr(self, paddr: usize)
        requires
            valid_frame_paddr(paddr),
            self.inv(),
        ensures
            self.contains(frame_to_index(paddr)),
    {
    }

    /// Rertuns the `MetaSlotOwner`, indexed by frame paddr.
    pub open spec fn slot_owner(self, paddr: Paddr) -> MetaSlotOwner {
        self.slot_owners[frame_to_index(paddr)]
    }

    /// Borrows the metadata slot permission, indexed by frame paddr.
    pub proof fn tracked_borrow_slot(tracked &self, paddr: Paddr) -> (tracked ret:
        &'static simple_pptr::PointsTo<MetaSlot>)
        requires
            valid_frame_paddr(paddr),
            self.inv(),
        returns
            self.slots[frame_to_index(paddr)],
    {
        self.lemma_contains_valid_frame_paddr(paddr);
        *self.slots.tracked_borrow(frame_to_index(paddr))
    }

    /// Borrows the `MetaSlotOwner`, indexed by frame paddr.
    pub proof fn tracked_borrow_slot_owner(tracked &self, paddr: Paddr) -> (tracked ret:
        &MetaSlotOwner)
        requires
            valid_frame_paddr(paddr),
            self.inv(),
        returns
            self.slot_owner(paddr),
    {
        self.lemma_contains_valid_frame_paddr(paddr);
        self.slot_owners.tracked_borrow(frame_to_index(paddr))
    }

    /// Mutably borrows the `MetaSlotOwner`, indexed by frame paddr.
    pub proof fn tracked_borrow_mut_slot_owner(tracked &mut self, paddr: Paddr) -> (tracked ret:
        &mut MetaSlotOwner)
        requires
            valid_frame_paddr(paddr),
            self.inv(),
        ensures
            *ret == old(self).slot_owner(paddr),
            *final(self) == (Self {
                slot_owners: old(self).slot_owners.insert(frame_to_index(paddr), *final(ret)),
                ..*old(self)
            }),
    {
        self.lemma_contains_valid_frame_paddr(paddr);
        self.slot_owners.tracked_borrow_mut(frame_to_index(paddr))
    }
}

} // verus!
