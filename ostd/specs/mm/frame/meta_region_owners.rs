use core::ops::Range;

use vstd::prelude::*;

use vstd::{
    atomic::*,
    simple_pptr::{self, *},
};
use vstd_extra::{
    cast_ptr::{self, Repr},
    ownership::*,
};

use crate::specs::{
    arch::{MAX_PADDR, PAGE_SIZE},
    mm::frame::{
        mapping::{frame_to_index, max_meta_slots, meta_addr},
        meta_owners::Metadata,
    },
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
    meta_owners::{MetaPerm, MetaSlotModel, MetaSlotOwner, MetaSlotStorage},
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
    pub slots: Map<usize, FramePermissionResource>,
    pub slot_owners: Map<usize, MetaSlotOwner>,
}

pub ghost struct MetaRegionModel {
    pub slots: Map<usize, MetaSlotModel>,
}

impl Inv for MetaRegionOwners {
    open spec fn inv(self) -> bool {
        &&& {
            // All accessible slots are within the valid address range.
            forall|i: usize| i < max_meta_slots() <==> #[trigger] self.slot_owners.contains_key(i)
        }
        &&& {
            forall|i: usize| #[trigger]
                self.slot_owners.contains_key(i) ==> self.slots.contains_key(i)
        }
        &&& { forall|i: usize| #[trigger] self.slots.contains_key(i) ==> i < max_meta_slots() }
        &&& {
            forall|i: usize| #[trigger]
                self.slots.contains_key(i) ==> {
                    &&& self.slot_owners[i].inv()
                    &&& self.slots[i].is_init()
                    &&& self.slots[i].addr() == meta_addr(i)
                    &&& self.slots[i].value().wf(self.slot_owners[i])
                    &&& self.slot_owners[i].slot_vaddr == self.slots[i].addr()
                }
        }
    }
}

impl Inv for MetaRegionModel {
    open spec fn inv(self) -> bool {
        &&& forall|i: usize| i < max_meta_slots() <==> #[trigger] self.slots.contains_key(i)
        &&& forall|i: usize| #[trigger] self.slots.contains_key(i) ==> self.slots[i].inv()
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
    pub open spec fn insert_slot_owner(self, paddr: Paddr, owner: MetaSlotOwner) -> Self {
        let index = frame_to_index(paddr);
        Self { slot_owners: self.slot_owners.insert(index, owner), ..self }
    }

    pub open spec fn ref_count(self, i: usize) -> (res: u64)
        recommends
            self.inv(),
            i < max_meta_slots() as usize,
    {
        self.slot_owners[i].inner_perms.ref_count.value()
    }

    /// `other` agrees with `self` on every slot owner except the one at index
    /// `idx`: a single-slot operation leaves all other slots' owners untouched.
    pub open spec fn slot_owners_agree_except(self, other: MetaRegionOwners, idx: usize) -> bool {
        forall|i: usize|
            #![trigger other.slot_owners[i]]
            i != idx ==> other.slot_owners[i] == self.slot_owners[i]
    }

    pub axiom fn borrow_typed_perm<M: AnyFrameMeta + Repr<MetaSlotStorage>>(
        &self,
        i: usize,
    ) -> (tracked res: &vstd_extra::cast_ptr::PointsTo<MetaSlot, Metadata<M>>)
        requires
            self.slots.contains_key(i),
            self.slot_owners.contains_key(i),
            vstd_extra::cast_ptr::PointsTo::<MetaSlot, Metadata<M>>::new_spec(
                self.slots[i],
                self.slot_owners[i].inner_perms,
            ).wf(&self.slot_owners[i].inner_perms),
        ensures
            res.points_to == self.slots[i],
            res.inner_perms == self.slot_owners[i].inner_perms,
            res.wf(&res.inner_perms),
    ;

    /// Mutable analog of [`borrow_typed_perm`]. Lends out a `&'a mut cast_ptr`
    /// reconstructed from `slots[i]` (outer simple-pptr) and
    /// `slot_owners[i].inner_perms` (inner perms). While the returned reference
    /// is live, `self` is mutably borrowed; on borrow-end, `self.slots[i]` and
    /// `self.slot_owners[i].inner_perms` are restored from the final cast_ptr.
    /// Every other slot/slot_owner is fully preserved, and the other fields of
    /// `slot_owners[i]` (raw_count/usage/slot_vaddr/paths_in_pt) are unchanged.
    pub axiom fn borrow_mut_typed_perm<M: AnyFrameMeta + Repr<MetaSlotStorage>>(
        &mut self,
        i: usize,
    ) -> (tracked res: &mut vstd_extra::cast_ptr::PointsTo<MetaSlot, Metadata<M>>)
        requires
            old(self).slots.contains_key(i),
            old(self).slot_owners.contains_key(i),
            vstd_extra::cast_ptr::PointsTo::<MetaSlot, Metadata<M>>::new_spec(
                old(self).slots[i],
                old(self).slot_owners[i].inner_perms,
            ).wf(&old(self).slot_owners[i].inner_perms),
        ensures
            res.points_to == old(self).slots[i],
            res.inner_perms == old(self).slot_owners[i].inner_perms,
            res.wf(&res.inner_perms),
            final(self).slots.dom() == old(self).slots.dom(),
            final(self).slot_owners.dom() == old(self).slot_owners.dom(),
            final(self).slots[i] == final(res).points_to,
            final(self).slot_owners[i].inner_perms == final(res).inner_perms,
            forall|k: usize| k != i ==> #[trigger] final(self).slots[k] == old(self).slots[k],
            forall|k: usize|
                k != i ==> #[trigger] final(self).slot_owners[k] == old(self).slot_owners[k],
            final(self).slot_owners[i].usage == old(self).slot_owners[i].usage,
            final(self).slot_owners[i].slot_vaddr == old(self).slot_owners[i].slot_vaddr,
            final(self).slot_owners[i].paths_in_pt == old(self).slot_owners[i].paths_in_pt,
    ;

    pub open spec fn paddr_range_in_region(self, range: Range<Paddr>) -> bool
        recommends
            self.inv(),
            range.start < range.end < MAX_PADDR,
    {
        forall|paddr: Paddr|
            #![trigger frame_to_index(paddr)]
            (range.start <= paddr < range.end && paddr % PAGE_SIZE == 0)
                ==> self.slots.contains_key(frame_to_index(paddr))
    }

    pub open spec fn paddr_range_not_mapped(self, range: Range<Paddr>) -> bool
        recommends
            self.inv(),
            range.start < range.end < MAX_PADDR,
    {
        forall|paddr: Paddr|
            #![trigger frame_to_index(paddr)]
            (range.start <= paddr < range.end && paddr % PAGE_SIZE == 0)
                ==> self.slot_owners[frame_to_index(paddr)].paths_in_pt.is_empty()
    }

    pub open spec fn paddr_range_not_in_region(self, range: Range<Paddr>) -> bool
        recommends
            self.inv(),
            range.start < range.end < MAX_PADDR,
    {
        forall|paddr: Paddr|
            #![trigger frame_to_index(paddr)]
            (range.start <= paddr < range.end && paddr % PAGE_SIZE == 0)
                ==> !self.slots.contains_key(frame_to_index(paddr))
    }

    /// Instantiates `paddr_range_not_mapped` at a specific paddr in the range.
    pub proof fn paddr_not_mapped_at(self, range: Range<Paddr>, paddr: Paddr)
        requires
            self.paddr_range_not_mapped(range),
            range.start <= paddr,
            paddr < range.end,
            paddr % PAGE_SIZE == 0,
        ensures
            self.slot_owners[frame_to_index(paddr)].paths_in_pt.is_empty(),
    {
        // The trigger frame_to_index(paddr) fires from the ensures clause,
        // instantiating the forall in paddr_range_not_mapped at this paddr.
    }

    pub proof fn inv_implies_correct_addr(self, paddr: usize)
        requires
            paddr < MAX_PADDR,
            paddr % PAGE_SIZE == 0,
            self.inv(),
        ensures
            self.slot_owners.contains_key(frame_to_index(paddr) as usize),
    {
    }

}

} // verus!
