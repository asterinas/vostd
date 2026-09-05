use vstd::prelude::*;

use vstd_extra::{cast_ptr::*, ownership::*, prelude::*};

use crate::specs::{
    arch::{MAX_NR_PAGES, valid_frame_paddr},
    mm::{
        Paddr,
        frame::{
            mapping::{frame_to_index, index_to_meta, max_meta_slots, meta_to_index},
            meta_region_owners::MetaRegionOwners,
        },
    },
};

use crate::mm::{
    frame::{
        meta::{
            META_SLOT_SIZE, REF_COUNT_MAX, REF_COUNT_UNIQUE, REF_COUNT_UNUSED,
            mapping::{frame_to_meta, meta_to_frame},
        },
        *,
    },
    kspace::FRAME_METADATA_RANGE,
};

use super::meta_owners::*;

verus! {

impl<M: AnyFrameMeta + ?Sized + Repr<MetaSlotStorage> + OwnerOf> UniqueFrame<M> {
    pub open spec fn start_paddr_spec(self) -> Paddr {
        meta_to_frame(self.ptr.addr())
    }

    pub open spec fn index(self) -> int {
        frame_to_index(self.start_paddr_spec())
    }

    /// The complete metadata permission carried by this unique handle.
    #[verifier::inline]
    pub open spec fn metadata_perm(self) -> MetadataPerm {
        self.tracked_metadata_perm@->0
    }

    /// The metadata-slot permission carried by this unique handle.
    pub open spec fn slot_perm(self) -> vstd::simple_pptr::PointsTo<MetaSlot> {
        *self.tracked_slot_perm@
    }

    #[verifier::inline]
    pub open spec fn ptr_inv(self) -> bool {
        &&& valid_frame_paddr(self.start_paddr_spec())
        &&& self.ptr.addr() % META_SLOT_SIZE == 0
        &&& FRAME_METADATA_RANGE.start <= self.ptr.addr() < FRAME_METADATA_RANGE.start
            + MAX_NR_PAGES * META_SLOT_SIZE
        &&& self.slot_perm().pptr() == self.ptr
        &&& self.slot_perm().is_init()
    }
}

impl<M: AnyFrameMeta + ?Sized + Repr<MetaSlotStorage> + OwnerOf> Inv for UniqueFrame<M> {
    open spec fn inv(self) -> bool {
        &&& self.ptr_inv()
        &&& self.tracked_metadata_perm@ is Some
        &&& MetaSlot::perms_related(self.slot_perm(), self.metadata_perm())
    }
}

//FIXME: why do we need a index here?
pub tracked struct UniqueFrameOwner<M: AnyFrameMeta + ?Sized + Repr<MetaSlotStorage> + OwnerOf> {
    pub meta_own: M::Owner,
    pub repr_perm: Option<M::ReprPerm>,
    pub ghost slot_index: int,
}

impl<M: AnyFrameMeta + ?Sized + Repr<MetaSlotStorage> + OwnerOf> Inv for UniqueFrameOwner<M> {
    open spec fn inv(self) -> bool {
        &&& 0 <= self.slot_index < MAX_NR_PAGES
        &&& self.slot_index < max_meta_slots()
        &&& self.repr_perm is Some
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> OwnerOf for UniqueFrame<M> {
    type Owner = UniqueFrameOwner<M>;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& self.ptr.addr() == index_to_meta(owner.slot_index)
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> UniqueFrame<M> {
    pub open spec fn meta_wf(self, owner: UniqueFrameOwner<M>) -> bool {
        typed_meta_wf::<M>(self.slot_perm(), self.metadata_perm(), owner.repr_perm->0)
    }

    pub open spec fn meta_value(self, owner: UniqueFrameOwner<M>) -> M {
        typed_meta_value::<M>(self.metadata_perm(), owner.repr_perm->0)
    }

    /// Cross-object validity of a live UNIQUE handle against the region map —
    /// the [`UniqueFrame`] analog of [`Frame::wf_with_region`] (which covers
    /// the SHARED state).
    pub open spec fn wf_with_region(self, owner: UniqueFrameOwner<M>, s: MetaRegionOwners) -> bool {
        let idx = owner.slot_index;
        let so = s.slot_owners[idx];
        &&& self.wf(owner)
        &&& s.contains(idx)
        &&& self.tracked_slot_perm@ == s.slots[idx]
        &&& self.meta_wf(owner)
        &&& self.meta_value(owner).wf(owner.meta_own)
        &&& so.metadata_perm.is_resource_vacant()
        &&& so.ref_count() == REF_COUNT_UNIQUE
        &&& so.usage is Frame
        &&& so.paths_in_pt.is_empty()
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> UniqueFrameOwner<M> {
    pub open spec fn meta_wf(self, regions: MetaRegionOwners) -> bool {
        typed_meta_wf::<M>(
            *regions.slots[self.slot_index],
            regions.slot_owners[self.slot_index].metadata_perm.resource(),
            self.repr_perm->0,
        )
    }

    pub open spec fn meta_value(self, regions: MetaRegionOwners) -> M {
        typed_meta_value::<M>(
            regions.slot_owners[self.slot_index].metadata_perm.resource(),
            self.repr_perm->0,
        )
    }

    /// Borrow-model global invariant: the frame's permission is parked in
    /// `regions.slots[slot_index]` (NOT owned by the frame), and the
    /// concrete storage and representation permissions decode to metadata
    /// matching `meta_own`. A `UniqueFrame` is the sole live reference to its
    /// slot, so the slot sits at `REF_COUNT_UNIQUE` — the unique-frame analog
    /// of the segment's `0 < ref_count <= REF_COUNT_MAX` regime in
    /// [`Segment::relate_regions`].
    pub open spec fn global_inv(self, regions: MetaRegionOwners) -> bool {
        &&& regions.contains(self.slot_index)
        &&& self.meta_wf(regions)
        &&& regions.slots[self.slot_index].addr() == index_to_meta(self.slot_index)
        &&& self.meta_value(regions).wf(self.meta_own)
        &&& regions.slot_owners[self.slot_index].metadata_perm.is_resource_vacant()
        &&& regions.slot_owners[self.slot_index].metadata_perm.resource().storage_perm.id()
            == regions.slots[self.slot_index].value().storage.id()
        &&& regions.slot_owners[self.slot_index].metadata_perm.resource().vtable_ptr_perm.pptr()
            == regions.slots[self.slot_index].value().vtable_ptr
        &&& regions.slot_owners[self.slot_index].metadata_perm.resource().vtable_ptr_perm.is_init()
        &&& regions.slot_owners[self.slot_index].slot_vaddr == index_to_meta(self.slot_index)
        &&& regions.slot_owners[self.slot_index].ref_count() == REF_COUNT_UNIQUE
        &&& regions.slot_owners[self.slot_index].usage is Frame
    }

    pub open spec fn from_unused_owner(
        meta_own: M::Owner,
        repr_perm: M::ReprPerm,
        slot_index: int,
    ) -> Self {
        Self { meta_own, repr_perm: Some(repr_perm), slot_index }
    }

    pub proof fn tracked_from_unused_owner(
        tracked meta_own: M::Owner,
        tracked repr_perm: M::ReprPerm,
        slot_index: int,
    ) -> (tracked res: Self)
        returns
            Self::from_unused_owner(meta_own, repr_perm, slot_index),
    {
        Self { meta_own, repr_perm: Some(repr_perm), slot_index }
    }

    pub proof fn tracked_borrow_repr_perm(tracked &self) -> (tracked res: &M::ReprPerm)
        requires
            self.repr_perm is Some,
        ensures
            *res == self.repr_perm->0,
    {
        self.repr_perm.tracked_borrow()
    }

    pub proof fn tracked_borrow_mut_repr_perm(tracked &mut self) -> (tracked res: &mut M::ReprPerm)
        requires
            old(self).inv(),
        ensures
            *res == old(self).repr_perm->0,
            final(self).meta_own == old(self).meta_own,
            final(self).slot_index == old(self).slot_index,
            final(self).repr_perm is Some,
            final(self).repr_perm->0 == *final(res),
            final(self).inv(),
    {
        self.repr_perm.tracked_borrow_mut()
    }
}

} // verus!
