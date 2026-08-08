use vstd::prelude::*;

use vstd_extra::{cast_ptr::*, drop_tracking::*, ownership::*};

use crate::specs::{
    arch::MAX_NR_PAGES,
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
            REF_COUNT_MAX, REF_COUNT_UNIQUE, REF_COUNT_UNUSED,
            mapping::{frame_to_meta, meta_to_frame},
        },
        *,
    },
    kspace::FRAME_METADATA_RANGE,
};

use super::meta_owners::*;

verus! {

impl<M: AnyFrameMeta + ?Sized + Repr<MetaSlotStorage> + OwnerOf> UniqueFrame<M> {
    pub open spec fn paddr(self) -> Paddr {
        meta_to_frame(self.ptr.addr())
    }

    pub open spec fn index(self) -> int {
        frame_to_index(self.paddr())
    }
}

//FIXME: why do we need a index here?
pub tracked struct UniqueFrameOwner<M: AnyFrameMeta + ?Sized + Repr<MetaSlotStorage> + OwnerOf> {
    pub meta_own: M::Owner,
    pub repr_perm: Option<M::ReprPerm>,
    /// The complete permission for the metadata contents.
    pub metadata_perms: Option<MetadataPerms>,
    pub ghost slot_index: int,
}

pub ghost struct UniqueFrameModel<M: AnyFrameMeta + ?Sized + Repr<MetaSlotStorage> + OwnerOf> {
    pub meta: <M::Owner as View>::V,
}

impl<M: AnyFrameMeta + ?Sized + Repr<MetaSlotStorage> + OwnerOf> Inv for UniqueFrameOwner<M> {
    open spec fn inv(self) -> bool {
        &&& 0 <= self.slot_index < MAX_NR_PAGES
        &&& self.slot_index < max_meta_slots()
        &&& self.repr_perm is Some
        &&& self.metadata_perms is Some
    }
}

impl<M: AnyFrameMeta + Sized + Repr<MetaSlotStorage> + OwnerOf> Inv for UniqueFrameModel<M> {
    open spec fn inv(self) -> bool {
        true
    }
}

impl<M: AnyFrameMeta + ?Sized + Repr<MetaSlotStorage> + OwnerOf> View for UniqueFrameOwner<M> {
    type V = UniqueFrameModel<M>;

    open spec fn view(&self) -> Self::V {
        UniqueFrameModel { meta: self.meta_own@ }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> InvView for UniqueFrameOwner<M> {
    proof fn view_preserves_inv(self) {
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> OwnerOf for UniqueFrame<M> {
    type Owner = UniqueFrameOwner<M>;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& self.ptr.addr() == index_to_meta(owner.slot_index)
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> UniqueFrame<M> {
    /// Cross-object validity of a live UNIQUE handle against the region map —
    /// the [`UniqueFrame`] analog of [`Frame::wf_with_region`] (which covers
    /// the SHARED state). Bundles the structural `wf` / `owner.inv` /
    /// `regions.inv` facts with the UNIQUE-state slot facts so a consumer (e.g.
    /// [`UniqueFrame::drop`]) can state a single invariant instead of re-listing
    /// each conjunct.
    ///
    /// The slot's `slot_owners.contains_key(idx)`, `slot_vaddr == index_to_meta(idx)`,
    /// `storage.is_init()`, and `vtable_ptr.is_init()` are **derived**, not
    /// required: `regions.inv()` (with `owner.inv()`'s `idx < max_meta_slots`)
    /// delivers the first two and `slot_owners[idx].inv()`; the latter's UNIQUE
    /// branch (under `rc == REF_COUNT_UNIQUE`) gives the storage/vtable init.
    /// The genuinely-extra conjuncts are the UNIQUE state itself plus
    /// `in_list == 0` and `paths_in_pt.is_empty()` (a sole owner is neither on
    /// the free list nor mapped into any page table).
    pub open spec fn wf_with_region(self, owner: UniqueFrameOwner<M>, s: MetaRegionOwners) -> bool {
        let idx = owner.slot_index;
        let so = s.slot_owners[idx];
        &&& self.wf(owner)
        &&& owner.inv()
        &&& s.inv()
        &&& owner.global_inv(s)
        &&& so.ref_count() == REF_COUNT_UNIQUE
        &&& so.in_list_perm.value() == 0
        &&& so.paths_in_pt.is_empty()
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> UniqueFrameOwner<M> {
    pub open spec fn meta_wf(self, regions: MetaRegionOwners) -> bool {
        typed_meta_wf::<M>(
            *regions.slots[self.slot_index],
            self.metadata_perms->0,
            self.repr_perm->0,
        )
    }

    pub open spec fn meta_value(self, regions: MetaRegionOwners) -> M {
        typed_meta_value::<M>(self.metadata_perms->0, self.repr_perm->0)
    }

    pub open spec fn perm_inv(self, perm: vstd::simple_pptr::PointsTo<MetaSlot>) -> bool {
        &&& perm.is_init()
        &&& perm.addr() == index_to_meta(self.slot_index)
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
        &&& self.metadata_perms->0.storage_perm.id()
            == regions.slots[self.slot_index].value().storage.id()
        &&& self.metadata_perms->0.vtable_ptr_perm.pptr()
            == regions.slots[self.slot_index].value().vtable_ptr
        &&& self.metadata_perms->0.vtable_ptr_perm.is_init()
        &&& regions.slot_owners[self.slot_index].slot_vaddr == index_to_meta(self.slot_index)
        &&& regions.slot_owners[self.slot_index].ref_count()
            == REF_COUNT_UNIQUE
        // Data-frame node-repark discriminator (our change): a unique frame's
        // slot is tracked with `Frame` usage, distinguishing it from page-table
        // node slots (`PageTable`) and letting linked-list/list-store consumers
        // derive `usage == Frame` (e.g. for the empty-`paths_in_pt` argument).
        &&& regions.slot_owners[self.slot_index].usage is Frame
    }

    pub open spec fn from_unused_owner(
        meta_own: M::Owner,
        repr_perm: M::ReprPerm,
        metadata_perms: MetadataPerms,
        slot_index: int,
    ) -> Self {
        Self {
            meta_own,
            repr_perm: Some(repr_perm),
            metadata_perms: Some(metadata_perms),
            slot_index,
        }
    }

    pub proof fn tracked_from_unused_owner(
        tracked meta_own: M::Owner,
        tracked repr_perm: M::ReprPerm,
        tracked metadata_perms: MetadataPerms,
        slot_index: int,
    ) -> (tracked res: Self)
        returns
            Self::from_unused_owner(meta_own, repr_perm, metadata_perms, slot_index),
    {
        Self {
            meta_own,
            repr_perm: Some(repr_perm),
            metadata_perms: Some(metadata_perms),
            slot_index,
        }
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
            final(self).metadata_perms == old(self).metadata_perms,
            final(self).inv(),
    {
        match &mut self.repr_perm {
            Some(perm) => perm,
            None => proof_from_false(),
        }
    }

    pub proof fn tracked_borrow_metadata_perms(tracked &self) -> (tracked res: &MetadataPerms)
        requires
            self.metadata_perms is Some,
        ensures
            *res == self.metadata_perms->0,
    {
        self.metadata_perms.tracked_borrow()
    }

    pub proof fn tracked_borrow_mut_metadata_perms(tracked &mut self) -> (tracked res:
        &mut MetadataPerms)
        requires
            old(self).inv(),
        ensures
            *res == old(self).metadata_perms->0,
            final(self).meta_own == old(self).meta_own,
            final(self).repr_perm == old(self).repr_perm,
            final(self).slot_index == old(self).slot_index,
            final(self).metadata_perms is Some,
            final(self).metadata_perms->0 == *final(res),
            final(self).inv(),
    {
        match &mut self.metadata_perms {
            Some(perms) => perms,
            None => proof_from_false(),
        }
    }

    /// Mutably borrows both independently-owned parts needed by
    /// `borrow_meta_mut` in one operation.
    pub proof fn tracked_borrow_mut_meta_parts(tracked &mut self) -> (tracked res: (
        &mut MetadataPerms,
        &mut M::ReprPerm,
    ))
        requires
            old(self).inv(),
        ensures
            *res.0 == old(self).metadata_perms->0,
            *res.1 == old(self).repr_perm->0,
            final(self).meta_own == old(self).meta_own,
            final(self).slot_index == old(self).slot_index,
            final(self).metadata_perms is Some,
            final(self).repr_perm is Some,
            final(self).metadata_perms->0 == *final(res.0),
            final(self).repr_perm->0 == *final(res.1),
            final(self).inv(),
    {
        match (&mut self.metadata_perms, &mut self.repr_perm) {
            (Some(metadata), Some(repr)) => (metadata, repr),
            _ => proof_from_false(),
        }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> TrackDrop for UniqueFrame<M> {
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
        s1 == s0
    }

    proof fn tracked_redeem(self, tracked s: &mut Self::State) -> (tracked obl: Self::Obligation) {
        ()
    }

    open spec fn drop_requires(self, s: Self::State, obl: Self::Obligation) -> bool {
        &&& s.contains(self.index())
        &&& s.inv()
    }

    open spec fn drop_ensures(
        self,
        s0: Self::State,
        s1: Self::State,
        obl: Self::Obligation,
    ) -> bool {
        &&& forall|i: int|
            #![trigger s1.slot_owners[i]]
            i != self.index() ==> s1.slot_owners[i] == s0.slot_owners[i]
        &&& s1.slots =~= s0.slots
        &&& s1.inv()
    }
}

} // verus!
