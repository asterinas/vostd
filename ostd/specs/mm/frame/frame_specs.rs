use vstd::cell::CellId;

use vstd::{prelude::*, simple_pptr};
use vstd_extra::{cast_ptr::*, ownership::*};

use crate::specs::{
    arch::*,
    mm::frame::{
        mapping::{frame_to_index, meta_to_index},
        meta_owners::{FracMetadataPerm, MetadataPerm, PageUsage},
        meta_region_owners::MetaRegionOwners,
    },
};

use crate::mm::{
    Paddr, PagingLevel, Vaddr,
    frame::{
        meta::{
            META_SLOT_SIZE, MetaSlot, REF_COUNT_MAX, REF_COUNT_UNIQUE, REF_COUNT_UNUSED,
            mapping::{frame_to_meta, meta_to_frame},
        },
        *,
    },
    kspace::FRAME_METADATA_RANGE,
};

verus! {

impl<M: ?Sized> Frame<M> {
    /// Accessor for the fractional metadata permission tracked by this `Frame` handle.
    #[verifier::inline]
    pub open spec fn frac_metadata_perm(self) -> FracMetadataPerm {
        self.tracked_metadata_perm@->0
    }

    /// Accessor for the full metadata permission tracked by the fractional permission.
    #[verifier::inline]
    pub open spec fn metadata_perm(self) -> MetadataPerm {
        self.frac_metadata_perm().resource()
    }

    /// Accessor for the [`MetaSlot`] permission tracked by this `Frame` handle.
    pub open spec fn slot_perm(self) -> simple_pptr::PointsTo<MetaSlot> {
        *self.tracked_slot_perm@
    }

    /// Accessor for the id of the `ref_count` field.
    #[verifier::inline]
    pub open spec fn ref_count_id(self) -> int {
        self.slot_perm().value().ref_count.id()
    }

    /// Accessor for the id of the `storage` field.
    #[verifier::inline]
    pub open spec fn storage_id(self) -> CellId {
        self.slot_perm().value().storage.id()
    }

    /// Address-related invariant shared by owning frames and non-owning
    /// `ManuallyDrop<Frame>` values embedded in `FrameRef`.
    #[verifier::inline]
    pub open spec fn ptr_inv(self) -> bool {
        &&& valid_frame_paddr(meta_to_frame(self.ptr.addr()))
        &&& self.ptr.addr() % META_SLOT_SIZE == 0
        &&& FRAME_METADATA_RANGE.start <= self.ptr.addr() < FRAME_METADATA_RANGE.start
            + MAX_NR_PAGES * META_SLOT_SIZE
        &&& self.slot_perm().pptr() == self.ptr
        &&& self.slot_perm().is_init()
    }

    // [`Frame::from_raw`] precondition
    pub open spec fn from_raw_requires(regions: MetaRegionOwners, paddr: Paddr) -> bool {
        &&& regions.slot_owner(paddr).slot_vaddr == frame_to_meta(paddr)
        &&& valid_frame_paddr(paddr)
        &&& regions.inv()
        &&& 0 < regions.slot_owner(paddr).ref_count() <= REF_COUNT_MAX
    }
}

impl<M: ?Sized> Inv for Frame<M> {
    open spec fn inv(self) -> bool {
        &&& self.ptr_inv()
        &&& self.tracked_metadata_perm@ is Some
        &&& self.frac_metadata_perm().frac() == 1
        &&& MetaSlot::perms_related(self.slot_perm(), self.metadata_perm())
    }
}

impl<M: ?Sized> Frame<M> {
    pub open spec fn index(self) -> int {
        frame_to_index(self.start_paddr_spec())
    }

    pub open spec fn start_paddr_spec(self) -> Paddr {
        meta_to_frame(self.ptr.addr())
    }

    pub open spec fn from_unused_spec(
        paddr: Paddr,
        pre: MetaRegionOwners,
        post: MetaRegionOwners,
    ) -> bool {
        let pre_owner = pre.slot_owner(paddr);
        let post_owner = post.slot_owner(paddr);
        {
            &&& pre_owner.ref_count() == REF_COUNT_UNUSED
            &&& MetaSlot::get_from_unused_owner_spec(false, post_owner)
            &&& post_owner.usage is Frame
            &&& post_owner.slot_vaddr == pre_owner.slot_vaddr
            &&& post_owner.paths_in_pt == pre_owner.paths_in_pt
            &&& post =~= pre.insert_slot_owner(paddr, post_owner)
        }
    }

    pub open spec fn drop_requires(self, region: MetaRegionOwners) -> bool {
        let idx = self.index();
        let slot_own = region.slot_owners[idx];
        &&& self.inv()
        &&& region.inv()
        &&& self.wf_with_region(region)
        &&& 0 < slot_own.ref_count() <= REF_COUNT_MAX
        &&& slot_own.ref_count() == 1 ==> {
            &&& slot_own.paths_in_pt.is_empty()
        }
    }

    pub open spec fn drop_ensures(self, old: MetaRegionOwners, new: MetaRegionOwners) -> bool {
        let paddr = self.start_paddr_spec();
        let old_owner = old.slot_owner(paddr);
        let new_owner = new.slot_owner(paddr);
        &&& new.inv()
        &&& new =~= old.insert_slot_owner(paddr, new_owner)
        &&& new_owner.slot_vaddr == old_owner.slot_vaddr
        &&& new_owner.usage == old_owner.usage
        &&& new_owner.paths_in_pt == old_owner.paths_in_pt
        &&& new_owner.metadata_perm.id() == old_owner.metadata_perm.id()
        &&& old_owner.ref_count() == 1 ==> { new_owner.ref_count() == REF_COUNT_UNUSED }
        &&& old_owner.ref_count() > 1 ==> new_owner.ref_count() == (old_owner.ref_count()
            - 1) as u64
    }
}

impl<M: ?Sized> Frame<M> {
    /// Relates this `Frame` handle to its metadata in the metadata region.
    pub open spec fn wf_with_region(self, s: MetaRegionOwners) -> bool {
        let idx = self.index();
        let slot_own = s.slot_owners[idx];
        &&& s.contains(idx)
        &&& self.tracked_slot_perm@ == s.slots[idx]
        &&& self.frac_metadata_perm().id() == slot_own.metadata_perm.id()
    }
}

} // verus!
