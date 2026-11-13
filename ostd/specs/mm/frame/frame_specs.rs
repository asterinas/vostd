use crate::specs::mm::frame::meta_owners::META_STORAGE_SIZE;
use vstd::{
    cell::CellId,
    prelude::*,
    simple_pptr::{self, PPtr, PointsTo},
};
use vstd_extra::ownership::*;
use vstd_extra::raw_ptr::ExposedPointsTo;
use vstd_extra::typing::tagged::MaxSize;

use crate::specs::{
    arch::*,
    mm::frame::{
        mapping::{frame_to_index, meta_to_index},
        meta_owners::*,
        meta_region_owners::MetaRegionOwners,
    },
};

use crate::mm::{
    Paddr, PagingLevel, Vaddr,
    frame::{
        meta::{
            AnyFrameMeta, META_SLOT_SIZE, MetaSlot, REF_COUNT_MAX, REF_COUNT_UNIQUE,
            REF_COUNT_UNUSED,
            mapping::{frame_to_meta, meta_to_frame},
        },
        *,
    },
    kspace::FRAME_METADATA_RANGE,
};
use core::marker::PhantomData;

verus! {

pub open spec fn valid_slot_vaddr(addr: Vaddr) -> bool {
    &&& valid_frame_paddr(meta_to_frame(addr))
    &&& addr % META_SLOT_SIZE == 0
    &&& FRAME_METADATA_RANGE.start <= addr < FRAME_METADATA_RANGE.start + MAX_NR_PAGES
        * META_SLOT_SIZE
}

/// The permission that is given out by `Frame::into_raw`
pub tracked struct FrameRawPerms {
    pub slot_perm: &'static ExposedPointsTo<MetaSlot>,
    pub metadata_perm: FracMetadataPerm,
}

// SAFETY: Slot and counted metadata permissions describe global memory ownership
// and do not carry subjective weak-memory observations.
#[cfg(feature = "irc11")]
unsafe impl vstd::thread_view::Objective for FrameRawPerms {

}

impl FrameRawPerms {
    pub open spec fn slot_vaddr(self) -> Vaddr {
        self.slot_perm.ptr().addr()
    }
}

impl Inv for FrameRawPerms {
    open spec fn inv(self) -> bool {
        &&& valid_slot_vaddr(self.slot_vaddr())
        &&& self.slot_perm.is_init()
        &&& self.metadata_perm.frac() == 1
        &&& MetaSlot::perms_related(*self.slot_perm, self.metadata_perm.resource())
    }
}

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
    pub open spec fn slot_perm(self) -> ExposedPointsTo<MetaSlot> {
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
        &&& valid_slot_vaddr(self.slot_vaddr())
        &&& self.slot_perm().ptr() == self.ptr
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

impl<M: AnyFrameMeta + MaxSize<META_STORAGE_SIZE> + ?Sized> Frame<M> {
    /// Relates an externally stored metadata permission to this frame's slot permission.
    pub open spec fn external_meta_wf(self, metadata_perm: MetadataPerm) -> bool {
        &&& self.ptr_inv()
        &&& self.tracked_metadata_perm@ is None
        &&& typed_meta_wf::<M>(self.slot_perm(), metadata_perm)
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

    #[verifier::inline]
    pub open spec fn slot_vaddr(self) -> Vaddr {
        self.ptr.addr()
    }

    pub open spec fn start_paddr_spec(self) -> Paddr {
        meta_to_frame(self.slot_vaddr())
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

impl<M: ?Sized> Frame<M> {
    /// Models a frame handle using the pointer and metadata permissions supplied.
    pub open spec fn from_perms_spec(
        slot_perm: &'static ExposedPointsTo<MetaSlot>,
        metadata_perm: Option<FracMetadataPerm>,
    ) -> Self {
        Frame::<M> {
            ptr: slot_perm.ptr(),
            _marker: PhantomData,
            #[cfg(verus_keep_ghost_body)]
            tracked_slot_perm: Tracked(slot_perm),
            #[cfg(verus_keep_ghost_body)]
            tracked_metadata_perm: Tracked(metadata_perm),
        }
    }
}

} // verus!
