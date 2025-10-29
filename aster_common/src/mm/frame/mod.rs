mod frame_ref;
mod linked_list;
mod linked_list_owners;
mod meta;
mod meta_owners;
mod meta_region_owners;
mod unique;

pub use frame_ref::*;
pub use linked_list::*;
pub use linked_list_owners::*;
pub use meta::*;
pub use meta_owners::*;
pub use meta_region_owners::*;
pub use unique::*;

use vstd::prelude::*;
use vstd::simple_pptr::{self, PPtr};

use vstd_extra::ownership::*;

use std::marker::PhantomData;

use super::*;

verus! {

/// A smart pointer to a frame.
///
/// A frame is a contiguous range of bytes in physical memory. The [`Frame`]
/// type is a smart pointer to a frame that is reference-counted.
///
/// Frames are associated with metadata. The type of the metadata `M` is
/// determines the kind of the frame. If `M` implements [`AnyUFrameMeta`], the
/// frame is a untyped frame. Otherwise, it is a typed frame.
#[repr(transparent)]
#[rustc_has_incoherent_inherent_impls]
pub struct Frame<M: AnyFrameMeta> {
    pub ptr: PPtr<MetaSlot>,
    pub _marker: PhantomData<M>,
}

impl<M: AnyFrameMeta> Inv for Frame<M> {
    open spec fn inv(&self) -> bool {
        &&& self.ptr.addr() % META_SLOT_SIZE() == 0
        &&& FRAME_METADATA_RANGE().start <= self.ptr.addr() < FRAME_METADATA_RANGE().start
            + MAX_NR_PAGES() * META_SLOT_SIZE()
        &&& self.ptr.addr() < VMALLOC_BASE_VADDR() - LINEAR_MAPPING_BASE_VADDR()
    }
}

impl<M: AnyFrameMeta> Frame<M> {
    pub open spec fn paddr(self) -> usize {
        meta_to_frame(self.ptr.addr())
    }

    pub open spec fn index(self) -> usize {
        frame_to_index(self.paddr())
    }

    #[verifier::external_body]
    pub fn meta_pt<'a, C: PageTableConfig>(
        &'a self,
        Tracked(p_slot): Tracked<&'a simple_pptr::PointsTo<MetaSlot>>,
        owner:
            MetaSlotOwner,
        //        Tracked(p_inner): Tracked<&'a cell::PointsTo<MetaSlotInner>>,
    ) -> (res: &'a PageTablePageMeta<C>)
        requires
            self.inv(),
            p_slot.pptr() == self.ptr,
            p_slot.is_init(),
            p_slot.value().wf(&owner),
            is_variant(owner.view().storage.value(), "PTNode"),
        ensures
    //            PTNode(*res) == owner.view().storage.value(),

    {
        let slot = self.ptr.borrow(Tracked(p_slot));
        unimplemented!()
        //        slot.storage.borrow(owner.storage)

    }
}

} // verus!
