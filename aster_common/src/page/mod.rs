pub mod dyn_page;
pub mod meta;

pub use dyn_page::*;
pub use meta::*;

use crate::mm::Paddr;
use crate::x86_64::mm::{MAX_NR_PAGES, MAX_PADDR, PAGE_SIZE};
use core::marker::PhantomData;
use vstd::cell;
use vstd::prelude::*;
use vstd::simple_pptr::{self, PPtr};

use crate::prelude::MetaSlotStorage::PTNode;
use crate::prelude::*;

use vstd_extra::ownership::*;

use std::mem::ManuallyDrop;
use std::ops::Deref;

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

/// A struct that can work as `&'a Frame<M>`.
#[rustc_has_incoherent_inherent_impls]
pub struct FrameRef<'a, M: AnyFrameMeta> {
    pub inner:   /*ManuallyDrop<*/
    Frame<M>  /*>*/
    ,
    pub _marker: PhantomData<&'a Frame<M>>,
}

impl<M: AnyFrameMeta> Deref for FrameRef<'_, M> {
    type Target = Frame<M>;

    #[verus_spec(ensures returns self.inner)]
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<M: AnyFrameMeta> Inv for Frame<M> {
    open spec fn inv(self) -> bool {
        &&& self.ptr.addr() % META_SLOT_SIZE() == 0
        &&& FRAME_METADATA_RANGE().start <= self.ptr.addr() < FRAME_METADATA_RANGE().start
            + MAX_NR_PAGES() * META_SLOT_SIZE()
        &&& self.ptr.addr() < VMALLOC_BASE_VADDR() - LINEAR_MAPPING_BASE_VADDR()
    }
}

impl<M: AnyFrameMeta> Frame<M> {
    #[verifier::external_body]
    pub fn meta_pt<'a, C: PageTableConfig>(
        &'a self,
        Tracked(p_slot): Tracked<&'a simple_pptr::PointsTo<MetaSlot>>,
        owner:
            MetaSlotOwner,
        //        Tracked(p_inner): Tracked<&'a cell::PointsTo<MetaSlotInner>>,
    ) -> (res: &PageTablePageMeta<C>)
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
