pub mod allocator;
mod frame_ref;
pub mod meta;

pub use frame_ref::FrameRef;

use std::marker::PhantomData;
use std::mem::ManuallyDrop;

use meta::AnyFrameMeta;
use meta::GetFrameError;
use meta::MetaSlot;
use vstd::prelude::*;
use vstd::simple_pptr::*;

use crate::mm::Paddr;
use crate::mm::PagingLevel;
use crate::mm::PAGE_SIZE;
use crate::exec::MockPageTablePage;

use super::PageTableConfig;

verus! {

// #[repr(transparent)] TODO: repr(transparent)
// pub struct Frame<M: AnyFrameMeta + ?Sized> { // NOTE: Verus does not support dyn type, so we remove it currently
pub struct Frame<M: AnyFrameMeta> {
    pub meta_ptr: PPtr<M>,
    pub meta_perm: Tracked<PointsTo<M>>,
    pub ptr: PPtr<MockPageTablePage>,
}

impl<M: AnyFrameMeta> Frame<M> {
    /// Gets the metadata of this page.
    #[verifier::external_body]
    #[verifier::allow_in_spec]
    pub fn meta(&self) -> &M
        returns
            self.meta_perm@.value(),
    {
        self.meta_ptr.borrow(Tracked(self.meta_perm.borrow()))
    }
}

impl<M: AnyFrameMeta> Frame<M> {
    /// Gets the physical address of the start of the frame.
    // TODO: Implement
    #[verifier::allow_in_spec]
    pub fn start_paddr(&self) -> Paddr
        returns
            self.ptr.addr() as Paddr,
    {
        // self.slot().frame_paddr() // TODO
        self.ptr.addr() as Paddr
    }

    /// Gets the paging level of this page.
    ///
    /// This is the level of the page table entry that maps the frame,
    /// which determines the size of the frame.
    ///
    /// Currently, the level is always 1, which means the frame is a regular
    /// page frame.
    #[verifier::allow_in_spec]
    pub const fn map_level(&self) -> (res: PagingLevel)
        returns
            1 as PagingLevel,
    {
        1
    }

    /// Gets the size of this page in bytes.
    #[verifier::allow_in_spec]
    pub fn size(&self) -> (res: usize)
        returns
            PAGE_SIZE(),
    {
        PAGE_SIZE()
    }

    /// Borrows a reference from the given frame.
    pub fn borrow(&self) -> FrameRef<'_, M> {
        FrameRef::borrow_paddr(self.start_paddr())
    }

    /// Forgets the handle to the frame.
    ///
    /// This will result in the frame being leaked without calling the custom dropper.
    ///
    /// A physical address to the frame is returned in case the frame needs to be
    /// restored using [`Frame::from_raw`] later. This is useful when some architectural
    /// data structures need to hold the frame handle such as the page table.
    /// TODO: Implement Frame::into_raw
    #[verifier::external_body]
    pub(in crate::mm) fn into_raw(self) -> Paddr {
        let this = ManuallyDrop::new(self);
        this.start_paddr()
    }

    /// Restores a forgotten [`Frame`] from a physical address.
    ///
    /// # Safety
    ///
    /// The caller should only restore a `Frame` that was previously forgotten using
    /// [`Frame::into_raw`].
    ///
    /// And the restoring operation should only be done once for a forgotten
    /// [`Frame`]. Otherwise double-free will happen.
    ///
    /// Also, the caller ensures that the usage of the frame is correct. There's
    /// no checking of the usage in this function.
    #[verifier::external_body]
    pub(crate) fn from_raw(paddr: Paddr) -> (res: Self)
        ensures
            res.ptr.addr() == paddr,
    {
        // let vaddr = mapping::frame_to_meta::<PagingConsts>(paddr);
        // let ptr = vaddr as *const MetaSlot;
        // FIXME: Need to allocate and use metadata, currently this is just a placeholder.
        Self {
            ptr: PPtr::from_addr(paddr),
            meta_ptr: PPtr::from_addr(paddr),
            meta_perm: Tracked::assume_new(),
        }
    }
}

} // verus!
