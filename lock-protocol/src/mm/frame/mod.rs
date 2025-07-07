pub mod meta;

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

verus! {

// #[repr(transparent)] TODO: repr(transparent)
// pub struct Frame<M: AnyFrameMeta + ?Sized> { // NOTE: Verus does not support dyn type, so we remove it currently
pub struct Frame {
    // pub ptr: PPtr<MetaSlot>,
    // pub ptr: *const MetaSlot,
    pub ptr: usize,  // TODO: MetaSlot is currently ignored
    // pub _marker: PhantomData<M>,
}

// impl<M: AnyFrameMeta> Frame<M> {
//     /// Gets the metadata of this page.
//     // TODO: Implement Frame::meta
//     #[verifier::external_body]
//     pub fn meta(&self) -> &M {
//         // SAFETY: The type is tracked by the type system.
//         // unsafe { &*self.slot().as_meta_ptr::<M>() }
//         unimplemented!("Frame::meta")
//     }
// }
// impl<M: AnyFrameMeta + ?Sized> Frame<M> {
impl Frame {
    /// Gets the physical address of the start of the frame.
    // TODO: Implement
    #[verifier::allow_in_spec]
    pub fn start_paddr(&self) -> Paddr
        returns
            self.ptr as Paddr,
    {
        // self.slot().frame_paddr() // TODO
        self.ptr as Paddr
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
    pub const fn size(&self) -> (res: usize)
        returns
            PAGE_SIZE,
    {
        PAGE_SIZE
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
    /// TODO: Implement Frame::from_raw
    pub(in crate::mm) fn from_raw(paddr: Paddr) -> (res: Self)
        ensures
            res.ptr == paddr,
    {
        // let vaddr = mapping::frame_to_meta::<PagingConsts>(paddr);
        // let ptr = vaddr as *const MetaSlot;
        Self {
            ptr: paddr,
            // _marker: PhantomData,
        }
        // Self {
        //     ptr: PPtr::<MetaSlot>::from_addr(paddr),
        //      _marker: PhantomData
        // }

    }
}

} // verus!
