// SPDX-License-Identifier: MPL-2.0
//! Frame (physical memory page) management.
//!
//! A frame is an aligned, contiguous range of bytes in physical memory. The
//! sizes of base frames and huge frames (that are mapped as "huge pages") are
//! architecture-dependent. A frame can be mapped to virtual address spaces
//! using the page table.
//!
//! Frames can be accessed through frame handles, namely, [`Frame`]. A frame
//! handle is a reference-counted pointer to a frame. When all handles to a
//! frame are dropped, the frame is released and can be reused.  Contiguous
//! frames are managed with [`Segment`].
//!
//! There are various kinds of frames. The top-level grouping of frame kinds
//! are "typed" frames and "untyped" frames. Typed frames host Rust objects
//! that must follow the visibility, lifetime and borrow rules of Rust, thus
//! not being able to be directly manipulated. Untyped frames are raw memory
//! that can be manipulated directly. So only untyped frames can be
//!  - safely shared to external entities such as device drivers or user-space
//!    applications.
//!  - or directly manipulated with readers and writers that neglect Rust's
//!    "alias XOR mutability" rule.
//!
//! The kind of a frame is determined by the type of its metadata. Untyped
//! frames have its metadata type that implements the [`AnyUFrameMeta`]
//! trait, while typed frames don't.
//!
//! Frames can have dedicated metadata, which is implemented in the [`meta`]
//! module. The reference count and usage of a frame are stored in the metadata
//! as well, leaving the handle only a pointer to the metadata slot. Users
//! can create custom metadata types by implementing the [`AnyFrameMeta`] trait.
//pub mod allocator;
pub mod linked_list;
pub mod meta;
pub mod segment;
pub mod unique;
pub mod untyped;

mod frame_ref;

#[cfg(ktest)]
mod test;

use vstd::atomic::PermissionU64;
use vstd::prelude::*;
use vstd::simple_pptr::PPtr;

use core::{
    marker::PhantomData,
    mem::ManuallyDrop,
    sync::atomic::{AtomicUsize, Ordering},
};

//pub use allocator::GlobalFrameAllocator;
use meta::REF_COUNT_UNUSED;
//pub use segment::Segment;
use untyped::{/*AnyUFrameMeta,*/ UFrame};

use super::{PagingLevel, PAGE_SIZE};
use crate::mm::{Paddr, Vaddr};

use vstd_extra::cast_ptr::*;
use vstd_extra::ownership::*;

use aster_common::prelude::frame::*;
use aster_common::prelude::*;

verus! {

/*
unsafe impl<M: AnyFrameMeta + ?Sized> Send for Frame<M> {}

unsafe impl<M: AnyFrameMeta + ?Sized> Sync for Frame<M> {}

impl<M: AnyFrameMeta + ?Sized> core::fmt::Debug for Frame<M> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "Frame({:#x})", self.start_paddr())
    }
}

impl<M: AnyFrameMeta + ?Sized> PartialEq for Frame<M> {
    fn eq(&self, other: &Self) -> bool {
        self.start_paddr() == other.start_paddr()
    }
}
impl<M: AnyFrameMeta + ?Sized> Eq for Frame<M> {}
*/
impl<'a, M: AnyFrameMeta> Frame<M> {
    /// Gets a [`Frame`] with a specific usage from a raw, unused page.
    ///
    /// The caller should provide the initial metadata of the page.
    ///
    /// If the provided frame is not truly unused at the moment, it will return
    /// an error. If wanting to acquire a frame that is already in use, use
    /// [`Frame::from_in_use`] instead.
    #[verus_spec(
        with Tracked(regions): Tracked<&mut MetaRegionOwners>
    )]
    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub fn from_unused(paddr: Paddr, metadata: M) -> (res: Result<Self, GetFrameError>)
        requires
            old(regions).inv(),
            paddr < MAX_PADDR(),
            paddr % PAGE_SIZE() == 0,
            old(regions).slots.contains_key(frame_to_index(paddr)),
            old(regions).slot_owners[frame_to_index(paddr)].usage is Unused,
            old(regions).slot_owners[frame_to_index(paddr)].in_list@.points_to(0),
            old(regions).slot_owners[frame_to_index(paddr)].self_addr == frame_to_meta(paddr),
        ensures
            res.is_ok() ==> regions.view() == MetaSlot::get_from_unused_spec::<M>(
                paddr,
                metadata,
                false,
                old(regions).view(),
            ).1,
            regions.inv(),
            forall|paddr: Paddr| #[trigger]
                old(regions).slots.contains_key(frame_to_index(paddr))
                    ==> regions.slots.contains_key(frame_to_index(paddr)),
    {
        #[verus_spec(with Tracked(regions))]
        let from_unused = MetaSlot::get_from_unused(paddr, metadata, false);
        Ok(Self { ptr: from_unused?, _marker: PhantomData })
    }

    /// Gets the metadata of this page.
    #[verus_spec(
        with Tracked(slot_own) : Tracked<&MetaSlotOwner>,
            Tracked(slot_perm) : Tracked<&'a vstd::simple_pptr::PointsTo<MetaSlot>>,
            Tracked(perm) : Tracked<&'a PointsTo<MetaSlotStorage, M>>
    )]
    #[rustc_allow_incoherent_impl]
    pub fn meta(&self) -> &'a M
        requires
            self.ptr == slot_perm.pptr(),
            slot_perm.is_init(),
            slot_perm.value().wf(*slot_own),
            slot_own.inv(),
            perm.pptr().ptr.0 == slot_own.storage@.addr(),
            perm.pptr().addr == slot_own.storage@.addr(),
            perm.is_init(),
            perm.wf(),
        returns
            &perm.value(),
    {
        // SAFETY: The type is tracked by the type system.
        #[verus_spec(with Tracked(slot_perm))]
        let slot = self.slot();

        #[verus_spec(with Tracked(slot_own))]
        let ptr = slot.as_meta_ptr();
        assert(ptr.ptr.0 == slot_own.storage@.addr());

        ptr.borrow(Tracked(perm))
    }
}

impl<M: AnyFrameMeta> Frame<M> {
    /// Gets a dynamically typed [`Frame`] from a raw, in-use page.
    ///
    /// If the provided frame is not in use at the moment, it will return an error.
    ///
    /// The returned frame will have an extra reference count to the frame.
    #[verus_spec(
        with Tracked(regions) : Tracked<&mut MetaRegionOwners>
    )]
    #[rustc_allow_incoherent_impl]
    pub fn from_in_use(paddr: Paddr) -> Result<Self, GetFrameError> {
        #[verus_spec(with Tracked(regions))]
        let from_in_use = MetaSlot::get_from_in_use(paddr);
        Ok(Self { ptr: from_in_use?, _marker: PhantomData })
    }
}

impl<'a, M: AnyFrameMeta> Frame<M> {
    /// Gets the physical address of the start of the frame.
    #[verus_spec(
        with Tracked(slot_own) : Tracked<&MetaSlotOwner>,
            Tracked(slot_perm) : Tracked<&vstd::simple_pptr::PointsTo<MetaSlot>>
    )]
    #[rustc_allow_incoherent_impl]
    pub fn start_paddr(&self) -> Paddr
        requires
            slot_perm.pptr() == self.ptr,
            slot_perm.is_init(),
            slot_perm.value().wf(*slot_own),
            slot_own.inv(),
        returns
            slot_perm.value().frame_paddr_spec(slot_own@),
    {
        #[verus_spec(with Tracked(slot_perm))]
        let slot = self.slot();

        #[verus_spec(with Tracked(slot_own))]
        slot.frame_paddr()
    }

    /// Gets the map level of this page.
    ///
    /// This is the level of the page table entry that maps the frame,
    /// which determines the size of the frame.
    ///
    /// Currently, the level is always 1, which means the frame is a regular
    /// page frame.
    #[rustc_allow_incoherent_impl]
    pub const fn map_level(&self) -> PagingLevel {
        1
    }

    /// Gets the size of this page in bytes.
    #[rustc_allow_incoherent_impl]
    pub const fn size(&self) -> usize {
        PAGE_SIZE()
    }

    /*    /// Gets the dyncamically-typed metadata of this frame.
    ///
    /// If the type is known at compile time, use [`Frame::meta`] instead.
    pub fn dyn_meta(&self) -> FrameMeta {
        // SAFETY: The metadata is initialized and valid.
        unsafe { &*self.slot().dyn_meta_ptr() }
    }*/
    /// Gets the reference count of the frame.
    ///
    /// It returns the number of all references to the frame, including all the
    /// existing frame handles ([`Frame`], [`Frame<dyn AnyFrameMeta>`]), and all
    /// the mappings in the page table that points to the frame.
    ///
    /// # Safety
    ///
    /// The function is safe to call, but using it requires extra care. The
    /// reference count can be changed by other threads at any time including
    /// potentially between calling this method and acting on the result.
    #[verus_spec(
        with Tracked(slot_own): Tracked<&mut MetaSlotOwner>,
            Tracked(slot_perm) : Tracked<& vstd::simple_pptr::PointsTo<MetaSlot>>
    )]
    #[rustc_allow_incoherent_impl]
    pub fn reference_count(&self) -> u64
        requires
            slot_perm.pptr() == self.ptr,
            slot_perm.is_init(),
            old(slot_own).ref_count@.is_for(slot_perm.value().ref_count),
        returns
            old(slot_own)@.ref_count,
    {
        #[verus_spec(with Tracked(slot_perm))]
        let slot = self.slot();
        slot.ref_count.load(Tracked(slot_own.ref_count.borrow()))
    }

    /// Borrows a reference from the given frame.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(regions): Tracked<&mut MetaRegionOwners>
    )]
    pub fn borrow(&self) -> FrameRef<'_, M>
        requires
            old(regions).inv(),
            self.paddr() % PAGE_SIZE() == 0,
            self.paddr() < MAX_PADDR(),
            !old(regions).slots.contains_key(self.index()),
            old(regions).dropped_slots.contains_key(self.index()),
            old(regions).dropped_slots[self.index()]@.pptr() == self.ptr,
    {
        assert(regions.slot_owners.contains_key(self.index()));
        // SAFETY: Both the lifetime and the type matches `self`.
        #[verus_spec(with Tracked(regions.slot_owners.tracked_borrow(self.index())),
                            Tracked(regions.dropped_slots.tracked_borrow(self.index()).borrow()))]
        let paddr = self.start_paddr();

        #[verus_spec(with Tracked(regions))]
        FrameRef::borrow_paddr(paddr)
    }

    /// Forgets the handle to the frame.
    ///
    /// This will result in the frame being leaked without calling the custom dropper.
    ///
    /// A physical address to the frame is returned in case the frame needs to be
    /// restored using [`Frame::from_raw`] later. This is useful when some architectural
    /// data structures need to hold the frame handle such as the page table.
    #[verus_spec(
        with Tracked(regions) : Tracked<&mut MetaRegionOwners>
    )]
    #[rustc_allow_incoherent_impl]
    pub fn into_raw(self) -> (res: Paddr)
        requires
    //            FRAME_METADATA_RANGE().start <= frame_to_index(self.ptr.addr())
    //                < FRAME_METADATA_RANGE().end,

            old(regions).slots.contains_key(self.index()),
            !old(regions).dropped_slots.contains_key(self.index()),
            old(regions).inv(),
        ensures
            res == meta_to_frame(self.ptr.addr()),
            regions.slot_owners == old(regions).slot_owners,
            regions.dropped_slots == old(regions).dropped_slots,
            forall|i: usize|
                i != frame_to_index(self.ptr.addr()) ==> regions.slots[i] == old(regions).slots[i],
    {
        assert(regions.slots[self.index()]@.addr() == self.paddr()) by { admit() };
        let tracked owner = regions.slot_owners.tracked_borrow(self.index());
        let tracked perm = regions.slots.tracked_remove(self.index());

        // TODO: implement ManuallyDrop
        // let this = ManuallyDrop::new(self);
        #[verus_spec(with Tracked(owner), Tracked(perm.borrow()))]
        let paddr = self.start_paddr();

        proof {
            regions.dropped_slots.tracked_insert(frame_to_index(paddr), perm);
        }

        paddr
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
    #[verus_spec(
        with Tracked(regions) : Tracked<&mut MetaRegionOwners>
    )]
    #[rustc_allow_incoherent_impl]
    pub fn from_raw(paddr: Paddr) -> (res: Self)
        requires
            paddr % PAGE_SIZE() == 0,
            paddr < MAX_PADDR(),
            !old(regions).slots.contains_key(frame_to_index(paddr)),
            old(regions).dropped_slots.contains_key(frame_to_index(paddr)),
            old(regions).inv(),
        ensures
            regions.slots.contains_key(frame_to_index(paddr)),
            !regions.dropped_slots.contains_key(frame_to_index(paddr)),
            regions.slots[frame_to_index(paddr)] == old(regions).dropped_slots[frame_to_index(
                paddr,
            )],
            forall|i: usize|
                i != frame_to_index(paddr) ==> regions.slots[i] == old(regions).slots[i],
            forall|i: usize|
                i != frame_to_index(paddr) ==> regions.dropped_slots[i] == old(
                    regions,
                ).dropped_slots[i],
            regions.slot_owners == old(regions).slot_owners,
            res.ptr == regions.slots[frame_to_index(paddr)]@.pptr(),
    {
        let vaddr = frame_to_meta(paddr);
        let ptr = PPtr::from_addr(vaddr);

        let tracked perm = regions.dropped_slots.tracked_remove(frame_to_index(paddr));
        proof {
            regions.slots.tracked_insert(frame_to_index(paddr), perm);
        }

        Self { ptr, _marker: PhantomData }
    }

    #[verus_spec(
        with Tracked(slot_perm): Tracked<&'a vstd::simple_pptr::PointsTo<MetaSlot>>
    )]
    #[rustc_allow_incoherent_impl]
    pub fn slot(&self) -> (slot: &'a MetaSlot)
        requires
            slot_perm.pptr() == self.ptr,
            slot_perm.is_init(),
        returns
            slot_perm.value(),
    {
        // SAFETY: `ptr` points to a valid `MetaSlot` that will never be
        // mutably borrowed, so taking an immutable reference to it is safe.
        self.ptr.borrow(Tracked(slot_perm))
    }
}

} // verus!
/*
impl<M: AnyFrameMeta + ?Sized> Clone for Frame<M> {
    fn clone(&self) -> Self {
        // SAFETY: We have already held a reference to the frame.
        unsafe { self.slot().inc_ref_count() };

        Self {
            ptr: self.ptr,
            _marker: PhantomData,
        }
    }
}*/
/*
impl<M: AnyFrameMeta + ?Sized> Drop for Frame<M> {
    fn drop(&mut self) {
        let last_ref_cnt = self.slot().ref_count.fetch_sub(1, Ordering::Release);
        debug_assert!(last_ref_cnt != 0 && last_ref_cnt != REF_COUNT_UNUSED);

        if last_ref_cnt == 1 {
            // A fence is needed here with the same reasons stated in the implementation of
            // `Arc::drop`: <https://doc.rust-lang.org/std/sync/struct.Arc.html#method.drop>.
            core::sync::atomic::fence(Ordering::Acquire);

            // SAFETY: this is the last reference and is about to be dropped.
            unsafe { self.slot().drop_last_in_place() };

            allocator::get_global_frame_allocator().dealloc(self.start_paddr(), PAGE_SIZE);
        }
    }
}
*/
/*
impl<M: AnyFrameMeta> TryFrom<Frame<dyn AnyFrameMeta>> for Frame<M> {
    type Error = Frame<dyn AnyFrameMeta>;

    /// Tries converting a [`Frame<dyn AnyFrameMeta>`] into the statically-typed [`Frame`].
    ///
    /// If the usage of the frame is not the same as the expected usage, it will
    /// return the dynamic frame itself as is.
    fn try_from(dyn_frame: Frame<dyn AnyFrameMeta>) -> Result<Self, Self::Error> {
        if (dyn_frame.dyn_meta() as &dyn core::any::Any).is::<M>() {
            // SAFETY: The metadata is coerceable and the struct is transmutable.
            Ok(unsafe { core::mem::transmute::<Frame<dyn AnyFrameMeta>, Frame<M>>(dyn_frame) })
        } else {
            Err(dyn_frame)
        }
    }
}*/
/*impl<M: AnyFrameMeta> From<Frame<M>> for Frame<dyn AnyFrameMeta> {
    fn from(frame: Frame<M>) -> Self {
        // SAFETY: The metadata is coerceable and the struct is transmutable.
        unsafe { core::mem::transmute(frame) }
    }
}*/
/*impl<M: AnyUFrameMeta> From<Frame<M>> for UFrame {
    fn from(frame: Frame<M>) -> Self {
        // SAFETY: The metadata is coerceable and the struct is transmutable.
        unsafe { core::mem::transmute(frame) }
    }
}*/
/*impl From<UFrame> for Frame<FrameMeta> {
    fn from(frame: UFrame) -> Self {
        // SAFETY: The metadata is coerceable and the struct is transmutable.
        unsafe { core::mem::transmute(frame) }
    }
}*/
/*impl TryFrom<Frame<FrameMeta>> for UFrame {
    type Error = Frame<FrameMeta>;

    /// Tries converting a [`Frame<dyn AnyFrameMeta>`] into [`UFrame`].
    ///
    /// If the usage of the frame is not the same as the expected usage, it will
    /// return the dynamic frame itself as is.
    fn try_from(dyn_frame: Frame<FrameMeta>) -> Result<Self, Self::Error> {
        if dyn_frame.dyn_meta().is_untyped() {
            // SAFETY: The metadata is coerceable and the struct is transmutable.
            Ok(unsafe { core::mem::transmute::<Frame<FrameMeta>, UFrame>(dyn_frame) })
        } else {
            Err(dyn_frame)
        }
    }
}*/
/// Increases the reference count of the frame by one.
///
/// # Safety
///
/// The caller should ensure the following conditions:
///  1. The physical address must represent a valid frame;
///  2. The caller must have already held a reference to the frame.
#[verifier::external_body]
pub(in crate::mm) unsafe fn inc_frame_ref_count(paddr: Paddr) {
    debug_assert!(paddr % PAGE_SIZE() == 0);

    let vaddr: Vaddr = frame_to_meta(paddr);
    // SAFETY: `vaddr` points to a valid `MetaSlot` that will never be mutably borrowed, so taking
    // an immutable reference to it is always safe.
    let slot = unsafe { &*(vaddr as *const MetaSlot) };

    // SAFETY: We have already held a reference to the frame.
    slot.inc_ref_count();
}
