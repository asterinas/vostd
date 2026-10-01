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
use vstd::{
    assert_maps_equal, assert_sets_equal,
    atomic::PermissionU64,
    map::assert_maps_equal_internal,
    prelude::*,
    simple_pptr::{self, PPtr},
    std_specs::cmp::PartialEqSpecImpl,
};
use vstd_extra::{cast_ptr::*, ownership::*, panic::may_panic};
#[cfg(feature = "type_id")]
use vstd::std_specs::convert::TryFromSpecImpl;
#[cfg(feature = "type_id")]
use core::any::TypeId;
use vstd_extra::transmute::{can_transmute, transmuted};
use vstd::std_specs::convert::FromSpecImpl;
#[cfg(feature = "type_id")]
use vstd_extra::typing::types::{Any, is_};

pub mod allocator;
pub mod linked_list;
pub mod meta;
pub mod segment;
pub mod unique;
pub mod untyped;

mod frame_ref;
pub use frame_ref::FrameRef;

#[cfg(ktest)]
mod test;

use crate::specs::{
    arch::*,
    mm::frame::{
        frame_specs::*,
        mapping::{frame_to_index, group_page_meta, index_to_meta, max_meta_slots},
        meta_owners::*,
        meta_region_owners::MetaRegionOwners,
    },
};

use core::{
    marker::PhantomData,
    mem::ManuallyDrop,
    sync::atomic::{AtomicUsize, Ordering},
};

//pub use allocator::GlobalFrameAllocator;
use super::PagingLevel;
use crate::mm::kspace::FRAME_METADATA_RANGE;
use crate::mm::page_table::RCClone;
use crate::mm::page_table::{PageTableConfig, PageTablePageMeta};
use crate::mm::{
    MAX_PADDR, Paddr, Vaddr,
    frame::meta::{
        META_SLOT_SIZE,
        mapping::{frame_to_meta, meta_to_frame},
    },
    kspace::{LINEAR_MAPPING_BASE_VADDR, VMALLOC_BASE_VADDR},
};
pub use linked_list::{CursorMut, Link, LinkedList};
pub use meta::{AnyFrameMeta, GetFrameError, MetaSlot};
use meta::{REF_COUNT_MAX, REF_COUNT_UNIQUE, REF_COUNT_UNUSED, mapping};
pub use segment::Segment;
pub use unique::UniqueFrame;
pub use untyped::{AnyUFrameMeta, UFrame};

verus! {

/*
static MAX_PADDR: AtomicUsize = AtomicUsize::new(0);
*/
/// Returns the maximum physical address that is tracked by frame metadata.
#[verifier::external_body]
pub(in crate::mm) fn max_paddr() -> Paddr
    returns
        MAX_PADDR,
{
    // let max_paddr = MAX_PADDR.load(Ordering::Relaxed) as Paddr;
    // debug_assert_ne!(max_paddr, 0);
    // max_paddr
    unimplemented!()
}

#[verifier::external_body]
fn acquire_fence() {
    core::sync::atomic::fence(Ordering::Acquire);
}

/// A smart pointer to a frame.
///
/// A frame is a contiguous range of bytes in physical memory. The [`Frame`]
/// type is a smart pointer to a frame that is reference-counted.
///
/// Frames are associated with metadata. The type of the metadata `M` is
/// determines the kind of the frame. If `M` implements [`AnyUFrameMeta`], the
/// frame is a untyped frame. Otherwise, it is a typed frame.
// #[repr(transparent)]
pub struct Frame<M: ?Sized> {
    pub ptr: PPtr<MetaSlot>,
    pub _marker: PhantomData<M>,
    /// The permission to access the `MetaSlot` fields.
    #[cfg(verus_keep_ghost_body)]
    pub tracked_slot_perm: Tracked<&'static simple_pptr::PointsTo<MetaSlot>>,
    /// One fractional permission for the currently installed metadata.
    #[cfg(verus_keep_ghost_body)]
    pub tracked_metadata_perm: Tracked<Option<FracMetadataPerm>>,
}

#[verifier::external]
unsafe impl<M: AnyFrameMeta + ?Sized> Send for Frame<M> {

}

#[verifier::external]
unsafe impl<M: AnyFrameMeta + ?Sized> Sync for Frame<M> {

}

/*
impl<M: AnyFrameMeta + ?Sized> core::fmt::Debug for Frame<M> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "Frame({:#x})", self.start_paddr())
    }
}
*/

verus!{

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + ?Sized> PartialEqSpecImpl for Frame<M>{
    open spec fn obeys_eq_spec() -> bool { true }

    open spec fn eq_spec(&self, other: &Self) -> bool {
        self.start_paddr_spec() == other.start_paddr_spec()
    }
}

}

#[verus_verify]
impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + ?Sized> PartialEq for Frame<M> {
    fn eq(&self, other: &Self) -> bool {
        proof!{
            //FIXME: Add `ptr_inv` as type invariant when we fix visibility.
            assume(self.ptr_inv());
            assume(other.ptr_inv());
        }
        self.start_paddr() == other.start_paddr()
    }
}

#[verus_verify]
impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + ?Sized> Eq for Frame<M> {

}

#[verus_verify]
impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> Frame<M> {
    /// Gets a [`Frame`] with a specific usage from a raw, unused page.
    ///
    /// The caller should provide the initial metadata of the page.
    ///
    /// If the provided frame is not truly unused at the moment, it will return
    /// an error. If wanting to acquire a frame that is already in use, use
    /// [`Frame::from_in_use`] instead.
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariant**: Metaslot region invariants must hold.
    /// ## Postconditions
    /// - **Safety Invariant**: Metaslot region invariants hold after the call.
    /// - **Correctness**: If successful, the function returns a pointer to the metadata slot and a permission to the slot.
    /// - **Correctness**: If successful, the slot is initialized with the given metadata.
    /// - **Correctness**: If `paddr` does not have a corresponding metadata slot, the function returns an error.
    /// - **Drop Bookkeeping**: If successful, the function returns a live frame, which is tracked correctly as needing to be dropped.
    /// ## Safety
    /// - This function returns an error if `paddr` does not correspond to a valid slot or the slot is in use.
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(repr_perm): Tracked<&mut M::ReprPerm>
        requires
            old(regions).inv(),
        ensures
            final(regions).inv(),
            r matches Ok(res) ==> {
                &&& MetaSlot::get_from_unused_region_spec(paddr, false, *old(regions), *final(regions))
                &&& res.inv()
                &&& res.start_paddr_spec() == paddr
                &&& res.wf_with_region(*final(regions))
            },
            r is Err ==> *final(regions) == *old(regions)
    )]
    pub fn from_unused(paddr: Paddr, metadata: M) -> Result<Self, GetFrameError> {
        #[verus_spec(with
            Tracked(regions),
            Tracked(repr_perm) => Tracked(permissions)
        )]
        let from_unused = MetaSlot::get_from_unused(paddr, metadata, false);
        if let Err(err) = from_unused {
            Err(err)
        } else {
            proof_decl! {
                let tracked slot_perm = regions.tracked_borrow_slot(paddr);
                let ghost idx = frame_to_index(paddr);
                assert(regions.slot_owners.contains_key(idx));
                let tracked metadata_perm = permissions.tracked_unwrap().tracked_take_left();
            }
            let ptr = from_unused.unwrap();
            Ok(
                Self {
                    ptr,
                    _marker: PhantomData,
                    #[cfg(verus_keep_ghost_body)]
                    tracked_slot_perm: Tracked(slot_perm),
                    #[cfg(verus_keep_ghost_body)]
                    tracked_metadata_perm: Tracked(Some(metadata_perm)),
                },
            )
        }
    }

    /// Gets the metadata of this page.
    /// # Verified Properties
    /// ## Preconditions
    /// - The caller must have a valid permission for the frame.
    /// ## Postconditions
    /// - The function returns the borrowed metadata of the frame.
    /// ## Safety
    /// - By requiring the caller to provide a typed permission, we ensure that the metadata is of type `M`.
    /// While a non-verified caller cannot be trusted to obey this interface, all functions that return a `Frame<M>` also
    /// return an appropriate permission.
    #[verus_spec(ret =>
        with
            Tracked(metadata_perm): Tracked<Option<&'a MetadataPerm>>,
            Tracked(repr_perm): Tracked<&'a M::ReprPerm>,
        requires
            self.ptr_inv(),
            {
                self.inv() && metadata_perm is None
                && typed_meta_wf::<M>(self.slot_perm(), self.metadata_perm(), *repr_perm) ||
                metadata_perm is Some
                && self.external_meta_wf(*metadata_perm->0, *repr_perm)
            },
        ensures
            {
                let metadata_perm = if metadata_perm is Some {*metadata_perm -> 0} else
                    { self.metadata_perm() };
                ret == typed_meta_value::<M>(metadata_perm, *repr_perm)
            },
    )]
    pub fn meta<'a>(&'a self) -> &'a M {
        // SAFETY: The type is tracked by the typed storage permission.
        //  unsafe { &*self.slot().as_meta_ptr::<M>() }
        proof_decl! {
            let tracked slot_perm = self.tracked_slot_perm.borrow();
            let tracked metadata_perm = if metadata_perm is Some {
                metadata_perm.tracked_borrow()
            } else {
                self.tracked_metadata_perm.tracked_borrow().tracked_borrow()
            };
        }
        borrow_meta(
            ReprPtr::<MetaSlotStorage, M>::from_pptr(PPtr::from_addr(self.ptr.addr())),
            Tracked(slot_perm),
            Tracked(metadata_perm),
            Tracked(repr_perm),
        )
    }
}

#[verus_verify]
impl<M: AnyFrameMeta + Repr<MetaSlotStorage>> Frame<M> {
    /// Gets a dynamically typed [`Frame`] from a raw, in-use page.
    ///
    /// If the provided frame is not in use at the moment, it will return an error.
    ///
    /// The returned frame will have an extra reference count to the frame.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariant**: Metaslot region invariants must hold.
    /// - *Termination*: The function may panic if `paddr` is a valid slot and its reference count is saturated.
    /// ## Postconditions
    /// - **Safety Invariant**: Metaslot region invariants hold after the call.
    /// - **Correctness**: If successful, the function returns the frame at `paddr`.
    /// - **Correctness**: If successful, the frame has an extra reference count.
    /// - **Correctness**: If `paddr` does not have a valid metadata slot, the function returns an error.
    /// - **Safety**: Frames other than the one at `paddr` are not affected by the call.
    /// ## Safety
    /// - If `paddr` is a valid frame address, it is safe to take a reference to the frame.
    /// - If `paddr` is not a valid frame address, the function will return an error.
    #[verus_spec(res =>
        with Tracked(regions) : Tracked<&mut MetaRegionOwners>,
        requires
            old(regions).inv(),
            valid_frame_paddr(paddr) ==> old(regions).ref_count(frame_to_index(paddr)) >= REF_COUNT_MAX ==> may_panic(),
        ensures
            final(regions).inv(),
            res matches Ok(res) ==> {
                &&& old(regions).inc_frame_reference_region_spec(paddr, *final(regions))
                &&& res.inv()
                &&& res.start_paddr_spec() == paddr
                &&& res.wf_with_region(*final(regions))
            },
            res is Err ==> *old(regions) == *final(regions),
    )]
    pub fn from_in_use(paddr: Paddr) -> Result<Self, GetFrameError> {
        proof_decl!{
            let tracked frame_permission: Option<FracMetadataPerm>;
        }
        let res = #[verus_spec(with Tracked(regions) => Tracked(frame_permission))]
        MetaSlot::get_from_in_use(paddr);
        match res {
            Ok(ptr) => {
                proof {
                    regions.lemma_contains_valid_frame_paddr(paddr);
                }
                let tracked slot_perm = regions.tracked_borrow_slot(paddr);
                Ok(
                    Self {
                        ptr,
                        _marker: PhantomData,
                        #[cfg(verus_keep_ghost_body)]
                        tracked_slot_perm: Tracked(slot_perm),
                        #[cfg(verus_keep_ghost_body)]
                        tracked_metadata_perm: Tracked(frame_permission),
                    },
                )
            },
            Err(e) => Err(e),
        }
    }
}

#[verus_verify]
impl<M: AnyFrameMeta + ?Sized> Frame<M> {
    /// Gets the physical address of the start of the frame.
    /// # Verified Properties
    /// ## Preconditions
    /// - **Bookkeeping**: takes the permission for the frame's metadata slot.
    /// ## Postconditions
    /// - **Correctness**: returns the physical address of the frame.
    /// ## Safety
    /// The caller cannot obtain a frame that doesn't have a valid permission,
    /// and this function does not mutate any state, so it is always sound to call.
    #[verus_spec(
    requires
        self.ptr_inv(),
    returns
        self.start_paddr_spec(),
    )]
    pub fn start_paddr(&self) -> Paddr {
        let slot = self.slot();

        #[verus_spec(with self.tracked_slot_perm)]
        slot.frame_paddr()
    }

    /// Gets the map level of this page.
    ///
    /// This is the level of the page table entry that maps the frame,
    /// which determines the size of the frame.
    ///
    /// Currently, the level is always 1, which means the frame is a regular
    /// page frame.
    pub const fn map_level(&self) -> PagingLevel
        returns
            1u8,
    {
        1
    }

    /// Gets the size of this page in bytes.
    pub const fn size(&self) -> usize
        returns
            PAGE_SIZE,
    {
        PAGE_SIZE
    }

    /// Gets the reference count of the frame.
    ///
    /// It returns the number of all references to the frame, including all the
    /// existing frame handles ([`Frame`], [`Frame<dyn AnyFrameMeta>`]), and all
    /// the mappings in the page table that points to the frame.
    ///
    /// ## Safety
    ///
    /// The function is safe to call, but using it requires extra care. The
    /// reference count can be changed by other threads at any time including
    /// potentially between calling this method and acting on the result.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariant**: Metaslot region invariants must hold.
    /// - **Bookkeeping**: The caller must have a valid and well-typed permission for the frame.
    /// ## Postconditions
    /// - **Correctness**: The function returns the reference count of the frame.
    #[verus_spec(
        with
            Tracked(slot_own): Tracked<&MetaSlotOwner>,
        requires
            self.ptr_inv(),
            self.tracked_slot_perm@.value().wf(*slot_own),
        returns
            slot_own.ref_count(),
    )]
    pub fn reference_count(&self) -> u64 {
        let refcnt = self.slot().ref_count.load(Tracked(&slot_own.ref_count_perm));
        refcnt
    }

    /// Borrows a reference from the given frame.
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariant**: Metaslot region invariants must hold.
    /// ## Postconditions
    /// - **Safety Invariant**: Metaslot region invariants hold after the call.
    /// - **Correctness**: The function returns a reference to the frame.
    /// - **Correctness**: The system context is unchanged.
    #[verus_spec(res =>
        requires
            self.inv(),
        ensures
            res.inner@.ptr.addr() == self.ptr.addr(),
    )]
    pub fn borrow<'a>(&self) -> FrameRef<'a, M> {
        let tracked slot_perm = *self.tracked_slot_perm.borrow();
        let tracked metadata_perm = self.tracked_metadata_perm.borrow().tracked_borrow();
        // SAFETY: Both the lifetime and the type matches `self`.
        unsafe {
            #[verus_spec(with Tracked(slot_perm), Tracked(metadata_perm))]
            FrameRef::borrow_paddr(self.start_paddr())
        }
    }

    /// Borrows a frame whose owning handle is represented by an external
    /// counting permission, as is the case for page-table nodes stored raw in
    /// PTEs.
    #[verus_spec(res =>
        with
            Tracked(frame_permission): Tracked<&FracMetadataPerm>,
            Tracked(regions): Tracked<&MetaRegionOwners>,
        requires
            self.ptr_inv(),
            regions.inv(),
            frame_permission.frac() == 1,
            frame_permission.id() == regions.slot_owners[self.index()].metadata_perm.id(),
            MetaSlot::perms_related(
                *regions.slots[self.index()],
                frame_permission.resource(),
            ),
        ensures
            res.inner@.ptr.addr() == self.ptr.addr(),
            res.inner@.ptr_inv(),
            res.inner@.tracked_slot_perm@ == regions.slots[self.index()],
            res.inner@.tracked_metadata_perm@ is None,
            MetaSlot::perms_related(res.inner@.slot_perm(), frame_permission.resource()),
    )]
    pub(in crate::mm) fn borrow_with_permission<'a>(&self) -> FrameRef<'a, M> {
        unsafe {
            proof {
                broadcast use group_page_meta;

                regions.lemma_contains_valid_frame_paddr(self.start_paddr_spec());
            }
            let tracked slot_perm = regions.tracked_borrow_slot(self.start_paddr_spec());
            #[verus_spec(with Tracked(slot_perm), Tracked(frame_permission))]
            FrameRef::borrow_paddr(self.start_paddr())
        }
    }

    /// Forgets the handle to the frame.
    ///
    /// This will result in the frame being leaked without calling the custom dropper.
    ///
    /// A physical address to the frame is returned in case the frame needs to be
    /// restored using [`Frame::from_raw`] later. This is useful when some architectural
    /// data structures need to hold the frame handle such as the page table.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety**: The frame's invariant must be satisfied.
    /// ## Postconditions
    /// - **Correctness**: The function returns the physical address of the frame.
    /// ## Safety
    /// - We require the slot to be in use to ensure that a fresh frame handle will not be created until the raw frame is restored.
    /// - The owner's raw count is incremented so that we can enforce the safety requirement on `Frame::from_raw`.
    #[verus_spec(r =>
        with
            -> raw_permission: Tracked<FrameRawPerms>,
        requires
            self.inv(),
        ensures
            r == self.start_paddr_spec(),
            raw_permission@.inv(),
    )]
    pub(in crate::mm) fn into_raw(self) -> Paddr {
        broadcast use group_page_meta;

        let mut this = self;
        proof_decl!{
            let tracked perm = FrameRawPerms {
                slot_perm: &*this.tracked_slot_perm,
                metadata_perm: this.tracked_metadata_perm.tracked_take(),
            };
        }

        let this = ManuallyDrop::new(this);
        proof_with!(|= Tracked(perm));
        this.start_paddr()
    }
}

#[verus_verify]
impl<M: ?Sized> Frame<M> {
    /// Gets the metadata slot of the frame.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety**: The caller must have a valid permission for the frame.
    /// ## Postconditions
    /// - **Correctness**: The function returns a reference to the metadata slot of the frame.
    /// ## Safety
    /// - There is no way to mutably borrow the metadata slot, so taking an immutable reference is safe.
    /// (The fields of the slot can be mutably borrowed, but not the slot itself.)
    #[verus_spec(
        requires
            self.ptr_inv(),
        returns
            self.tracked_slot_perm@.value(),
    )]
    pub fn slot<'a>(&'a self) -> &'a MetaSlot {
        // SAFETY: `ptr` points to a valid `MetaSlot` that will never be
        // mutably borrowed, so taking an immutable reference to it is safe.
        proof_decl! {
            let tracked slot_perm = *self.tracked_slot_perm;
        }
        self.ptr.borrow(Tracked(slot_perm))
    }
}

#[verus_verify]
impl<M: AnyFrameMeta + ?Sized> Frame<M> {
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
    #[verus_spec(r =>
        with
            Tracked(perm): Tracked<FrameRawPerms>,
        requires
            valid_frame_paddr(paddr),
            perm.slot_vaddr() == frame_to_meta(paddr),
            perm.inv(),
        ensures
            r.tracked_slot_perm@ == perm.slot_perm,
            r.tracked_metadata_perm@ == Some(perm.metadata_perm),
            r.start_paddr_spec() == paddr,
            r.inv(),
    )]
    pub(in crate::mm) unsafe fn from_raw(paddr: Paddr) -> Self
        no_unwind
    {
        // debug_assert!(paddr < max_paddr());
        let vaddr = frame_to_meta(paddr);
        // let ptr = vaddr as *const MetaSlot;
        let ptr = PPtr(vaddr, PhantomData);

        proof_with!{ tracked_slot_perm: Tracked(perm.slot_perm), tracked_metadata_perm: Tracked(Some(perm.metadata_perm)) }
        Self { ptr, _marker: PhantomData }
    }
}

#[verus_verify]
impl<M: AnyFrameMeta + ?Sized> RCClone for Frame<M> {
    open spec fn clone_requires(self, regions: MetaRegionOwners) -> bool {
        let paddr = self.start_paddr_spec();
        let ref_count = regions.slot_owner(paddr).ref_count();
        &&& self.inv()
        &&& regions.inv()
        &&& self.wf_with_region(regions)
        &&& ref_count > 0
        &&& ref_count != REF_COUNT_UNUSED
        &&& ref_count >= REF_COUNT_MAX ==> may_panic()
    }

    open spec fn clone_ensures(
        self,
        pre: MetaRegionOwners,
        post: MetaRegionOwners,
        res: Self,
    ) -> bool {
        let idx = self.index();
        &&& pre.inc_frame_reference_region_spec(self.start_paddr_spec(), post)
        &&& post.inv()
        &&& res.tracked_metadata_perm@ is Some
        &&& res.tracked_metadata_perm@->0.frac() == 1
        &&& res.tracked_metadata_perm@->0.id() == post.slot_owners[idx].metadata_perm.id()
        &&& res.tracked_slot_perm@ == post.slots[idx]
        &&& res.ptr == self.ptr
    }

    fn clone(&self, Tracked(regions): Tracked<&mut MetaRegionOwners>) -> Self {
        proof_decl! {
            regions.lemma_contains_valid_frame_paddr(self.start_paddr_spec());
            let ghost paddr = self.start_paddr_spec();
            let tracked slot_perm = regions.tracked_borrow_slot(paddr);
            let tracked slot_own = regions.tracked_borrow_mut_slot_owner(paddr);
        }

        // SAFETY: We have already held a reference to the frame.
        unsafe {
            #[verus_spec(with Tracked(&mut slot_own.ref_count_perm))]
            self.slot().inc_ref_count();
        }

        proof_decl!{
            let tracked metadata_perm = slot_own.metadata_perm.split_one();
        };

        Self {
            ptr: PPtr::<MetaSlot>::from_addr(self.ptr.0),
            _marker: PhantomData,
            #[cfg(verus_keep_ghost_body)]
            tracked_slot_perm: Tracked(slot_perm),
            #[cfg(verus_keep_ghost_body)]
            tracked_metadata_perm: Tracked(Some(metadata_perm)),
        }
    }
}

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
}*/

impl<M: ?Sized> Frame<M> {
    pub fn drop(self, Tracked(regions): Tracked<&mut MetaRegionOwners>)
        requires
            self.drop_requires(*old(regions)),
        ensures
            self.drop_ensures(*old(regions), *final(regions)),
    {
        let mut this = self;
        proof_decl!{
            let ghost idx = this.index();
            let tracked slot_own = regions.tracked_borrow_mut_slot_owner(self.start_paddr_spec());
            let tracked frame_permission = this.tracked_metadata_perm.tracked_take();
            slot_own.metadata_perm.combine(frame_permission);
        }

        let last_ref_cnt = this.slot().ref_count.fetch_sub(
            Tracked(&mut slot_own.ref_count_perm),
            1,
        );

        if last_ref_cnt == 1 {
            // A fence is needed here with the same reasons stated in the implementation of
            // `Arc::drop`: <https://doc.rust-lang.org/std/sync/struct.Arc.html#method.drop>.
            acquire_fence();
            // SAFETY: this is the last reference and is about to be dropped.
            unsafe {
                #[verus_spec(with Tracked(slot_own))]
                this.slot().drop_last_in_place()
            };

            // TODO: return page to allocator
            // allocator::get_global_frame_allocator().dealloc(paddr, PAGE_SIZE);
        }
        proof {
            assert_maps_equal!(
                regions.slot_owners,
                old(regions).slot_owners.insert(idx, regions.slot_owners[idx]),
                i => {
                    if i != idx {
                        assert(regions.slot_owners[i] == old(regions).slot_owners[i]);
                    }
                }
            );
        }
    }
}

verus! {

#[cfg(feature = "type_id")]
impl<M: ?Sized> Frame<M> {
    /// The identity of the metadata this frame's slot holds.
    ///
    /// Reads the id recorded in the metadata permission by
    /// [`MetaSlot::write_meta`]. Defined for every `M`, not just the erased
    /// form: a `Frame<MetaSlotStorage>` is already an erased handle whose slot
    /// was written at some concrete type, so the recorded id is that concrete
    /// type's -- not `type_id::<M>()`. Which is why [`Frame::into_dyn`]
    /// *preserves* this rather than claiming it equals `type_id::<M>()`.
    pub open spec fn meta_type_id(&self) -> MetaTypeId {
        self.metadata_perm().meta_type_id
    }
}

#[cfg(feature = "type_id")]
/// Identity of an erased frame's metadata.
///
/// A separate impl block because the surrounding one is bounded by
/// `Repr<MetaSlotStorage>`, which `dyn AnyFrameMeta` does not satisfy -- and it is
/// exactly the erased case these two are for.
impl Frame<dyn AnyFrameMeta> {
    /// Gets the dynamically-typed metadata of this frame.
    ///
    /// If the type is known at compile time, use [`Frame::meta`] instead.
    ///
    /// `external_body` until we handle the vtable pointer again.
    #[verifier::external_body]
    pub fn dyn_meta(&self) -> (r: &dyn AnyFrameMeta)
        ensures
            r.meta_id() == self.meta_type_id(),
    {
        unimplemented!()
    }
}

/// Reparameterizing a frame handle's metadata type is always a valid transmute.
///
/// The layout claim is about the *compiled* struct. `Frame<M>` is a
/// `PPtr<MetaSlot>` beside a `PhantomData<M>` and two `Tracked` fields, and
/// ghost and tracked fields are erased at compile time -- so what actually
/// exists at runtime is one pointer, identically for every `M`. `PhantomData`
/// and `Tracked` are zero-sized at every parameter, including unsized ones,
/// because the `dyn` never reaches the pointer.
///
/// This is deliberately *opinionated*: `Frame` cannot carry
/// `#[repr(transparent)]`, because rustc refuses to count `Ghost`/`Tracked`
/// fields as trivially zero-sized -- they have private fields, so it will not
/// promise they stay that way. That is an attribute-level refusal, not a layout
/// fact, and the layout fact is what this axiom asserts. If `Frame` ever gains a
/// second *exec* field, this becomes false.
///
/// The tracked fields carry across unchanged, which is well-typed precisely
/// because neither `FracMetadataPerm` nor `PointsTo<MetaSlot>` mentions `M`.
///
/// Representation only. That the slot really holds a `B` is an identity claim,
/// which this does not make -- the `is_::<M>` guard in [`TryFrom`] establishes
/// that separately.
/// TODO: update `tracked_metadata_perm` to reflect the new value.
#[verifier::external_body]
pub proof fn axiom_frame_reparam<A: ?Sized, B: ?Sized>(f: Frame<A>)
    ensures
        can_transmute::<Frame<A>, Frame<B>>(f),
        transmuted::<Frame<A>, Frame<B>>(f) == (Frame::<B> {
            ptr: f.ptr,
            _marker: PhantomData,
            #[cfg(verus_keep_ghost_body)]
            tracked_slot_perm: f.tracked_slot_perm,
            #[cfg(verus_keep_ghost_body)]
            tracked_metadata_perm: f.tracked_metadata_perm,
        }),
{
}

/// The transmute half of the downcast.
pub fn transmute_frame_to_typed<M: AnyFrameMeta>(dyn_frame: Frame<dyn AnyFrameMeta>)
-> (r: Frame<M>)
    ensures
        r.ptr == dyn_frame.ptr,
        r.tracked_slot_perm == dyn_frame.tracked_slot_perm,
        r.tracked_metadata_perm == dyn_frame.tracked_metadata_perm,
{
    proof {
        axiom_frame_reparam::<dyn AnyFrameMeta, M>(dyn_frame);
    }
    // SAFETY: The metadata is coerceable and the struct is transmutable.
    unsafe { core::mem::transmute::<Frame<dyn AnyFrameMeta>, Frame<M>>(dyn_frame) }
}

#[cfg(feature = "type_id")]
impl<M: AnyFrameMeta> TryFromSpecImpl<Frame<dyn AnyFrameMeta>> for Frame<M> {
    open spec fn obeys_try_from_spec() -> bool {
        true
    }

    open spec fn try_from_spec(v: Frame<dyn AnyFrameMeta>) -> Result<Self, Self::Error> {
        if v.meta_type_id() == type_id::<M>() {
            Ok(
                Frame {
                    ptr: v.ptr,
                    _marker: PhantomData,
                    #[cfg(verus_keep_ghost_body)]
                    tracked_slot_perm: v.tracked_slot_perm,
                    #[cfg(verus_keep_ghost_body)]
                    tracked_metadata_perm: v.tracked_metadata_perm,
                },
            )
        } else {
            Err(v)
        }
    }
}

#[cfg(feature = "type_id")]
impl<M: AnyFrameMeta> TryFrom<Frame<dyn AnyFrameMeta>> for Frame<M> {
    type Error = Frame<dyn AnyFrameMeta>;

    /// Tries converting a [`Frame<dyn AnyFrameMeta>`] into the statically-typed [`Frame`].
    ///
    /// If the usage of the frame is not the same as the expected usage, it will
    /// return the dynamic frame itself as is.
    ///
    /// Upstream tests with
    ///
    /// ```text
    /// if (dyn_frame.dyn_meta() as &dyn core::any::Any).is::<M>() {
    /// ```
    ///
    /// In our code the upcast is a method, [`AnyFrameMeta::to_any`]. Each impl
    /// performs the coercion `&Self -> &dyn Any`, which Verus does model.
    /// `is_` is then the same `is` upstream calls.
    ///
    /// For now, `transmute_frame_to_typed` stands in for an axiomatized `transmute`
    /// function. Axiomatizing `transmute` is a separate task.
    fn try_from(dyn_frame: Frame<dyn AnyFrameMeta>) -> (res: Result<Self, Self::Error>) {
        if is_::<M>(dyn_frame.dyn_meta().to_any()) {
            Ok(transmute_frame_to_typed::<M>(dyn_frame))
        } else {
            Err(dyn_frame)
        }
    }
}

}  // verus!
/*impl<M: AnyFrameMeta> From<UFrame> for Frame<M> {
    fn from(frame: UFrame) -> Self {
        // SAFETY: The metadata is coerceable and the struct is transmutable.
        unsafe { core::mem::transmute(frame) }
    }
}*/
/*impl TryFrom<Frame<FrameMeta>> for UFrame {
    type Error = Frame<FrameMeta>;
}*/


#[verifier::external]
impl<M: AnyUFrameMeta> From<Frame<M>> for UFrame {
    fn from(frame: Frame<M>) -> Self {
        // SAFETY: The metadata is coerceable and the struct is transmutable.
        unsafe { core::mem::transmute(frame) }
    }
}

verus! {

impl FromSpecImpl<UFrame> for Frame<dyn AnyFrameMeta> {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(v: UFrame) -> Self {
        Frame {
            ptr: v.ptr,
            _marker: PhantomData,
            #[cfg(verus_keep_ghost_body)]
            tracked_slot_perm: v.tracked_slot_perm,
            #[cfg(verus_keep_ghost_body)]
            tracked_metadata_perm: v.tracked_metadata_perm,
        }
    }
}

/// Widens an already-erased handle from `UFrame` to `Frame<dyn AnyFrameMeta>`.
///
/// This is the conversion upstream writes as `old_frame.into()`. It is *not*
/// [`Frame::into_dyn`]: a `UFrame` is `Frame<MetaSlotStorage>`, which is already
/// an erased stand-in, so there is no static type here to pin. The recorded
/// identity is preserved, not asserted -- the slot was written at whatever
/// concrete type it actually holds.
impl From<UFrame> for Frame<dyn AnyFrameMeta> {
    fn from(frame: UFrame) -> (r: Self) {
        proof {
            axiom_frame_reparam::<MetaSlotStorage, dyn AnyFrameMeta>(frame);
        }
        // SAFETY: The metadata is coerceable and the struct is transmutable.
        unsafe { core::mem::transmute::<UFrame, Frame<dyn AnyFrameMeta>>(frame) }
    }
}

} // verus!

/*

impl TryFrom<Frame<dyn AnyFrameMeta>> for UFrame {
    type Error = Frame<dyn AnyFrameMeta>;

    /// Tries converting a [`Frame<dyn AnyFrameMeta>`] into [`UFrame`].
    ///
    /// If the usage of the frame is not the same as the expected usage, it will
    /// return the dynamic frame itself as is.
    fn try_from(dyn_frame: Frame<dyn AnyFrameMeta>) -> Result<Self, Self::Error> {
        if dyn_frame.dyn_meta().is_untyped() {
            // SAFETY: The metadata is coerceable and the struct is transmutable.
            Ok(unsafe { core::mem::transmute::<Frame<dyn AnyFrameMeta>, UFrame>(dyn_frame) })
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
///
/// # Verified Properties
/// ## Preconditions
/// - **Safety Invariant**: Metaslot region invariants must hold.
/// - **Safety**: The physical address must represent a valid frame.
/// ## Postconditions
/// - **Safety Invariant**: Metaslot region invariants hold after the call.
/// - **Correctness**: The reference count of the frame is increased by one.
/// - **Safety**: Frames other than this one are not affected by the call.
#[verus_spec(permission =>
    with
        Tracked(regions): Tracked<&mut MetaRegionOwners>,
    requires
        old(regions).inv(),
        old(regions).contains(frame_to_index(paddr)),
        valid_frame_paddr(paddr),
        old(regions).slot_owner(paddr).ref_count() > 0,
        old(regions).slot_owner(paddr).ref_count()
            != REF_COUNT_UNUSED,
        old(regions).slot_owner(paddr).ref_count()
            >= REF_COUNT_MAX ==> may_panic(),
    ensures
        final(regions).inv(),
        permission@.frac() == 1,
        permission@.id() == final(regions).slot_owner(paddr).metadata_perm.id(),
        permission@.resource() == old(regions).slot_owner(paddr).metadata_perm@,
        old(regions).inc_frame_reference_region_spec(paddr, *final(regions)),
)]
pub(in crate::mm) unsafe fn inc_frame_ref_count(paddr: Paddr) -> (permission: Tracked<
    FracMetadataPerm,
>) {
    let tracked perm = regions.tracked_borrow_slot(paddr);
    let tracked slot_own = regions.tracked_borrow_mut_slot_owner(paddr);

    let vaddr: Vaddr = frame_to_meta(paddr);
    // SAFETY: `vaddr` points to a valid `MetaSlot` that will never be mutably borrowed, so taking
    // an immutable reference to it is always safe.
    let slot = PPtr::<MetaSlot>(vaddr, PhantomData);

    unsafe {
        #[verus_spec(with Tracked(&mut slot_own.ref_count_perm))]
        slot.borrow(Tracked(perm)).inc_ref_count()
    };
    let tracked frame_permission = slot_own.metadata_perm.split_one();

    Tracked(frame_permission)
}

/// A dynamically-typed frame is represented by a frame of the underlying metadata type,
/// which can be cast from any other type.
pub type DynFrame = Frame<MetaSlotStorage>;

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + 'static> Frame<M> {
    /// Erases the static metadata type, yielding a `Frame<dyn AnyFrameMeta>`.
    ///
    /// Inherent method rather than `From`/`Into` to avoid trait-inference
    /// ambiguity at call sites that previously relied on the blanket
    /// `From<T> for T` (e.g. `frame.into()` for `Frame<UFrame>`).
    ///
    ///
    /// Two versions, differing only in strength. `type_id` adds the clause that
    /// pins the erased frame's identity, which is what makes the downcast in
    /// [`TryFrom`] able to conclude anything; without the feature the frame still
    /// erases, it just carries no recoverable identity. The runtime behaviour is
    /// identical -- one `transmute` either way.
    #[cfg(feature = "type_id")]
    pub fn into_dyn(self) -> (r: Frame<dyn AnyFrameMeta>)
        ensures
            r.ptr == self.ptr,
            r.meta_type_id() == self.meta_type_id(),
    {
        proof {
            axiom_frame_reparam::<M, dyn AnyFrameMeta>(self);
        }
        // SAFETY: see [`axiom_frame_reparam`] -- one pointer either way, once
        // the ghost and tracked fields are erased.
        // The permission fraction rides across unchanged (see the axiom), and it
        // is what carries the recorded identity -- so the clause below is proved.
        unsafe { core::mem::transmute::<Frame<M>, Frame<dyn AnyFrameMeta>>(self) }
    }

    #[cfg(not(feature = "type_id"))]
    pub fn into_dyn(self) -> (r: Frame<dyn AnyFrameMeta>)
        ensures
            r.ptr == self.ptr,
    {
        proof {
            axiom_frame_reparam::<M, dyn AnyFrameMeta>(self);
        }
        // SAFETY: as above.
        unsafe { core::mem::transmute::<Frame<M>, Frame<dyn AnyFrameMeta>>(self) }
    }
}

} // verus!
