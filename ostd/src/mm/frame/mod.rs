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
use vstd::atomic::PermissionU64;
use vstd::prelude::*;
use vstd::simple_pptr::{self, PPtr};
use vstd_extra::cast_ptr::*;
use vstd_extra::drop_tracking::*;
use vstd_extra::ownership::*;
use vstd_extra::panic::may_panic;

pub mod allocator;
pub mod linked_list;
pub mod meta;
pub mod segment;
pub mod unique;
pub mod untyped;

mod frame_ref;
pub mod obligation_demo;
pub use frame_ref::FrameRef;

#[cfg(ktest)]
mod test;

use core::{
    marker::PhantomData,
    sync::atomic::{AtomicUsize, Ordering},
};

//pub use allocator::GlobalFrameAllocator;
use meta::{REF_COUNT_MAX, REF_COUNT_UNIQUE, REF_COUNT_UNUSED, mapping};
pub use segment::Segment;
pub use untyped::{AnyUFrameMeta, UFrame};

use super::PagingLevel;

// Re-export commonly used types
use crate::mm::kspace::FRAME_METADATA_RANGE;
pub use linked_list::{CursorMut, Link, LinkedList};
pub use meta::{AnyFrameMeta, GetFrameError, MetaSlot};
pub use unique::UniqueFrame;

use crate::mm::page_table::{PageTableConfig, PageTablePageMeta};

use crate::mm::page_table::RCClone;
use crate::mm::{
    MAX_PADDR, Paddr, Vaddr,
    frame::meta::{
        META_SLOT_SIZE,
        mapping::{frame_to_meta, meta_to_frame},
    },
    kspace::{LINEAR_MAPPING_BASE_VADDR, VMALLOC_BASE_VADDR},
};
use crate::specs::arch::*;
use crate::specs::mm::frame::meta_owners::*;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::frame::{
    frame_specs::*,
    mapping::{frame_to_index, group_page_meta, max_meta_slots, meta_addr},
};

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
/// # Verification Design
#[repr(transparent)]
pub struct Frame<M: ?Sized> {
    pub ptr: PPtr<MetaSlot>,
    pub _marker: PhantomData<M>,
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

impl<M: AnyFrameMeta + ?Sized> PartialEq for Frame<M> {
    fn eq(&self, other: &Self) -> bool {
        self.start_paddr() == other.start_paddr()
    }
}

impl<M: AnyFrameMeta + ?Sized> Eq for Frame<M> {}
*/

#[verus_verify]
impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + ?Sized> Frame<M> {
    /// Compares two frames by their start physical address.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariant**: the frames and metadata regions must satisfy the global invariants.
    /// ## Postconditions
    /// - **Correctness**: the function returns true if the frames have
    /// the same physical addresses and false otherwise.
    /// ## Safety
    /// Everything is immutable, so the safety invariant is preserved implicitly.
    /// ## Verification Design
    /// This is an inherent impl equivalent to `PartialEq::eq` for `Frame<M>`: freed from the
    /// trait signature so that this version can thread the tracked `MetaRegionOwners` via `verus_spec`.
    #[verus_spec(res =>
        with
            Tracked(regions): Tracked<&MetaRegionOwners>,
        requires
            self.inv(),
            other.inv(),
            regions.inv(),
        ensures
            res == (meta_to_frame(self.ptr.addr()) == meta_to_frame(other.ptr.addr())),
    )]
    pub fn eq(&self, other: &Self) -> bool {
        proof {
            regions.inv_implies_correct_addr(self.paddr());
            regions.inv_implies_correct_addr(other.paddr());
        }
        let tracked self_perm = regions.slots.tracked_borrow(self.index());
        let tracked other_perm = regions.slots.tracked_borrow(other.index());

        (#[verus_spec(with Tracked(self_perm))]
        self.start_paddr() == #[verus_spec(with Tracked(other_perm))]
        other.start_paddr())
    }
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
            Tracked(regions): Tracked<&mut MetaRegionOwners>
        requires
            old(regions).inv(),
        ensures
            final(regions).inv(),
            r matches Ok(res) ==> {
                &&& res.ptr.addr() == frame_to_meta(paddr)
                &&& MetaSlot::get_from_unused_spec(paddr, false, *old(regions), *final(regions))
                &&& MetaSlot::slot_perm_reparked_spec(paddr, *old(regions), *final(regions))
                &&& MetaSlot::live_frame_obligations_ok_spec(paddr, *old(regions), *final(regions))
            },
            !has_safe_slot(paddr) ==> r is Err,
            r is Err ==> *final(regions) == *old(regions)
    )]
    pub fn from_unused(paddr: Paddr, metadata: M) -> Result<Self, GetFrameError> {
        #[verus_spec(with Tracked(regions))]
        let from_unused = MetaSlot::get_from_unused(paddr, metadata, false);
        if let Err(err) = from_unused {
            Err(err)
        } else {
            let (ptr, Tracked(perm)) = from_unused.unwrap();
            proof {
                let ghost idx = frame_to_index(paddr);
                assert(frame_to_index(paddr) < max_meta_slots());
                assert(regions.slot_owners.contains_key(idx));
                regions.sync_slot_perm(idx, &perm);
                // Mint the pending-Drop obligation for the new live value.
                let tracked _ = regions.tracked_mint_frame_obligation(idx);
            }
            Ok(Self { ptr, _marker: PhantomData })
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
    #[verus_spec(
        with
            Tracked(perm) : Tracked<&'a PointsTo<MetaSlot, Metadata<M>>>,
        requires
            self.ptr == perm.points_to.pptr(),
            perm.is_init(),
            perm.wf(&perm.inner_perms),
        returns
            perm.value().metadata,
    )]
    pub fn meta<'a>(&'a self) -> &'a M {
        // SAFETY: The type is tracked by the type system.
        // unsafe { &*self.slot().as_meta_ptr::<M>() }
        #[verus_spec(with Tracked(&perm.points_to))]
        let slot = self.slot();

        #[verus_spec(with Tracked(&perm.points_to))]
        let ptr = slot.as_meta_ptr();

        &ptr.borrow(Tracked(perm)).metadata
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
            has_safe_slot(paddr) ==> old(regions).ref_count(frame_to_index(paddr)) >= REF_COUNT_MAX ==> may_panic(),
        ensures
            final(regions).inv(),
            res matches Ok(res) ==> {
                &&& final(regions).ref_count(frame_to_index(paddr)) ==
                    old(regions).ref_count(frame_to_index(paddr)) + 1
                &&& res.ptr == old(regions).slots[frame_to_index(paddr)].pptr()
                &&& MetaSlot::live_frame_obligations_ok_spec(paddr, *old(regions), *final(regions))
            },
            !has_safe_slot(paddr) ==> res is Err,
            old(regions).slot_owners_agree_except(*final(regions), frame_to_index(paddr)),
            res is Err ==> *old(regions) == *final(regions),
    )]
    pub fn from_in_use(paddr: Paddr) -> Result<Self, GetFrameError> {
        let res = #[verus_spec(with Tracked(regions))]
        MetaSlot::get_from_in_use(paddr);
        match res {
            Ok(ptr) => {
                proof {
                    // Mint the pending-Drop obligation for the new live value.
                    let tracked _ = regions.tracked_mint_frame_obligation(frame_to_index(paddr));
                }
                Ok(Self { ptr, _marker: PhantomData })
            },
            Err(e) => Err(e),
        }
    }
}

#[verus_verify]
impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + ?Sized> Frame<M> {
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
        with Tracked(perm): Tracked<&vstd::simple_pptr::PointsTo<MetaSlot>>,
    requires
        perm.addr() == self.ptr.addr(),
        perm.is_init(),
        self.inv(),
    returns
        meta_to_frame(self.ptr.addr()),
    )]
    pub fn start_paddr(&self) -> Paddr {
        #[verus_spec(with Tracked(perm))]
        let slot = self.slot();

        #[verus_spec(with Tracked(perm))]
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

    /*    /// Gets the dynamically-typed metadata of this frame.
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
            Tracked(perm) : Tracked<&PointsTo<MetaSlot, Metadata<M>>>,
        requires
            perm.points_to.pptr() == self.ptr,
            perm.is_init(),
            perm.wf(&perm.inner_perms),
            perm.inner_perms.ref_count.id() == perm.points_to.value().ref_count.id(),
        returns
            perm.value().ref_count,
    )]
    pub fn reference_count(&self) -> u64 {
        let refcnt = (#[verus_spec(with Tracked(&perm.points_to))]
        self.slot()).ref_count.load(Tracked(&perm.inner_perms.ref_count));
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
    // FIXME: the lifetime is suspicious
    #[verus_spec(res =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
        requires
            self.wf_with_region(*old(regions)),
        ensures
            final(regions).inv(),
            res.inner@.ptr.addr() == self.ptr.addr(),
            *final(regions) == *old(regions),
    )]
    pub fn borrow<'a>(&self) -> FrameRef<'a, M> {
        proof {
            regions.inv_implies_correct_addr(self.paddr());
        }
        let tracked slot_perm = regions.slots.tracked_borrow(self.index());

        // SAFETY: Both the lifetime and the type matches `self`.
        unsafe {
            #[verus_spec(with Tracked(regions))]
            FrameRef::borrow_paddr(
                #[verus_spec(with Tracked(slot_perm))]
                self.start_paddr(),
            )
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
    /// - **Safety Invariant**: Metaslot region invariants must hold.
    /// - **Safety**: The frame must be in use (not unused).
    /// ## Postconditions
    /// - **Safety Invariant**: Metaslot region invariants hold after the call.
    /// - **Correctness**: The function returns the physical address of the frame.
    /// - **Correctness**: The frame's raw count is incremented.
    /// - **Safety**: Frames other than this one are not affected by the call.
    /// ## Safety
    /// - We require the slot to be in use to ensure that a fresh frame handle will not be created until the raw frame is restored.
    /// - The owner's raw count is incremented so that we can enforce the safety requirement on `Frame::from_raw`.
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
        requires
            self.inv(),
            old(regions).inv(),
            old(regions).slot_owners[self.index()].inner_perms.ref_count.value() != REF_COUNT_UNUSED,
            old(regions).slot_owners[self.index()].usage !is PageTable,
            old(regions).frame_obligations.count(self.index()) > 0,
        ensures
            final(regions).inv(),
            r == self.paddr(),
            final(regions).slot_owners[self.index()].usage
                == old(regions).slot_owners[self.index()].usage,
            self.into_raw_post_noninterference(*old(regions), *final(regions)),
            final(regions).slots == old(regions).slots,
            final(regions).frame_obligations == old(regions).frame_obligations.remove(self.index()),
    )]
    pub(in crate::mm) fn into_raw(self) -> Paddr {
        broadcast use group_page_meta;

        proof {
            regions.inv_implies_correct_addr(self.paddr());
        }

        let tracked perm = regions.slots.tracked_borrow(self.index());

        #[verus_spec(with Tracked(perm))]
        let paddr = self.start_paddr();

        let _ = ManuallyDrop::new(self, Tracked(regions));

        paddr
    }

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
    #[verus_spec(slot =>
        with
            Tracked(slot_perm): Tracked<&'a vstd::simple_pptr::PointsTo<MetaSlot>>,
        requires
            slot_perm.pptr() == self.ptr,
            slot_perm.is_init(),
        returns
            slot_perm.value(),
    )]
    pub fn slot<'a>(&'a self) -> &'a MetaSlot {
        // SAFETY: `ptr` points to a valid `MetaSlot` that will never be
        // mutably borrowed, so taking an immutable reference to it is safe.
        self.ptr.borrow(Tracked(slot_perm))
    }
}

#[verus_verify]
impl<M> Frame<M> {
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
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            -> obl: Tracked<vstd_extra::drop_tracking::DropObligation<usize>>,
        requires
            Self::from_raw_requires_safety(*old(regions), paddr),
            old(regions).slots.contains_key(frame_to_index(paddr)),
            // Borrow-protocol safety: the slot must be alive (not torn
            // down). The `unsafe` keyword still gates whether the produced
            // Frame corresponds to a real prior `into_raw`; this condition
            // only ensures the slot isn't a dead/unused one.
            old(regions).slot_owners[frame_to_index(paddr)].inner_perms.ref_count.value()
                != REF_COUNT_UNUSED,
        ensures
            Self::from_raw_ensures(*old(regions), *final(regions), paddr, r),
            final(regions).slots == old(regions).slots,
            obl@.value() == frame_to_index(paddr),
    )]
    pub(in crate::mm) unsafe fn from_raw(paddr: Paddr) -> Self
        no_unwind
    {
        let vaddr = frame_to_meta(paddr);
        let ptr = PPtr(vaddr, PhantomData);

        let ghost idx = frame_to_index(paddr);

        proof_decl! {
            let tracked obl_minted: vstd_extra::drop_tracking::DropObligation<usize>;
        }
        proof {
            // Mint the obligation that will be consumed by either
            // `ManuallyDrop::new` (FrameRef-style borrow) or
            // `Frame::drop` (reclaim-and-drop). `raw_count` is no longer
            // touched — the field is dormant pending its removal.
            obl_minted = regions.tracked_mint_frame_obligation(idx);
        }

        proof_with!(|= Tracked(obl_minted));
        Self { ptr, _marker: PhantomData }
    }
}

#[verus_verify]
impl<M: AnyFrameMeta + Repr<MetaSlotStorage>> RCClone for Frame<M> {
    open spec fn clone_requires(self, perm: MetaRegionOwners) -> bool {
        let idx = self.index();
        &&& self.inv()
        &&& perm.inv()
        &&& perm.slot_owners[idx].inner_perms.ref_count.value() > 0
        &&& perm.slot_owners[idx].inner_perms.ref_count.value()
            != REF_COUNT_UNUSED
        // Saturation aborts (Arc-style) via `inc_ref_count`'s diverging panic.
        &&& perm.slot_owners[idx].inner_perms.ref_count.value() >= REF_COUNT_MAX ==> may_panic()
        &&& has_safe_slot(self.paddr())
    }

    open spec fn clone_ensures(
        self,
        old_perm: MetaRegionOwners,
        new_perm: MetaRegionOwners,
        res: Self,
    ) -> bool {
        let idx = frame_to_index(meta_to_frame(self.ptr.addr()));
        &&& new_perm.inv()
        // ref_count incremented
        &&& new_perm.slot_owners[idx].inner_perms.ref_count.value()
            == old_perm.slot_owners[idx].inner_perms.ref_count.value() + 1
        &&& new_perm.slot_owners[idx].inner_perms.ref_count.id()
            == old_perm.slot_owners[idx].inner_perms.ref_count.id()
        // All other fields at idx unchanged
        &&& new_perm.slot_owners[idx].inner_perms.storage
            == old_perm.slot_owners[idx].inner_perms.storage
        &&& new_perm.slot_owners[idx].inner_perms.vtable_ptr
            == old_perm.slot_owners[idx].inner_perms.vtable_ptr
        &&& new_perm.slot_owners[idx].inner_perms.in_list
            == old_perm.slot_owners[idx].inner_perms.in_list
        &&& new_perm.slot_owners[idx].paths_in_pt == old_perm.slot_owners[idx].paths_in_pt
        &&& new_perm.slot_owners[idx].slot_vaddr == old_perm.slot_owners[idx].slot_vaddr
        &&& new_perm.slot_owners[idx].usage
            == old_perm.slot_owners[idx].usage
        // Other slot_owners unchanged
        &&& new_perm.slots == old_perm.slots
        &&& forall|i: usize|
            i != idx ==> (#[trigger] new_perm.slot_owners[i] == old_perm.slot_owners[i])
        &&& new_perm.slot_owners.dom() == old_perm.slot_owners.dom()
        &&& new_perm.frame_obligations == old_perm.frame_obligations.insert(idx)
    }

    fn clone(&self, Tracked(perm): Tracked<&mut MetaRegionOwners>) -> Self {
        proof {
            perm.inv_implies_correct_addr(self.paddr());
        }

        let paddr = meta_to_frame(self.ptr.addr());
        let ghost idx = frame_to_index(meta_to_frame(self.ptr.addr()));

        unsafe {
            #[verus_spec(with Tracked(perm))]
            inc_frame_ref_count(paddr)
        };

        proof {
            // Mint the pending-Drop obligation for the freshly cloned live
            // value; `inc_frame_ref_count` left `frame_obligations` intact.
            let tracked _ = perm.tracked_mint_frame_obligation(idx);
        }

        Self { ptr: PPtr::<MetaSlot>::from_addr(self.ptr.0), _marker: PhantomData }
    }
}

impl<M: ?Sized> Drop for Frame<M> {
    fn drop(
        self,
        Tracked(regions): Tracked<&mut MetaRegionOwners>,
        Tracked(obl): Tracked<DropObligation<usize>>,
    ) {
        // Single redeem path: route through `consume_obligation` before
        // running the destructor body. For Frame's current
        // ledger-less `Key = usize`, this is a no-op on state; for
        // future ledger-enforcing variants, this is where the ledger
        // entry is removed.
        proof {
            self.consume_obligation(regions, obl);
        }
        let ghost idx = frame_to_index(meta_to_frame(self.ptr.addr()));
        let ghost old_regions = *regions;

        let tracked mut slot_own = regions.slot_owners.tracked_remove(idx);
        // Design B: a shared `Frame` is Arc-like; its `drop` only adjusts
        // the refcount. The slot permission is *borrowed* from
        // `regions.slots`, never moved out and back.
        let tracked perm = regions.slots.tracked_borrow(idx);
        let slot = self.ptr.borrow(Tracked(perm));

        // Snapshot of the slot's pre-drop state for the strengthened
        // `drop_ensures` (refcount transition + identity preservation).
        let ghost so0 = slot_own;

        let last_ref_cnt = slot.ref_count.fetch_sub(
            Tracked(&mut slot_own.inner_perms.ref_count),
            1,
        );

        if last_ref_cnt == 1 {
            // A fence is needed here with the same reasons stated in the implementation of
            // `Arc::drop`: <https://doc.rust-lang.org/std/sync/struct.Arc.html#method.drop>.
            acquire_fence();
            unsafe {
                #[verus_spec(with Tracked(&mut slot_own))]
                slot.drop_last_in_place()
            };

            // TODO: return page to allocator
            // allocator::get_global_frame_allocator().dealloc(paddr, PAGE_SIZE);
        }
        proof {
            regions.slot_owners.tracked_insert(idx, slot_own);

            assert forall|i: usize| i != idx implies #[trigger] regions.slot_owners[i]
                == old_regions.slot_owners[i] by {}
            assert(regions.slots == old_regions.slots);
            assert(regions.slot_owners.dom() == old_regions.slot_owners.dom());

            // Re-establish `regions.inv()` for the post-state. The
            // tracked_insert at `idx` only touches that one entry; for other
            // indices, the invariant carries over from `old_regions.inv()`.
            // For `idx`, `slot_own.inv()` and the perm/slot agreement at
            // `idx` are already asserted above.
            assert forall|i: usize|
                i < max_meta_slots() <==> #[trigger] regions.slot_owners.contains_key(i) by {}

            assert forall|i: usize| #[trigger] regions.slots.contains_key(i) implies i
                < max_meta_slots() by {
                if i == idx {
                    assert(regions.slot_owners.contains_key(idx));
                }
            }

            assert forall|i: usize| #[trigger] regions.slots.contains_key(i) implies ({
                &&& regions.slot_owners.contains_key(i)
                &&& regions.slot_owners[i].inv()
                &&& regions.slots[i].is_init()
                &&& regions.slots[i].addr() == meta_addr(i)
                &&& regions.slots[i].value().wf(regions.slot_owners[i])
                &&& regions.slot_owners[i].slot_vaddr == regions.slots[i].addr()
            }) by {
                if i == idx {
                    assert(regions.slots[i].is_init());
                    assert(regions.slots[i].addr() == meta_addr(i));
                    assert(regions.slots[i].value().wf(regions.slot_owners[i]));
                    assert(regions.slot_owners[i].slot_vaddr == regions.slots[i].addr());
                }
            }

            assert forall|i: usize| #[trigger]
                regions.slot_owners.contains_key(i) implies regions.slot_owners[i].inv() by {
                if i == idx {
                    assert(slot_own.inv());
                }
            }
        }
    }
}

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

/*
impl From<UFrame> for Frame<dyn AnyFrameMeta> {
    fn from(frame: UFrame) -> Self {
        // SAFETY: The metadata is coerceable and the struct is transmutable.
        unsafe { core::mem::transmute(frame) }
    }
}

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
/// # Verified Properties
/// ## Preconditions
/// - **Safety Invariant**: Metaslot region invariants must hold.
/// - **Safety**: The physical address must represent a valid frame.
/// ## Postconditions
/// - **Safety Invariant**: Metaslot region invariants hold after the call.
/// - **Correctness**: The reference count of the frame is increased by one.
/// - **Safety**: Frames other than this one are not affected by the call.
/// ## Safety
/// We enforce the safety requirements that `paddr` represents a valid frame and the caller has already held a reference to the it.
/// It is safe to require these as preconditions because the function is internal, so the caller must obey the preconditions.
#[verus_spec(
    with
        Tracked(regions): Tracked<&mut MetaRegionOwners>,
    requires
        old(regions).inv(),
        old(regions).slots.contains_key(frame_to_index(paddr)),
        has_safe_slot(paddr),
        // The caller holds a reference, so rc > 0, and the slot must be live
        // (not the UNUSED sentinel). Saturation is caught at runtime by
        // `inc_ref_count`'s Arc-style abort.
        old(regions).slot_owners[frame_to_index(paddr)].inner_perms.ref_count.value() > 0,
        old(regions).slot_owners[frame_to_index(paddr)].inner_perms.ref_count.value()
            != REF_COUNT_UNUSED,
        old(regions).slot_owners[frame_to_index(paddr)].inner_perms.ref_count.value()
            >= REF_COUNT_MAX ==> may_panic(),
    ensures
        final(regions).inv(),
        final(regions).slot_owners[frame_to_index(paddr)].inner_perms.ref_count.value() == old(
            regions,
        ).slot_owners[frame_to_index(paddr)].inner_perms.ref_count.value() + 1,
        final(regions).slot_owners[frame_to_index(paddr)].inner_perms.ref_count.id() == old(
            regions,
        ).slot_owners[frame_to_index(paddr)].inner_perms.ref_count.id(),
        final(regions).slot_owners[frame_to_index(paddr)].inner_perms.storage == old(
            regions,
        ).slot_owners[frame_to_index(paddr)].inner_perms.storage,
        final(regions).slot_owners[frame_to_index(paddr)].inner_perms.vtable_ptr == old(
            regions,
        ).slot_owners[frame_to_index(paddr)].inner_perms.vtable_ptr,
        final(regions).slot_owners[frame_to_index(paddr)].inner_perms.in_list == old(
            regions,
        ).slot_owners[frame_to_index(paddr)].inner_perms.in_list,
        final(regions).slot_owners[frame_to_index(paddr)].paths_in_pt == old(
            regions,
        ).slot_owners[frame_to_index(paddr)].paths_in_pt,
        final(regions).slot_owners[frame_to_index(paddr)].slot_vaddr == old(
            regions,
        ).slot_owners[frame_to_index(paddr)].slot_vaddr,
        final(regions).slot_owners[frame_to_index(paddr)].usage == old(
            regions,
        ).slot_owners[frame_to_index(paddr)].usage,
        final(regions).slots == old(regions).slots,
        forall|i: usize|
            i != frame_to_index(paddr) ==> (#[trigger] final(regions).slot_owners[i] == old(
                regions,
            ).slot_owners[i]),
        final(regions).slot_owners.dom() == old(regions).slot_owners.dom(),
        // Linear-drop pilot: refcount bump doesn't touch segment or frame
        // obligation ledgers.
        final(regions).frame_obligations == old(regions).frame_obligations,
)]
pub(in crate::mm) unsafe fn inc_frame_ref_count(paddr: Paddr) {
    let tracked mut slot_own = regions.slot_owners.tracked_remove(frame_to_index(paddr));
    let tracked perm = regions.slots.tracked_borrow(frame_to_index(paddr));
    let tracked inner_perms = slot_own.tracked_borrow_mut_inner_perms();

    let vaddr: Vaddr = frame_to_meta(paddr);
    // SAFETY: `vaddr` points to a valid `MetaSlot` that will never be mutably borrowed, so taking
    // an immutable reference to it is always safe.
    let slot = PPtr::<MetaSlot>::from_addr(vaddr);

    unsafe {
        #[verus_spec(with Tracked(&mut inner_perms.ref_count))]
        slot.borrow(Tracked(perm)).inc_ref_count()
    };

    proof {
        let idx = frame_to_index(paddr);

        // inc_ref_count preserves permission id
        assert(inner_perms.ref_count.id() == old(
            regions,
        ).slot_owners[idx].inner_perms.ref_count.id());

        // slot_own.inv() holds: rc in (0, REF_COUNT_MAX), vtable_ptr init, slot_vaddr ok
        assert(slot_own.inv());

        // wf: the slot's cell ids still match the (updated) inner_perms ids
        assert(regions.slots[idx].value().wf(slot_own));

        regions.slot_owners.tracked_insert(idx, slot_own);
    }
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
    /// Axiomatized (`external_body`) because the body is `transmute`, which
    /// Verus has no built-in spec for.
    #[verifier::external_body]
    pub fn into_dyn(self) -> Frame<dyn AnyFrameMeta> {
        // SAFETY: `Frame<M>` is `#[repr(transparent)]` over `PPtr<MetaSlot>`
        // plus a zero-size `PhantomData<M>`. `Frame<dyn AnyFrameMeta>` has
        // the same runtime layout (thin pointer + ZST phantom).
        unsafe { core::mem::transmute(self) }
    }
}

} // verus!
