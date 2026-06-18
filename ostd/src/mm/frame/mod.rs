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
pub mod allocator;
pub mod linked_list;
pub mod meta;
pub mod segment;
pub mod unique;
pub mod untyped;

mod frame_ref;
pub mod obligation_demo;

#[cfg(ktest)]
mod test;

use vstd::atomic::PermissionU64;
use vstd::prelude::*;
use vstd::simple_pptr::{self, PPtr};
use vstd_extra::cast_ptr::*;
use vstd_extra::drop_tracking::*;
use vstd_extra::ownership::*;
use vstd_extra::panic::may_panic;

use core::{
    marker::PhantomData,
    sync::atomic::{AtomicUsize, Ordering},
};

//pub use allocator::GlobalFrameAllocator;
use meta::{REF_COUNT_MAX, REF_COUNT_UNIQUE, REF_COUNT_UNUSED};
pub use segment::Segment;

// Re-export commonly used types
use crate::mm::kspace::FRAME_METADATA_RANGE;
pub use frame_ref::FrameRef;
pub use linked_list::{CursorMut, Link, LinkedList};
pub use meta::mapping::{META_SLOT_SIZE, frame_to_index, frame_to_meta, meta_addr, meta_to_frame};
pub use meta::{AnyFrameMeta, GetFrameError, MetaSlot};
pub use unique::UniqueFrame;
pub use untyped::{AnyUFrameMeta, UFrame};

use crate::mm::page_table::{PageTableConfig, PageTablePageMeta};

use crate::mm::page_table::RCClone;
use crate::mm::{
    MAX_PADDR, Paddr, PagingLevel, Vaddr,
    kspace::{LINEAR_MAPPING_BASE_VADDR, VMALLOC_BASE_VADDR},
};
use crate::specs::arch::*;
use crate::specs::mm::frame::frame_specs::*;
use crate::specs::mm::frame::meta_owners::*;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;

verus! {

/*
static MAX_PADDR: AtomicUsize = AtomicUsize::new(0);

/// Returns the maximum physical address that is tracked by frame metadata.
pub(in crate::mm) fn max_paddr() -> Paddr {
    let max_paddr = MAX_PADDR.load(Ordering::Relaxed) as Paddr;
    debug_assert_ne!(max_paddr, 0);
    max_paddr
}*/
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

/*
impl<M: ?Sized> Inv for Frame<M> {
    open spec fn inv(self) -> bool {
        &&& self.ptr.addr() % META_SLOT_SIZE == 0
        &&& FRAME_METADATA_RANGE.start <= self.ptr.addr() < FRAME_METADATA_RANGE.start
            + MAX_NR_PAGES * META_SLOT_SIZE
    }
}

// Unbounded so the PT-node `on_drop` body can use `Frame::<Self>::from_raw` /
// `Drop for Frame<Self>` without forcing trait resolution back through the
// in-flight `AnyFrameMeta for PageTablePageMeta<C>` impl. Body is pure
// pointer arithmetic — no M-specific machinery.
impl<M: ?Sized> Frame<M> {
    pub open spec fn paddr(self) -> usize {
        meta_to_frame(self.ptr.addr())
    }
}*/

/*
impl<M: AnyFrameMeta + ?Sized> PartialEq for Frame<M> {
    fn eq(&self, other: &Self) -> bool {
        self.start_paddr() == other.start_paddr()
    }
}

impl<M: AnyFrameMeta + ?Sized> Eq for Frame<M> {}
*/

impl<M: ?Sized> Frame<M> {
    /// Cross-object well-formedness predicate: this `Frame` handle and
    /// the supplied [`MetaRegionOwners`] state are mutually consistent.
    /// Packages the static "Frame ⟷ state" conjuncts (slot/pointer
    /// identity, slot in-use range) so that consumer specs
    /// ([`drop_requires`], [`clone_requires`]) read uniformly.
    ///
    /// **Name**: `wf_state` (not just `wf`) to avoid clashing with the
    /// `OwnerOf::wf(self, Self::Owner)` impl that
    /// [`PageTableNode<C> = Frame<PageTablePageMeta<C>>`] inherits — the
    /// two predicates take different argument types and serve different
    /// purposes (per-handle vs. per-owner well-formedness).
    ///
    /// The rc range (`> 0 ∧ ≠ UNUSED ∧ ≠ UNIQUE ∧ ≤ MAX`) captures the
    /// fact that holding a `Frame<M>` is itself evidence that the slot
    /// is in the SHARED state — no UNUSED, no UNIQUE (which is reserved
    /// for [`UniqueFrame`]). Combined with
    /// [`MetaSlotOwner::inv`]'s SHARED branch (post Item 1), `wf_state`
    /// implies `storage.is_init`, `in_list == 0`, and `vtable_ptr.is_init`
    /// at the slot, so consumers don't have to repeat those.
    ///
    /// **Not preserved by `drop` for `self`**: dropping `self` releases
    /// the reference; for *other* handles to the same slot, `wf_state`
    /// is preserved by `drop`'s `>1` branch (post rc ∈ [1, MAX-1]) and
    /// vacuous in the `==1` branch (no other handles to break).
    pub open spec fn wf_state(self, s: MetaRegionOwners) -> bool {
        let idx = self.index();
        let slot_own = s.slot_owners[idx];
        &&& self.inv()
        &&& s.inv()
        &&& s.slots.contains_key(idx)
        &&& s.slots[idx].pptr() == self.ptr
        &&& s.slot_owners.contains_key(idx)
        &&& slot_own.inner_perms.ref_count.value() != REF_COUNT_UNUSED
        &&& slot_own.inner_perms.ref_count.value() != REF_COUNT_UNIQUE
        &&& slot_own.inner_perms.ref_count.value() > 0
        &&& slot_own.inner_perms.ref_count.value() <= REF_COUNT_MAX
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
    pub(in crate::mm) unsafe fn from_raw(paddr: Paddr) -> Self {
        let vaddr = frame_to_meta(paddr);
        let ptr = PPtr::from_addr(vaddr);

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
impl<'a, M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> Frame<M> {
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
            r matches Ok(res) ==> res.ptr.addr() == frame_to_meta(paddr),
            r is Ok ==> MetaSlot::get_from_unused_spec(paddr, false, *old(regions), *final(regions)),
            r is Ok ==> MetaSlot::slot_perm_reparked_spec(paddr, *old(regions), *final(regions)),
            !has_safe_slot(paddr) ==> r is Err,
            r is Ok ==> MetaSlot::live_frame_obligations_ok_spec(paddr, *old(regions), *final(regions)),
            r is Err ==> MetaSlot::live_frame_obligations_err_spec(*old(regions), *final(regions)),
            // On failure nothing was claimed: the region state is untouched.
            r is Err ==> *final(regions) == *old(regions),
    )]
    pub fn from_unused(paddr: Paddr, metadata: M) -> Result<Self, GetFrameError> {
        let ghost pre = *regions;
        #[verus_spec(with Tracked(regions))]
        let from_unused = MetaSlot::get_from_unused(paddr, metadata, false);
        if let Err(err) = from_unused {
            Err(err)
        } else {
            let (ptr, Tracked(perm)) = from_unused.unwrap();
            let ghost idx = frame_to_index(paddr);
            proof {
                assert(frame_to_index(paddr) < crate::mm::frame::meta::mapping::max_meta_slots());
                assert(pre.slot_owners.contains_key(idx));
                assert(pre.slots.contains_key(idx));
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
            self.ptr.addr() == perm.addr(),
            self.ptr == perm.points_to.pptr(),
            perm.is_init(),
            perm.wf(&perm.inner_perms),
        returns
            perm.value().metadata,
    )]
    pub fn meta(&self) -> &'a M {
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
            res is Ok ==>
                final(regions).ref_count(frame_to_index(paddr)) ==
                old(regions).ref_count(frame_to_index(paddr)) + 1,
            res matches Ok(res) ==>
                res.ptr == old(regions).slots[frame_to_index(paddr)].pptr(),
            !has_safe_slot(paddr) ==> res is Err,
            old(regions).slot_owners_agree_except(*final(regions), frame_to_index(paddr)),
            res is Ok ==> MetaSlot::live_frame_obligations_ok_spec(paddr, *old(regions), *final(regions)),
            res is Err ==> MetaSlot::live_frame_obligations_err_spec(*old(regions), *final(regions)),
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

impl<'a, M: AnyFrameMeta + Repr<MetaSlotStorage>> Frame<M> {
    /// Gets the map level of this page.
    ///
    /// This is the level of the page table entry that maps the frame,
    /// which determines the size of the frame.
    ///
    /// Currently, the level is always 1, which means the frame is a regular
    /// page frame.
    pub const fn map_level(&self) -> PagingLevel {
        1
    }

    /// Gets the size of this page in bytes.
    pub const fn size(&self) -> usize {
        PAGE_SIZE
    }
}

#[verus_verify]
impl<'a, M: AnyFrameMeta + Repr<MetaSlotStorage>> Frame<M> {
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
        FRAME_METADATA_RANGE.start <= perm.addr() < FRAME_METADATA_RANGE.end,
        perm.addr() % META_SLOT_SIZE == 0,
    returns
        meta_to_frame(self.ptr.addr()),
    )]
    pub fn start_paddr(&self) -> Paddr {
        #[verus_spec(with Tracked(perm))]
        let slot = self.slot();

        #[verus_spec(with Tracked(perm))]
        slot.frame_paddr()
    }

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
        let ghost self_idx = frame_to_index(meta_to_frame(self.ptr.addr()));
        let ghost other_idx = frame_to_index(meta_to_frame(other.ptr.addr()));
        proof {
            broadcast use crate::mm::frame::meta::mapping::group_page_meta;

            regions.inv_implies_correct_addr(meta_to_frame(self.ptr.addr()));
            regions.inv_implies_correct_addr(meta_to_frame(other.ptr.addr()));
            assert(regions.slots.contains_key(self_idx));
            assert(regions.slots.contains_key(other_idx));
            assert(regions.slots[self_idx].addr() == self.ptr.addr());
            assert(regions.slots[other_idx].addr() == other.ptr.addr());
        }
        let tracked self_perm = regions.slots.tracked_borrow(self_idx);
        let tracked other_perm = regions.slots.tracked_borrow(other_idx);

        (#[verus_spec(with Tracked(self_perm))]
        self.start_paddr() == #[verus_spec(with Tracked(other_perm))]
        other.start_paddr())
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
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariant**: Metaslot region invariants must hold.
    /// - **Bookkeeping**: The caller must have a valid and well-typed permission for the frame.
    /// ## Postconditions
    /// - **Correctness**: The function returns the reference count of the frame.
    /// ## Safety
    /// - The function is safe to call, but using it requires extra care. The
    /// reference count can be changed by other threads at any time including
    /// potentially between calling this method and acting on the result.
    #[verus_spec(
        with
            Tracked(slot_own): Tracked<&mut MetaSlotOwner>,
            Tracked(perm) : Tracked<&PointsTo<MetaSlot, Metadata<M>>>,
        requires
            perm.addr() == self.ptr.addr(),
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
    #[verus_spec(res =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
        requires
            self.inv_with_regions(*old(regions)),
        ensures
            final(regions).inv(),
            res.inner@.ptr.addr() == self.ptr.addr(),
            final(regions).slot_owners == old(regions).slot_owners,
            final(regions).slots == old(regions).slots,
            final(regions).frame_obligations == old(regions).frame_obligations,
    )]
    pub fn borrow(&self) -> FrameRef<'a, M> {
        proof {
            // The slot perm is canonical in `regions.slots`; `inv_with_regions` already
            // pins its presence and that `slots[idx].pptr() == self.ptr`, so the
            // caller no longer threads a separate `MetaPerm`.
            broadcast use crate::mm::frame::meta::mapping::group_page_meta;

            regions.inv_implies_correct_addr(self.paddr());
            assert(regions.slots.contains_key(self.index()));
            assert(regions.slots[self.index()].addr() == self.ptr.addr());
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
            old(regions).inv(),
            old(regions).slots.contains_key(self.index()),
            self.inv(),
            old(regions).slot_owners[self.index()].inner_perms.ref_count.value() != REF_COUNT_UNUSED,
            old(regions).slot_owners[self.index()].usage
                != crate::specs::mm::frame::meta_owners::PageUsage::PageTable,
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
        broadcast use crate::mm::frame::meta::mapping::group_page_meta;

        let tracked perm = regions.slots.tracked_borrow(self.index());

        assert(perm.addr() == self.ptr.addr()) by {
            assert(frame_to_meta(meta_to_frame(self.ptr.addr())) == self.ptr.addr());
        };

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
    pub fn slot(&self) -> &'a MetaSlot {
        // SAFETY: `ptr` points to a valid `MetaSlot` that will never be
        // mutably borrowed, so taking an immutable reference to it is safe.
        self.ptr.borrow(Tracked(slot_perm))
    }
}

#[verus_verify]
impl<M: AnyFrameMeta + Repr<MetaSlotStorage>> RCClone for Frame<M> {
    open spec fn clone_requires(self, perm: MetaRegionOwners) -> bool {
        let idx = frame_to_index(meta_to_frame(self.ptr.addr()));
        &&& self.inv()
        &&& perm.inv()
        &&& perm.slots.contains_key(idx)
        &&& perm.slot_owners.contains_key(idx)
        &&& perm.slot_owners[idx].inner_perms.ref_count.value() > 0
        &&& perm.slot_owners[idx].inner_perms.ref_count.value()
            != meta::REF_COUNT_UNUSED
        // Saturation aborts (Arc-style) via `inc_ref_count`'s diverging panic.
        &&& perm.slot_owners[idx].inner_perms.ref_count.value() >= meta::REF_COUNT_MAX
            ==> may_panic()
        &&& has_safe_slot(meta_to_frame(self.ptr.addr()))
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
        &&& new_perm.slot_owners[idx].self_addr == old_perm.slot_owners[idx].self_addr
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

        proof {
            assert(slot.ref_count.id() == slot_own.inner_perms.ref_count.id());
        }
        let last_ref_cnt = slot.ref_count.fetch_sub(
            Tracked(&mut slot_own.inner_perms.ref_count),
            1,
        );
        // `fetch_sub` returns the pre-decrement value and only mutates
        // the `ref_count` permission — the other `MetaSlotOwner` fields
        // are untouched here.
        proof {
            assert(last_ref_cnt == so0.inner_perms.ref_count.value());
            assert(slot_own.self_addr == so0.self_addr);
            assert(slot_own.usage == so0.usage);
            assert(slot_own.paths_in_pt == so0.paths_in_pt);
        }

        if last_ref_cnt == 1 {
            // A fence is needed here with the same reasons stated in the implementation of
            // `Arc::drop`: <https://doc.rust-lang.org/std/sync/struct.Arc.html#method.drop>.
            acquire_fence();

            proof {
                // Teardown reclaims the last reference and any dormant
                // forgotten references: zero `raw_count` so the resulting
                // `UNUSED` slot satisfies `MetaSlotOwner::inv`
                assert(slot_own.inner_perms.ref_count.value() == 0u64);
                assert(slot_own.inner_perms.storage.is_init());
                assert(slot_own.inner_perms.in_list.value() == 0u64);
                assert(slot_own.inv());
                assert(MetaSlot::drop_last_in_place_safety_cond(slot_own));
                assert(slot.ref_count.id() == slot_own.inner_perms.ref_count.id());
            }
            unsafe {
                #[verus_spec(with Tracked(&mut slot_own))]
                slot.drop_last_in_place()
            };

            proof {
                // last-ref teardown: slot is UNUSED, identity preserved
                // (drop_last_in_place ensures self_addr/usage/paths_in_pt).
                assert(so0.inner_perms.ref_count.value() == 1);
                assert(slot_own.inner_perms.ref_count.value() == REF_COUNT_UNUSED);
                assert(slot_own.self_addr == so0.self_addr);
                assert(slot_own.usage == so0.usage);
                assert(slot_own.paths_in_pt == so0.paths_in_pt);
            }

            // TODO: return page to allocator
            // allocator::get_global_frame_allocator().dealloc(paddr, PAGE_SIZE);
        } else {
            proof {
                assert(last_ref_cnt > 1);
                assert(slot_own.inner_perms.ref_count.value() == last_ref_cnt - 1);
                assert(slot_own.inner_perms.vtable_ptr.is_init());
                assert(slot_own.inv());
                // Decrement branch: refcount = old - 1, identity preserved.
                assert(so0.inner_perms.ref_count.value() > 1);
                assert(slot_own.inner_perms.ref_count.value() == (so0.inner_perms.ref_count.value()
                    - 1) as u64);
                assert(slot_own.self_addr == so0.self_addr);
                assert(slot_own.usage == so0.usage);
                assert(slot_own.paths_in_pt == so0.paths_in_pt);
            }
        }

        proof {
            regions.slot_owners.tracked_insert(idx, slot_own);

            assert forall|i: usize| i != idx implies #[trigger] regions.slot_owners[i]
                == old_regions.slot_owners[i] by {}
            assert(regions.slots == old_regions.slots);
            assert(regions.slot_owners.dom() == old_regions.slot_owners.dom());

            // Strengthened `drop_ensures`: `so0` is exactly the
            // pre-drop owner at `idx`, and `regions.slot_owners[idx]`
            // is now `slot_own` (the post-drop owner).
            assert(so0 == old_regions.slot_owners[idx]);
            assert(regions.slot_owners[idx] == slot_own);
            assert(regions.slot_owners[idx].self_addr == old_regions.slot_owners[idx].self_addr);
            assert(regions.slot_owners[idx].usage == old_regions.slot_owners[idx].usage);
            assert(regions.slot_owners[idx].paths_in_pt
                == old_regions.slot_owners[idx].paths_in_pt);
            assert(old_regions.slot_owners[idx].inner_perms.ref_count.value() == 1
                ==> regions.slot_owners[idx].inner_perms.ref_count.value() == REF_COUNT_UNUSED);
            assert(old_regions.slot_owners[idx].inner_perms.ref_count.value() > 1
                ==> regions.slot_owners[idx].inner_perms.ref_count.value() == (
            old_regions.slot_owners[idx].inner_perms.ref_count.value() - 1) as u64);

            // Re-establish `regions.inv()` for the post-state. The
            // tracked_insert at `idx` only touches that one entry; for other
            // indices, the invariant carries over from `old_regions.inv()`.
            // For `idx`, `slot_own.inv()` and the perm/slot agreement at
            // `idx` are already asserted above.
            assert forall|i: usize|
                i < crate::mm::frame::meta::mapping::max_meta_slots()
                    <==> #[trigger] regions.slot_owners.contains_key(i) by {}

            assert forall|i: usize| #[trigger] regions.slots.contains_key(i) implies i
                < crate::mm::frame::meta::mapping::max_meta_slots() by {
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
                &&& regions.slot_owners[i].self_addr == regions.slots[i].addr()
            }) by {
                if i == idx {
                    assert(regions.slots[i].is_init());
                    assert(regions.slots[i].addr() == meta_addr(i));
                    assert(regions.slots[i].value().wf(regions.slot_owners[i]));
                    assert(regions.slot_owners[i].self_addr == regions.slots[i].addr());
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
        final(regions).slot_owners[frame_to_index(paddr)].self_addr == old(
            regions,
        ).slot_owners[frame_to_index(paddr)].self_addr,
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
    let tracked mut inner_perms = slot_own.take_inner_perms();

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

        // sync_inner: slot_own.inner_perms = inner_perms, other fields unchanged
        slot_own.sync_inner(&inner_perms);

        // slot_own.inv() holds: rc in (0, REF_COUNT_MAX), vtable_ptr init, self_addr ok
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
