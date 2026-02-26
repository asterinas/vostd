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

#[cfg(ktest)]
mod test;

use vstd::atomic::PermissionU64;
use vstd::prelude::*;
use vstd::simple_pptr::{self, PPtr};

use vstd_extra::cast_ptr;

use core::{
    marker::PhantomData,
    sync::atomic::{AtomicUsize, Ordering},
};

//pub use allocator::GlobalFrameAllocator;
use meta::REF_COUNT_UNUSED;
pub use segment::Segment;

// Re-export commonly used types
use crate::specs::arch::kspace::FRAME_METADATA_RANGE;
pub use frame_ref::FrameRef;
pub use linked_list::{CursorMut, Link, LinkedList};
pub use meta::mapping::{
    frame_to_index, frame_to_index_spec, frame_to_meta, meta_addr, meta_to_frame, META_SLOT_SIZE,
};
pub use meta::{has_safe_slot, AnyFrameMeta, GetFrameError, MetaSlot};
pub use unique::UniqueFrame;

use crate::mm::page_table::{PageTableConfig, PageTablePageMeta};

use vstd_extra::cast_ptr::*;
use vstd_extra::drop_tracking::*;
use vstd_extra::ownership::*;

use crate::mm::{
    kspace::{LINEAR_MAPPING_BASE_VADDR, VMALLOC_BASE_VADDR},
    Paddr, PagingLevel, Vaddr, MAX_PADDR,
};
use crate::specs::arch::mm::{MAX_NR_PAGES, PAGE_SIZE};
use crate::specs::mm::frame::meta_owners::*;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::frame::frame_specs::*;

verus! {

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
pub struct Frame<M: AnyFrameMeta> {
    pub ptr: PPtr<MetaSlot>,
    pub _marker: PhantomData<M>,
}

impl<M: AnyFrameMeta> Clone for Frame<M> {
    fn clone(&self) -> Self {
        Self { ptr: PPtr::<MetaSlot>::from_addr(self.ptr.0), _marker: PhantomData }
    }
}

/// We need to keep track of when frames are forgotten with `ManuallyDrop`.
/// We maintain a counter for each frame of how many times it has been forgotten (`raw_count`).
/// Calling `ManuallyDrop::new` increments the counter. It is technically safe to forget a frame multiple times,
/// and this will happen with read-only `FrameRef`s. All such references need to be dropped by the time
/// `from_raw` is called. So, `ManuallyDrop::drop` decrements the counter when the reference is dropped,
/// and `from_raw` may only be called when the counter is 1.
impl<M: AnyFrameMeta> TrackDrop for Frame<M> {
    type State = MetaRegionOwners;

    open spec fn constructor_requires(self, s: Self::State) -> bool {
        &&& s.slot_owners.contains_key(frame_to_index(meta_to_frame(self.ptr.addr())))
        &&& s.inv()
    }

    open spec fn constructor_ensures(self, s0: Self::State, s1: Self::State) -> bool {
        let slot_own = s0.slot_owners[frame_to_index(meta_to_frame(self.ptr.addr()))];
        &&& s1.slot_owners[frame_to_index(meta_to_frame(self.ptr.addr()))] ==
            MetaSlotOwner {
                raw_count: (slot_own.raw_count + 1) as usize,
                ..slot_own
            }
        &&& forall|i: usize| #![trigger s1.slot_owners[i]]
            i != frame_to_index(meta_to_frame(self.ptr.addr())) ==> s1.slot_owners[i] == s0.slot_owners[i]
        &&& s1.slots =~= s0.slots
        &&& s1.slot_owners.dom() =~= s0.slot_owners.dom()
    }

    proof fn constructor_spec(self, tracked s: &mut Self::State) {
        let meta_addr = self.ptr.addr();
        let index = frame_to_index(meta_to_frame(meta_addr));
        let tracked mut slot_own = s.slot_owners.tracked_remove(index);
        slot_own.raw_count = (slot_own.raw_count + 1) as usize;
        s.slot_owners.tracked_insert(index, slot_own);
    }

    open spec fn drop_requires(self, s: Self::State) -> bool {
        &&& s.slot_owners.contains_key(frame_to_index(meta_to_frame(self.ptr.addr())))
        &&& s.slot_owners[frame_to_index(meta_to_frame(self.ptr.addr()))].raw_count > 0
    }

    open spec fn drop_ensures(self, s0: Self::State, s1: Self::State) -> bool {
        let slot_own = s0.slot_owners[frame_to_index(meta_to_frame(self.ptr.addr()))];
        &&& s1.slot_owners[frame_to_index(meta_to_frame(self.ptr.addr()))].raw_count == (slot_own.raw_count - 1) as usize
        &&& forall|i: usize| #![trigger s1.slot_owners[i]]
            i != frame_to_index(meta_to_frame(self.ptr.addr())) ==> s1.slot_owners[i] == s0.slot_owners[i]
        &&& s1.slots =~= s0.slots
        &&& s1.slot_owners.dom() =~= s0.slot_owners.dom()
    }

    proof fn drop_spec(self, tracked s: &mut Self::State) {
        let index = frame_to_index(meta_to_frame(self.ptr.addr()));
        let tracked mut slot_own = s.slot_owners.tracked_remove(index);
        slot_own.raw_count = (slot_own.raw_count - 1) as usize;
        s.slot_owners.tracked_insert(index, slot_own);
    }
}

impl<M: AnyFrameMeta> Inv for Frame<M> {
    open spec fn inv(self) -> bool {
        &&& self.ptr.addr() % META_SLOT_SIZE == 0
        &&& FRAME_METADATA_RANGE.start <= self.ptr.addr() < FRAME_METADATA_RANGE.start
            + MAX_NR_PAGES * META_SLOT_SIZE
        &&& self.ptr.addr() < VMALLOC_BASE_VADDR - LINEAR_MAPPING_BASE_VADDR
    }
}

impl<M: AnyFrameMeta> Frame<M> {
    pub open spec fn paddr(self) -> usize {
        meta_to_frame(self.ptr.addr())
    }

    pub open spec fn index(self) -> usize {
        frame_to_index(self.paddr())
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
    /// - **Bookkeeping**: The slot must be available in order to get the permission.
    /// This is stronger than it needs to be; absent permissions correspond to error cases.
    /// ## Postconditions
    /// - **Safety Invariant**: Metaslot region invariants hold after the call.
    /// - **Correctness**: If successful, the function returns a pointer to the metadata slot and a permission to the slot.
    /// - **Correctness**: If successful, the slot is initialized with the given metadata.
    /// ## Safety
    /// - This function returns an error if `paddr` does not correspond to a valid slot or the slot is in use.
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>
            -> perm: Tracked<Option<PointsTo<MetaSlot, Metadata<M>>>>
        requires
            old(regions).inv(),
            old(regions).slots.contains_key(frame_to_index(paddr)),
        ensures
            regions.inv(),
            r matches Ok(res) ==> perm@ is Some && MetaSlot::get_from_unused_perm_spec(paddr, metadata, false, res.ptr, perm@.unwrap()),
            r is Ok ==> MetaSlot::get_from_unused_spec(paddr, false, *old(regions), *regions),
            !has_safe_slot(paddr) ==> r is Err,
    )]
    pub fn from_unused(paddr: Paddr, metadata: M) -> Result<Self, GetFrameError>
    {
        #[verus_spec(with Tracked(regions))]
        let from_unused = MetaSlot::get_from_unused(paddr, metadata, false);
        if let Err(err) = from_unused {
            proof_with!(|= Tracked(None));
            Err(err)
        } else {
            let (ptr, Tracked(perm)) = from_unused.unwrap();
            proof_with!(|= Tracked(Some(perm)));
            Ok(Self { ptr, _marker: PhantomData })
        }
    }

    /// Gets the metadata of this page.
    /// # Verified Properties
    /// ## Preconditions
    /// - The caller must have a valid permission for the frame.
    /// ## Postconditions
    /// - The function returns the metadata of the frame.
    /// ## Safety
    /// - By requiring the caller to provide a typed permission, we ensure that the metadata is of type `M`.
    /// While a non-verified caller cannot be trusted to obey this interface, all functions that return a `Frame<M>` also
    /// return an appropriate permission.
    #[verus_spec(
        with Tracked(perm) : Tracked<&'a PointsTo<MetaSlot, Metadata<M>>>,
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
        #[verus_spec(with Tracked(&perm.points_to))]
        let slot = self.slot();

        #[verus_spec(with Tracked(&perm.points_to))]
        let ptr = slot.as_meta_ptr();

        &ptr.borrow(Tracked(perm)).metadata
    }
}

#[verus_verify]
impl<M: AnyFrameMeta> Frame<M> {
    /// Gets a dynamically typed [`Frame`] from a raw, in-use page.
    ///
    /// If the provided frame is not in use at the moment, it will return an error.
    ///
    /// The returned frame will have an extra reference count to the frame.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariant**: Metaslot region invariants must hold.
    /// - **Liveness**: The slot must have fewer than `REF_COUNT_MAX - 1` references or the function will panic.
    /// ## Postconditions
    /// - **Safety Invariant**: Metaslot region invariants hold after the call.
    /// - **Correctness**: If successful, the function returns the frame at `paddr`.
    /// - **Correctness**: If successful, the frame has an extra reference count to the frame.
    /// - **Safety**: Frames other than the one at `paddr` are not affected by the call.
    /// ## Safety
    /// - If `paddr` is a valid frame address, it is safe to take a reference to the frame.
    /// - If `paddr` is not a valid frame address, the function will return an error.
    #[verus_spec(res =>
        with Tracked(regions) : Tracked<&mut MetaRegionOwners>,
        requires
            old(regions).inv(),
            old(regions).slots.contains_key(frame_to_index(paddr)),
            !MetaSlot::get_from_in_use_panic_cond(paddr, *old(regions)),
        ensures
            regions.inv(),
            res is Ok ==>
                regions.slot_owners[frame_to_index(paddr)].inner_perms.ref_count.value() ==
                old(regions).slot_owners[frame_to_index(paddr)].inner_perms.ref_count.value() + 1,
            res matches Ok(res) ==>
                res.ptr == old(regions).slots[frame_to_index(paddr)].pptr(),
            !has_safe_slot(paddr) ==> res is Err,
            forall|i: usize|
                #![trigger regions.slot_owners[i]]
                i != frame_to_index(paddr) ==> regions.slot_owners[i] == old(regions).slot_owners[i]
    )]
    pub fn from_in_use(paddr: Paddr) -> Result<Self, GetFrameError> {
        #[verus_spec(with Tracked(regions))]
        let from_in_use = MetaSlot::get_from_in_use(paddr);
        Ok(Self { ptr: from_in_use?, _marker: PhantomData })
    }
}

#[verus_verify]
impl<'a, M: AnyFrameMeta> Frame<M> {
    /// Gets the physical address of the start of the frame.
    #[verus_spec(
        with Tracked(perm): Tracked<&vstd::simple_pptr::PointsTo<MetaSlot>>
    )]
    pub fn start_paddr(&self) -> Paddr
        requires
            perm.addr() == self.ptr.addr(),
            perm.is_init(),
            FRAME_METADATA_RANGE.start <= perm.addr() < FRAME_METADATA_RANGE.end,
            perm.addr() % META_SLOT_SIZE == 0,
        returns
            meta_to_frame(self.ptr.addr()),
    {
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
    pub const fn map_level(&self) -> PagingLevel {
        1
    }

    /// Gets the size of this page in bytes.
    pub const fn size(&self) -> usize {
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
        with Tracked(slot_own): Tracked<&mut MetaSlotOwner>,
            Tracked(perm) : Tracked<&PointsTo<MetaSlot, Metadata<M>>>
    )]
    pub fn reference_count(&self) -> u64
        requires
            perm.addr() == self.ptr.addr(),
            perm.points_to.pptr() == self.ptr,
            perm.is_init(),
            perm.wf(&perm.inner_perms),
            perm.inner_perms.ref_count.id() == perm.points_to.value().ref_count.id(),
        returns
            perm.value().ref_count,
    {
        #[verus_spec(with Tracked(&perm.points_to))]
        let slot = self.slot();
        slot.ref_count.load(Tracked(&perm.inner_perms.ref_count))
    }

    /// Borrows a reference from the given frame.
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariant**: Metaslot region invariants must hold.
    /// - **Bookkeeping**: The caller must have a valid and well-typed permission for the frame.
    /// ## Postconditions
    /// - **Safety Invariant**: Metaslot region invariants hold after the call.
    /// - **Correctness**: The function returns a reference to the frame.
    /// - **Correctness**: The system context is unchanged.
    #[verus_spec(res =>
        with Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(perm): Tracked<&MetaPerm<M>>,
        requires
            old(regions).inv(),
            !old(regions).slots.contains_key(self.index()),
            perm.points_to.pptr() == self.ptr,
            perm.is_init(),
            self.inv(),
        ensures
            regions.inv(),
            res.inner@.ptr.addr() == self.ptr.addr(),
            regions.slots =~= old(regions).slots,
            regions.slot_owners =~= old(regions).slot_owners,
    )]
    pub fn borrow(&self) -> FrameRef<'a, M> {
        assert(regions.slot_owners.contains_key(self.index()));
        broadcast use crate::mm::frame::meta::mapping::group_page_meta;
        // SAFETY: Both the lifetime and the type matches `self`.
        #[verus_spec(with Tracked(&perm.points_to))]
        let paddr = self.start_paddr();

        #[verus_spec(with Tracked(regions), Tracked(perm))]
        FrameRef::borrow_paddr(paddr)
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
                -> frame_perm: Tracked<MetaPerm<M>>,
        requires
            old(regions).inv(),
            old(regions).slots.contains_key(self.index()),
            self.inv(),
            old(regions).slot_owners[self.index()].inner_perms.ref_count.value() != REF_COUNT_UNUSED,
        ensures
            regions.inv(),
            r == self.paddr(),
            frame_perm@.points_to == old(regions).slots[self.index()],
            regions.slot_owners[self.index()].raw_count
                == (old(regions).slot_owners[self.index()].raw_count + 1) as usize,
            self.into_raw_post_noninterference(*old(regions), *regions),
    )]
    pub(in crate::mm) fn into_raw(self) -> Paddr {
        broadcast use crate::mm::frame::meta::mapping::group_page_meta;

        let tracked perm = regions.slots.tracked_borrow(self.index());

        assert(perm.addr() == self.ptr.addr()) by {
            assert(frame_to_meta(meta_to_frame(self.ptr.addr())) == self.ptr.addr());
        };

        #[verus_spec(with Tracked(perm))]
        let paddr = self.start_paddr();

        let ghost index = self.index();

        assert(self.constructor_requires(*regions));
        let _ = ManuallyDrop::new(self, Tracked(regions));

        assert(regions.slots.contains_key(index));
        let tracked meta_perm = regions.copy_perm::<M>(index);

        proof_with!(|= Tracked(meta_perm));
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
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariant**: Metaslot region invariants must hold.
    /// - **Safety**: The caller must have a valid and well-typed permission for the frame.
    /// - **Safety**: There must be at least one raw frame at `paddr`.
    /// ## Postconditions
    /// - **Safety Invariant**: Metaslot region invariants hold after the call.
    /// - **Correctness**: The function returns the frame at `paddr`.
    /// - **Correctness**: The frame's raw count is decremented.
    /// - **Safety**: Frames other than this one are not affected by the call.
    /// - **Safety**: The count of raw frames is restored to 0.
    /// ## Safety
    /// - When `into_raw` was called, the frame was marked to be ignored by the garbage collector.
    /// Now we construct a new frame at the same address, which will be managed by the garbage collector again.
    /// We ensure that we only do this once by setting the raw count to 0. We will only call this function again
    /// if we have since forgotten the frame again.
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(perm): Tracked<&MetaPerm<M>>,
        requires
            Self::from_raw_requires(*old(regions), paddr),
            perm.points_to.is_init(),
            perm.points_to.addr() == frame_to_meta(paddr),
            perm.points_to.value().wf(old(regions).slot_owners[frame_to_index(paddr)]),
        ensures
            Self::from_raw_ensures(*old(regions), *regions, paddr, r),
    )]
    pub(in crate::mm) fn from_raw(paddr: Paddr) -> Self {
        let vaddr = frame_to_meta(paddr);
        let ptr = PPtr::from_addr(vaddr);

        proof {
            let index = frame_to_index(paddr);
            regions.sync_perm::<M>(index, perm);

            let tracked mut slot_own = regions.slot_owners.tracked_remove(index);
            slot_own.raw_count = 0usize;
            regions.slot_owners.tracked_insert(index, slot_own);
        }

        Self { ptr, _marker: PhantomData }
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
    #[verus_spec(
        with Tracked(slot_perm): Tracked<&'a vstd::simple_pptr::PointsTo<MetaSlot>>
    )]
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
    with Tracked(regions): Tracked<&mut MetaRegionOwners>
)]
pub(in crate::mm) fn inc_frame_ref_count(paddr: Paddr)
    requires
        old(regions).inv(),
        old(regions).slots.contains_key(frame_to_index(paddr)),
        has_safe_slot(paddr),
        !MetaSlot::inc_ref_count_panic_cond(old(regions).slot_owners[frame_to_index(paddr)].inner_perms.ref_count),
    ensures
        regions.inv(),
        regions.slot_owners[frame_to_index(paddr)].inner_perms.ref_count.value() ==
            old(regions).slot_owners[frame_to_index(paddr)].inner_perms.ref_count.value() + 1,
        regions.slots =~= old(regions).slots,
        forall|i: usize| i != frame_to_index(paddr) ==>
            (#[trigger] regions.slot_owners[i] == old(regions).slot_owners[i]),
        regions.slot_owners.dom() =~= old(regions).slot_owners.dom(),
{
    let tracked mut slot_own = regions.slot_owners.tracked_remove(frame_to_index(paddr));
    let tracked perm = regions.slots.tracked_borrow(frame_to_index(paddr));
    let tracked mut inner_perms = slot_own.take_inner_perms();

    let vaddr: Vaddr = frame_to_meta(paddr);
    // SAFETY: `vaddr` points to a valid `MetaSlot` that will never be mutably borrowed, so taking
    // an immutable reference to it is always safe.
    let slot = PPtr::<MetaSlot>::from_addr(vaddr);

    #[verus_spec(with Tracked(&mut inner_perms.ref_count))]
    slot.borrow(Tracked(perm)).inc_ref_count();

    proof {
        admit();
        slot_own.sync_inner(&inner_perms);
        regions.slot_owners.tracked_insert(frame_to_index(paddr), slot_own);
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

