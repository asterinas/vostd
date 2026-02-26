// SPDX-License-Identifier: MPL-2.0
//! Metadata management of frames.
//!
//! You can picture a globally shared, static, gigantic array of metadata
//! initialized for each frame.
//! Each entry in this array holds the metadata for a single frame.
//! There would be a dedicated small
//! "heap" space in each slot for dynamic metadata. You can store anything as
//! the metadata of a frame as long as it's [`Sync`].
//!
//! # Implementation
//!
//! The slots are placed in the metadata pages mapped to a certain virtual
//! address in the kernel space. So finding the metadata of a frame often
//! comes with no costs since the translation is a simple arithmetic operation.
use vstd::prelude::*;

pub mod mapping;

use self::mapping::{frame_to_index, frame_to_meta, meta_addr, meta_to_frame, META_SLOT_SIZE};
use crate::specs::mm::frame::meta_owners::*;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;

use vstd::atomic::{PAtomicU64, PAtomicU8, PermissionU64};
use vstd::cell::{self, PCell};

use vstd::simple_pptr::{self, PPtr};
use vstd_extra::cast_ptr::*;
use vstd_extra::ownership::*;

use core::{
    alloc::Layout,
    any::Any,
    cell::UnsafeCell,
    fmt::Debug,
    marker::PhantomData,
    mem::{align_of, size_of, ManuallyDrop, MaybeUninit},
    result::Result,
    sync::atomic::{AtomicU64, AtomicU8, Ordering},
};

//use align_ext::AlignExt;
//use log::info;

use crate::{
    //    boot::memory_region::MemoryRegionType,
    //    const_assert,
    mm::{
        //        frame::allocator::{self, EarlyAllocatedFrameMeta},
        paddr_to_vaddr,
        //        page_table::boot_pt,
        page_prop::{CachePolicy, PageFlags, PageProperty, PrivilegedPageFlags},
        /*Infallible,*/ Paddr,
        PagingLevel,
        //Segment,
        Vaddr,
        MAX_NR_PAGES,
        MAX_PADDR,
        /*VmReader,*/ PAGE_SIZE,
    },
    specs::arch::kspace::FRAME_METADATA_RANGE,
    //    panic::abort,
    //    util::ops::range_difference,
};

verus! {

#[repr(C)]
pub struct MetaSlot {
    /// The metadata of a frame.
    ///
    /// It is placed at the beginning of a slot because:
    ///  - the implementation can simply cast a `*const MetaSlot`
    ///    to a `*const AnyFrameMeta` for manipulation;
    ///  - if the metadata need special alignment, we can provide
    ///    at most `PAGE_METADATA_ALIGN` bytes of alignment;
    ///  - the subsequent fields can utilize the padding of the
    ///    reference count to save space.
    ///
    /// # Verification Design
    /// We model the metadata of the slot as a `MetaSlotStorage`, which is a tagged union of the different
    /// types of metadata defined in the development.
    pub storage: PCell<MetaSlotStorage>,
    /// The reference count of the page.
    ///
    /// Specifically, the reference count has the following meaning:
    ///  - `REF_COUNT_UNUSED`: The page is not in use.
    ///  - `REF_COUNT_UNIQUE`: The page is owned by a [`UniqueFrame`].
    ///  - `0`: The page is being constructed ([`Frame::from_unused`])
    ///    or destructured ([`drop_last_in_place`]).
    ///  - `1..REF_COUNT_MAX`: The page is in use.
    ///  - `REF_COUNT_MAX..REF_COUNT_UNIQUE`: Illegal values to
    ///    prevent the reference count from overflowing. Otherwise,
    ///    overflowing the reference count will cause soundness issue.
    pub ref_count: PAtomicU64,
    /// The virtual table that indicates the type of the metadata. Currently we do not verify this because
    /// of the dependency on the `dyn Trait` pattern. But we can revisit it now that `dyn Trait` is supported by Verus.
    pub vtable_ptr: PPtr<usize>,
    /// This is only accessed by [`crate::mm::frame::linked_list`].
    /// It stores 0 if the frame is not in any list, otherwise it stores the
    /// ID of the list.
    ///
    /// It is ugly but allows us to tell if a frame is in a specific list by
    /// one relaxed read. Otherwise, if we store it conditionally in `storage`
    /// we would have to ensure that the type is correct before the read, which
    /// costs a synchronization.
    pub in_list: PAtomicU64,
}

pub const REF_COUNT_UNUSED: u64 = u64::MAX;

pub const REF_COUNT_UNIQUE: u64 = u64::MAX - 1;

pub const REF_COUNT_MAX: u64 = i64::MAX as u64;

type FrameMetaVtablePtr = core::ptr::DynMetadata<dyn AnyFrameMeta>;

/// The error type for getting the frame from a physical address.
#[derive(Debug)]
pub enum GetFrameError {
    /// The frame is in use.
    InUse,
    /// The frame is not in use.
    Unused,
    /// The frame is being initialized or destructed.
    Busy,
    /// The frame is private to an owner of [`UniqueFrame`].
    ///
    /// [`UniqueFrame`]: super::unique::UniqueFrame
    Unique,
    /// The provided physical address is out of bound.
    OutOfBound,
    /// The provided physical address is not aligned.
    NotAligned,
    /// Verification only: `compare_exchange` returned `Err`, retry
    Retry,
}

pub open spec fn get_slot_spec(paddr: Paddr) -> (res: PPtr<MetaSlot>)
    recommends
        paddr % 4096 == 0,
        paddr < MAX_PADDR,
{
    let slot = frame_to_meta(paddr);
    PPtr(slot, PhantomData::<MetaSlot>)
}

/// Space-holder of the AnyFrameMeta virtual table.
pub trait AnyFrameMeta: Repr<MetaSlotStorage> {
    exec fn on_drop(&mut self) {
    }

    exec fn is_untyped(&self) -> bool {
        false
    }

    spec fn vtable_ptr(&self) -> usize;
}

//global layout MetaSlot is size == 64, align == 8;
pub broadcast proof fn lemma_meta_slot_size()
    ensures
        #[trigger] size_of::<MetaSlot>() == META_SLOT_SIZE,
{
    admit()
}

pub proof fn size_of_meta_slot()
    ensures
        size_of::<MetaSlot>() == 64,
        align_of::<MetaSlot>() == 8,
{
    admit()
}

#[inline(always)]
#[verifier::allow_in_spec]
pub const fn meta_slot_size() -> (res: usize)
    returns
        64usize,
{
    proof {
        size_of_meta_slot();
    }
    size_of::<MetaSlot>()
}

pub open spec fn has_safe_slot(paddr: Paddr) -> bool {
    &&& paddr % PAGE_SIZE == 0
    &&& paddr < MAX_PADDR
}

/// Gets the reference to a metadata slot.
/// # Verified Properties
/// ## Preconditions
/// `paddr` is the physical address of a frame, with a valid owner.
/// ## Postconditions
/// If `paddr` is aligned properly and in-bounds, the function returns a pointer to its metadata slot.
/// ## Safety
/// Verus ensures that the pointer will only be used when we have a permission object, so creating it is safe.
pub(super) fn get_slot(paddr: Paddr) -> (res: Result<PPtr<MetaSlot>, GetFrameError>)
    ensures
        has_safe_slot(paddr) <==> res is Ok,
        res is Ok ==> res.unwrap().addr() == frame_to_meta(paddr),
{
    if paddr % PAGE_SIZE != 0 {
        return Err(GetFrameError::NotAligned);
    }
    if paddr >= MAX_PADDR {
        return Err(GetFrameError::OutOfBound);
    }
    let vaddr = frame_to_meta(paddr);
    let ptr = PPtr::<MetaSlot>::from_addr(vaddr);

    // SAFETY: `ptr` points to a valid `MetaSlot` that will never be
    // mutably borrowed, so taking an immutable reference to it is safe.
    Ok(ptr)
}

#[verus_verify]
impl MetaSlot {
    /// This is the equivalent of &self as *const as Vaddr, but we need to axiomatize it.
    /// # Safety
    /// It is safe to take the address of a pointer, but it may not be safe to use that
    /// address for all purposes.
    #[verifier::external_body]
    fn addr_of(&self, Tracked(perm): Tracked<&vstd::simple_pptr::PointsTo<MetaSlot>>) -> Paddr
        requires
            self == perm.value(),
        returns
            perm.addr(),
    {
        unimplemented!()
    }

    /// A helper function that casts a `MetaSlot` pointer to a `Metadata` pointer of type `M`.
    pub fn cast_slot<M: AnyFrameMeta + Repr<MetaSlotStorage>>(
        &self,
        addr: usize,
        Tracked(perm): Tracked<&vstd::simple_pptr::PointsTo<MetaSlot>>,
    ) -> (res: ReprPtr<MetaSlot, Metadata<M>>)
        requires
            perm.value() == self,
            addr == perm.addr(),
        ensures
            res.ptr.addr() == addr,
            res.addr == addr,
    {
        ReprPtr::<MetaSlot, Metadata<M>> { addr: addr, ptr: PPtr::from_addr(addr), _T: PhantomData }
    }

    /// A helper function that casts `MetaSlot` permission to a `Metadata` permission of type `M`.
    pub fn cast_perm<M: AnyFrameMeta + Repr<MetaSlotStorage>>(
        addr: usize,
        Tracked(perm): Tracked<vstd::simple_pptr::PointsTo<MetaSlot>>,
        Tracked(inner_perms): Tracked<MetadataInnerPerms>,
    ) -> (res: Tracked<PointsTo<MetaSlot, Metadata<M>>>)
        ensures
            res@.addr == addr,
            res@.points_to == perm,
            res@.inner_perms == inner_perms,
    {
        Tracked(PointsTo { addr, points_to: perm, inner_perms, _T: PhantomData })
    }

    /// Initializes the metadata slot of a frame assuming it is unused.
    ///
    /// If successful, the function returns a pointer to the metadata slot.
    /// And the slot is initialized with the given metadata.
    ///
    /// The resulting reference count held by the returned pointer is
    /// [`REF_COUNT_UNIQUE`] if `as_unique_ptr` is `true`, otherwise `1`.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariant**: Metaslot region invariants must hold.
    /// - **Bookkeeping**: The slot permissions must be available in order to check the reference count.
    /// This precondition is stronger than it needs to be; absent permissions correspond to error cases.
    /// ## Postconditions
    /// - **Safety Invariant**: Metaslot region invariants hold after the call.
    /// - **Safety**: Other slots are not affected by the call.
    /// - **Correctness**: If successful, the function returns a pointer to the metadata slot and a permission to the slot.
    /// - **Correctness**: If successful, the slot is initialized with the given metadata.
    /// ## Safety
    /// - This function returns an error if `paddr` does not correspond to a valid slot or the slot is in use.
    /// - Accesses to the slot itself are gated by atomic checks, avoiding data races.
    #[verus_spec(res =>
        with Tracked(regions): Tracked<&mut MetaRegionOwners>
        requires
            old(regions).inv(),
            old(regions).slots.contains_key(frame_to_index(paddr)),
        ensures
            regions.inv(),
            res matches Ok((res, perm)) ==> Self::get_from_unused_perm_spec(paddr, metadata, as_unique_ptr, res, perm@),
            res is Ok ==> Self::get_from_unused_spec(paddr, as_unique_ptr, *old(regions), *regions),
            /// If we can make the failure conditions exhaustive, we can add this as a liveness condition.
            !has_safe_slot(paddr) ==> res is Err,
    )]
    pub(super) fn get_from_unused<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf>(
        paddr: Paddr,
        metadata: M,
        as_unique_ptr: bool,
    ) -> (res: Result<(PPtr<Self>, Tracked<PointsTo<MetaSlot, Metadata<M>>>), GetFrameError>)
    {
        let slot = get_slot(paddr)?;

        proof {
            if has_safe_slot(paddr) {
                regions.inv_implies_correct_addr(paddr);
            }
        }

        let tracked mut slot_own = regions.slot_owners.tracked_remove(frame_to_index(paddr));
        let tracked mut slot_perm = regions.slots.tracked_remove(frame_to_index(paddr));
        let tracked mut inner_perms = slot_own.take_inner_perms();

        // `Acquire` pairs with the `Release` in `drop_last_in_place` and ensures the metadata
        // initialization won't be reordered before this memory compare-and-exchange.
        let last_ref_cnt = slot.borrow(Tracked(&slot_perm)).ref_count.compare_exchange(
            Tracked(&mut inner_perms.ref_count),
            REF_COUNT_UNUSED,
            0,
        ).map_err(
            |val|
                match val {
                    REF_COUNT_UNIQUE => GetFrameError::Unique,
                    0 => GetFrameError::Busy,
                    _ => GetFrameError::InUse,
                },
        );

        if let Err(err) = last_ref_cnt {
            proof {
                slot_own.sync_inner(&inner_perms);
                regions.slot_owners.tracked_insert(frame_to_index(paddr), slot_own);
                regions.slots.tracked_insert(frame_to_index(paddr), slot_perm);
            }

            return Err(err);
        }

        // SAFETY: The slot now has a reference count of `0`, other threads will
        // not access the metadata slot so it is safe to have a mutable reference.

        #[verus_spec(with Tracked(&mut inner_perms.storage), Tracked(&mut inner_perms.vtable_ptr))]
        slot.borrow(Tracked(&slot_perm)).write_meta(metadata);

        if as_unique_ptr {
            // No one can create a `Frame` instance directly from the page
            // address, so `Relaxed` is fine here.
            let mut contents = slot.take(Tracked(&mut slot_perm));
            contents.ref_count.store(
                Tracked(&mut inner_perms.ref_count),
                REF_COUNT_UNIQUE,
            );
            slot.put(Tracked(&mut slot_perm), contents);
        } else {
            // `Release` is used to ensure that the metadata initialization
            // won't be reordered after this memory store.
            slot.borrow(Tracked(&slot_perm)).ref_count.store(Tracked(&mut inner_perms.ref_count), 1);
        }

        proof {
            slot_own.usage = PageUsage::Frame;
            slot_own.sync_inner(&inner_perms);
            regions.slot_owners.tracked_insert(frame_to_index(paddr), slot_own);

            assert(regions.inv());
        }

        let perm = MetaSlot::cast_perm::<M>(slot.addr(), Tracked(slot_perm), Tracked(inner_perms));

        Ok((slot, perm))
    }

    /// The inner loop of `Self::get_from_in_use`.
    /// # Verified Properties
    /// ## Preconditions
    /// - The permission must point to the slot.
    /// - The permission must be initialized.
    /// - **Liveness**: The reference count of the inner permissions must not be at the maximum.
    /// ## Postconditions
    /// - The reference count of the inner permissions is increased by one.
    #[verus_spec(res =>
        with Tracked(perm): Tracked<&vstd::simple_pptr::PointsTo<MetaSlot>>,
            Tracked(inner_perms): Tracked<&mut MetadataInnerPerms>,
        requires
            perm.pptr() == slot,
            perm.is_init(),
            perm.value().ref_count.id() == old(inner_perms).ref_count.id(),
            // In order to not panic, the reference count shouldn't be at the maximum.
            old(inner_perms).ref_count.value() + 1 < REF_COUNT_MAX,
        ensures
            res is Ok ==> inner_perms.ref_count.value() == old(inner_perms).ref_count.value() + 1,
            res is Err ==> inner_perms.ref_count.value() == old(inner_perms).ref_count.value(),
            inner_perms.ref_count.id() == old(inner_perms).ref_count.id(),
            inner_perms.storage == old(inner_perms).storage,
            inner_perms.vtable_ptr == old(inner_perms).vtable_ptr,
            inner_perms.in_list == old(inner_perms).in_list,
    )]
    fn get_from_in_use_loop(slot: PPtr<MetaSlot>) -> Result<PPtr<Self>, GetFrameError> {

        match slot.borrow(Tracked(perm)).ref_count.load(Tracked(&mut inner_perms.ref_count)) {
            REF_COUNT_UNUSED => {
                return Err(GetFrameError::Unused);
            },
            REF_COUNT_UNIQUE => {
                return Err(GetFrameError::Unique);
            },
            0 => {
                return Err(GetFrameError::Busy);
            },
            last_ref_cnt => {
                if last_ref_cnt >= REF_COUNT_MAX {
                    // See `Self::inc_ref_count` for the explanation.
                    assert(false)
                }
                // Using `Acquire` here to pair with `get_from_unused` or
                // `<Frame<M> as From<UniqueFrame<M>>>::from` (who must be
                // performed after writing the metadata).
                //
                // It ensures that the written metadata will be visible to us.

                if slot.borrow(Tracked(perm)).ref_count.compare_exchange_weak(
                    Tracked(&mut inner_perms.ref_count),
                    last_ref_cnt,
                    last_ref_cnt + 1,
                ).is_ok() {
                    return Ok(slot);
                } else {
                    return Err(GetFrameError::Retry);
                }
            },
        }
    }

    /// Gets another owning pointer to the metadata slot from the given page.
    /// # Verified Properties
    /// ## Verification Design
    /// To simplify the verification, we verify the loop body separately from the outer loop. We do not prove termination.
    /// ## Preconditions
    /// - **Safety Invariant**: Metaslot region invariants must hold.
    /// - **Bookkeeping**: The slot permissions must be available in order to check the reference count.
    /// This precondition is stronger than it needs to be; absent permissions correspond to error cases.
    /// - **Liveness**: The reference count of the inner permissions must not be at the maximum, or the function will panic.
    /// ## Postconditions
    /// - **Safety**: Metaslot region invariants hold after the call.
    /// - **Correctness**: If successful, the slot's reference count is increased by one.
    /// - **Correctness**: If unsuccessful, the metaslot region remains unchanged.
    /// ## Safety
    /// The potential data race is avoided by the spin-lock.
    #[verus_spec(res =>
        with Tracked(regions): Tracked<&mut MetaRegionOwners>
        requires
            old(regions).inv(),
            !Self::get_from_in_use_panic_cond(paddr, *old(regions)),
            old(regions).slots.contains_key(frame_to_index(paddr)),
            old(regions).slot_owners.contains_key(frame_to_index(paddr)),
            old(regions).slots[frame_to_index(paddr)].addr() == frame_to_meta(paddr),
            old(regions).slot_owners[frame_to_index(paddr)].inner_perms.ref_count.id() ==
                old(regions).slots[frame_to_index(paddr)].value().ref_count.id(),
        ensures
            regions.inv(),
            !has_safe_slot(paddr) ==> res is Err,
            res is Ok ==> Self::get_from_in_use_success(paddr, *old(regions), *regions),
            res matches Ok(ptr) ==> ptr == old(regions).slots[frame_to_index(paddr)].pptr(),
            res is Err ==> *regions == *old(regions),
    )]
    #[verifier::exec_allows_no_decreases_clause]
    pub(super) fn get_from_in_use(paddr: Paddr) -> Result<PPtr<Self>, GetFrameError> {

        let ghost regions0 = *regions;

        let slot = get_slot(paddr)?;

        let tracked mut slot_own = regions.slot_owners.tracked_remove(frame_to_index(paddr));
        let tracked mut slot_perm = regions.slots.tracked_remove(frame_to_index(paddr));
        let tracked mut inner_perms = slot_own.take_inner_perms();

        let ghost pre = inner_perms.ref_count.value();

        // Try to increase the reference count for an in-use frame. Otherwise fail.
        loop
            invariant
                has_safe_slot(paddr),
                slot_perm.addr() == slot.addr(),
                slot_perm.is_init(),
                slot_perm.value().ref_count.id() == inner_perms.ref_count.id(),
                inner_perms.ref_count.value() == pre,
                inner_perms.ref_count.value() + 1 < REF_COUNT_MAX,
                regions0.slots.contains_key(frame_to_index(paddr)),
                regions0.slot_owners.contains_key(frame_to_index(paddr)),
                regions0.inv(),
                regions0.slots[frame_to_index(paddr)] == slot_perm,
                !Self::get_from_in_use_panic_cond(paddr, *old(regions)),
        {
            match #[verus_spec(with Tracked(&slot_perm), Tracked(&mut inner_perms))]
                  Self::get_from_in_use_loop(slot) {
                Err(GetFrameError::Retry) => {
                    core::hint::spin_loop();
                },
                res => {
                    proof {
                        admit();

                        slot_own.sync_inner(&inner_perms);
                        regions.slot_owners.tracked_insert(frame_to_index(paddr), slot_own);
                        regions.slots.tracked_insert(frame_to_index(paddr), slot_perm);
                    }

                    return res;
                },
            }
        }
    }

    /// Increases the frame reference count by one.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Bookkeeping**: The permission must match the reference count being updated.
    /// - **Liveness**: The function will abort if the reference count is at the maximum.
    /// ## Postconditions
    /// - **Correctness**: The reference count is increased by one.
    /// ## Safety
    /// By requiring the caller to provide a permission for the reference count, we ensure that it already has a reference to the frame.
    #[verus_spec(
        with Tracked(rc_perm): Tracked<&mut PermissionU64>
    )]
    pub(super) fn inc_ref_count(&self)
        requires
            old(rc_perm).is_for(self.ref_count),
            !Self::inc_ref_count_panic_cond(*old(rc_perm)),
        ensures
            rc_perm.value() == old(rc_perm).value() + 1,
    {
        let last_ref_cnt = self.ref_count.fetch_add(Tracked(rc_perm), 1);

        if last_ref_cnt >= REF_COUNT_MAX {
            // This follows the same principle as the `Arc::clone` implementation to prevent the
            // reference count from overflowing. See also
            // <https://doc.rust-lang.org/std/sync/struct.Arc.html#method.clone>.
            assert(false);
        }
    }

    /// Gets the corresponding frame's physical address.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety**: The permission must point to a valid metadata slot.
    /// - **Correctness**: The permission must point to the metadata slot.
    /// ## Postconditions
    /// - **Correctness**: The function returns the physical address of the frame.
    /// ## Safety
    /// The safety precondition requires that the permission points to a valid metadata slot.
    /// This is an internal function, so it is fine to require the caller to verify this.
    #[verus_spec(
        with Tracked(perm): Tracked<&vstd::simple_pptr::PointsTo<MetaSlot>>,
        requires
            perm.value() == self,
            Self::frame_paddr_safety_cond(*perm),
        returns
            meta_to_frame(perm.addr()),
    )]
    pub(super) fn frame_paddr(&self) -> (pa: Paddr) {
        let addr = self.addr_of(Tracked(perm));
        meta_to_frame(addr)
    }

    /*
    /// Gets a dynamically typed pointer to the stored metadata.
    ///
    /// # Safety
    ///
    /// The caller should ensure that:
    ///  - the stored metadata is initialized (by [`Self::write_meta`]) and valid.
    ///
    /// The returned pointer should not be dereferenced as mutable unless having
    /// exclusive access to the metadata slot.

    #[verifier::external_body]
    pub(super) unsafe fn dyn_meta_ptr<M: AnyFrameMeta>(&self) -> PPtr<M> {
        unimplemented!()

        // SAFETY: The page metadata is valid to be borrowed immutably, since
        // it will never be borrowed mutably after initialization.
        let vtable_ptr = unsafe { *self.vtable_ptr.get() };

        // SAFETY: The page metadata is initialized and valid.
        let vtable_ptr = *unsafe { vtable_ptr.assume_init_ref() };

        let meta_ptr: *mut dyn AnyFrameMeta =
            core::ptr::from_raw_parts_mut(self as *const MetaSlot as *mut MetaSlot, vtable_ptr);

        meta_ptr
    }*/

    /// Gets the stored metadata as type `M`.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety**: The caller must provide an existing permission that matches the contents of the metadata slot.
    /// ## Postconditions
    /// - **Correctness**: The function returns a pointer to the stored metadata, of type `M`.
    /// ## Safety
    /// - Calling the method is always safe, but using the returned pointer could
    /// be unsafe. Specifically, the dereferencer should ensure that:
    ///  - the stored metadata is initialized (by [`Self::write_meta`]) and valid;
    ///  - the initialized metadata is of type `M` (`Repr<M>::wf`);
    ///  - the returned pointer should not be dereferenced as mutable unless having exclusive access to the metadata slot.
    #[verus_spec(
        with Tracked(perm): Tracked<&vstd::simple_pptr::PointsTo<MetaSlot>>
    )]
    pub(super) fn as_meta_ptr<M: AnyFrameMeta + Repr<MetaSlotStorage>>(&self) -> (res: ReprPtr<MetaSlot, Metadata<M>>)
        requires
            self == perm.value(),
        ensures
            res.ptr.addr() == perm.addr(),
            res.addr == perm.addr(),
    {
        let addr = self.addr_of(Tracked(perm));
        self.cast_slot(addr, Tracked(perm))
    }

    /// Writes the metadata to the slot without reading or dropping the previous value.
    ///
    /// # Verification Design
    /// This function is axiomatized for now because of trait constraints.
    /// ## Preconditions
    /// - The caller must provide the permission token to the metadata slot's storage.
    /// ## Postconditions
    /// - The permission is initialized to the new metadata.
    /// ## Safety
    /// The caller must have exclusive access to the metadata slot's storage in order to provide the permission token.
    #[verus_spec(
        with Tracked(meta_perm): Tracked<&mut cell::PointsTo<MetaSlotStorage>>,
            Tracked(vtable_perm): Tracked<&mut vstd::simple_pptr::PointsTo<usize>>
        requires
            self.storage.id() === old(meta_perm).id(),
            self.vtable_ptr == old(vtable_perm).pptr(),
            old(vtable_perm).is_uninit(),
        ensures
            meta_perm.id() == old(meta_perm).id(),
            meta_perm.is_init(),
            vtable_perm.pptr() == old(vtable_perm).pptr(),
            vtable_perm.is_init(),
            Metadata::<M>::metadata_from_inner_perms(*meta_perm) == metadata,
    )]
    #[verifier::external_body]
    pub(super) fn write_meta<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf>(&self, metadata: M)
    {
        //        const { assert!(size_of::<M>() <= FRAME_METADATA_MAX_SIZE) };
        //        const { assert!(align_of::<M>() <= FRAME_METADATA_MAX_ALIGN) };
        // SAFETY: Caller ensures that the access to the fields are exclusive.
        //        let vtable_ptr = unsafe { &mut *self.vtable_ptr.get() };
        //        vtable_ptr.write(core::ptr::metadata(&metadata as &dyn AnyFrameMeta));
        let ptr = &self.storage;

        // SAFETY:
        // 1. `ptr` points to the metadata storage.
        // 2. The size and the alignment of the metadata storage is large enough to hold `M`
        //    (guaranteed by the const assertions above).
        // 3. We have exclusive access to the metadata storage (guaranteed by the caller).
        //ReprPtr::<MetaSlot, M>::new_borrowed(ptr).put(Tracked(slot_own.storage.borrow_mut()), &metadata);
    }

    /// Drops the metadata and deallocates the frame.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariant**: The metadata slot must satisfy the safety invariants.
    /// - **Safety**: The caller must provide an owner object for the metadata slot, which must include the permission for the
    /// slot's `ref_count` field.
    /// - **Safety**: The owner must satisfy [`drop_last_in_place_safety_cond`], which ensures that its reference count is 0
    /// and it has no dangling raw pointers.
    /// ## Postconditions
    /// - **Safety**: The metadata slot satisfies the safety invariants after the call.
    /// - **Correctness**: The reference count is set to `REF_COUNT_UNUSED` and the contents of the slot are uninitialized.
    /// ## Safety
    /// - By requiring the caller to provide an owner object, we ensure that it already has a reference to the frame.
    /// - The safety precondition ensures that there are no dangling pointers, including raw pointer, guaranteeing temporal safety.
    #[verus_spec(
        with Tracked(owner): Tracked<&mut MetaSlotOwner>
    )]
    pub(super) fn drop_last_in_place(&self)
        requires
            old(owner).inv(),
            self.ref_count.id() == old(owner).inner_perms.ref_count.id(),
            Self::drop_last_in_place_safety_cond(*old(owner)),
        ensures
            owner.inv(),
            owner.inner_perms.ref_count.value() == REF_COUNT_UNUSED,
            owner.inner_perms.ref_count.id() == old(owner).inner_perms.ref_count.id(),
            owner.inner_perms.storage.id() == old(owner).inner_perms.storage.id(),
            owner.inner_perms.storage.is_uninit(),
            owner.inner_perms.vtable_ptr.is_uninit(),
            owner.inner_perms.vtable_ptr.pptr() == old(owner).inner_perms.vtable_ptr.pptr(),
            owner.inner_perms.in_list == old(owner).inner_perms.in_list,
            owner.self_addr == old(owner).self_addr,
            owner.usage == old(owner).usage,
            owner.raw_count == old(owner).raw_count,
            owner.path_if_in_pt == old(owner).path_if_in_pt,
    {
        // This should be guaranteed as a safety requirement.
        //        debug_assert_eq!(self.ref_count.load(Tracked(&*rc_perm)), 0);
        // SAFETY: The caller ensures safety.
        #[verus_spec(with Tracked(owner))]
        self.drop_meta_in_place();

        let tracked mut inner_perms = owner.take_inner_perms();

        // `Release` pairs with the `Acquire` in `Frame::from_unused` and ensures
        // `drop_meta_in_place` won't be reordered after this memory store.
        self.ref_count.store(Tracked(&mut inner_perms.ref_count), REF_COUNT_UNUSED);

        proof {
            owner.sync_inner(&inner_perms);
        }
    }

    /// Drops the metadata of a slot in place.
    ///
    /// After this operation, the metadata becomes uninitialized. Any access to the
    /// metadata is undefined behavior unless it is re-initialized by [`Self::write_meta`].
    ///
    /// # Verification Design
    /// This function is axiomatized because of its reliance on dynamic trait methods and `VmReader`.
    /// The latter dependency makes it part of the "bootstrap gap".
    /// Now that Verus better supports the `dyn Trait` pattern and we have verified `VmReader`, we can revisit it.
    /// ## Preconditions
    /// - The caller must provide an owner object for the metadata slot.
    /// - The reference count must be 0
    /// ## Safety
    ///
    /// The caller should ensure that:
    ///  - the reference count is `0` (so we are the sole owner of the frame);
    ///  - the metadata is initialized;
    #[verifier::external_body]
    #[verus_spec(
        with Tracked(slot_own): Tracked<&mut MetaSlotOwner>
        requires
            old(slot_own).inner_perms.ref_count.value() == 0 || old(slot_own).inner_perms.ref_count.value() == REF_COUNT_UNIQUE,
            old(slot_own).inner_perms.storage.is_init(),
            old(slot_own).inner_perms.in_list.value() == 0,
        ensures
            slot_own.inner_perms.ref_count == old(slot_own).inner_perms.ref_count,
            slot_own.inner_perms.storage.is_uninit(),
            slot_own.inner_perms.storage.id() == old(slot_own).inner_perms.storage.id(),
            slot_own.inner_perms.in_list == old(slot_own).inner_perms.in_list,
            slot_own.inner_perms.vtable_ptr.is_uninit(),
            slot_own.inner_perms.vtable_ptr.pptr() == old(slot_own).inner_perms.vtable_ptr.pptr(),
            slot_own.self_addr == old(slot_own).self_addr,
            slot_own.usage == old(slot_own).usage,
            slot_own.raw_count == old(slot_own).raw_count,
            slot_own.path_if_in_pt == old(slot_own).path_if_in_pt,
    )]
    #[verifier::external_body]
    pub(super) fn drop_meta_in_place(&self) {
        unimplemented!()/*        let paddr = self.frame_paddr();

        // SAFETY: We have exclusive access to the frame metadata.
        let vtable_ptr = unsafe { &mut *self.vtable_ptr.get() };
        // SAFETY: The frame metadata is initialized and valid.
        let vtable_ptr = unsafe { vtable_ptr.assume_init_read() };

        let meta_ptr: *mut dyn AnyFrameMeta =
            core::ptr::from_raw_parts_mut(self.storage.get(), vtable_ptr);

        // SAFETY: The implementer of the frame metadata decides that if the frame
        // is safe to be read or not.
        let mut reader =
            unsafe { VmReader::from_kernel_space(paddr_to_vaddr(paddr) as *const u8, PAGE_SIZE) };

        // SAFETY: `ptr` points to the metadata storage which is valid to be mutably borrowed under
        // `vtable_ptr` because the metadata is valid, the vtable is correct, and we have the exclusive
        // access to the frame metadata.
        unsafe {
            // Invoke the custom `on_drop` handler.
            (*meta_ptr).on_drop(&mut reader);
            // Drop the frame metadata.
            core::ptr::drop_in_place(meta_ptr);
        }*/

    }
}

/// The metadata of frames that holds metadata of frames.
#[derive(Debug, Default)]
pub struct MetaPageMeta {}

//impl_frame_meta_for!(MetaPageMeta);
/*
/// Initializes the metadata of all physical frames.
///
/// The function returns a list of `Frame`s containing the metadata.
///
/// # Safety
///
/// This function should be called only once and only on the BSP,
/// before any APs are started.
pub(crate) unsafe fn init() -> Segment<MetaPageMeta> {
    let max_paddr = {
        let regions = &crate::boot::EARLY_INFO.get().unwrap().memory_regions;
        regions
            .iter()
            .filter(|r| r.typ() == MemoryRegionType::Usable)
            .map(|r| r.base() + r.len())
            .max()
            .unwrap()
    };

    info!(
        "Initializing frame metadata for physical memory up to {:x}",
        max_paddr
    );

    // In RISC-V, the boot page table has mapped the 512GB memory,
    // so we don't need to add temporary linear mapping.
    // In LoongArch, the DWM0 has mapped the whole memory,
    // so we don't need to add temporary linear mapping.
    #[cfg(target_arch = "x86_64")]
    add_temp_linear_mapping(max_paddr);

    let tot_nr_frames = max_paddr / page_size::<PagingConsts>(1);
    let (nr_meta_pages, meta_pages) = alloc_meta_frames(tot_nr_frames);

    // Map the metadata frames.
    boot_pt::with_borrow(|boot_pt| {
        for i in 0..nr_meta_pages {
            let frame_paddr = meta_pages + i * PAGE_SIZE;
            let vaddr = frame_to_meta::<PagingConsts>(0) + i * PAGE_SIZE;
            let prop = PageProperty {
                flags: PageFlags::RW,
                cache: CachePolicy::Writeback,
                priv_flags: PrivilegedPageFlags::GLOBAL,
            };
            // SAFETY: we are doing the metadata mappings for the kernel.
            unsafe { boot_pt.map_base_page(vaddr, frame_paddr / PAGE_SIZE, prop) };
        }
    })
    .unwrap();

    // Now the metadata frames are mapped, we can initialize the metadata.
    super::MAX_PADDR.store(max_paddr, Ordering::Relaxed);

    let meta_page_range = meta_pages..meta_pages + nr_meta_pages * PAGE_SIZE;

    let (range_1, range_2) = allocator::EARLY_ALLOCATOR
        .lock()
        .as_ref()
        .unwrap()
        .allocated_regions();
    for r in range_difference(&range_1, &meta_page_range) {
        let early_seg = Segment::from_unused(r, |_| EarlyAllocatedFrameMeta).unwrap();
        let _ = ManuallyDrop::new(early_seg);
    }
    for r in range_difference(&range_2, &meta_page_range) {
        let early_seg = Segment::from_unused(r, |_| EarlyAllocatedFrameMeta).unwrap();
        let _ = ManuallyDrop::new(early_seg);
    }

    mark_unusable_ranges();

    Segment::from_unused(meta_page_range, |_| MetaPageMeta {}).unwrap()
}

/// Returns whether the global frame allocator is initialized.
pub(in crate::mm) fn is_initialized() -> bool {
    // `init` sets it with relaxed ordering somewhere in the middle. But due
    // to the safety requirement of the `init` function, we can assume that
    // there is no race conditions.
    super::MAX_PADDR.load(Ordering::Relaxed) != 0
}

fn alloc_meta_frames(tot_nr_frames: usize) -> (usize, Paddr) {
    let nr_meta_pages = tot_nr_frames
        .checked_mul(size_of::<MetaSlot>())
        .unwrap()
        .div_ceil(PAGE_SIZE);
    let start_paddr = allocator::early_alloc(
        Layout::from_size_align(nr_meta_pages * PAGE_SIZE, PAGE_SIZE).unwrap(),
    )
    .unwrap();

    let slots = paddr_to_vaddr(start_paddr) as *mut MetaSlot;

    // Initialize the metadata slots.
    for i in 0..tot_nr_frames {
        // SAFETY: The memory is successfully allocated with `tot_nr_frames`
        // slots so the index must be within the range.
        let slot = unsafe { slots.add(i) };
        // SAFETY: The memory is just allocated so we have exclusive access and
        // it's valid for writing.
        unsafe {
            slot.write(MetaSlot {
                storage: UnsafeCell::new(MetaSlotStorage::Empty([0; FRAME_METADATA_MAX_SIZE - 1])),
                ref_count: AtomicU64::new(REF_COUNT_UNUSED),
                vtable_ptr: UnsafeCell::new(MaybeUninit::uninit()),
                in_list: AtomicU64::new(0),
            })
        };
    }

    (nr_meta_pages, start_paddr)
}

/// Unusable memory metadata. Cannot be used for any purposes.
#[derive(Debug)]
pub struct UnusableMemoryMeta;
impl_frame_meta_for!(UnusableMemoryMeta);

/// Reserved memory metadata. Maybe later used as I/O memory.
#[derive(Debug)]
pub struct ReservedMemoryMeta;
impl_frame_meta_for!(ReservedMemoryMeta);

/// The metadata of physical pages that contains the kernel itself.
#[derive(Debug, Default)]
pub struct KernelMeta;
impl_frame_meta_for!(KernelMeta);

macro_rules! mark_ranges {
    ($region: expr, $typ: expr) => {{
        debug_assert!($region.base() % PAGE_SIZE == 0);
        debug_assert!($region.len() % PAGE_SIZE == 0);

        let seg = Segment::from_unused($region.base()..$region.end(), |_| $typ).unwrap();
        let _ = ManuallyDrop::new(seg);
    }};
}

fn mark_unusable_ranges() {
    let regions = &crate::boot::EARLY_INFO.get().unwrap().memory_regions;

    for region in regions
        .iter()
        .rev()
        .skip_while(|r| r.typ() != MemoryRegionType::Usable)
    {
        match region.typ() {
            MemoryRegionType::BadMemory => mark_ranges!(region, UnusableMemoryMeta),
            MemoryRegionType::Unknown => mark_ranges!(region, ReservedMemoryMeta),
            MemoryRegionType::NonVolatileSleep => mark_ranges!(region, UnusableMemoryMeta),
            MemoryRegionType::Reserved => mark_ranges!(region, ReservedMemoryMeta),
            MemoryRegionType::Kernel => mark_ranges!(region, KernelMeta),
            MemoryRegionType::Module => mark_ranges!(region, UnusableMemoryMeta),
            MemoryRegionType::Framebuffer => mark_ranges!(region, ReservedMemoryMeta),
            MemoryRegionType::Reclaimable => mark_ranges!(region, UnusableMemoryMeta),
            MemoryRegionType::Usable => {} // By default it is initialized as usable.
        }
    }
}

/// Adds a temporary linear mapping for the metadata frames.
///
/// We only assume boot page table to contain 4G linear mapping. Thus if the
/// physical memory is huge we end up depleted of linear virtual memory for
/// initializing metadata.
#[cfg(target_arch = "x86_64")]
fn add_temp_linear_mapping(max_paddr: Paddr) {
    const PADDR4G: Paddr = 0x1_0000_0000;

    if max_paddr <= PADDR4G {
        return;
    }

    // TODO: We don't know if the allocator would allocate from low to high or
    // not. So we prepare all linear mappings in the boot page table. Hope it
    // won't drag the boot performance much.
    let end_paddr = max_paddr.align_up(PAGE_SIZE);
    let prange = PADDR4G..end_paddr;
    let prop = PageProperty {
        flags: PageFlags::RW,
        cache: CachePolicy::Writeback,
        priv_flags: PrivilegedPageFlags::GLOBAL,
    };

    // SAFETY: we are doing the linear mapping for the kernel.
    unsafe {
        boot_pt::with_borrow(|boot_pt| {
            for paddr in prange.step_by(PAGE_SIZE) {
                let vaddr = LINEAR_MAPPING_BASE_VADDR + paddr;
                boot_pt.map_base_page(vaddr, paddr / PAGE_SIZE, prop);
            }
        })
        .unwrap();
    }
}
*/
} // verus!
