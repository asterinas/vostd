// SPDX-License-Identifier: MPL-2.0
//! The unique frame pointer that is not shared with others.
use vstd::atomic::PermissionU64;
use vstd::prelude::*;
use vstd::simple_pptr::{self, PPtr};

use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;

use vstd_extra::cast_ptr::*;
use vstd_extra::ownership::*;
use vstd_extra::undroppable::*;

use super::meta::{AnyFrameMeta, GetFrameError, MetaSlot, has_safe_slot};

use core::{marker::PhantomData, mem::ManuallyDrop, sync::atomic::Ordering};

use super::meta::mapping::{
    frame_to_index, frame_to_meta, max_meta_slots, meta_addr, meta_to_frame, META_SLOT_SIZE,
};
use super::meta::{REF_COUNT_UNIQUE, REF_COUNT_UNUSED};
use crate::mm::{Paddr, PagingLevel, MAX_NR_PAGES, MAX_PADDR, PAGE_SIZE};
use crate::mm::frame::MetaPerm;
use crate::specs::arch::kspace::FRAME_METADATA_RANGE;
use crate::specs::arch::paging_consts::PagingConsts;
use crate::specs::mm::frame::unique::UniqueFrameOwner;

verus! {

pub struct UniqueFrame<M: AnyFrameMeta + Repr<MetaSlot> + OwnerOf> {
    pub ptr: PPtr<MetaSlot>,
    pub _marker: PhantomData<M>,
}

#[verus_verify]
impl<M: AnyFrameMeta + Repr<MetaSlot> + OwnerOf> UniqueFrame<M> {
    /// Gets a [`UniqueFrame`] with a specific usage from a raw, unused page.
    ///
    /// The caller should provide the initial metadata of the page.
    /// # Verified Properties
    /// ## Preconditions
    /// The page must be unused and the metadata region must be well-formed.
    /// ## Postconditions
    /// If the page is valid, the function returns a unique frame.
    /// ## Safety
    /// If `paddr` is misaligned or out of bounds, the function will return an error. If it returns a frame,
    /// it also returns an owner for that frame, indicating that the caller now has exclusive ownership of it.
    /// See [Safe Encapsulation] for more details.
    #[verus_spec(res =>
        with Tracked(regions): Tracked<&mut MetaRegionOwners>
        -> owner: Tracked<Option<UniqueFrameOwner<M>>>
        requires
            old(regions).slot_owners[frame_to_index(paddr)].usage is Unused,
            old(regions).inv(),
        ensures
            has_safe_slot(paddr) ==> res is Ok,
            res is Ok ==> res.unwrap().wf(owner@.unwrap()),
    )]
    pub fn from_unused(paddr: Paddr, metadata: M) -> Result<Self, GetFrameError>
    {
        #[verus_spec(with Tracked(regions))]
        let from_unused = MetaSlot::get_from_unused(paddr, metadata, true);

        if let Err(err) = from_unused {
            proof_with!(|= Tracked(None));
            Err(err)
        } else {
            let ptr = from_unused.unwrap();
            proof_decl! {
                let tracked owner = UniqueFrameOwner::<M>::from_unused_owner(regions, paddr, metadata);
            } 
            proof_with!(|= Tracked(Some(owner)));
            Ok(Self { ptr, _marker: PhantomData })
        }
    }

    pub open spec fn transmute_spec<M1: AnyFrameMeta + Repr<MetaSlot> + OwnerOf>(self, transmuted: UniqueFrame<M1>) -> bool {
        &&& transmuted.ptr.addr() == self.ptr.addr()
        &&& transmuted._marker == PhantomData::<M1>
    }

    #[verifier::external_body]
    pub fn transmute<M1: AnyFrameMeta + Repr<MetaSlot> + OwnerOf>(self) -> (res: UniqueFrame<M1>)
        ensures
            Self::transmute_spec(self, res)
    {
        unimplemented!()
    }

    /// Repurposes the frame with a new metadata.
    /// # Verified Properties
    /// ## Preconditions
    /// The caller must provide a valid owner for the frame, and the metadata region invariants must hold.
    /// The frame must be tracked by the metadata region, not forgotten.
    /// The meta slot's reference count must be `REF_COUNT_UNIQUE`.
    /// ## Postconditions
    /// The function returns a new owner for the frame with the new metadata,
    /// and the metadata region invariants are preserved.
    /// ## Safety
    /// The existence of a valid owner guarantees that the memory is initialized with metadata of type `M`,
    /// and represents that the caller has exclusive ownership of the frame.
    #[verus_spec(res =>
        with Tracked(owner): Tracked<UniqueFrameOwner<M>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>
        -> new_owner: Tracked<UniqueFrameOwner<M1>>
        requires
            self.wf(owner),
            owner.inv(),
            old(regions).slots.contains_key(frame_to_index(meta_to_frame(self.ptr.addr()))),
            old(regions).slot_owners.contains_key(frame_to_index(meta_to_frame(self.ptr.addr()))),
            old(regions).slot_owners[frame_to_index(meta_to_frame(self.ptr.addr()))].ref_count.value() == REF_COUNT_UNIQUE,
            old(regions).inv(),
        ensures
            res.wf(new_owner@),
            new_owner@.meta_perm.value() == metadata,
            regions.inv(),
    )]
    pub fn repurpose<M1: AnyFrameMeta + Repr<MetaSlot> + OwnerOf>(self, metadata: M1) -> UniqueFrame<M1> {
        assert(regions.slots.contains_key(frame_to_index(meta_to_frame(self.ptr.addr())))) by { admit() };
        assert(regions.slots[frame_to_index(meta_to_frame(self.ptr.addr()))].addr() == self.ptr.addr()) by { admit() };

        let tracked mut slot_own = regions.slot_owners.tracked_remove(frame_to_index(meta_to_frame(self.ptr.addr())));
        let tracked mut slot_perm = regions.slots.tracked_remove(frame_to_index(meta_to_frame(self.ptr.addr())));

        assert(slot_own.storage.addr() == slot_perm.value().storage.addr()) by { admit() };

        #[verus_spec(with Tracked(&slot_perm))]
        let slot = self.slot();

        // SAFETY: We are the sole owner and the metadata is initialized.
        #[verus_spec(with Tracked(&mut slot_own))]
        slot.drop_meta_in_place();

        proof_decl! {
            let tracked new_owner = UniqueFrameOwner::<M1>::from_unused_owner(regions, meta_to_frame(self.ptr.addr()), metadata);
        }

        // SAFETY: We are the sole owner.
        #[verus_spec(with Tracked(&mut slot_own), Tracked(&mut new_owner.meta_perm))]
        slot.write_meta(metadata);

        proof {
            regions.slot_owners.tracked_insert(frame_to_index(meta_to_frame(self.ptr.addr())), slot_own);
            regions.slots.tracked_insert(frame_to_index(meta_to_frame(self.ptr.addr())), slot_perm);
        }

        // SAFETY: The metadata is initialized with type `M1`.
        proof_with!(|= Tracked(new_owner));
        self.transmute()
    }

    /// Gets the metadata of this page.
    /// Note that this function body differs from the original, because `as_meta_ptr` returns
    /// a `ReprPtr<MetaSlot, M>` instead of a `*M`. So in order to keep the immutable borrow, we
    /// borrow the metadata value from that pointer.
    /// # Verified Properties
    /// ## Preconditions
    /// The caller must provide a valid owner for the frame.
    /// ## Postconditions
    /// The function returns the metadata of the frame.
    /// ## Safety
    /// The existence of a valid owner guarantees that the memory is initialized with metadata of type `M`,
    /// and represents that the caller has exclusive ownership of the frame.
    #[verus_spec(
        with Tracked(owner): Tracked<&'a UniqueFrameOwner<M>>
    )]
    pub fn meta<'a>(&self) -> (l: &'a M)
        requires
            owner.inv(),
            self.wf(*owner),
        ensures
            owner.meta_perm.mem_contents().value() == l,
    {
        // SAFETY: The type is tracked by the type system.
        #[verus_spec(with Tracked(&owner.meta_perm.points_to))]
        let slot = self.slot();

        #[verus_spec(with Tracked(&owner.meta_perm.points_to))]
        let ptr = slot.as_meta_ptr();

        ptr.borrow(Tracked(&owner.meta_perm))
    }

    /// Gets the mutable metadata of this page.
    /// Verified Properties
    /// ## Preconditions
    /// The caller must provide a valid owner for the frame.
    /// ## Postconditions
    /// The function returns the mutable metadata of the frame.
    /// ## Safety
    /// The existence of a valid owner guarantees that the memory is initialized with metadata of type `M`,
    /// and represents that the caller has exclusive ownership of the frame. (See [Safe Encapsulation])
    #[verus_spec(
        with Tracked(owner): Tracked<&UniqueFrameOwner<M>>
    )]
    pub fn meta_mut(&mut self) -> (res: ReprPtr<MetaSlot, M>)
        requires
            owner.inv(),
            old(self).wf(*owner),
        ensures
            res.addr() == self.ptr.addr(),
            res.ptr.addr() == self.ptr.addr(),
            *self == *old(self),
    {
        // SAFETY: The type is tracked by the type system.
        // And we have the exclusive access to the metadata.
        #[verus_spec(with Tracked(&owner.meta_perm.points_to))]
        let slot = self.slot();

        #[verus_spec(with Tracked(&owner.meta_perm.points_to))]
        slot.as_meta_ptr()
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlot> + OwnerOf + ?Sized> UniqueFrame<M> {
    /// Gets the physical address of the start of the frame.
    #[verus_spec(
        with Tracked(owner): Tracked<&UniqueFrameOwner<M>>,
        requires
            owner.inv(),
            self.wf(*owner),
        returns
            meta_to_frame(self.ptr.addr()),
    )]
    pub fn start_paddr(&self) -> Paddr {
        
        #[verus_spec(with Tracked(&owner.meta_perm.points_to))]
        let slot = self.slot();

        #[verus_spec(with Tracked(&owner.meta_perm.points_to))]
        slot.frame_paddr()
    }

    /// Gets the paging level of this page.
    ///
    /// This is the level of the page table entry that maps the frame,
    /// which determines the size of the frame.
    ///
    /// Currently, the level is always 1, which means the frame is a regular
    /// page frame.
    pub const fn level(&self) -> PagingLevel {
        1
    }

    /// Gets the size of this page in bytes.
    pub const fn size(&self) -> usize {
        PAGE_SIZE
    }

    /*    /// Gets the dynamically-typed metadata of this frame.
    ///
    /// If the type is known at compile time, use [`Frame::meta`] instead.
    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub fn dyn_meta(&self) -> &M {
        // SAFETY: The metadata is initialized and valid.
        unsafe { &*self.slot().dyn_meta_ptr::<M>() }
    }

    /// Gets the dynamically-typed metadata of this frame.
    ///
    /// If the type is known at compile time, use [`Frame::meta`] instead.
    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub fn dyn_meta_mut(&mut self) -> &mut FrameMeta {
        // SAFETY: The metadata is initialized and valid. We have the exclusive
        // access to the frame.
        unsafe { &mut *self.slot().dyn_meta_ptr() }
    }*/

    pub open spec fn into_raw_requires(self, regions: MetaRegionOwners) -> bool {
        &&& regions.slots.contains_key(frame_to_index(meta_to_frame(self.ptr.addr())))
        &&& !regions.dropped_slots.contains_key(frame_to_index(meta_to_frame(self.ptr.addr())))
        &&& regions.inv()
    }

    pub open spec fn into_raw_ensures(
        self,
        old_regions: MetaRegionOwners,
        regions: MetaRegionOwners,
        r: Paddr,
    ) -> bool {
        &&& r == meta_to_frame(self.ptr.addr())
        &&& regions.inv()
        &&& regions.slots == old_regions.slots.remove(frame_to_index(meta_to_frame(self.ptr.addr())))
        &&& regions.dropped_slots == old_regions.dropped_slots.insert(frame_to_index(meta_to_frame(self.ptr.addr())),
            old_regions.slots[frame_to_index(meta_to_frame(self.ptr.addr()))])
    }

    /*
    /// Resets the frame to unused without up-calling the allocator.
    ///
    /// This is solely useful for the allocator implementation/testing and
    /// is highly experimental. Usage of this function is discouraged.
    ///
    /// Usage of this function other than the allocator would actually leak
    /// the frame since the allocator would not be aware of the frame.
    //
    // FIXME: We may have a better `Segment` and `UniqueSegment` design to
    // allow the allocator hold the ownership of all the frames in a chunk
    // instead of the head. Then this weird public API can be `#[cfg(ktest)]`.
    pub fn reset_as_unused(self) {
        let this = ManuallyDrop::new(self);

        this.slot().ref_count.store(0, Ordering::Release);
        // SAFETY: We are the sole owner and the reference count is 0.
        // The slot is initialized.
        unsafe { this.slot().drop_last_in_place() };
    }*/

    /// Converts this frame into a raw physical address.
    #[verus_spec(r =>
        with Tracked(owner): Tracked<&UniqueFrameOwner<M>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>
        requires
            Self::into_raw_requires(self, *old(regions)),
            self.wf(*owner),
            owner.inv(),
        ensures
            Self::into_raw_ensures(self, *old(regions), *regions, r),
    )]
    pub(crate) fn into_raw(self) -> Paddr
    {
        assert(regions.slots[frame_to_index(meta_to_frame(self.ptr.addr()))].addr() == self.ptr.addr()) by { admit() };
        #[verus_spec(with Tracked(owner))]
        let paddr = self.start_paddr();

        let _ = NeverDrop::new(self, Tracked(regions));

        paddr
    }

    /// Restores a raw physical address back into a unique frame.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the physical address is valid and points to
    /// a forgotten frame that was previously casted by [`Self::into_raw`].
    #[verus_spec(res =>
        with Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(meta_perm): Tracked<PointsTo<MetaSlot, M>>,
            Tracked(meta_own): Tracked<M::Owner>
    )]
    #[verifier::external_body]
    pub(crate) fn from_raw(paddr: Paddr) -> (res: (Self, Tracked<UniqueFrameOwner<M>>))
        requires
            paddr < MAX_PADDR,
            paddr % PAGE_SIZE == 0,
            old(regions).dropped_slots.contains_key(frame_to_index(paddr)),
        ensures
            res.0.ptr.addr() == frame_to_meta(paddr),
            res.0.wf(res.1@),
            res.1@.meta_own == meta_own,
            res.1@.meta_perm == meta_perm,
            regions.slots[frame_to_index(paddr)] == old(regions).dropped_slots[frame_to_index(
                paddr,
            )],
            !regions.dropped_slots.contains_key(frame_to_index(paddr)),
            regions.slots == old(regions).slots,
            regions.slot_owners == old(regions).slot_owners,
    {
        let vaddr = frame_to_meta(paddr);
        let ptr = vstd::simple_pptr::PPtr::<MetaSlot>::from_addr(vaddr);

        let tracked slot_own = regions.dropped_slots.tracked_remove(frame_to_index(paddr));
        proof { regions.slots.tracked_insert(frame_to_index(paddr), slot_own) }

        (
            Self { ptr, _marker: PhantomData },
            Tracked(
                UniqueFrameOwner::<M>::from_raw_owner(
                    meta_own,
                    Ghost(frame_to_index(paddr)),
                    meta_perm,
                ),
            ),
        )
    }

    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    #[verus_spec(
        with Tracked(slot_perm): Tracked<&'a vstd::simple_pptr::PointsTo<MetaSlot>>
    )]
    pub fn slot<'a>(&self) -> &'a MetaSlot
        requires
            slot_perm.pptr() == self.ptr,
            slot_perm.is_init(),
        returns
            slot_perm.value(),
    {
        unimplemented!()
        // SAFETY: `ptr` points to a valid `MetaSlot` that will never be
        // mutably borrowed, so taking an immutable reference to it is safe.
        //        unsafe { &*self.ptr }

    }
}

/*impl<M: AnyFrameMeta + ?Sized> Drop for UniqueFrame<M> {
    fn drop(&mut self) {
        self.slot().ref_count.store(0, Ordering::Relaxed);
        // SAFETY: We are the sole owner and the reference count is 0.
        // The slot is initialized.
        unsafe { self.slot().drop_last_in_place() };

        super::allocator::get_global_frame_allocator().dealloc(self.start_paddr(), PAGE_SIZE);
    }
}*/
/*impl<M: AnyFrameMeta> From<UniqueFrame<Link<M>>> for Frame<M> {
    #[verifier::external_body]
    fn from(unique: UniqueFrame<Link<M>>) -> Self {
        unimplemented!()/*
        // The `Release` ordering make sure that previous writes are visible
        // before the reference count is set to 1. It pairs with
        // `MetaSlot::get_from_in_use`.
        unique.slot().ref_count.store(1, Ordering::Release);
        // SAFETY: The internal representation is now the same.
        unsafe { core::mem::transmute(unique) }*/

    }
}*/
/*impl<M: AnyFrameMeta> TryFrom<Frame<M>> for UniqueFrame<Link<M>> {
    type Error = Frame<M>;

    #[verifier::external_body]
    /// Tries to get a unique frame from a shared frame.
    ///
    /// If the reference count is not 1, the frame is returned back.
    fn try_from(frame: Frame<M>) -> Result<Self, Self::Error> {
        unimplemented!()/*        match frame.slot().ref_count.compare_exchange(
            1,
            REF_COUNT_UNIQUE,
            Ordering::Relaxed,
            Ordering::Relaxed,
        ) {
            Ok(_) => {
                // SAFETY: The reference count is now `REF_COUNT_UNIQUE`.
                Ok(unsafe { core::mem::transmute::<Frame<M>, UniqueFrame<M>>(frame) })
            }
            Err(_) => Err(frame),
        }*/

    }
}*/
} // verus!
