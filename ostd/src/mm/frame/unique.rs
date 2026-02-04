// SPDX-License-Identifier: MPL-2.0
//! The unique frame pointer that is not shared with others.
use vstd::atomic::PermissionU64;
use vstd::prelude::*;
use vstd::simple_pptr::{self, PPtr};

use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;

use vstd_extra::cast_ptr::*;
use vstd_extra::ownership::*;

use super::meta::{AnyFrameMeta, GetFrameError, MetaSlot};

use core::{marker::PhantomData, mem::ManuallyDrop, sync::atomic::Ordering};

use super::meta::mapping::{
    frame_to_index, frame_to_meta, max_meta_slots, meta_to_frame, META_SLOT_SIZE,
};
use super::meta::REF_COUNT_UNIQUE;
use crate::mm::{Paddr, PagingLevel, MAX_NR_PAGES, MAX_PADDR, PAGE_SIZE};
use crate::specs::arch::kspace::FRAME_METADATA_RANGE;
use crate::specs::arch::paging_consts::PagingConsts;

verus! {

#[rustc_has_incoherent_inherent_impls]
pub struct UniqueFrame<M: AnyFrameMeta + Repr<MetaSlot> + OwnerOf> {
    pub ptr: PPtr<MetaSlot>,
    pub _marker: PhantomData<M>,
}

pub tracked struct UniqueFrameOwner<M: AnyFrameMeta + Repr<MetaSlot> + OwnerOf> {
    pub meta_own: M::Owner,
    pub meta_perm: vstd_extra::cast_ptr::PointsTo<MetaSlot, M>,
    pub ghost slot_index: usize,
}

pub ghost struct UniqueFrameModel<M: AnyFrameMeta + Repr<MetaSlot> + OwnerOf> {
    pub meta: <M::Owner as View>::V,
}

impl<M: AnyFrameMeta + Repr<MetaSlot> + OwnerOf> Inv for UniqueFrameOwner<M> {
    open spec fn inv(self) -> bool {
        &&& self.meta_perm.is_init()
        &&& self.meta_perm.wf()
        &&& self.slot_index == frame_to_index(meta_to_frame(self.meta_perm.addr()))
        &&& self.slot_index < max_meta_slots()
        &&& (self.slot_index - FRAME_METADATA_RANGE().start) as usize % META_SLOT_SIZE() == 0
        &&& self.meta_perm.addr() < FRAME_METADATA_RANGE().start + MAX_NR_PAGES() * META_SLOT_SIZE()
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlot> + OwnerOf> Inv for UniqueFrameModel<M> {
    open spec fn inv(self) -> bool {
        true
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlot> + OwnerOf> View for UniqueFrameOwner<M> {
    type V = UniqueFrameModel<M>;

    open spec fn view(&self) -> Self::V {
        UniqueFrameModel { meta: self.meta_own@ }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlot> + OwnerOf> InvView for UniqueFrameOwner<M> {
    proof fn view_preserves_inv(self) {
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlot> + OwnerOf> OwnerOf for UniqueFrame<M> {
    type Owner = UniqueFrameOwner<M>;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& self.ptr.addr() == owner.meta_perm.addr()
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlot> + OwnerOf> ModelOf for UniqueFrame<M> {

}

impl<M: AnyFrameMeta + Repr<MetaSlot> + OwnerOf> UniqueFrameOwner<M> {
    pub open spec fn perm_inv(self, perm: vstd::simple_pptr::PointsTo<MetaSlot>) -> bool {
        &&& perm.is_init()
        &&& perm.value().storage.addr() == self.meta_perm.addr()
        &&& perm.value().storage.addr() == self.meta_perm.points_to.addr()
    }

    pub open spec fn global_inv(self, regions: MetaRegionOwners) -> bool {
        &&& regions.slots.contains_key(self.slot_index) ==> self.perm_inv(
            regions.slots[self.slot_index],
        )
        &&& regions.dropped_slots.contains_key(self.slot_index) ==> self.perm_inv(
            regions.dropped_slots[self.slot_index],
        )
    }

    pub proof fn from_raw_owner(
        owner: M::Owner,
        index: Ghost<usize>,
        perm: vstd_extra::cast_ptr::PointsTo<MetaSlot, M>,
    ) -> Self {
        UniqueFrameOwner::<M> { meta_own: owner, meta_perm: perm, slot_index: index@ }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlot> + OwnerOf> UniqueFrame<M> {
    /// Gets a [`UniqueFrame`] with a specific usage from a raw, unused page.
    ///
    /// The caller should provide the initial metadata of the page.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(regions): Tracked<&mut MetaRegionOwners>
    )]
    pub fn from_unused(paddr: Paddr, metadata: M) -> Result<Self, GetFrameError>
        requires
            paddr < MAX_PADDR(),
            paddr % PAGE_SIZE() == 0,
            old(regions).slots.contains_key(frame_to_meta(paddr)),
            old(regions).inv(),
    {
        #[verus_spec(with Tracked(regions))]
        let from_unused = MetaSlot::get_from_unused(paddr, metadata, true);
        Ok(Self { ptr: from_unused?, _marker: PhantomData })
    }

    /*
    /// Repurposes the frame with a new metadata.
    pub fn repurpose<M1: AnyFrameMeta>(self, metadata: M1) -> UniqueFrame<M1> {
        // SAFETY: We are the sole owner and the metadata is initialized.
        unsafe { self.slot().drop_meta_in_place() };
        // SAFETY: We are the sole owner.
        unsafe { self.slot().write_meta(metadata) };
        // SAFETY: The metadata is initialized with type `M1`.
        unsafe { core::mem::transmute(self) }
    }*/
    /// Gets the metadata of this page.
    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub fn meta(&self) -> (l: &M)
        ensures
    //            perm.mem_contents().value() == l,

    {
        unimplemented!()
        // SAFETY: The type is tracked by the type system.
        //        unsafe { &*self.slot().as_meta_ptr() }

    }

    /// Gets the mutable metadata of this page.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(perm) : Tracked<&vstd::simple_pptr::PointsTo<MetaSlot>>
    )]
    #[verifier::external_body]
    pub fn meta_mut(&mut self) -> (res: ReprPtr<MetaSlot, M>)
        requires
    //            perm.is_init(),
    //            perm.pptr() == old(self).ptr,
    //            perm.value().wf(owner)

        ensures
            res.addr() == self.ptr.addr(),
            res.ptr.addr() == self.ptr.addr(),
            *self == *old(self),
    {
        // SAFETY: The type is tracked by the type system.
        // And we have the exclusive access to the metadata.
        //        let owner = regions.slot_owners.tracked_remove(frame_to_index(meta_to_frame(self.ptr.addr())));
        //        let perm = owner.cast_perm();
        //        regions.slot_owners.tracked_insert(frame_to_index(meta_to_frame(self.ptr.addr())), owner);
        #[verus_spec(with Tracked(perm))]
        let slot = self.slot();

        #[verus_spec(with Tracked(perm))]
        slot.as_meta_ptr()
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlot> + OwnerOf> UniqueFrame<M> {
    /// Gets the physical address of the start of the frame.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(regions) : Tracked<& MetaRegionOwners>
    )]
    #[verifier::external_body]
    pub fn start_paddr(&self) -> Paddr {
        //        #[verus_spec(with Tracked(&regions))]
        let slot = self.slot();
        slot.frame_paddr()
    }

    /// Gets the paging level of this page.
    ///
    /// This is the level of the page table entry that maps the frame,
    /// which determines the size of the frame.
    ///
    /// Currently, the level is always 1, which means the frame is a regular
    /// page frame.
    #[rustc_allow_incoherent_impl]
    pub const fn level(&self) -> PagingLevel {
        1
    }

    /// Gets the size of this page in bytes.
    #[rustc_allow_incoherent_impl]
    pub const fn size(&self) -> usize {
        PAGE_SIZE()
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
    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub(crate) fn into_raw(self) -> Paddr {
        let this = ManuallyDrop::new(self);
        this.start_paddr()
    }

    /// Restores a raw physical address back into a unique frame.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the physical address is valid and points to
    /// a forgotten frame that was previously casted by [`Self::into_raw`].
    #[rustc_allow_incoherent_impl]
    #[verus_spec(res =>
        with Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(meta_perm): Tracked<PointsTo<MetaSlot, M>>,
            Tracked(meta_own): Tracked<M::Owner>
    )]
    #[verifier::external_body]
    pub fn from_raw(paddr: Paddr) -> (res: (Self, Tracked<UniqueFrameOwner<M>>))
        requires
            paddr < MAX_PADDR(),
            paddr % PAGE_SIZE() == 0,
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
