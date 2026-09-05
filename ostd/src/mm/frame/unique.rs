// SPDX-License-Identifier: MPL-2.0
//! The unique frame pointer that is not shared with others.
use vstd::prelude::*;
use vstd::simple_pptr::{self, PPtr};

use vstd_extra::auxiliary::OptionExtraFns;
use vstd_extra::cast_ptr::*;
use vstd_extra::ownership::*;

use crate::specs::arch::*;
use crate::specs::mm::frame::{
    mapping::{frame_to_index, group_page_meta, index_to_meta, max_meta_slots, meta_to_index},
    meta_owners::{MetaSlotStorage, MetadataPerm, borrow_meta, borrow_meta_mut},
    meta_region_owners::MetaRegionOwners,
    unique::*,
};

use core::{marker::PhantomData, mem::ManuallyDrop, sync::atomic::Ordering};

use super::{
    AnyFrameMeta, Frame, MetaSlot,
    mapping::{frame_to_meta, meta_to_frame},
    meta::{GetFrameError, META_SLOT_SIZE, REF_COUNT_UNIQUE, REF_COUNT_UNUSED},
};
use crate::mm::{Paddr, PagingConsts, PagingLevel};

verus! {

pub struct UniqueFrame<M: AnyFrameMeta + ?Sized + Repr<MetaSlotStorage> + OwnerOf> {
    pub ptr: PPtr<MetaSlot>,
    pub _marker: PhantomData<M>,
    /// The permission to access the `MetaSlot` fields.
    #[cfg(verus_keep_ghost_body)]
    pub tracked_slot_perm: Tracked<&'static simple_pptr::PointsTo<MetaSlot>>,
    /// The complete permission for the currently installed metadata.
    #[cfg(verus_keep_ghost_body)]
    pub tracked_metadata_perm: Tracked<Option<MetadataPerm>>,
}

#[verifier::external]
unsafe impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf + Send> Send for UniqueFrame<M> {

}

#[verifier::external]
unsafe impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf + Sync> Sync for UniqueFrame<M> {

}

/*
impl<M: AnyFrameMeta + ?Sized> core::fmt::Debug for UniqueFrame<M> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "UniqueFrame({:#x})", self.start_paddr())
    }
}*/

#[verus_verify]
impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> UniqueFrame<M> {
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
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(meta_own_in): Tracked<M::Owner>,
            Tracked(repr_perm_in): Tracked<M::ReprPerm>,
                -> owner: Tracked<Option<UniqueFrameOwner<M>>>,
        requires
            old(regions).contains(frame_to_index(paddr)),
            old(regions).slot_owner(paddr).usage is Unused,
            old(regions).inv(),
            <M as OwnerOf>::wf(metadata, meta_own_in),
        ensures
            res matches Ok(res) ==> {
                &&& owner@ is Some
                &&& res.wf(owner@->0)
                &&& res.wf_with_region(owner@->0, *final(regions))
                &&& owner@->0.meta_own == meta_own_in
                &&& res.meta_value(owner@->0) == metadata
                &&& res.inv()
                &&& res.start_paddr_spec() == paddr
            },
            res is Err ==> {
                &&& owner@ is None
                &&& *final(regions) == *old(regions)
            },
            final(regions).inv(),
    )]
    pub fn from_unused(paddr: Paddr, metadata: M) -> Result<Self, GetFrameError> {
        let tracked mut repr_perm = repr_perm_in;
        #[verus_spec(with
            Tracked(regions),
            Tracked(&mut repr_perm) => Tracked(permissions)
        )]
        let from_unused = MetaSlot::get_from_unused(paddr, metadata, true);

        if let Err(err) = from_unused {
            proof_with!(|= Tracked(None));
            Err(err)
        } else {
            proof_decl! {
                let tracked metadata_perms = permissions.tracked_unwrap().tracked_take_right();
                let tracked slot_perm = regions.tracked_borrow_slot(paddr);
                let tracked owner = UniqueFrameOwner::<M>::tracked_from_unused_owner(
                    meta_own_in,
                    repr_perm,
                    frame_to_index(paddr),
                );
            }

            let ptr = from_unused.unwrap();

            proof_with!(|= Tracked(Some(owner)));
            Ok(
                Self {
                    ptr,
                    _marker: PhantomData,
                    #[cfg(verus_keep_ghost_body)]
                    tracked_slot_perm: Tracked(slot_perm),
                    #[cfg(verus_keep_ghost_body)]
                    tracked_metadata_perm: Tracked(Some(metadata_perms)),
                },
            )
        }
    }

    pub open spec fn transmute_spec<M1: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf>(
        self,
        transmuted: UniqueFrame<M1>,
    ) -> bool {
        &&& transmuted.ptr.addr() == self.ptr.addr()
        &&& transmuted._marker == PhantomData::<M1>
        &&& transmuted.tracked_slot_perm@ == self.tracked_slot_perm@
        &&& transmuted.tracked_metadata_perm@ == self.tracked_metadata_perm@
    }

    #[verifier::external_body]
    #[verus_spec(res =>
        ensures
            Self::transmute_spec(self, res),
    )]
    pub fn transmute<M1: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf>(self) -> UniqueFrame<M1> {
        unimplemented!()
    }

    /// Repurposes the frame with a new metadata.
    /// # Verified Properties
    /// ## Preconditions
    /// - The caller must provide a valid owner for the frame, and the metadata region invariants must hold.
    /// - The meta slot's reference count must be `REF_COUNT_UNIQUE`.
    /// ## Postconditions
    /// The function returns a new owner for the frame with the new metadata,
    /// and the metadata region invariants are preserved.
    /// ## Safety
    /// The existence of a valid owner guarantees that the memory is initialized with metadata of type `M`,
    /// and represents that the caller has exclusive ownership of the frame.
    #[verus_spec(res =>
        with
            Tracked(owner): Tracked<UniqueFrameOwner<M>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(meta_own_in): Tracked<M1::Owner>,
            Tracked(repr_perm_in): Tracked<M1::ReprPerm>,
                -> new_owner: Tracked<UniqueFrameOwner<M1>>,
        requires
            self.wf_with_region(owner, *old(regions)),
            old(regions).slot_owners[self.index()].in_list_perm.value() == 0,
            old(regions).inv(),
            self.inv(),
            owner.inv(),
            <M1 as OwnerOf>::wf(metadata, meta_own_in),
        ensures
            res.wf(new_owner@),
            res.wf_with_region(new_owner@, *final(regions)),
            new_owner@.meta_own == meta_own_in,
            res.meta_value(new_owner@) == metadata,
            final(regions).inv(),
    )]
    pub fn repurpose<M1: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf>(
        self,
        metadata: M1,
    ) -> UniqueFrame<M1> {
        let mut this = self;
        proof_decl! {
            broadcast use group_page_meta;
            let tracked mut repr_perm = repr_perm_in;
            let ghost idx = this.index();
            let tracked slot_own = regions.slot_owners.tracked_borrow_mut(idx);
            let tracked metadata_perm = this.tracked_metadata_perm.tracked_take();
        }

        // SAFETY: We are the sole owner and the metadata is initialized.
        unsafe {
            #[verus_spec(with
                Tracked(&slot_own.ref_count_perm),
                Tracked(&slot_own.in_list_perm),
                Tracked(&mut metadata_perm)
            )]
            this.slot().drop_meta_in_place()
        };

        unsafe {
            #[verus_spec(with
                Tracked(&mut metadata_perm),
                Tracked(&mut repr_perm)
            )]
            this.slot().write_meta(metadata)
        };

        proof_decl!{
        let tracked new_owner = UniqueFrameOwner::<M1>::tracked_from_unused_owner(
            meta_own_in,
            repr_perm,
            meta_to_index(this.ptr.addr()),
        );
        }

        #[cfg(verus_keep_ghost_body)]
        {
            this.tracked_metadata_perm = Tracked(Some(metadata_perm));
        }

        // SAFETY: The metadata is initialized with type `M1`.
        proof_with!(|= Tracked(new_owner));
        this.transmute()
    }

    /// Gets the metadata of this page.
    /// # Verified Properties
    /// ## Preconditions
    /// The caller must provide a valid owner for the frame.
    /// ## Postconditions
    /// The function returns the metadata of the frame.
    /// ## Safety
    /// The existence of a valid owner guarantees that the memory is initialized with metadata of type `M`,
    /// and represents that the caller has exclusive ownership of the frame.
    #[verus_spec(l =>
        with
            Tracked(owner): Tracked<&'a UniqueFrameOwner<M>>,
            Tracked(regions): Tracked<&'a MetaRegionOwners>,
        requires
            owner.inv(),
            regions.inv(),
            self.inv(),
            self.wf_with_region(*owner, *regions),
        ensures
            self.meta_value(*owner) == l,
    )]
    pub fn meta<'a>(&'a self) -> &'a M {
        // SAFETY: The type is tracked by the type system.
        // unsafe { &*self.slot().as_meta_ptr::<M>() }
        let tracked points_to = *self.tracked_slot_perm.borrow();
        let tracked metadata_perms = self.tracked_metadata_perm.borrow().tracked_borrow();
        borrow_meta(
            ReprPtr::<MetaSlotStorage, M>::from_pptr(PPtr::from_addr(self.ptr.addr())),
            Tracked(points_to),
            Tracked(metadata_perms),
            Tracked(owner.tracked_borrow_repr_perm()),
        )
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
    #[verus_spec(res =>
        with
            Tracked(owner): Tracked<&'a mut UniqueFrameOwner<M>>,
            Tracked(regions): Tracked<&'a mut MetaRegionOwners>,
        requires
            old(self).wf_with_region(*owner, *old(regions)),
            old(self).inv(),
            owner.inv(),
            regions.inv(),
        ensures
            *res == old(self).meta_value(*old(owner)),
            *final(res) == final(self).meta_value(*final(owner)),
            final(self).inv(),
            final(self).ptr == old(self).ptr,
            final(self).tracked_slot_perm@ == old(self).tracked_slot_perm@,
            final(owner).meta_own == old(owner).meta_own,
            final(owner).slot_index == old(owner).slot_index,
            final(owner).inv(),
            final(self).meta_wf(*final(owner)),
            (*final(self)).wf(*final(owner)),
            final(regions).inv(),
            final(regions).slots == old(regions).slots,
            final(regions).slots.dom() == old(regions).slots.dom(),
            final(regions).slot_owners.dom() == old(regions).slot_owners.dom(),
            forall|j: int|
                #![trigger final(regions).slot_owners[j]]
                j != old(owner).slot_index
                    ==> final(regions).slot_owners[j] == old(regions).slot_owners[j],
            final(regions).slot_owners[final(owner).slot_index].slot_vaddr
                == old(regions).slot_owners[old(owner).slot_index].slot_vaddr,
            final(regions).slot_owners[final(owner).slot_index].usage
                == old(regions).slot_owners[old(owner).slot_index].usage,
            final(regions).slot_owners[final(owner).slot_index].ref_count_perm
                == old(regions).slot_owners[old(owner).slot_index].ref_count_perm,
            final(regions).slot_owners[final(owner).slot_index].in_list_perm
                == old(regions).slot_owners[old(owner).slot_index].in_list_perm,
            final(regions).slot_owners[final(owner).slot_index].paths_in_pt
                == old(regions).slot_owners[old(owner).slot_index].paths_in_pt,
            <M as OwnerOf>::wf(final(self).meta_value(*final(owner)), final(owner).meta_own)
                ==> final(self).wf_with_region(*final(owner), *final(regions)),
    )]
    pub fn meta_mut<'a>(&'a mut self) -> &'a mut M {
        let tracked points_to = *self.tracked_slot_perm.borrow();
        let tracked metadata_perms = self.tracked_metadata_perm.borrow_mut().tracked_borrow_mut();
        let tracked repr_perm = owner.tracked_borrow_mut_repr_perm();
        borrow_meta_mut(
            ReprPtr::<MetaSlotStorage, M>::from_pptr(PPtr::from_addr(self.ptr.addr())),
            Tracked(points_to),
            Tracked(metadata_perms),
            Tracked(repr_perm),
        )
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf + ?Sized> UniqueFrame<M> {
    /// Gets the size of this page in bytes.
    pub const fn size(&self) -> usize
        returns
            PAGE_SIZE,
    {
        PAGE_SIZE
    }

    /// Gets the paging level of this page.
    ///
    /// This is the level of the page table entry that maps the frame,
    /// which determines the size of the frame.
    ///
    /// Currently, the level is always 1, which means the frame is a regular
    /// page frame.
    pub const fn level(&self) -> PagingLevel
        returns
            1u8,
    {
        1
    }
}

#[verus_verify]
impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf + ?Sized> UniqueFrame<M> {
    /// Gets the physical address of the start of the frame.
    #[verus_spec(
        requires
            self.ptr_inv(),
        returns
            meta_to_frame(self.ptr.addr()),
    )]
    pub fn start_paddr(&self) -> Paddr {
        let slot = self.slot();

        #[verus_spec(with self.tracked_slot_perm)]
        slot.frame_paddr()
    }

    /*    /// Gets the dynamically-typed metadata of this frame.
    ///
    /// If the type is known at compile time, use [`Frame::meta`] instead.

    #[verifier::external_body]
    pub fn dyn_meta(&self) -> &M {
        // SAFETY: The metadata is initialized and valid.
        unsafe { &*self.slot().dyn_meta_ptr::<M>() }
    }

    /// Gets the dynamically-typed metadata of this frame.
    ///
    /// If the type is known at compile time, use [`Frame::meta`] instead.

    #[verifier::external_body]
    pub fn dyn_meta_mut(&mut self) -> &mut FrameMeta {
        // SAFETY: The metadata is initialized and valid. We have the exclusive
        // access to the frame.
        unsafe { &mut *self.slot().dyn_meta_ptr() }
    }*/
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
    #[verus_spec(
        with
            Tracked(owner): Tracked<UniqueFrameOwner<M>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
        requires
            self.inv(),
            owner.inv(),
            regions.inv(),
            self.wf_with_region(owner, *old(regions)),
            old(regions).slot_owners[owner.slot_index].in_list_perm.value() == 0,
        ensures
            final(regions).inv(),
    )]
    pub fn reset_as_unused(self) {
        let mut this = self;

        proof_decl! {
            let tracked mut owner = owner;
            let ghost idx = owner.slot_index;
            let tracked slot_own = regions.slot_owners.tracked_borrow_mut(idx);
            let tracked metadata_perms = this.tracked_metadata_perm.tracked_take();
            slot_own.metadata_perm.put_resource(metadata_perms);
        }

        this.slot().ref_count.store(Tracked(&mut slot_own.ref_count_perm), 0);

        // SAFETY: We are the sole owner and the reference count is 0.
        // The slot is initialized.
        unsafe {
            #[verus_spec(with Tracked(slot_own))]
            this.slot().drop_last_in_place()
        };
    }

    /// Converts this frame into a raw physical address.
    #[verus_spec(r =>
        with
            Tracked(owner): Tracked<&UniqueFrameOwner<M>>,
                -> metadata_perms: Tracked<MetadataPerm>,
        requires
            self.inv(),
        ensures
            metadata_perms@ == self.metadata_perm(),
            r == meta_to_frame(self.ptr.addr()),
    )]
    pub(crate) fn into_raw(self) -> Paddr {
        let mut this = self;

        let tracked metadata_perms = this.tracked_metadata_perm.tracked_take();
        let this = ManuallyDrop::new(this);

        proof_with!(|= Tracked(metadata_perms));
        this.start_paddr()
    }

    /// Restores a raw physical address back into a unique frame.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the physical address is valid and points to
    /// a forgotten frame that was previously casted by [`Self::into_raw`].
    #[verus_spec(res =>
        with
            Tracked(slot_perm): Tracked<&'static simple_pptr::PointsTo<MetaSlot>>,
            Tracked(meta_own): Tracked<M::Owner>,
            Tracked(repr_perm): Tracked<M::ReprPerm>,
            Tracked(metadata_perm): Tracked<MetadataPerm>,
            ->
                owner: Tracked<UniqueFrameOwner<M>>,
        requires
            valid_frame_paddr(paddr),
            slot_perm.addr() == frame_to_meta(paddr),
            slot_perm.is_init(),
            MetaSlot::perms_related(*slot_perm, metadata_perm)
        ensures
            res.inv(),
            res.start_paddr_spec() == paddr,
            res.tracked_slot_perm@ == slot_perm,
            res.wf(owner@),
            owner@.meta_own == meta_own,
            owner@.repr_perm == Some(repr_perm),
            res.tracked_metadata_perm@ == Some(metadata_perm),
            owner@.slot_index == frame_to_index(paddr),
    )]
    pub(crate) unsafe fn from_raw(paddr: Paddr) -> Self {
        let vaddr = frame_to_meta(paddr);
        let ptr = vstd::simple_pptr::PPtr::<MetaSlot>::from_addr(vaddr);

        let tracked owner = UniqueFrameOwner {
            meta_own,
            repr_perm: Some(repr_perm),
            slot_index: frame_to_index(paddr),
        };

        proof_with!{ |= Tracked(owner)}
        Self {
            ptr,
            _marker: PhantomData,
            #[cfg(verus_keep_ghost_body)]
            tracked_slot_perm: Tracked(slot_perm),
            #[cfg(verus_keep_ghost_body)]
            tracked_metadata_perm: Tracked(Some(metadata_perm)),
        }
    }

    #[verus_spec(
        requires
            self.ptr_inv(),
        returns
            self.tracked_slot_perm@.value(),
    )]
    pub fn slot<'a>(&self) -> &'a MetaSlot {
        // SAFETY: `ptr` points to a valid `MetaSlot` that will never be
        // mutably borrowed, so taking an immutable reference to it is safe.
        let tracked slot_perm = *self.tracked_slot_perm;
        self.ptr.borrow(Tracked(slot_perm))
    }
}

/*
impl<M: AnyFrameMeta + ?Sized> Drop for UniqueFrame<M> {
    fn drop(&mut self) {
        self.slot().ref_count.store(0, Ordering::Relaxed);
        // SAFETY: We are the sole owner and the reference count is 0.
        // The slot is initialized.
        unsafe { self.slot().drop_last_in_place() };

        super::allocator::get_global_frame_allocator().dealloc(self.start_paddr(), PAGE_SIZE);
    }
} */

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf + ?Sized> UniqueFrame<M> {
    #[verus_spec(
        with
            Tracked(owner): Tracked<UniqueFrameOwner<M>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
        requires
            old(self).inv(),
            owner.inv(),
            regions.inv(),
            old(self).wf_with_region(owner, *old(regions)),
            old(regions).slot_owners[owner.slot_index].in_list_perm.value() == 0,
        ensures
            final(regions).inv(),
            final(regions).slots == old(regions).slots,
            forall|i: int| #![trigger final(regions).slot_owners[i]]
                i != owner.slot_index ==> final(regions).slot_owners[i]
                    == old(regions).slot_owners[i],
    )]
    pub(crate) fn drop(&mut self) {
        let tracked mut owner = owner;
        let ghost idx = owner.slot_index;

        let tracked slot_own = regions.slot_owners.tracked_borrow_mut(idx);
        let tracked metadata_perms = self.tracked_metadata_perm.tracked_take();
        proof {
            slot_own.metadata_perm.put_resource(metadata_perms);
        }
        // SAFETY: We are the sole owner and the reference count is 0.
        // The slot is initialized.
        self.slot().ref_count.store(Tracked(&mut slot_own.ref_count_perm), 0);

        unsafe {
            #[verus_spec(with Tracked(&mut slot_own))]
            self.slot().drop_last_in_place()
        };

        // super::allocator::get_global_frame_allocator().dealloc(self.start_paddr(), PAGE_SIZE);
    }
}

#[verus_verify]
impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> Frame<M> {
    #[verus_spec(res =>
        with
            Tracked(owner): Tracked<UniqueFrameOwner<M>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
        requires
            unique.inv(),
            owner.inv(),
            old(regions).inv(),
            unique.wf_with_region(owner, *old(regions)),
            old(regions).slot_owners[owner.slot_index].in_list_perm.value() == 0,
        ensures
            res.inv(),
            final(regions).inv(),
            res.wf_with_region(*final(regions)),
            final(regions).slots == old(regions).slots,
            final(regions).slot_owners.dom() == old(regions).slot_owners.dom(),
    )]
    pub fn from_unique(unique: UniqueFrame<M>) -> Self {
        let tracked mut owner = owner;
        let ptr = unique.ptr;
        let ghost idx = meta_to_index(unique.ptr.addr());
        proof {
            broadcast use group_page_meta;

            regions.lemma_contains_valid_frame_paddr(meta_to_frame(unique.ptr.addr()));
        }
        let tracked slot_own = regions.slot_owners.tracked_borrow_mut(idx);
        let slot = unique.slot();
        let tracked metadata_perms = unique.tracked_metadata_perm.get().tracked_unwrap();
        proof {
            slot_own.metadata_perm.put_resource(metadata_perms);
        }
        let tracked frame_permission = slot_own.metadata_perm.split_one();
        let tracked mut inner_perms = &mut slot_own;

        slot.ref_count.store(Tracked(&mut inner_perms.ref_count_perm), 1);

        let res = Frame {
            ptr,
            _marker: PhantomData,
            #[cfg(verus_keep_ghost_body)]
            tracked_slot_perm: unique.tracked_slot_perm,
            #[cfg(verus_keep_ghost_body)]
            tracked_metadata_perm: Tracked(Some(frame_permission)),
        };
        res
    }
}

#[verus_verify]
impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> UniqueFrame<M> {
    /// Tries to convert a shared frame into a unique one by CAS'ing ref_count
    /// from 1 to `REF_COUNT_UNIQUE`. Inherent sibling of
    /// `TryFrom<Frame<M>> for UniqueFrame<M>`.
    #[verus_spec(res =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
        requires
            frame.inv(),
            old(regions).inv(),
            frame.wf_with_region(*old(regions)),
        ensures
            final(regions).slots == old(regions).slots,
            final(regions).slot_owners.dom() == old(regions).slot_owners.dom(),
    )]
    pub fn try_from_shared(mut frame: Frame<M>) -> Result<Self, Frame<M>> {
        let ghost idx = meta_to_index(frame.ptr.addr());
        proof {
            broadcast use group_page_meta;

            regions.lemma_contains_valid_frame_paddr(frame.start_paddr_spec());
        }
        let tracked mut slot_own = regions.slot_owners.tracked_borrow_mut(idx);
        let tracked inner_perms = &mut slot_own;
        let res = frame.slot().ref_count.compare_exchange(
            Tracked(&mut inner_perms.ref_count_perm),
            1,
            REF_COUNT_UNIQUE,
        );

        match res {
            Ok(_) => {
                let tracked frame_permission = frame.tracked_metadata_perm.tracked_take();
                proof {
                    slot_own.metadata_perm.combine(frame_permission);
                }
                let tracked metadata_perms = slot_own.metadata_perm.take_resource();
                Ok(
                    UniqueFrame {
                        ptr: frame.ptr,
                        _marker: PhantomData,
                        #[cfg(verus_keep_ghost_body)]
                        tracked_slot_perm: frame.tracked_slot_perm,
                        #[cfg(verus_keep_ghost_body)]
                        tracked_metadata_perm: Tracked(Some(metadata_perms)),
                    },
                )
            },
            Err(_) => Err(frame),
        }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> From<UniqueFrame<M>> for Frame<M> {
    #[verifier::external_body]
    fn from(unique: UniqueFrame<M>) -> Self {
        Frame::from_unique(unique)
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> TryFrom<Frame<M>> for UniqueFrame<M> {
    type Error = Frame<M>;

    /// Tries to get a unique frame from a shared frame.
    ///
    /// If the reference count is not 1, the frame is returned back.
    #[verifier::external_body]
    fn try_from(frame: Frame<M>) -> Result<Self, Self::Error> {
        UniqueFrame::try_from_shared(frame)
    }
}

} // verus!
