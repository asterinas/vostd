// SPDX-License-Identifier: MPL-2.0
//! Enabling linked lists of frames without heap allocation.
//!
//! This module leverages the customizability of the metadata system (see
//! [super::meta]) to allow any type of frame to be used in a linked list.
use vstd::prelude::*;

use vstd::atomic::PermissionU64;
use vstd::seq_lib::*;
use vstd::simple_pptr::*;

use vstd_extra::cast_ptr::*;
use vstd_extra::drop_tracking::{Drop, TrackDrop};
use vstd_extra::ownership::*;
use vstd_extra::trans_macros::*;

use crate::mm::frame::meta::mapping::frame_to_meta;
use crate::mm::frame::meta::REF_COUNT_UNUSED;
use crate::mm::frame::UniqueFrame;
use crate::mm::{Paddr, PagingLevel, Vaddr};
use crate::specs::arch::mm::{MAX_NR_PAGES, MAX_PADDR, PAGE_SIZE};
use crate::specs::mm::frame::linked_list::linked_list_owners::*;
use crate::specs::mm::frame::meta_owners::{MetaSlotOwner, Metadata};
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::frame::unique::UniqueFrameOwner;

use core::borrow::BorrowMut;
use core::{
    ops::{Deref, DerefMut},
    ptr::NonNull,
    sync::atomic::{AtomicU64, Ordering},
};

use crate::specs::*;

use crate::mm::frame::meta::mapping::{
    frame_to_index, frame_to_index_spec, max_meta_slots, meta_addr, meta_to_frame,
    meta_to_frame_spec, META_SLOT_SIZE,
};
use crate::mm::frame::meta::{get_slot, has_safe_slot, AnyFrameMeta, MetaSlot};
use crate::specs::arch::kspace::FRAME_METADATA_RANGE;

verus! {

/// A link in the linked list.
pub struct Link<M: AnyFrameMeta + Repr<MetaSlotSmall>> {
    pub next: Option<ReprPtr<MetaSlot, MetadataAsLink<M>>>,
    pub prev: Option<ReprPtr<MetaSlot, MetadataAsLink<M>>>,
    pub meta: M,
}

/// A linked list of frames.
///
/// Two key features that [`LinkedList`] is different from
/// [`alloc::collections::LinkedList`] is that:
///  1. It is intrusive, meaning that the links are part of the frame metadata.
///     This allows the linked list to be used without heap allocation. But it
///     disallows a frame to be in multiple linked lists at the same time.
///  2. The linked list exclusively own the frames, meaning that it takes
///     unique pointers [`UniqueFrame`]. And other bodies cannot
///     [`from_in_use`] a frame that is inside a linked list.
///  3. We also allow creating cursors at a specific frame, allowing $O(1)$
///     removal without iterating through the list at a cost of some checks.
/// # Verified Properties
/// ## Verification Design
/// The linked list is abstractly represented by a [`LinkedListOwner`]:
/// ```rust
/// tracked struct LinkedListOwner<M: AnyFrameMeta + Repr<MetaSlotStorage>> {
///     pub list: Seq<LinkOwner>,
///     pub list_id: u64,
/// }
/// ```
/// The pointer permission for each link is parked in the global
/// [`MetaRegionOwners`] (`regions.slots[idx]` paired with
/// `regions.slot_owners[idx].inner_perms`); cursor accessors borrow it on
/// demand via `borrow_typed_perm`/`borrow_mut_typed_perm` rather than carrying
/// an owned `Map<int, _>` inside `LinkedListOwner`.
/// ## Invariant
/// The linked list uniquely owns the raw frames that it contains, so they cannot be used by other
/// data structures. The frame metadata field `in_list` is equal to `list_id` for all links in the list.
/// The per-link well-formedness against the region (pptr/inner_perms wiring,
/// `next`/`prev` pointer chain) is captured by
/// [`LinkedListOwner::relate_region`] (opaque, with per-position
/// [`LinkedListOwner::relate_region_at`]). The cursor exposes this via
/// [`CursorOwner::inv_region`] and [`CursorMut::wf_region`].
/// ## Safety
/// A given linked list can only have one cursor at a time, so there are no data races.
/// The `prev` and `next` fields of the metadata for each link always points to valid
/// links in the list, so the structure is memory safe (will not read or write invalid memory).
pub struct LinkedList<M: AnyFrameMeta + Repr<MetaSlotSmall>> {
    pub front: Option<ReprPtr<MetaSlot, MetadataAsLink<M>>>,
    pub back: Option<ReprPtr<MetaSlot, MetadataAsLink<M>>>,
    /// The number of frames in the list.
    pub size: usize,
    /// A lazily initialized ID, used to check whether a frame is in the list.
    /// 0 means uninitialized.
    pub list_id: u64,
}

/// A cursor that can mutate the linked list links.
///
/// The cursor points to either a frame or the "ghost" non-element. It points
/// to the "ghost" non-element when the cursor surpasses the back of the list.
pub struct CursorMut<'a, M: AnyFrameMeta + Repr<MetaSlotSmall>> {
    pub list: &'a mut LinkedList<M>,
    pub current: Option<ReprPtr<MetaSlot, MetadataAsLink<M>>>,
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> LinkedList<M> {
    /// Creates a new linked list.
    pub const fn new() -> Self {
        Self { front: None, back: None, size: 0, list_id: 0 }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> Default for LinkedList<M> {
    fn default() -> Self {
        Self::new()
    }
}

// SAFETY: Only the pointers are not `Send` and `Sync`. But our interfaces
// enforces that only with `&mut` references can we access with the pointers.
//unsafe impl<M> Send for LinkedList<M> where Link<M>: AnyFrameMeta {}
//unsafe impl<M> Sync for LinkedList<M> where Link<M>: AnyFrameMeta {}
#[verus_verify]
impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> LinkedList<M> {
    /// Gets the number of frames in the linked list.
    #[verus_spec(s =>
        with
            Tracked(owner): Tracked<LinkedListOwner<M>>,
        requires
            self.wf(owner),
            owner.inv(),
        ensures
            s == self.model(owner).list.len(),
    )]
    pub fn size(&self) -> usize {
        proof {
            LinkedListOwner::<M>::view_preserves_len(owner.list);
        }
        self.size
    }

    /// Tells if the linked list is empty.
    #[verus_spec(b =>
        with
            Tracked(owner): Tracked<LinkedListOwner<M>>,
        requires
            self.wf(owner),
            owner.inv(),
        ensures
            b ==> self.size == 0 && self.front is None && self.back is None,
            !b ==> self.size > 0 && self.front is Some && self.back is Some,
    )]
    pub fn is_empty(&self) -> bool {
        let is_empty = self.size == 0;
        is_empty
    }

    /// Pushes a frame to the front of the linked list.
    /// # Verified Properties
    /// ## Preconditions
    /// The list must be well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects. The new frame must be active, so that it is
    /// valid to call `into_raw` on it inside of `insert_before`.
    /// ## Postconditions
    /// The new frame is inserted at the front of the list, and the cursor is moved to the new frame.
    /// The list invariants are preserved.
    /// ## Safety
    /// See [`insert_before`] for the safety guarantees.
    #[verus_spec(
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(owner): Tracked<&mut LinkedListOwner<M>>,
            Tracked(frame_own): Tracked<&mut UniqueFrameOwner<Link<M>>>,
        requires
            old(self).wf_region(*old(owner), *old(regions)),
            old(owner).relate_region(*old(regions)),
            old(owner).list_id != 0,
            old(frame_own).inv(),
            old(frame_own).global_inv(*old(regions)),
            frame.wf(*old(frame_own)),
            old(frame_own).frame_link_inv(*old(regions)),
            old(owner).list.len() < usize::MAX,
            old(regions).inv(),
            old(regions).slot_owners[old(frame_own).slot_index].raw_count == 0,
            old(regions).slot_owners[old(frame_own).slot_index].inner_perms.ref_count.value()
                == crate::specs::mm::frame::meta_owners::REF_COUNT_UNIQUE,
            old(regions).slot_owners[old(frame_own).slot_index].inner_perms.in_list.is_for(
                old(regions).slots[old(frame_own).slot_index].value().in_list,
            ),
            forall|p: int| #![trigger old(owner).slot_index_at(p)]
                0 <= p < old(owner).list.len()
                ==> old(owner).slot_index_at(p) != old(frame_own).slot_index,
        ensures
            final(owner).relate_region(*final(regions)),
            final(regions).inv(),
            final(owner).list == old(owner).list.insert(0, final(frame_own).meta_own),
            final(owner).list_id == old(owner).list_id,
            final(frame_own).meta_own.paddr == old(frame_own).meta_own.paddr,
            final(frame_own).meta_own.in_list == old(owner).list_id,
    )]
    pub fn push_front(&mut self, frame: UniqueFrame<Link<M>>) {
        let current = self.front;
        let tracked mut cursor_own = CursorOwner::tracked_front_owner(*owner);
        let mut cursor = CursorMut { list: self, current };

        #[verus_spec(with Tracked(regions), Tracked(&mut cursor_own), Tracked(frame_own))]
        cursor.insert_before(frame);

        proof {
            *owner = cursor_own.list_own;
        }
    }

    /// Pops a frame from the front of the linked list.
    /// # Verified Properties
    /// ## Preconditions
    /// The list must be well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects. The list must be non-empty, so that the
    /// current frame is valid.
    /// ## Postconditions
    /// The front frame is removed from the list, and the cursor is moved to the next frame.
    /// The list invariants are preserved.
    /// ## Safety
    /// See [`take_current`] for the safety guarantees.
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(owner): Tracked<LinkedListOwner<M>>,
            Tracked(frame_own): Tracked<UniqueFrameOwner<Link<M>>>,
        requires
            old(regions).inv(),
            old(self).wf_region(owner, *old(regions)),
            owner.relate_region(*old(regions)),
        ensures
            owner.list.len() == 0 ==> r.is_none(),
            r.is_some() ==> r.unwrap().0.model(r.unwrap().1@).meta == owner.list[0]@,
            r.is_some() ==> r.unwrap().1@.frame_link_inv(*final(regions)),
    )]
    pub fn pop_front(&mut self) -> Option<
        (UniqueFrame<Link<M>>, Tracked<UniqueFrameOwner<Link<M>>>),
    > {
        let tracked mut cursor_own = CursorOwner::tracked_front_owner(owner);
        let current = self.front;
        let mut cursor = CursorMut { list: self, current };

        proof {
            if owner.list.len() > 0 {
                let _ = owner.list[0];
                owner.relate_region_at_facts(*regions, 0);
            }
        }

        #[verus_spec(with Tracked(regions), Tracked(&mut cursor_own))]
        cursor.take_current()
    }

    /// Pushes a frame to the back of the linked list.
    /// # Verified Properties
    /// ## Preconditions
    /// The list must be well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects. The new frame must be active, so that it is
    /// valid to call `into_raw` on it inside of `insert_before`.
    /// ## Postconditions
    /// - The new frame is inserted at the back of the list, and the cursor is moved to the new frame.
    /// - The list invariants are preserved.
    /// ## Safety
    /// See [`insert_before`] for the safety guarantees.
    #[verus_spec(
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(owner): Tracked<&mut LinkedListOwner<M>>,
            Tracked(frame_own): Tracked<&mut UniqueFrameOwner<Link<M>>>,
        requires
            old(self).wf_region(*old(owner), *old(regions)),
            old(owner).relate_region(*old(regions)),
            old(owner).list_id != 0,
            old(frame_own).inv(),
            old(frame_own).global_inv(*old(regions)),
            frame.wf(*old(frame_own)),
            old(frame_own).frame_link_inv(*old(regions)),
            old(owner).list.len() < usize::MAX,
            old(regions).inv(),
            old(regions).slot_owners[old(frame_own).slot_index].raw_count == 0,
            old(regions).slot_owners[old(frame_own).slot_index].inner_perms.ref_count.value()
                == crate::specs::mm::frame::meta_owners::REF_COUNT_UNIQUE,
            old(regions).slot_owners[old(frame_own).slot_index].inner_perms.in_list.is_for(
                old(regions).slots[old(frame_own).slot_index].value().in_list,
            ),
            forall|p: int| #![trigger old(owner).slot_index_at(p)]
                0 <= p < old(owner).list.len()
                ==> old(owner).slot_index_at(p) != old(frame_own).slot_index,
        ensures
            final(owner).relate_region(*final(regions)),
            final(regions).inv(),
            old(owner).list.len() > 0 ==> final(owner).list == old(owner).list.insert(
                old(owner).list.len() as int - 1, final(frame_own).meta_own),
            old(owner).list.len() == 0 ==> final(owner).list == old(owner).list.insert(
                0, final(frame_own).meta_own),
            final(owner).list_id == old(owner).list_id,
            final(frame_own).meta_own.paddr == old(frame_own).meta_own.paddr,
            final(frame_own).meta_own.in_list == old(owner).list_id,
    )]
    pub fn push_back(&mut self, frame: UniqueFrame<Link<M>>) {
        let current = self.back;
        let tracked mut cursor_own = CursorOwner::tracked_back_owner(*owner);
        let mut cursor = CursorMut { list: self, current };

        #[verus_spec(with Tracked(regions), Tracked(&mut cursor_own), Tracked(frame_own))]
        cursor.insert_before(frame);

        proof {
            *owner = cursor_own.list_own;
        }
    }

    /// Pops a frame from the back of the linked list.
    /// # Verified Properties
    /// ## Preconditions
    /// - The list must be well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects.
    /// - The list must be non-empty, so that the
    /// current frame is valid.
    /// ## Postconditions
    /// - The back frame is removed from the list, and the cursor is moved to the "ghost" non-element.
    /// - The list invariants are preserved.
    /// ## Safety
    /// See [`take_current`] for the safety guarantees.
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(owner): Tracked<LinkedListOwner<M>>,
            Tracked(frame_own): Tracked<UniqueFrameOwner<Link<M>>>,
        requires
            old(regions).inv(),
            old(self).wf_region(owner, *old(regions)),
            owner.relate_region(*old(regions)),
        ensures
            owner.list.len() == 0 ==> r.is_none(),
            r.is_some() ==> r.unwrap().0.model(r.unwrap().1@).meta == owner.list[owner.list.len() - 1]@,
            r.is_some() ==> r.unwrap().1@.frame_link_inv(*final(regions)),
    )]
    pub fn pop_back(&mut self) -> Option<
        (UniqueFrame<Link<M>>, Tracked<UniqueFrameOwner<Link<M>>>),
    > {
        let current = self.back;
        let tracked mut cursor_own = CursorOwner::tracked_back_owner(owner);
        let mut cursor = CursorMut { list: self, current };

        proof {
            if owner.list.len() > 0 {
                let _ = owner.list[owner.list.len() - 1];
                owner.relate_region_at_facts(*regions, owner.list.len() - 1);
            }
        }

        #[verus_spec(with Tracked(regions), Tracked(&mut cursor_own))]
        cursor.take_current()
    }

    /// Tells if a frame is in the list.
    /// # Verified Properties
    /// ## Preconditions
    /// - The list must be well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects.
    /// - The frame must be a valid, active frame.
    /// ## Postconditions
    /// The function returns `true` if the frame is in the list, `false` otherwise.
    /// ## Safety
    /// - `lazy_get_id` uses atomic memory accesses, so there are no data races.
    /// - We assume that the ID allocator has an available ID if the list previously didn't have one,
    /// but the consequence if that is not the case is a failsafe panic.
    /// - Everything else conforms to the safe interface.
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(slot_own): Tracked<&MetaSlotOwner>,
            Tracked(owner): Tracked<&mut LinkedListOwner<M>>,
        requires
            slot_own.inv(),
            old(regions).inv(),
            old(regions).slots[frame_to_index(frame)].is_init(),
            old(regions).slot_owners.contains_key(frame_to_index(frame)),
            old(regions).slot_owners[frame_to_index(frame)].inner_perms.in_list.is_for(
                old(regions).slots[frame_to_index(frame)].mem_contents().value().in_list,
            ),
        ensures
            old(owner).list_id != 0 ==> *final(owner) == *old(owner),
    )]
    pub fn contains(&mut self, frame: Paddr) -> bool {
        let Ok(slot_ptr) = get_slot(frame) else {
            return false;
        };

        let tracked mut slot_perm = regions.slots.tracked_remove(frame_to_index(frame));
        let tracked mut slot_own = regions.slot_owners.tracked_remove(frame_to_index(frame));

        let slot = slot_ptr.take(Tracked(&mut slot_perm));

        let tracked mut inner_perms = slot_own.take_inner_perms();

        let in_list = slot.in_list.load(Tracked(&mut inner_perms.in_list));
        slot_ptr.put(Tracked(&mut slot_perm), slot);

        proof {
            slot_own.sync_inner(&inner_perms);
            regions.slot_owners.tracked_insert(frame_to_index(frame), slot_own);
            regions.slots.tracked_insert(frame_to_index(frame), slot_perm);
        }

        in_list == #[verus_spec(with Tracked(owner))]
        self.lazy_get_id()
    }

    /// Gets a cursor at the specified frame if the frame is in the list.
    ///
    /// This method fails if the frame is not in the list.
    /// # Verified Properties
    /// ## Preconditions
    /// - The list must be well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects.
    /// - The frame should be raw (because it is owned by the list)
    /// ## Postconditions
    /// - This functions post-conditions are incomplete due to refactoring of the permission model.
    /// When complete, it will guarantee that the cursor is well-formed and points to the matching
    /// element in the list.
    /// ## Safety
    /// - `lazy_get_id` uses atomic memory accesses, so there are no data races.
    /// - We assume that the ID allocator has an available ID if the list previously didn't have one,
    /// but the consequence if that is not the case is a failsafe panic.
    /// - Everything else conforms to the safe interface.
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(owner): Tracked<LinkedListOwner<M>>,
            -> cursor_owner: Tracked<Option<CursorOwner<M>>>,
        requires
            old(regions).inv(),
        ensures
            !has_safe_slot(frame) ==> r is None,
            final(regions).inv(),
            final(regions).slots == old(regions).slots,
            final(regions).slot_owners.dom() == old(regions).slot_owners.dom(),
    )]
    pub fn cursor_mut_at(&mut self, frame: Paddr) -> Option<CursorMut<'_, M>> {
        if let Ok(slot_ptr) = get_slot(frame) {
            let ghost idx = frame_to_index(frame);
            proof {
                broadcast use crate::mm::frame::meta::mapping::group_page_meta;

                assert(idx < max_meta_slots());
                assert(regions.slot_owners.contains_key(idx));
                assert(regions.slots.contains_key(idx));
            }
            let tracked slot_perm = regions.slots.tracked_borrow(idx);
            let tracked mut slot_own = regions.slot_owners.tracked_remove(idx);
            let tracked mut inner_perms = slot_own.take_inner_perms();

            let slot = slot_ptr.borrow(Tracked(slot_perm));

            let in_list = slot.in_list.load(Tracked(&mut inner_perms.in_list));

            let contains = in_list == #[verus_spec(with Tracked(&owner))]
            self.lazy_get_id();

            #[verus_spec(with Tracked(slot_perm))]
            let meta_ptr = slot.as_meta_ptr::<Link<M>>();

            proof {
                slot_own.sync_inner(&inner_perms);
                regions.slot_owners.tracked_insert(idx, slot_own);
            }

            if contains {
                let ghost link = owner.list.filter(|link: LinkOwner| link.paddr == frame).first();
                let ghost index = owner.list.index_of(link);
                let tracked cursor_owner = CursorOwner::tracked_cursor_mut_at_owner(owner, index);

                proof_with!(|= Tracked(Some(cursor_owner)));
                Some(
                    CursorMut {
                        list: self,
                        current: Some(MetadataAsLink::cast_from_metadata(meta_ptr)),
                    },
                )
            } else {
                proof_with!(|= Tracked(None));
                None
            }
        } else {
            assert(!has_safe_slot(frame));
            proof_with!(|= Tracked(None));
            None
        }
    }

    /// Gets a cursor at the front that can mutate the linked list links.
    ///
    /// If the list is empty, the cursor points to the "ghost" non-element.
    /// # Verified Properties
    /// ## Preconditions
    /// - The list must be well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects.
    /// ## Postconditions
    /// - The cursor is well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects. The list invariants are preserved.
    /// - See [`CursorOwner::front_owner`] for the precise specification.
    /// ## Safety
    /// - This function only uses the list permission, so there are no illegal memory accesses.
    /// - No data races are possible.
    #[verus_spec(r =>
        with
            Tracked(owner): Tracked<LinkedListOwner<M>>,
        requires
            old(self).wf(owner),
            owner.inv(),
        ensures
            r.0.wf(r.1@),
            r.1@.inv(),
            r.1@ == CursorOwner::front_owner(owner),
    )]
    pub fn cursor_front_mut(&mut self) -> (CursorMut<'_, M>, Tracked<CursorOwner<M>>) {
        let current = self.front;

        (CursorMut { list: self, current }, Tracked(CursorOwner::tracked_front_owner(owner)))
    }

    /// Gets a cursor at the back that can mutate the linked list links.
    ///
    /// If the list is empty, the cursor points to the "ghost" non-element.
    /// # Verified Properties
    /// ## Preconditions
    /// - The list must be well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects.
    /// ## Postconditions
    /// - The cursor is well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects. The list invariants are preserved.
    /// See [`CursorOwner::back_owner`] for the precise specification.
    /// ## Safety
    /// - This function only uses the list permission, so there are no illegal memory accesses.
    /// - No data races are possible.
    #[verus_spec(
        with
            Tracked(owner): Tracked<LinkedListOwner<M>>,
    )]
    pub fn cursor_back_mut(&mut self) -> (res: (CursorMut<'_, M>, Tracked<CursorOwner<M>>))
        requires
            old(self).wf(owner),
            owner.inv(),
        ensures
            res.0.wf(res.1@),
            res.1@.inv(),
            res.1@ == CursorOwner::back_owner(owner),
    {
        let current = self.back;

        (CursorMut { list: self, current }, Tracked(CursorOwner::tracked_back_owner(owner)))
    }

    /// Gets a cursor at the "ghost" non-element that can mutate the linked list links.
    #[verus_spec(
        with Tracked(owner): Tracked<&mut LinkedListOwner<M>>
    )]
    fn cursor_at_ghost_mut(&mut self) -> CursorMut<'_, M> {
        CursorMut { list: self, current: None }
    }

    /// # Verification Assumption
    /// We assume that there is an available ID for `lazy_get_id` to return.
    /// This is safe because it will panic if the ID allocator is exhausted.
    #[verifier::external_body]
    #[verus_spec(
        with Tracked(owner): Tracked<& LinkedListOwner<M>>
    )]
    fn lazy_get_id(&mut self) -> (id: u64)
        ensures
            owner.list_id != 0 ==> id == owner.list_id,
            final(self).size == old(self).size,
            final(self).front == old(self).front,
            final(self).back == old(self).back,
            old(self).list_id != 0 ==> final(self).list_id == old(self).list_id,
    {
        unimplemented!()/*        // FIXME: Self-incrementing IDs may overflow, while `core::pin::Pin`
        // is not compatible with locks. Think about a better solution.
        static LIST_ID_ALLOCATOR: AtomicU64 = AtomicU64::new(1);
        const MAX_LIST_ID: u64 = i64::MAX as u64;

        if self.list_id == 0 {
            let id = LIST_ID_ALLOCATOR.fetch_add(1, Ordering::Relaxed);
            if id >= MAX_LIST_ID {
//                log::error!("The frame list ID allocator has exhausted.");
//                abort();
                unimplemented!()
            }
            self.list_id = id;
            id
        } else {
            self.list_id
        }*/

    }
}

impl<'a, M: AnyFrameMeta + Repr<MetaSlotSmall>> CursorMut<'a, M> {
    /// Moves the cursor to the next frame towards the back.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this will
    /// move it to the first element of the [`LinkedList`]. If it is pointing
    /// to the last element of the LinkedList then this will move it to the
    /// "ghost" non-element.
    #[verus_spec(
        with Tracked(owner): Tracked<CursorOwner<M>>,
            Tracked(regions): Tracked<&MetaRegionOwners>,
    )]
    pub fn move_next(&mut self)
        requires
            owner.inv_region(*regions),
            old(self).wf_region(owner, *regions),
        ensures
            final(self).model(owner.move_next_owner_spec()) == old(self).model(
                owner,
            ).move_next_spec(),
            owner.move_next_owner_spec().inv_region(*regions),
            final(self).wf_region(owner.move_next_owner_spec(), *regions),
    {
        let ghost old_self = *self;

        proof {
            if self.current is Some {
                let _ = owner.list_own.list[owner.index];
                owner.list_own.relate_region_at_facts(*regions, owner.index);
            }
            if owner.index < owner.length() - 1 {
                let _ = owner.list_own.list[owner.index + 1];
                owner.list_own.relate_region_at_facts(*regions, owner.index + 1);
            }
        }

        self.current = match self.current {
            // SAFETY: The cursor is pointing to a valid element.
            Some(current) => {
                let current_md = MetadataAsLink::cast_to_metadata(current);
                let idx = frame_to_index(meta_to_frame(current.addr()));

                proof {
                    assert(idx == owner.list_own.slot_index_at(owner.index));
                    assert(regions.slots.contains_key(idx));
                    assert(regions.slot_owners.contains_key(idx));
                }

                let tracked meta_perm = regions.borrow_typed_perm::<Link<M>>(idx);

                borrow_field!(current_md => next, Meta(meta_perm))
            },
            None => self.list.front,
        };

        proof {
            LinkedListOwner::<M>::view_preserves_len(owner.list_own.list);
            assert(self.model(owner.move_next_owner_spec()).fore == old_self.model(
                owner,
            ).move_next_spec().fore);
            assert(self.model(owner.move_next_owner_spec()).rear == old_self.model(
                owner,
            ).move_next_spec().rear);
        }
    }

    /// Moves the cursor to the previous frame towards the front.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this will
    /// move it to the last element of the [`LinkedList`]. If it is pointing
    /// to the first element of the LinkedList then this will move it to the
    /// "ghost" non-element.
    #[verus_spec(
        with Tracked(owner): Tracked<CursorOwner<M>>,
            Tracked(regions): Tracked<&MetaRegionOwners>,
    )]
    pub fn move_prev(&mut self)
        requires
            owner.inv_region(*regions),
            old(self).wf_region(owner, *regions),
        ensures
            final(self).model(owner.move_prev_owner_spec()) == old(self).model(
                owner,
            ).move_prev_spec(),
            owner.move_prev_owner_spec().inv_region(*regions),
            final(self).wf_region(owner.move_prev_owner_spec(), *regions),
    {
        let ghost old_self = *self;

        proof {
            if self.current is Some {
                let _ = owner.list_own.list[owner.index];
                owner.list_own.relate_region_at_facts(*regions, owner.index);
            }
            if 0 < owner.index {
                let _ = owner.list_own.list[owner.index - 1];
                owner.list_own.relate_region_at_facts(*regions, owner.index - 1);
            }
        }

        self.current = match self.current {
            // SAFETY: The cursor is pointing to a valid element.
            Some(current) => {
                let current_md = MetadataAsLink::cast_to_metadata(current);
                let idx = frame_to_index(meta_to_frame(current.addr()));

                proof {
                    assert(idx == owner.list_own.slot_index_at(owner.index));
                    assert(regions.slots.contains_key(idx));
                    assert(regions.slot_owners.contains_key(idx));
                }

                let tracked meta_perm = regions.borrow_typed_perm::<Link<M>>(idx);

                borrow_field!(current_md => prev, Meta(meta_perm))
            },
            None => self.list.back,
        };

        proof {
            LinkedListOwner::<M>::view_preserves_len(owner.list_own.list);

            if owner@.list_model.list.len() > 0 {
                if owner@.fore.len() > 0 {
                    assert(self.model(owner.move_prev_owner_spec()).fore == old_self.model(
                        owner,
                    ).move_prev_spec().fore);
                    assert(self.model(owner.move_prev_owner_spec()).rear == old_self.model(
                        owner,
                    ).move_prev_spec().rear);
                    if owner@.rear.len() > 0 {
                        let _ = owner.list_own.list[owner.index];
                        owner.list_own.relate_region_at_facts(*regions, owner.index);
                    }
                } else {
                    let _ = owner.list_own.list[owner.index];
                    owner.list_own.relate_region_at_facts(*regions, owner.index);
                    assert(self.model(owner.move_prev_owner_spec()).rear == old_self.model(
                        owner,
                    ).move_prev_spec().rear);
                    assert(owner@.rear == owner@.list_model.list);
                }
            }
        }
    }

    /// Gets the mutable reference to the current frame's metadata.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// The cursor must be well-formed with respect to the tracked `CursorOwner`.
    /// ## Postconditions
    /// If the cursor is on an element, returns `Some(&mut meta)` borrowing the
    /// current link's metadata. The cursor state and list shape are otherwise
    /// unchanged; the current metadata permission remains borrowed while the
    /// returned reference is live.
    /// ## Safety
    /// The `&mut self` guarantees exclusive access to the cursor; the tracked
    /// `CursorOwner` guarantees the perm for the current link is live.
    #[verus_spec(
        with Tracked(owner): Tracked<&'b mut CursorOwner<M>>,
            Tracked(regions): Tracked<&'b mut MetaRegionOwners>,
    )]
    pub fn current_meta<'b>(&'b mut self) -> (res: Option<&'b mut M>)
        requires
            old(self).wf_region(*old(owner), *old(regions)),
            old(owner).inv_region(*old(regions)),
            old(regions).inv(),
        ensures
            final(owner).index == old(owner).index,
            final(owner).list_own.list == old(owner).list_own.list,
            final(owner).list_own.list_id == old(owner).list_own.list_id,
            *final(self) == *old(self),
            res.is_some() == (0 <= final(owner).index < final(owner).length()),
            final(regions).slots.dom() == old(regions).slots.dom(),
            final(regions).slot_owners.dom() == old(regions).slot_owners.dom(),
    {
        // Verus does not support option.map very well.
        // self.current.map(|current| {
        //     let link_mut = unsafe { &mut *(current.ptr.addr() as *mut Link<M>) };
        //     &mut link_mut.meta
        // })
        match self.current {
            Some(current) => {
                proof {
                    assert(self.wf_region(*owner, *regions));
                    assert(owner.inv_region(*regions));
                    assert(0 <= owner.index <= owner.length());
                    if !(0 <= owner.index < owner.length()) {
                        assert(owner.index == owner.length());
                        assert(self.current.is_none());
                        assert(false);
                    }
                    let _ = owner.list_own.list[owner.index];
                    owner.list_own.relate_region_at_facts(*regions, owner.index);
                    assert(current == self.current.unwrap());
                }
                let current_md = MetadataAsLink::cast_to_metadata(current);
                let idx = frame_to_index(meta_to_frame(current.addr()));
                proof {
                    assert(idx == owner.list_own.slot_index_at(owner.index));
                    assert(regions.slots.contains_key(idx));
                    assert(regions.slot_owners.contains_key(idx));
                }
                let tracked current_perm = regions.borrow_mut_typed_perm::<Link<M>>(idx);
                let link_md = current_md.borrow_mut(Tracked(current_perm));
                let meta = &mut link_md.metadata.meta;
                Some(meta)
            },
            None => {
                proof {
                    assert(self.wf_region(*owner, *regions));
                    assert(owner.inv_region(*regions));
                    if 0 <= owner.index < owner.length() {
                        assert(self.current.is_some());
                        assert(false);
                    }
                }
                None
            },
        }
    }

    /// Takes the current pointing frame out of the linked list.
    ///
    /// If successful, the frame is returned and the cursor is moved to the
    /// next frame. If the cursor is pointing to the back of the list then it
    /// is moved to the "ghost" non-element.
    /// # Verified Properties
    /// ## Preconditions
    /// The cursor must be well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects. The list must be non-empty, so that the
    /// current frame is valid.
    /// ## Postconditions
    /// The current frame is removed from the list, and the cursor is moved to the next frame.
    /// The list invariants are preserved.
    /// ## Safety
    /// This function calls `from_raw` on the frame, but we guarantee that the frame is forgotten
    /// if it is in the list. So, double-free will not occur. All loads and stores are through track
    /// tracked permissions, so there are no illegal memory accesses. No data races are possible.
    #[verus_spec(
        with Tracked(regions) : Tracked<&mut MetaRegionOwners>,
            Tracked(owner) : Tracked<&mut CursorOwner<M>>
    )]
    #[verifier::rlimit(8000)]
    #[verifier::spinoff_prover]
    pub fn take_current(&mut self) -> (res: Option<
        (UniqueFrame<Link<M>>, Tracked<UniqueFrameOwner<Link<M>>>),
    >)
        requires
            old(self).wf_region(*old(owner), *old(regions)),
            old(owner).inv_region(*old(regions)),
            old(regions).inv(),
            old(owner).length() > 0 ==> old(regions).slot_owners.contains_key(
                frame_to_index(meta_to_frame(old(self).current.unwrap().addr())),
            ),
        ensures
            old(owner).length() == 0 ==> res.is_none(),
            old(self).current.is_some() ==> res.is_some(),
            res.is_some() ==> res.unwrap().0.model(res.unwrap().1@).meta == old(
                owner,
            ).list_own.list[old(owner).index]@,
            res.is_some() ==> final(self).model(*final(owner)) == old(self).model(
                *old(owner),
            ).remove(),
            res.is_some() ==> res.unwrap().1@.frame_link_inv(*final(regions)),
            // Invariant preservation
            res.is_some() ==> final(owner).inv_region(*final(regions)),
            res.is_some() ==> final(self).wf_region(*final(owner), *final(regions)),
            res.is_none() ==> *final(owner) =~= *old(owner),
            final(regions).inv(),
            // Structural: remove_owner_spec
            res.is_some() ==> final(owner).index == old(owner).index,
            res.is_some() ==> final(owner).list_own.list == old(owner).list_own.list.remove(
                old(owner).index,
            ),
            final(owner).list_own.list_id == old(owner).list_own.list_id,
            res.is_some() ==> {
                let paddr = old(self).current.unwrap().addr();
                let idx = frame_to_index(meta_to_frame(paddr));
                &&& final(regions).slot_owners[idx].raw_count == old(
                    regions,
                ).slot_owners[idx].raw_count - 1
                &&& final(regions).slots.dom() =~= old(regions).slots.dom()
                &&& final(regions).slot_owners[idx].inner_perms.ref_count.value()
                    == crate::specs::mm::frame::meta_owners::REF_COUNT_UNIQUE
                &&& final(regions).slot_owners[idx].inner_perms.in_list.value() == 0
                &&& final(regions).slot_owners[idx].inner_perms.storage.is_init()
                &&& final(regions).slot_owners[idx].inner_perms.vtable_ptr.is_init()
                &&& final(regions).slot_owners[idx].self_addr == meta_addr(idx)
                &&& final(regions).slot_owners[idx].paths_in_pt == old(
                    regions,
                ).slot_owners[idx].paths_in_pt
            },
            res.is_some() ==> forall|j: usize|
                #![trigger final(regions).slot_owners[j]]
                j != frame_to_index(meta_to_frame(old(self).current.unwrap().addr())) ==> {
                    &&& final(regions).slot_owners[j].raw_count == old(
                        regions,
                    ).slot_owners[j].raw_count
                    &&& final(regions).slot_owners[j].usage == old(regions).slot_owners[j].usage
                    &&& final(regions).slot_owners[j].self_addr == old(
                        regions,
                    ).slot_owners[j].self_addr
                    &&& final(regions).slot_owners[j].paths_in_pt == old(
                        regions,
                    ).slot_owners[j].paths_in_pt
                },
            res.is_none() ==> *final(regions) =~= *old(regions),
            // Properties of the returned frame needed for UniqueFrame::drop
            res.is_some() ==> res.unwrap().0.wf(res.unwrap().1@),
            res.is_some() ==> res.unwrap().1@.inv(),
            res.is_some() ==> res.unwrap().1@.slot_index == frame_to_index(
                meta_to_frame(old(self).current.unwrap().addr()),
            ),
            res.is_some() ==> res.unwrap().0.ptr.addr() == old(self).current.unwrap().addr(),
    {
        let ghost owner0 = *owner;
        let ghost regions0 = *regions;

        let current = self.current?;
        let current_md = MetadataAsLink::cast_to_metadata(current);

        proof {
            assert(0 <= owner.index < owner.list_own.list.len());
            let _ = owner.list_own.list[owner.index];
            owner.list_own.relate_region_at_facts(*regions, owner.index);
            if owner.index > 0 {
                let _ = owner.list_own.list[owner.index - 1];
                owner.list_own.relate_region_at_facts(*regions, owner.index - 1);
            }
            if owner.index < owner.list_own.list.len() - 1 {
                let _ = owner.list_own.list[owner.index + 1];
                owner.list_own.relate_region_at_facts(*regions, owner.index + 1);
            }
        }

        let meta_ptr = current.addr();
        let paddr = meta_to_frame(meta_ptr);
        let idx = frame_to_index(paddr);

        assert(current.addr() == owner.list_own.list[owner.index].paddr);
        assert(idx == owner.list_own.slot_index_at(owner.index));

        let tracked mut cur_own = owner.list_own.list.tracked_remove(owner.index);

        let (frame, frame_own) = unsafe {
            #[verus_spec(with Tracked(regions), Tracked(cur_own))]
            UniqueFrame::<Link<M>>::from_raw(paddr)
        };
        let frame = frame;
        let tracked frame_own = frame_own.get();

        proof {
            assert(regions.slots.dom() =~= regions0.slots.dom());
            assert(regions.slot_owners[idx].raw_count == regions0.slot_owners[idx].raw_count - 1);
            assert forall|j: usize| j != idx implies {
                &&& regions.slot_owners[j].raw_count == regions0.slot_owners[j].raw_count
                &&& regions.slot_owners[j].usage == regions0.slot_owners[j].usage
                &&& regions.slot_owners[j].self_addr == regions0.slot_owners[j].self_addr
                &&& regions.slot_owners[j].paths_in_pt == regions0.slot_owners[j].paths_in_pt
            } by {}
        }

        let tracked tp = regions.borrow_typed_perm::<Link<M>>(idx);
        proof {
            assert(*tp =~= owner0.list_own.meta_perm_of(regions0, owner0.index));
        }
        let next_ptr = borrow_field!(current_md => next, Meta(tp));
        let prev_ptr = borrow_field!(current_md => prev, Meta(tp));

        if let Some(prev_link) = prev_ptr {
            let prev = MetadataAsLink::cast_to_metadata(prev_link);
            proof {
                assert(owner0.index > 0);
                assert(prev.addr() == owner0.list_own.list[owner0.index - 1].paddr);
                assert(frame_to_index(meta_to_frame(prev.addr())) == owner0.list_own.slot_index_at(
                    owner0.index - 1,
                ));
                assert(frame_to_index(meta_to_frame(prev.addr())) != idx);  // distinctness
                assert(regions.slots[frame_to_index(meta_to_frame(prev.addr()))].pptr()
                    == prev.ptr);
            }

            let tracked prev_perm = regions.borrow_mut_typed_perm::<Link<M>>(
                frame_to_index(meta_to_frame(prev.addr())),
            );
            update_field!(prev => next <- next_ptr, Meta(prev_perm));

            proof {
                assert(regions.inv());
                assert(regions.slot_owners[idx].raw_count == regions0.slot_owners[idx].raw_count
                    - 1);
                assert(regions.slots.dom() =~= regions0.slots.dom());
                assert forall|j: usize| j != idx implies {
                    &&& regions.slot_owners[j].raw_count == regions0.slot_owners[j].raw_count
                    &&& regions.slot_owners[j].usage == regions0.slot_owners[j].usage
                    &&& regions.slot_owners[j].self_addr == regions0.slot_owners[j].self_addr
                    &&& regions.slot_owners[j].paths_in_pt == regions0.slot_owners[j].paths_in_pt
                } by {
                    if j == frame_to_index(meta_to_frame(prev.addr())) {
                    }
                }
            }

            assert(owner0.index > 0);
        } else {
            self.list.front = next_ptr;
            proof {
                assert(regions.slot_owners[idx].raw_count == regions0.slot_owners[idx].raw_count
                    - 1);
                assert(regions.slots.dom() =~= regions0.slots.dom());
                assert forall|j: usize| j != idx implies {
                    &&& regions.slot_owners[j].raw_count == regions0.slot_owners[j].raw_count
                    &&& regions.slot_owners[j].usage == regions0.slot_owners[j].usage
                    &&& regions.slot_owners[j].self_addr == regions0.slot_owners[j].self_addr
                    &&& regions.slot_owners[j].paths_in_pt == regions0.slot_owners[j].paths_in_pt
                } by {}
            }
        }

        if let Some(next_link) = next_ptr {
            let next = MetadataAsLink::cast_to_metadata(next_link);
            proof {
                assert(owner0.index < owner0.list_own.list.len() - 1);
                assert(next.addr() == owner0.list_own.list[owner0.index + 1].paddr);
                assert(frame_to_index(meta_to_frame(next.addr())) == owner0.list_own.slot_index_at(
                    owner0.index + 1,
                ));
                assert(frame_to_index(meta_to_frame(next.addr())) != idx);  // distinctness
                assert(regions.slots[frame_to_index(meta_to_frame(next.addr()))].pptr()
                    == next.ptr);
            }

            let tracked next_perm = regions.borrow_mut_typed_perm::<Link<M>>(
                frame_to_index(meta_to_frame(next.addr())),
            );
            update_field!(next => prev <- prev_ptr, Meta(next_perm));

            proof {
                assert(regions.inv());
                assert(regions.slot_owners[idx].raw_count == regions0.slot_owners[idx].raw_count
                    - 1);
                assert(regions.slots.dom() =~= regions0.slots.dom());
                assert forall|j: usize| j != idx implies {
                    &&& regions.slot_owners[j].raw_count == regions0.slot_owners[j].raw_count
                    &&& regions.slot_owners[j].usage == regions0.slot_owners[j].usage
                    &&& regions.slot_owners[j].self_addr == regions0.slot_owners[j].self_addr
                    &&& regions.slot_owners[j].paths_in_pt == regions0.slot_owners[j].paths_in_pt
                } by {
                    if j == frame_to_index(meta_to_frame(next.addr())) {
                    }
                }
            }

            self.current = Some(next_link);
        } else {
            self.list.back = prev_ptr;

            self.current = None;
            proof {
                assert(regions.slot_owners[idx].raw_count == regions0.slot_owners[idx].raw_count
                    - 1);
                assert(regions.slots.dom() =~= regions0.slots.dom());
                assert forall|j: usize| j != idx implies {
                    &&& regions.slot_owners[j].raw_count == regions0.slot_owners[j].raw_count
                    &&& regions.slot_owners[j].usage == regions0.slot_owners[j].usage
                    &&& regions.slot_owners[j].self_addr == regions0.slot_owners[j].self_addr
                    &&& regions.slot_owners[j].paths_in_pt == regions0.slot_owners[j].paths_in_pt
                } by {}
            }
        }

        let tracked frame_perm = regions.borrow_mut_typed_perm::<Link<M>>(idx);
        update_field!(current_md => next <- None, Meta(frame_perm));

        let tracked frame_perm = regions.borrow_mut_typed_perm::<Link<M>>(idx);
        update_field!(current_md => prev <- None, Meta(frame_perm));

        let tracked frame_outer = regions.slots.tracked_remove(idx);
        let tracked mut frame_so = regions.slot_owners.tracked_remove(idx);
        let tracked mut fip = frame_so.take_inner_perms();
        #[verus_spec(with Tracked(&frame_outer))]
        let slot = frame.slot();
        slot.in_list.store(Tracked(&mut fip.in_list), 0);
        proof {
            frame_so.sync_inner(&fip);
            regions.slots.tracked_insert(idx, frame_outer);
            regions.slot_owners.tracked_insert(idx, frame_so);
            assert(regions.inv());
            assert(regions.slots.dom() =~= regions0.slots.dom());
            assert(regions.slot_owners[idx].raw_count == regions0.slot_owners[idx].raw_count - 1);
            assert(regions.slot_owners[idx].paths_in_pt == regions0.slot_owners[idx].paths_in_pt);
            assert forall|j: usize| j != idx implies {
                &&& regions.slot_owners[j].raw_count == regions0.slot_owners[j].raw_count
                &&& regions.slot_owners[j].usage == regions0.slot_owners[j].usage
                &&& regions.slot_owners[j].self_addr == regions0.slot_owners[j].self_addr
                &&& regions.slot_owners[j].paths_in_pt == regions0.slot_owners[j].paths_in_pt
            } by {}
        }

        self.list.size = self.list.size - 1;

        proof {
            owner0.remove_owner_spec_implies_model_spec(*owner);
            let ghost oldl = owner0.list_own;
            let ghost nn = owner0.index as int;
            assert forall|p: int|
                #![trigger oldl.slot_index_at(p)]
                (0 <= p < oldl.list.len() && p != nn) implies ({
                let i = oldl.slot_index_at(p);
                let fp = vstd_extra::cast_ptr::PointsTo::<MetaSlot, Metadata<Link<M>>>::new_spec(
                    regions.slots[i],
                    regions.slot_owners[i].inner_perms,
                );
                &&& regions.slots.contains_key(i)
                &&& regions.slot_owners.contains_key(i)
                &&& fp.addr() == oldl.list[p].paddr
                &&& fp.points_to.addr() == oldl.list[p].paddr
                &&& fp.points_to.pptr() == regions0.slots[i].pptr()
                &&& fp.inner_perms.ref_count.value()
                    == crate::specs::mm::frame::meta_owners::REF_COUNT_UNIQUE
                &&& regions.slot_owners[i].raw_count > 0
                &&& fp.wf(&fp.inner_perms)
                &&& fp.addr() % META_SLOT_SIZE == 0
                &&& FRAME_METADATA_RANGE.start <= fp.addr() < FRAME_METADATA_RANGE.start
                    + MAX_NR_PAGES * META_SLOT_SIZE
                &&& fp.is_init()
                &&& (p == nn - 1 ==> fp.value().metadata.next == oldl.meta_perm_of(
                    regions0,
                    nn,
                ).value().metadata.next)
                &&& (p != nn - 1 ==> fp.value().metadata.next == oldl.meta_perm_of(
                    regions0,
                    p,
                ).value().metadata.next)
                &&& (p == nn + 1 ==> fp.value().metadata.prev == oldl.meta_perm_of(
                    regions0,
                    nn,
                ).value().metadata.prev)
                &&& (p != nn + 1 ==> fp.value().metadata.prev == oldl.meta_perm_of(
                    regions0,
                    p,
                ).value().metadata.prev)
            }) by {
                let i = oldl.slot_index_at(p);
                let _ = oldl.list[p];
                oldl.relate_region_at_facts(regions0, p);
                let _ = oldl.list[nn];
                oldl.relate_region_at_facts(regions0, nn);
                let _ = oldl.slot_index_at(nn - 1);
                let _ = oldl.slot_index_at(nn + 1);
                let _ = oldl.slot_index_at(nn);
            }
            LinkedListOwner::pop_preserves_relate_region(
                oldl,
                regions0,
                owner.list_own,
                *regions,
                nn,
            );
        }
        Some((frame, Tracked(frame_own)))
    }

    /// Inserts a frame before the current frame.
    ///
    /// If the cursor is pointing at the "ghost" non-element then the new
    /// element is inserted at the back of the [`LinkedList`].
    /// # Verified Properties
    /// ## Preconditions
    /// The cursor must be well-formed, with the pointers to its links' metadata slots matching the tracked permission objects.
    /// - The new frame must be active, so that it is valid to call `into_raw` on it.
    /// ## Postconditions
    /// - The new frame is inserted into the list, immediately before the current index.
    /// - The list invariants are preserved.
    /// ## Safety
    /// - This function calls `into_raw` on the frame, so the caller must ensure that the frame is active and
    /// has not been forgotten already to avoid a memory leak. If the caller attempts to insert a forgotten frame,
    /// the invariant around `into_raw` and `from_raw` will be violated. But, it is the safe failure case in that
    /// it will not cause a double-free. (Note: we should be able to move this requirement into the `UniqueFrame` invariants.)
    #[verus_spec(
        with Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(owner): Tracked<&mut CursorOwner<M>>,
            Tracked(frame_own): Tracked<&mut UniqueFrameOwner<Link<M>>>
    )]
    #[verifier::rlimit(8000)]
    #[verifier::spinoff_prover]
    pub fn insert_before(&mut self, mut frame: UniqueFrame<Link<M>>)
        requires
            old(self).wf_region(*old(owner), *old(regions)),
            old(owner).inv_region(*old(regions)),
            old(regions).inv(),
            old(owner).list_own.list_id != 0,
            old(frame_own).inv(),
            old(frame_own).global_inv(*old(regions)),
            frame.wf(*old(frame_own)),
            old(frame_own).frame_link_inv(*old(regions)),
            old(owner).length() < usize::MAX,
            old(regions).slot_owners[old(frame_own).slot_index].raw_count == 0,
            old(regions).slot_owners[old(frame_own).slot_index].inner_perms.ref_count.value()
                == crate::specs::mm::frame::meta_owners::REF_COUNT_UNIQUE,
            old(regions).slot_owners[old(frame_own).slot_index].inner_perms.in_list.is_for(
                old(regions).slots[old(frame_own).slot_index].value().in_list,
            ),
            forall|p: int|
                #![trigger old(owner).list_own.slot_index_at(p)]
                0 <= p < old(owner).list_own.list.len() ==> old(owner).list_own.slot_index_at(p)
                    != old(frame_own).slot_index,
        ensures
            final(owner).inv_region(*final(regions)),
            final(self).wf_region(*final(owner), *final(regions)),
            final(regions).inv(),
            final(owner).list_own.list == old(owner).list_own.list.insert(
                old(owner).index,
                final(frame_own).meta_own,
            ),
            final(owner).list_own.list_id == old(owner).list_own.list_id,
            final(owner).index == old(owner).index + 1,
            final(frame_own).meta_own.paddr == old(frame_own).meta_own.paddr,
            final(frame_own).meta_own.in_list == old(owner).list_own.list_id,
            final(self).model(*final(owner)) == old(self).model(*old(owner)).insert(
                final(frame_own).meta_own@,
            ),
    {
        let ghost owner0 = *owner;
        let ghost regions0 = *regions;
        let ghost nn = owner.index as int;

        proof {
            if nn > 0 {
                let _ = owner.list_own.list[nn - 1];
                owner.list_own.relate_region_at_facts(*regions, nn - 1);
            }
            if nn < owner.list_own.list.len() {
                let _ = owner.list_own.list[nn];
                owner.list_own.relate_region_at_facts(*regions, nn);
            }
        }

        #[verus_spec(with Tracked(&*frame_own), Tracked(&*regions))]
        let frame_ptr = frame.meta_mut();
        let frame_ptr_as_link = MetadataAsLink::cast_from_metadata(frame_ptr);

        let ghost frame_idx_g: usize = frame_own.slot_index;

        if let Some(current) = self.current {
            let current_md = MetadataAsLink::cast_to_metadata(current);

            // Read current's prev pointer.
            let opt_prev_link: Option<ReprPtr<MetaSlot, MetadataAsLink<M>>>;

            let tracked tp = regions.borrow_typed_perm::<Link<M>>(
                frame_to_index(meta_to_frame(current.addr())),
            );
            opt_prev_link = borrow_field!(current_md => prev, Meta(tp));

            if let Some(prev_link) = opt_prev_link {
                let prev = MetadataAsLink::cast_to_metadata(prev_link);

                let tracked perm = regions.borrow_mut_typed_perm::<Link<M>>(
                    frame_to_index(meta_to_frame(prev.addr())),
                );
                update_field!(prev => next <- Some(frame_ptr_as_link), Meta(perm));

                let tracked perm = regions.borrow_mut_typed_perm::<Link<M>>(frame_idx_g);
                update_field!(frame_ptr => prev <- Some(prev_link), Meta(perm));

                let tracked perm = regions.borrow_mut_typed_perm::<Link<M>>(frame_idx_g);
                update_field!(frame_ptr => next <- Some(current), Meta(perm));

                let tracked perm = regions.borrow_mut_typed_perm::<Link<M>>(
                    frame_to_index(meta_to_frame(current.addr())),
                );
                update_field!(current_md => prev <- Some(frame_ptr_as_link), Meta(perm));

                proof {
                    let fpn_local = vstd_extra::cast_ptr::PointsTo::<
                        MetaSlot,
                        Metadata<Link<M>>,
                    >::new_spec(
                        regions.slots[frame_idx_g],
                        regions.slot_owners[frame_idx_g].inner_perms,
                    );
                    assert(fpn_local.value().metadata.prev is Some);
                    assert(fpn_local.value().metadata.prev.unwrap().addr()
                        == owner0.list_own.list[nn - 1].paddr);
                    assert(fpn_local.value().metadata.prev.unwrap().ptr
                        == regions0.slots[owner0.list_own.slot_index_at(nn - 1)].pptr());
                    assert(fpn_local.value().metadata.next is Some);
                    assert(fpn_local.value().metadata.next.unwrap().addr()
                        == owner0.list_own.list[nn].paddr);
                    assert(fpn_local.value().metadata.next.unwrap().ptr
                        == regions0.slots[owner0.list_own.slot_index_at(nn)].pptr());
                    assert(fpn_local.inner_perms.ref_count.value()
                        == crate::specs::mm::frame::meta_owners::REF_COUNT_UNIQUE);
                }
            } else {
                let tracked perm = regions.borrow_mut_typed_perm::<Link<M>>(frame_idx_g);
                update_field!(frame_ptr => next <- Some(current), Meta(perm));

                let tracked perm = regions.borrow_mut_typed_perm::<Link<M>>(
                    frame_to_index(meta_to_frame(current.addr())),
                );
                update_field!(current_md => prev <- Some(frame_ptr_as_link), Meta(perm));

                self.list.front = Some(frame_ptr_as_link);
                proof {
                    let fpn_local = vstd_extra::cast_ptr::PointsTo::<
                        MetaSlot,
                        Metadata<Link<M>>,
                    >::new_spec(
                        regions.slots[frame_idx_g],
                        regions.slot_owners[frame_idx_g].inner_perms,
                    );
                    assert(fpn_local.value().metadata.prev is None);
                    assert(fpn_local.value().metadata.next is Some);
                    assert(fpn_local.value().metadata.next.unwrap().addr()
                        == owner0.list_own.list[nn].paddr);
                    assert(fpn_local.value().metadata.next.unwrap().ptr
                        == regions0.slots[owner0.list_own.slot_index_at(nn)].pptr());
                    assert(fpn_local.inner_perms.ref_count.value()
                        == crate::specs::mm::frame::meta_owners::REF_COUNT_UNIQUE);
                }
            }
        } else {
            if let Some(back) = self.list.back {
                let back_md = MetadataAsLink::cast_to_metadata(back);

                let tracked perm = regions.borrow_mut_typed_perm::<Link<M>>(
                    frame_to_index(meta_to_frame(back.addr())),
                );
                update_field!(back_md => next <- Some(frame_ptr_as_link), Meta(perm));

                let tracked perm = regions.borrow_mut_typed_perm::<Link<M>>(frame_idx_g);
                update_field!(frame_ptr => prev <- Some(back), Meta(perm));

                self.list.back = Some(frame_ptr_as_link);
                proof {
                    let fpn_local = vstd_extra::cast_ptr::PointsTo::<
                        MetaSlot,
                        Metadata<Link<M>>,
                    >::new_spec(
                        regions.slots[frame_idx_g],
                        regions.slot_owners[frame_idx_g].inner_perms,
                    );
                    assert(fpn_local.value().metadata.prev is Some);
                    assert(fpn_local.value().metadata.prev.unwrap().addr()
                        == owner0.list_own.list[nn - 1].paddr);
                    assert(fpn_local.value().metadata.prev.unwrap().ptr
                        == regions0.slots[owner0.list_own.slot_index_at(nn - 1)].pptr());
                    assert(fpn_local.value().metadata.next is None);
                    assert(fpn_local.inner_perms.ref_count.value()
                        == crate::specs::mm::frame::meta_owners::REF_COUNT_UNIQUE);
                }
            } else {
                // EMPTY list: just point both ends at the inserted frame.
                self.list.front = Some(frame_ptr_as_link);
                self.list.back = Some(frame_ptr_as_link);
                proof {
                    let fpn_local = vstd_extra::cast_ptr::PointsTo::<
                        MetaSlot,
                        Metadata<Link<M>>,
                    >::new_spec(
                        regions.slots[frame_idx_g],
                        regions.slot_owners[frame_idx_g].inner_perms,
                    );
                    assert(fpn_local.value().metadata.prev is None);
                    assert(fpn_local.value().metadata.next is None);
                    assert(fpn_local.inner_perms.ref_count.value()
                        == crate::specs::mm::frame::meta_owners::REF_COUNT_UNIQUE);
                }
            }
        }

        #[verus_spec(with Tracked(&owner.list_own))]
        let list_id = self.list.lazy_get_id();

        let tracked frame_outer = regions.slots.tracked_remove(frame_idx_g);
        let tracked mut frame_so = regions.slot_owners.tracked_remove(frame_idx_g);
        let tracked mut fip = frame_so.take_inner_perms();
        #[verus_spec(with Tracked(&frame_outer))]
        let slot = frame.slot();
        slot.in_list.store(Tracked(&mut fip.in_list), list_id);
        proof {
            frame_so.sync_inner(&fip);
            regions.slots.tracked_insert(frame_idx_g, frame_outer);
            regions.slot_owners.tracked_insert(frame_idx_g, frame_so);
            assert(regions.inv());  // slot's UNIQUE branch: vtable+storage init preserved; in_list value change OK under UNIQUE.
        }

        #[verus_spec(with Tracked(&*frame_own), Tracked(regions))]
        let _ = frame.into_raw();

        proof {
            assert(self.list.size == owner.list_own.list.len());
            assert(owner.list_own.list.len() == owner0.list_own.list.len());
            assert(owner0.list_own.list.len() < usize::MAX);
        }
        self.list.size = self.list.size + 1;

        proof {
            CursorOwner::<M>::list_insert(owner, &mut frame_own.meta_own);

            let oldl = owner0.list_own;
            let nn = owner0.index as int;
            let flink = frame_own.meta_own;
            let ins = frame_own.slot_index;

            assert forall|p: int|
                #![trigger oldl.slot_index_at(p)]
                (0 <= p < oldl.list.len()) implies ({
                let i = oldl.slot_index_at(p);
                let fp = vstd_extra::cast_ptr::PointsTo::<MetaSlot, Metadata<Link<M>>>::new_spec(
                    regions.slots[i],
                    regions.slot_owners[i].inner_perms,
                );
                &&& regions.slots.contains_key(i)
                &&& regions.slot_owners.contains_key(i)
                &&& fp.addr() == oldl.list[p].paddr
                &&& fp.points_to.addr() == oldl.list[p].paddr
                &&& fp.points_to.pptr() == regions0.slots[i].pptr()
                &&& fp.inner_perms.ref_count.value()
                    == crate::specs::mm::frame::meta_owners::REF_COUNT_UNIQUE
                &&& regions.slot_owners[i].raw_count > 0
                &&& fp.wf(&fp.inner_perms)
                &&& fp.addr() % META_SLOT_SIZE == 0
                &&& FRAME_METADATA_RANGE.start <= fp.addr() < FRAME_METADATA_RANGE.start
                    + MAX_NR_PAGES * META_SLOT_SIZE
                &&& fp.is_init()
                &&& (p == nn - 1 ==> {
                    &&& fp.value().metadata.next is Some
                    &&& fp.value().metadata.next.unwrap().addr() == flink.paddr
                    &&& fp.value().metadata.next.unwrap().ptr == regions.slots[ins].pptr()
                })
                &&& (p != nn - 1 ==> fp.value().metadata.next == oldl.meta_perm_of(
                    regions0,
                    p,
                ).value().metadata.next)
                &&& (p == nn ==> {
                    &&& fp.value().metadata.prev is Some
                    &&& fp.value().metadata.prev.unwrap().addr() == flink.paddr
                    &&& fp.value().metadata.prev.unwrap().ptr == regions.slots[ins].pptr()
                })
                &&& (p != nn ==> fp.value().metadata.prev == oldl.meta_perm_of(
                    regions0,
                    p,
                ).value().metadata.prev)
            }) by {
                let i = oldl.slot_index_at(p);
                let _ = oldl.list[p];
                oldl.relate_region_at_facts(regions0, p);
                if nn - 1 >= 0 && nn - 1 < oldl.list.len() {
                    let _ = oldl.list[nn - 1];
                    oldl.relate_region_at_facts(regions0, nn - 1);
                }
                if nn >= 0 && nn < oldl.list.len() {
                    let _ = oldl.list[nn];
                    oldl.relate_region_at_facts(regions0, nn);
                }
                let _ = oldl.slot_index_at(nn - 1);
                let _ = oldl.slot_index_at(nn);
                let _ = oldl.slot_index_at(nn + 1);
            }

            let fpn = vstd_extra::cast_ptr::PointsTo::<MetaSlot, Metadata<Link<M>>>::new_spec(
                regions.slots[ins],
                regions.slot_owners[ins].inner_perms,
            );
            assert(regions.slots.contains_key(ins));
            assert(regions.slot_owners.contains_key(ins));
            assert(fpn.addr() == flink.paddr);
            assert(fpn.points_to.addr() == flink.paddr);
            assert(fpn.inner_perms.ref_count.value()
                == crate::specs::mm::frame::meta_owners::REF_COUNT_UNIQUE);
            assert(regions.slot_owners[ins].raw_count > 0);
            assert(fpn.wf(&fpn.inner_perms));
            assert(fpn.addr() % META_SLOT_SIZE == 0);
            assert(FRAME_METADATA_RANGE.start <= fpn.addr() < FRAME_METADATA_RANGE.start
                + MAX_NR_PAGES * META_SLOT_SIZE);
            assert(fpn.is_init());
            assert(nn == 0 <==> fpn.value().metadata.prev is None);
            assert(nn == oldl.list.len() <==> fpn.value().metadata.next is None);
            assert(nn > 0 ==> {
                &&& fpn.value().metadata.prev is Some
                &&& fpn.value().metadata.prev.unwrap().addr() == oldl.list[nn - 1].paddr
                &&& fpn.value().metadata.prev.unwrap().ptr == regions0.slots[oldl.slot_index_at(
                    nn - 1,
                )].pptr()
            });
            assert(nn < oldl.list.len() ==> {
                &&& fpn.value().metadata.next is Some
                &&& fpn.value().metadata.next.unwrap().addr() == oldl.list[nn].paddr
                &&& fpn.value().metadata.next.unwrap().ptr == regions0.slots[oldl.slot_index_at(
                    nn,
                )].pptr()
            });

            LinkedListOwner::insert_preserves_relate_region(
                oldl,
                regions0,
                owner.list_own,
                *regions,
                nn,
                flink,
            );

            owner0.insert_owner_spec_implies_model_spec(flink, *owner);
        }
    }

    /// Provides a reference to the linked list.
    pub fn as_list(&self) -> &LinkedList<M> {
        self.list
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> TrackDrop for LinkedList<M> {
    type State = (LinkedListOwner<M>, MetaRegionOwners);

    open spec fn constructor_requires(self, s: Self::State) -> bool {
        true
    }

    open spec fn constructor_ensures(self, s0: Self::State, s1: Self::State) -> bool {
        s0 =~= s1
    }

    proof fn constructor_spec(self, tracked s: &mut Self::State) {
    }

    open spec fn drop_requires(self, s: Self::State) -> bool {
        &&& self.wf(s.0)
        &&& s.0.inv()
        &&& s.1.inv()
        &&& forall|i: int|
            #![trigger s.0.list[i]]
            0 <= i < s.0.list.len() ==> s.1.slot_owners.contains_key(
                frame_to_index(meta_to_frame(s.0.list[i].paddr)),
            )
        &&& forall|i: int|
            #![trigger s.0.list[i]]
            0 <= i < s.0.list.len() ==> {
                let idx = frame_to_index(meta_to_frame(s.0.list[i].paddr));
                s.1.slots.contains_key(idx)
            }
        &&& forall|i: int|
            #![trigger s.0.list[i]]
            0 <= i < s.0.list.len() ==> {
                let idx = frame_to_index(meta_to_frame(s.0.list[i].paddr));
                s.1.slot_owners[idx].inner_perms.ref_count.value()
                    == crate::specs::mm::frame::meta_owners::REF_COUNT_UNIQUE
            }
        &&& forall|i: int|
            #![trigger s.0.list[i]]
            0 <= i < s.0.list.len() ==> {
                let idx = frame_to_index(meta_to_frame(s.0.list[i].paddr));
                s.1.slot_owners[idx].raw_count == 1
            }
        &&& forall|i: int|
            #![trigger s.0.list[i]]
            0 <= i < s.0.list.len() ==> {
                let idx = frame_to_index(meta_to_frame(s.0.list[i].paddr));
                s.1.slot_owners[idx].paths_in_pt.is_empty()
            }
        &&& forall|i: int, j: int|
            #![trigger s.0.list[i], s.0.list[j]]
            0 <= i < j < s.0.list.len() ==> frame_to_index(meta_to_frame(s.0.list[i].paddr))
                != frame_to_index(meta_to_frame(s.0.list[j].paddr))
        &&& s.0.relate_region(s.1)
    }

    open spec fn drop_ensures(self, s0: Self::State, s1: Self::State) -> bool {
        &&& s1.0.list.len() == 0
        &&& forall|i: int|
            #![trigger s0.0.list[i]]
            0 <= i < s0.0.list.len() ==> {
                let idx = frame_to_index(meta_to_frame(s0.0.list[i].paddr));
                s1.1.slot_owners[idx].raw_count == s0.1.slot_owners[idx].raw_count - 1
            }
        &&& forall|idx: usize|
            #![trigger s1.1.slot_owners[idx]]
            (forall|i: int|
                #![trigger s0.0.list[i]]
                0 <= i < s0.0.list.len() ==> idx != frame_to_index(
                    meta_to_frame(s0.0.list[i].paddr),
                )) ==> {
                &&& s1.1.slot_owners[idx].raw_count == s0.1.slot_owners[idx].raw_count
                &&& s1.1.slot_owners[idx].usage == s0.1.slot_owners[idx].usage
                &&& s1.1.slot_owners[idx].self_addr == s0.1.slot_owners[idx].self_addr
                &&& s1.1.slot_owners[idx].paths_in_pt == s0.1.slot_owners[idx].paths_in_pt
            }
        &&& s1.1.slots.dom() =~= s0.1.slots.dom()
        &&& s1.1.inv()
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> Drop for LinkedList<M> {
    #[verifier::rlimit(8000)]
    #[verifier::spinoff_prover]
    fn drop(self, Tracked(s): Tracked<&mut Self::State>) {
        // Pull the tuple components out from behind the `&mut`. We can't
        // move directly (E0507) and `cursor_front_mut` requires owned
        // `LinkedListOwner`. `tracked_take` swaps `s.0` with a fresh-empty
        // `LinkedListOwner`; we'll restore `*s` at the end of the body.
        // `MetaRegionOwners` can't be similarly emptied (its `inv()` requires
        // all valid slot indices), so we re-borrow `&mut s.1` for it.
        proof_decl! {
            let tracked mut list_own: LinkedListOwner<M>;
        }
        let ghost original_list = s.0.list;
        let ghost original_list_id = s.0.list_id;
        let ghost n = original_list.len();
        let ghost original_regions = s.1;
        proof {
            assert forall|j: int| #![trigger original_list[j]] 0 <= j < n implies ({
                let idx = frame_to_index(meta_to_frame(original_list[j].paddr));
                &&& original_regions.slot_owners.contains_key(idx)
                &&& original_regions.slots.contains_key(idx)
                &&& original_regions.slot_owners[idx].raw_count == 1
                &&& original_regions.slot_owners[idx].paths_in_pt.is_empty()
                &&& original_regions.slot_owners[idx].inner_perms.ref_count.value()
                    == crate::specs::mm::frame::meta_owners::REF_COUNT_UNIQUE
            }) by {
                let _ = s.0.list[j];
            };
            list_own = LinkedListOwner::<M>::tracked_take(&mut s.0);
        }
        let tracked regions: &mut MetaRegionOwners = &mut s.1;
        let mut this = self;

        #[verus_spec(with Tracked(list_own))]
        let cursor_pair = this.cursor_front_mut();
        let (mut cursor, Tracked(mut cursor_own)) = cursor_pair;

        proof {
            if n > 0 {
                let _ = cursor_own.list_own.list[0];
                cursor_own.list_own.relate_region_at_facts(*regions, 0);
                let _ = cursor_own.list_own.list[n as int - 1];
                cursor_own.list_own.relate_region_at_facts(*regions, n as int - 1);
            }
        }

        let ghost mut k: int = 0;

        loop
            invariant_except_break
                cursor.wf_region(cursor_own, *regions),
                cursor.current.is_some() <==> k < n,
            invariant
                cursor_own.inv_region(*regions),
                cursor_own.list_own.list_id == original_list_id,
                cursor_own.index == 0,
                regions.inv(),
                cursor_own.list_own.list.len() == n - k,
                0 <= k <= n,
                // The remaining list is a suffix of the original
                forall|j: int|
                    #![trigger cursor_own.list_own.list[j]]
                    0 <= j < n - k ==> cursor_own.list_own.list[j] == original_list[j + k],
                // Elements already taken have raw_count decremented
                forall|j: int|
                    #![trigger original_list[j]]
                    0 <= j < k ==> {
                        let idx = frame_to_index(meta_to_frame(original_list[j].paddr));
                        regions.slot_owners[idx].raw_count
                            == original_regions.slot_owners[idx].raw_count - 1
                    },
                // slots values inside the original_list.
                forall|idx: usize|
                    #![trigger regions.slot_owners[idx]]
                    (forall|j: int|
                        #![trigger original_list[j]]
                        0 <= j < n ==> idx != frame_to_index(meta_to_frame(original_list[j].paddr)))
                        ==> {
                        &&& regions.slot_owners[idx].raw_count
                            == original_regions.slot_owners[idx].raw_count
                        &&& regions.slot_owners[idx].usage
                            == original_regions.slot_owners[idx].usage
                        &&& regions.slot_owners[idx].self_addr
                            == original_regions.slot_owners[idx].self_addr
                        &&& regions.slot_owners[idx].paths_in_pt
                            == original_regions.slot_owners[idx].paths_in_pt
                    },
                regions.slots.dom() =~= original_regions.slots.dom(),
                // `paths_in_pt.is_empty()` precondition).
                forall|j: int|
                    #![trigger original_list[j]]
                    k <= j < n ==> {
                        let idx = frame_to_index(meta_to_frame(original_list[j].paddr));
                        &&& regions.slot_owners[idx].raw_count
                            == original_regions.slot_owners[idx].raw_count
                        &&& regions.slot_owners[idx].paths_in_pt
                            == original_regions.slot_owners[idx].paths_in_pt
                    },
                // Each remaining element's slot is in slot_owners
                forall|j: int|
                    #![trigger original_list[j]]
                    k <= j < n ==> regions.slot_owners.contains_key(
                        frame_to_index(meta_to_frame(original_list[j].paddr)),
                    ),
                // Distinct slot indices in original list (from drop_requires)
                forall|i: int, j: int|
                    #![trigger original_list[i], original_list[j]]
                    0 <= i < j < n ==> frame_to_index(meta_to_frame(original_list[i].paddr))
                        != frame_to_index(meta_to_frame(original_list[j].paddr)),
                forall|j: int|
                    #![trigger original_list[j]]
                    0 <= j < n ==> {
                        let idx = frame_to_index(meta_to_frame(original_list[j].paddr));
                        &&& original_regions.slot_owners.contains_key(idx)
                        &&& original_regions.slots.contains_key(idx)
                        &&& original_regions.slot_owners[idx].raw_count == 1
                        &&& original_regions.slot_owners[idx].paths_in_pt.is_empty()
                        &&& original_regions.slot_owners[idx].inner_perms.ref_count.value()
                            == crate::specs::mm::frame::meta_owners::REF_COUNT_UNIQUE
                    },
            ensures
                k == n,
                cursor_own.list_own.list.len() == 0,
            decreases n - k,
        {
            proof {
                if cursor.current.is_some() {
                    assert(cursor_own.length() > 0);
                    let _ = cursor_own.list_own.list[0];
                    cursor_own.list_own.relate_region_at_facts(*regions, 0);
                    let ghost _trigger = original_list[k as int];
                    assert(cursor.current.unwrap().addr() == original_list[k].paddr);
                }
            }

            #[verus_spec(with Tracked(regions), Tracked(&mut cursor_own))]
            let entry = cursor.take_current();

            if let Some(current) = entry {
                let ghost cur_addr = current.0.ptr.addr();
                let ghost cur_idx = frame_to_index(meta_to_frame(cur_addr));

                let (mut frame, frame_own_tracked) = current;
                let tracked frame_own = frame_own_tracked.get();

                proof {
                    let ghost _trig = original_list[k as int];
                    assert(cur_addr == original_list[k].paddr);
                    assert(cur_idx == frame_to_index(meta_to_frame(original_list[k].paddr)));
                    assert(original_regions.slot_owners[cur_idx].raw_count == 1);
                    assert(original_regions.slot_owners[cur_idx].paths_in_pt.is_empty());
                    assert(regions.slot_owners[cur_idx].raw_count == 0);
                    assert(regions.slot_owners[cur_idx].paths_in_pt.is_empty());
                    assert(frame_own.slot_index == cur_idx);
                }

                let ghost regions_pre_drop = *regions;

                // Drop the frame, returning its slot to regions
                #[verus_spec(with Tracked(frame_own), Tracked(regions))]
                frame.drop();

                proof {
                    assert forall|i: int|
                        #![trigger cursor_own.list_own.list[i]]
                        0 <= i < cursor_own.list_own.list.len() implies ({
                        let idx = cursor_own.list_own.slot_index_at(i);
                        &&& regions.slot_owners.contains_key(idx)
                        &&& regions.slot_owners[idx] == regions_pre_drop.slot_owners[idx]
                    }) by {
                        let idx = cursor_own.list_own.slot_index_at(i);
                        let _ = cursor_own.list_own.list[i];
                        let ghost _trig_k = original_list[k as int];
                        let ghost _trig_ik = original_list[i + k + 1];
                        assert(cursor_own.list_own.list[i] == original_list[i + k + 1]);
                        assert(idx == frame_to_index(
                            meta_to_frame(original_list[i + k + 1].paddr),
                        ));
                        assert(idx != cur_idx);
                    };
                    cursor_own.list_own.relate_region_preserved_external_change(
                        regions_pre_drop,
                        *regions,
                    );

                    assert forall|j: int|
                        #![trigger cursor_own.list_own.list[j]]
                        0 <= j < n - k - 1 implies cursor_own.list_own.list[j] == original_list[j
                        + k + 1] by {};

                    assert forall|j: int| #![trigger original_list[j]] 0 <= j < k implies ({
                        let idx = frame_to_index(meta_to_frame(original_list[j].paddr));
                        regions.slot_owners[idx].raw_count
                            == original_regions.slot_owners[idx].raw_count - 1
                    }) by {
                        let idx = frame_to_index(meta_to_frame(original_list[j].paddr));
                        let ghost _a = original_list[j as int];
                        let ghost _b = original_list[k as int];
                        assert(j < k);
                        assert(idx != cur_idx);
                    };

                    k = k + 1;
                }
            } else {
                break;
            }
        }

        // `s.1` is already updated in place via the re-borrow `regions`;
        // restore `s.0` to the cursor's final (empty) `list_own`.
        proof {
            let tracked mut final_list_own = cursor_own.list_own;
            vstd::modes::tracked_swap(&mut s.0, &mut final_list_own);
            final_list_own.tracked_destroy_empty();
        }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> Deref for Link<M> {
    type Target = M;

    fn deref(&self) -> &Self::Target {
        &self.meta
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> DerefMut for Link<M> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.meta
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> Link<M> {
    /// Creates a new linked list metadata.
    pub const fn new(meta: M) -> Self {
        Self { next: None, prev: None, meta }
    }
}

// SAFETY: If `M::on_drop` reads the page using the provided `VmReader`,
// the safety is upheld by the one who implements `AnyFrameMeta` for `M`.
unsafe impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> AnyFrameMeta for Link<M> {
    open spec fn on_drop_pre(
        &self,
        reader: crate::mm::VmReader<'_, crate::mm::Infallible>,
        regions: crate::specs::mm::frame::meta_region_owners::MetaRegionOwners,
        vm_io_owner: crate::specs::mm::io::VmIoOwner,
    ) -> bool {
        self.meta.on_drop_pre(reader, regions, vm_io_owner)
    }

    fn on_drop(
        &mut self,
        reader: &mut crate::mm::VmReader<crate::mm::Infallible>,
        regions: Tracked<&mut crate::specs::mm::frame::meta_region_owners::MetaRegionOwners>,
        vm_io_owner: Tracked<&mut crate::specs::mm::io::VmIoOwner>,
    ) {
        self.meta.on_drop(reader, regions, vm_io_owner);
    }

    fn is_untyped(&self) -> bool {
        self.meta.is_untyped()
    }

    uninterp spec fn vtable_ptr(&self) -> usize;
}

} // verus!
