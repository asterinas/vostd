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

use crate::mm::frame::meta::mapping::{frame_to_index, max_meta_slots, meta_addr, meta_to_frame, META_SLOT_SIZE};
use crate::specs::arch::kspace::FRAME_METADATA_RANGE;
use crate::mm::frame::meta::{get_slot, has_safe_slot, AnyFrameMeta, MetaSlot};

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
///     pub perms: Map<int, vstd_extra::cast_ptr::PointsTo<MetaSlot, Metadata<Link<M>>>>,
///     pub list_id: u64,
/// }
/// ```
/// ## Invariant
/// The linked list uniquely owns the raw frames that it contains, so they cannot be used by other
/// data structures. The frame metadata field `in_list` is equal to `list_id` for all links in the list.
/// ```rust
///    pub open spec fn inv_at(self, i: int) -> bool {
///        &&& self.perms.contains_key(i)
///        &&& self.perms[i].addr() == self.list[i].paddr
///        &&& self.perms[i].is_init()
///        &&& self.perms[i].value().wf(self.list[i])
///        &&& i == 0 <==> self.perms[i].mem_contents().value().prev is None
///        &&& i == self.list.len() - 1 <==> self.perms[i].value().next is None
///        &&& 0 < i ==> self.perms[i].value().prev is Some && self.perms[i].value().prev.unwrap()
///            == self.perms[i - 1].pptr()
///        &&& i < self.list.len() - 1 ==> self.perms[i].value().next is Some
///            && self.perms[i].value().next.unwrap() == self.perms[i + 1].pptr()
///        &&& self.list[i].inv()
///        &&& self.list[i].in_list == self.list_id
///    }
///
///    pub open spec fn inv(self) -> bool {
///        forall|i: int| 0 <= i < self.list.len() ==> self.inv_at(i)
///    }
/// ```
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
    pub fn size(&self) -> usize
    {
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
    pub fn is_empty(&self) -> bool
    {
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
            old(self).wf(*old(owner)),
            old(owner).inv(),
            old(owner).list_id != 0,
            old(frame_own).inv(),
            old(frame_own).global_inv(*old(regions)),
            frame.wf(*old(frame_own)),
            old(frame_own).frame_link_inv(),
            old(owner).list.len() < usize::MAX,
            old(regions).inv(),
            old(regions).slots.contains_key(old(frame_own).slot_index),
            old(regions).slot_owners[old(frame_own).slot_index].inner_perms.in_list.is_for(
                old(regions).slots[old(frame_own).slot_index].value().in_list,
            ),
        ensures
            final(owner).inv(),
            final(owner).list == old(owner).list.insert(0, final(frame_own).meta_own),
            final(owner).list_id == old(owner).list_id,
            final(frame_own).meta_own.paddr == old(frame_own).meta_own.paddr,
            final(frame_own).meta_own.in_list == old(owner).list_id,
    )]
    pub fn push_front(&mut self, frame: UniqueFrame<Link<M>>) {
        let current = self.front;
        let tracked mut cursor_own = CursorOwner::front_owner(*owner);
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
            old(self).wf(owner),
            owner.inv(),
            old(regions).slots.contains_key(frame_to_index(owner.list[0].paddr)),
        ensures
            owner.list.len() == 0 ==> r.is_none(),
            r.is_some() ==> r.unwrap().0.model(r.unwrap().1@).meta == owner.list[0]@,
            r.is_some() ==> r.unwrap().1@.frame_link_inv(),
    )]
    pub fn pop_front(&mut self) -> Option<(UniqueFrame<Link<M>>, Tracked<UniqueFrameOwner<Link<M>>>)> {
        assert(owner.list.len() > 0 ==> owner.inv_at(0));

        let tracked mut cursor_own = CursorOwner::front_owner(owner);
        let current = self.front;
        let mut cursor = CursorMut { list: self, current };

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
            old(self).wf(*old(owner)),
            old(owner).inv(),
            old(owner).list_id != 0,
            old(frame_own).inv(),
            old(frame_own).global_inv(*old(regions)),
            frame.wf(*old(frame_own)),
            old(frame_own).frame_link_inv(),
            old(owner).list.len() < usize::MAX,
            old(regions).inv(),
            old(regions).slots.contains_key(old(frame_own).slot_index),
            old(regions).slot_owners[old(frame_own).slot_index].inner_perms.in_list.is_for(
                old(regions).slots[old(frame_own).slot_index].value().in_list,
            ),
        ensures
            final(owner).inv(),
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
        let tracked mut cursor_own = CursorOwner::back_owner(*owner);
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
            old(self).wf(owner),
            owner.inv(),
            old(regions).slots.contains_key(frame_to_index(owner.list[owner.list.len() - 1].paddr)),
        ensures
            owner.list.len() == 0 ==> r.is_none(),
            r.is_some() ==> r.unwrap().0.model(r.unwrap().1@).meta == owner.list[owner.list.len() - 1]@,
            r.is_some() ==> r.unwrap().1@.frame_link_inv(),
    )]
    pub fn pop_back(&mut self) -> Option<(UniqueFrame<Link<M>>, Tracked<UniqueFrameOwner<Link<M>>>)> {
        assert(owner.list.len() > 0 ==> owner.inv_at(owner.list.len() - 1));

        let current = self.back;
        let tracked mut cursor_own = CursorOwner::back_owner(owner);
        let mut cursor = CursorMut { list: self, current };

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
            old(regions).slots.contains_key(frame_to_index(frame)),
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
//            has_safe_slot(frame) && owner.list_id != 0 ==> r is Some,
            !has_safe_slot(frame) ==> r is None,
    )]
    #[verifier::external_body]
    pub fn cursor_mut_at(&mut self, frame: Paddr) -> Option<CursorMut<'_, M>>
    {
        let tracked mut slot_own = regions.slot_owners.tracked_remove(frame_to_index(frame));
        let tracked mut inner_perms = slot_own.take_inner_perms();

        if let Ok(slot_ptr) = get_slot(frame) {
            let slot = slot_ptr.borrow(Tracked(&regions.slots[frame_to_index(frame)]));

            let in_list = slot.in_list.load(Tracked(&mut inner_perms.in_list));

            let contains = in_list == #[verus_spec(with Tracked(&owner))]
            self.lazy_get_id();

            #[verus_spec(with Tracked(&regions.slots[frame_to_index(frame)]))]
            let meta_ptr = slot.as_meta_ptr::<Link<M>>();

            if contains {
                proof {
                    slot_own.sync_inner(&inner_perms);
                    regions.slot_owners.tracked_insert(frame_to_index(frame), slot_own);
                }

                let ghost link = owner.list.filter(|link: LinkOwner| link.paddr == frame).first();
                let ghost index = owner.list.index_of(link);
                let tracked cursor_owner = CursorOwner::cursor_mut_at_owner(owner, index);

                proof_with!(|= Tracked(Some(cursor_owner)));
                Some(CursorMut { list: self, current: Some(MetadataAsLink::cast_from_metadata(meta_ptr)) })
            } else {
                proof {
                    slot_own.sync_inner(&inner_perms);
                    regions.slot_owners.tracked_insert(frame_to_index(frame), slot_own);
                }

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
    /// - See [`CursorOwner::front_owner_spec`] for the precise specification.
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
            r.1@ == CursorOwner::front_owner_spec(owner),
    )]
    pub fn cursor_front_mut(&mut self) -> (CursorMut<'_, M>, Tracked<CursorOwner<M>>) {
        let current = self.front;

        (CursorMut { list: self, current }, Tracked(CursorOwner::front_owner(owner)))
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
    /// See [`CursorOwner::back_owner_spec`] for the precise specification.
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
            res.1@ == CursorOwner::back_owner_spec(owner),
    {
        let current = self.back;

        (CursorMut { list: self, current }, Tracked(CursorOwner::back_owner(owner)))
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
        with Tracked(owner): Tracked<CursorOwner<M>>
    )]
    pub fn move_next(&mut self)
        requires
            owner.inv(),
            old(self).wf(owner),
        ensures
            final(self).model(owner.move_next_owner_spec()) == old(self).model(owner).move_next_spec(),
            owner.move_next_owner_spec().inv(),
            final(self).wf(owner.move_next_owner_spec()),
    {
        let ghost old_self = *self;

        proof {
            if self.current is Some {
                assert(owner.list_own.inv_at(owner.index));
            }
            if owner.index < owner.length() - 1 {
                assert(owner.list_own.inv_at(owner.index + 1));
                owner.list_own.perms[owner.index + 1].pptr_implies_addr();
            }
        }

        self.current = match self.current {
            // SAFETY: The cursor is pointing to a valid element.
            Some(current) => {
                let current_md = MetadataAsLink::cast_to_metadata(current);
                borrow_field!(current_md => metadata.next, owner.list_own.perms.tracked_borrow(owner.index))
            },
            None => self.list.front,
        };

        proof {
            LinkedListOwner::<M>::view_preserves_len(owner.list_own.list);
            assert(self.model(owner.move_next_owner_spec()).fore == old_self.model(owner).move_next_spec().fore);
            assert(self.model(owner.move_next_owner_spec()).rear == old_self.model(owner).move_next_spec().rear);
        }
    }

    /// Moves the cursor to the previous frame towards the front.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this will
    /// move it to the last element of the [`LinkedList`]. If it is pointing
    /// to the first element of the LinkedList then this will move it to the
    /// "ghost" non-element.
    #[verus_spec(
        with Tracked(owner): Tracked<CursorOwner<M>>
    )]
    pub fn move_prev(&mut self)
        requires
            owner.inv(),
            old(self).wf(owner),
        ensures
            final(self).model(owner.move_prev_owner_spec()) == old(self).model(owner).move_prev_spec(),
            owner.move_prev_owner_spec().inv(),
            final(self).wf(owner.move_prev_owner_spec()),
    {
        let ghost old_self = *self;

        proof {
            if self.current is Some {
                assert(owner.list_own.inv_at(owner.index));
            }
            if 0 < owner.index {
                assert(owner.list_own.inv_at(owner.index - 1));
                owner.list_own.perms[owner.index - 1].pptr_implies_addr();
            }
        }

        self.current = match self.current {
            // SAFETY: The cursor is pointing to a valid element.
            Some(current) => {
                let current_md = MetadataAsLink::cast_to_metadata(current);
                borrow_field!(current_md => metadata.prev, owner.list_own.perms.tracked_borrow(owner.index))
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
                        assert(owner.list_own.inv_at(owner.index));
                    }
                } else {
                    assert(owner.list_own.inv_at(owner.index));
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
    /// current link's metadata. The cursor state and owner are otherwise
    /// unchanged.
    /// ## Safety
    /// The `&mut self` guarantees exclusive access to the cursor; the tracked
    /// `CursorOwner` guarantees the perm for the current link is live. Together
    /// they justify the mutable borrow of `link.meta`. The body is
    /// `external_body` because the map-indexed perm extraction needed to call
    /// `ReprPtr::borrow_mut` runs into a Verus modelling gap — see
    /// `vstd_extra::map_extra::tracked_borrow_mut_points_to`. The ownership
    /// invariants in the requires/ensures are what we rely on.
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<M>>
    )]
    #[verifier::external_body]
    pub fn current_meta(&mut self) -> (res: Option<&mut M>)
        requires
            old(self).wf(*old(owner)),
            old(owner).inv(),
        ensures
            final(self).wf(*final(owner)),
            final(owner).inv(),
            *final(owner) == *old(owner),
            *final(self) == *old(self),
            res.is_some() == (0 <= final(owner).index < final(owner).length()),
    {
        self.current.map(|current| {
            // SAFETY: `&mut self` + the tracked owner ensure exclusive access
            // to the current link's metadata.
            let link_mut = unsafe { &mut *(current.ptr.addr() as *mut Link<M>) };
            &mut link_mut.meta
        })
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
    pub fn take_current(&mut self) -> (res: Option<(UniqueFrame<Link<M>>, Tracked<UniqueFrameOwner<Link<M>>>)>)
        requires
            old(self).wf(*old(owner)),
            old(owner).inv(),
            old(regions).inv(),
            old(owner).length() > 0 ==> old(regions).slot_owners.contains_key(
                frame_to_index(old(self).current.unwrap().addr()),
            ),
        ensures
            old(owner).length() == 0 ==> res.is_none(),
            old(self).current.is_some() ==> res.is_some(),
            res.is_some() ==> res.unwrap().0.model(res.unwrap().1@).meta == old(
                owner,
            ).list_own.list[old(owner).index]@,
            res.is_some() ==> final(self).model(*final(owner)) == old(self).model(*old(owner)).remove(),
            res.is_some() ==> res.unwrap().1@.frame_link_inv(),
            // Invariant preservation
            res.is_some() ==> final(owner).inv(),
            res.is_some() ==> final(self).wf(*final(owner)),
            res.is_none() ==> *final(owner) =~= *old(owner),
            final(regions).inv(),
            // Structural: remove_owner_spec
            res.is_some() ==> final(owner).index == old(owner).index,
            res.is_some() ==> final(owner).list_own.list
                == old(owner).list_own.list.remove(old(owner).index),
            // Slot effects: from_raw decrements raw_count by 1
            res.is_some() ==> {
                let paddr = old(self).current.unwrap().addr();
                let idx = frame_to_index(meta_to_frame(paddr));
                &&& final(regions).slot_owners[idx].raw_count
                    == old(regions).slot_owners[idx].raw_count - 1
                &&& final(regions).slots =~= old(regions).slots
            },
            // Frame for other slots
            res.is_some() ==> forall|idx: usize| #![trigger final(regions).slot_owners[idx]]
                idx != frame_to_index(meta_to_frame(old(self).current.unwrap().addr()))
                ==> final(regions).slot_owners[idx] == old(regions).slot_owners[idx],
            res.is_none() ==> *final(regions) =~= *old(regions),
            // Properties of the returned frame needed for UniqueFrame::drop
            res.is_some() ==> res.unwrap().0.wf(res.unwrap().1@),
            res.is_some() ==> res.unwrap().1@.inv(),
    {
        let ghost owner0 = *owner;

        let current = self.current?;

        assert(owner.list_own.inv_at(owner.index));
        assert(owner.index > 0 ==> owner.list_own.inv_at(owner.index - 1));
        assert(owner.index < owner.length() - 1 ==> owner.list_own.inv_at(owner.index + 1));

        let meta_ptr = current.addr();
        let paddr = meta_to_frame(meta_ptr);

        let tracked cur_perm = owner.list_own.perms.tracked_remove(owner.index);
        let tracked mut cur_own = owner.list_own.list.tracked_remove(owner.index);

        #[verus_spec(with Tracked(regions), Tracked(cur_perm), Tracked(cur_own))]
        let (frame, frame_own) = UniqueFrame::<Link<M>>::from_raw(paddr);
        let mut frame = frame;
        let tracked mut frame_own = frame_own.get();

        let next_ptr = frame.meta().next;

        #[verus_spec(with Tracked(&frame_own))]
        let frame_meta = frame.meta_mut();

        let opt_prev_link = borrow_field!(frame_meta => metadata.prev, &frame_own.meta_perm);

        if let Some(prev_link) = opt_prev_link {
            let prev = MetadataAsLink::cast_to_metadata(prev_link);
            // SAFETY: We own the previous node by `&mut self` and the node is
            // initialized.
            update_field!(prev => metadata.next <- next_ptr; owner.list_own.perms, owner.index-1);

            assert(owner.index > 0);
        } else {
            self.list.front = next_ptr;
        }

        let prev_ptr = frame.meta().prev;

        #[verus_spec(with Tracked(&frame_own))]
        let frame_meta = frame.meta_mut();
        let opt_next_link = frame_meta.borrow(Tracked(&frame_own.meta_perm)).metadata.next;

        if let Some(next_link) = opt_next_link {
            let next = MetadataAsLink::cast_to_metadata(next_link);
            // SAFETY: We own the next node by `&mut self` and the node is
            // initialized.
            update_field!(next => metadata.prev <- prev_ptr; owner.list_own.perms, owner.index+1);

            self.current = Some(next_link);
        } else {
            self.list.back = prev_ptr;

            self.current = None;
        }

        #[verus_spec(with Tracked(&frame_own))]
        let frame_meta = frame.meta_mut();

        update_field!(frame_meta => metadata.next <- None; frame_own.meta_perm);
        update_field!(frame_meta => metadata.prev <- None; frame_own.meta_perm);

        let tracked mut slot_own = regions.slot_owners.tracked_remove(frame_to_index(paddr));

        #[verus_spec(with Tracked(&frame_own.meta_perm.points_to))]
        let slot = frame.slot();
        let tracked mut inner_perms = frame_own.meta_perm.inner_perms;
        slot.in_list.store(Tracked(&mut inner_perms.in_list), 0);
        proof { frame_own.meta_perm.inner_perms = inner_perms; }

        proof {
            regions.slot_owners.tracked_insert(frame_to_index(paddr), slot_own);
        }

        self.list.size = self.list.size - 1;

        proof {
            owner0.remove_owner_spec_implies_model_spec(*owner);
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
    pub fn insert_before(&mut self, mut frame: UniqueFrame<Link<M>>)
        requires
            old(self).wf(*old(owner)),
            old(owner).inv(),
            old(owner).list_own.list_id != 0,
            old(frame_own).inv(),
            old(frame_own).global_inv(*old(regions)),
            frame.wf(*old(frame_own)),
            old(owner).length() < usize::MAX,
            old(regions).inv(),
            old(regions).slots.contains_key(old(frame_own).slot_index),
            old(regions).slot_owners[old(frame_own).slot_index].inner_perms.in_list.is_for(
                old(regions).slots[old(frame_own).slot_index].value().in_list,
            ),
            old(frame_own).meta_perm.addr() == frame.ptr.addr(),
            old(frame_own).frame_link_inv(),
        ensures
            final(self).model(*final(owner)) == old(self).model(*old(owner)).insert(final(frame_own).meta_own@),
            final(self).wf(*final(owner)),
            final(owner).inv(),
            final(owner).list_own.list == old(owner).list_own.list.insert(old(owner).index, final(frame_own).meta_own),
            final(owner).list_own.list_id == old(owner).list_own.list_id,
            final(frame_own).meta_own.paddr == old(frame_own).meta_own.paddr,
            final(frame_own).meta_own.in_list == old(owner).list_own.list_id,
    {
        let ghost owner0 = *owner;

        assert(meta_addr(frame_own.slot_index) == frame.ptr.addr());
        assert(regions.slot_owners.contains_key(frame_own.slot_index));
        let tracked slot_own = regions.slot_owners.tracked_borrow(frame_own.slot_index);

        #[verus_spec(with Tracked(frame_own))]
        let frame_ptr = frame.meta_mut();
        assert(frame_ptr.addr() == frame.ptr.addr());

        let frame_ptr_as_link = MetadataAsLink::cast_from_metadata(frame_ptr);

        if let Some(current) = self.current {
            let current_md = MetadataAsLink::cast_to_metadata(current);

            assert(owner.list_own.inv_at(owner.index));
            assert(owner.index > 0 ==> owner.list_own.inv_at(owner.index - 1));
            assert(owner.index < owner.length() - 1 ==> owner.list_own.inv_at(owner.index + 1));

            // SAFETY: We own the current node by `&mut self` and the node is initialized.
            let tracked mut cur_perm = owner.list_own.perms.tracked_remove(owner.index);
            let opt_prev_link : Option<ReprPtr<MetaSlot, MetadataAsLink<M>>> =
                borrow_field!(current_md => metadata.prev, &cur_perm);
            proof {
                owner.list_own.perms.tracked_insert(owner.index, cur_perm);
            }

            if let Some(prev_link) = opt_prev_link {
                let prev = MetadataAsLink::cast_to_metadata(prev_link);

                // SAFETY: We own the previous node by `&mut self` and the node is initialized.
                update_field!(prev => metadata.next <- Some(frame_ptr_as_link); owner.list_own.perms, owner.index-1);

                update_field!(frame_ptr => metadata.prev <- Some(prev_link); frame_own.meta_perm);
                update_field!(frame_ptr => metadata.next <- Some(current); frame_own.meta_perm);

                update_field!(current_md => metadata.prev <- Some(frame_ptr_as_link); owner.list_own.perms, owner.index);
            } else {
                update_field!(frame_ptr => metadata.next <- Some(current); frame_own.meta_perm);

                update_field!(current_md => metadata.prev <- Some(frame_ptr_as_link); owner.list_own.perms, owner.index);

                self.list.front = Some(frame_ptr_as_link);
            }
        } else {
            assert(0 < owner.length() ==> owner.list_own.inv_at(owner.index - 1));

            if let Some(back) = self.list.back {
                let back_md = MetadataAsLink::cast_to_metadata(back);

                assert(owner.index == owner.length());

                // SAFETY: We have ownership of the links via `&mut self`.
                //                    debug_assert!(back.as_mut().next.is_none());
                update_field!(back_md => metadata.next <- Some(frame_ptr_as_link); owner.list_own.perms, owner.length()-1);

                update_field!(frame_ptr => metadata.prev <- Some(back); frame_own.meta_perm);

                self.list.back = Some(frame_ptr_as_link);
            } else {
                //                debug_assert_eq!(self.list.front, None);
                self.list.front = Some(frame_ptr_as_link);
                self.list.back = Some(frame_ptr_as_link);
            }
        }

        assert(regions.slot_owners.contains_key(frame_to_index(meta_to_frame(frame.ptr.addr()))));
        let tracked mut slot_own = regions.slot_owners.tracked_remove(
            frame_to_index(meta_to_frame(frame.ptr.addr())),
        );

        #[verus_spec(with Tracked(&mut owner.list_own))]
        let list_id = self.list.lazy_get_id();

        #[verus_spec(with Tracked(&frame_own.meta_perm.points_to))]
        let slot = frame.slot();
        slot.in_list.store(Tracked(&mut frame_own.meta_perm.inner_perms.in_list), list_id);

        proof {
            // The store only changed in_list.value(); ref_count is unchanged.
            // From global_inv: ref_count != REF_COUNT_UNUSED && ref_count != 0.
            // So slot_own.inv() holds after the store.
            assert(frame_own.slot_index == frame_to_index(meta_to_frame(frame.ptr.addr())));
            assert(slot_own.inner_perms.ref_count.value() != REF_COUNT_UNUSED);
            assert(slot_own.inner_perms.ref_count.value() != 0);
            assert(slot_own.inv());

            regions.slot_owners.tracked_insert(frame_to_index(meta_to_frame(frame.ptr.addr())), slot_own)
        }

        assert(regions.inv()) by {
            // slot_owners only changed at frame_own.slot_index.
            // For all other keys, the invariant is preserved from old(regions).inv().
            // For the modified key, we proved slot_own.inv() above.
            assert(forall|i: usize| #[trigger]
                regions.slots.contains_key(i) ==>
                    regions.slots[i].value().wf(regions.slot_owners[i]));
        };

        // Forget the frame to transfer the ownership to the list.
        #[verus_spec(with Tracked(frame_own), Tracked(regions))]
        let _ = frame.into_raw();

        self.list.size = self.list.size + 1;

        proof {
            CursorOwner::<M>::list_insert(owner, &mut frame_own.meta_own, &frame_own.meta_perm);

            assert(forall|i: int| 0 <= i < owner.index - 1 ==> #[trigger] owner0.list_own.inv_at(i) ==> owner.list_own.inv_at(i)) by {};
            assert(forall|i: int| owner.index <= i < owner.length() ==> owner0.list_own.inv_at(i - 1) == owner.list_own.inv_at(i)) by {};
            assert(owner.list_own.inv_at(owner0.index as int));

            assert(owner.list_own.list == owner0.list_own.list.insert(owner0.index, frame_own.meta_own));
            owner0.insert_owner_spec_implies_model_spec(frame_own.meta_own, *owner);
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
        // Each element's slot is in slot_owners
        &&& forall|i: int| #![trigger s.0.list[i]]
            0 <= i < s.0.list.len() ==>
                s.1.slot_owners.contains_key(frame_to_index(s.0.list[i].paddr))
        // List element slots are not unused (needed to preserve MetaSlotOwner::inv after raw_count change)
        &&& forall|i: int| #![trigger s.0.list[i]]
            0 <= i < s.0.list.len() ==> {
                let idx = frame_to_index(meta_to_frame(s.0.list[i].paddr));
                s.1.slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
            }
        // List element slots are not in regions.slots (perms owned by the list)
        &&& forall|i: int| #![trigger s.0.list[i]]
            0 <= i < s.0.list.len() ==> {
                let idx = frame_to_index(meta_to_frame(s.0.list[i].paddr));
                !s.1.slots.contains_key(idx)
            }
        // List element slots have raw_count > 0 (from into_raw when inserted)
        &&& forall|i: int| #![trigger s.0.list[i]]
            0 <= i < s.0.list.len() ==> {
                let idx = frame_to_index(meta_to_frame(s.0.list[i].paddr));
                s.1.slot_owners[idx].raw_count > 0
            }
        // Elements have distinct slot indices
        &&& forall|i: int, j: int|
            #![trigger s.0.list[i], s.0.list[j]]
            0 <= i < j < s.0.list.len() ==>
                frame_to_index(meta_to_frame(s.0.list[i].paddr))
                    != frame_to_index(meta_to_frame(s.0.list[j].paddr))
    }

    open spec fn drop_ensures(self, s0: Self::State, s1: Self::State) -> bool {
        &&& s1.0.list.len() == 0
        // Each element's slot has raw_count decremented by 1
        &&& forall|i: int| #![trigger s0.0.list[i]]
            0 <= i < s0.0.list.len() ==> {
                let idx = frame_to_index(meta_to_frame(s0.0.list[i].paddr));
                s1.1.slot_owners[idx].raw_count
                    == s0.1.slot_owners[idx].raw_count - 1
            }
        // Slots not in the list are unchanged
        &&& forall|idx: usize| #![trigger s1.1.slot_owners[idx]]
            (forall|i: int| #![trigger s0.0.list[i]]
                0 <= i < s0.0.list.len() ==>
                    idx != frame_to_index(meta_to_frame(s0.0.list[i].paddr)))
            ==> s1.1.slot_owners[idx] == s0.1.slot_owners[idx]
        &&& s1.1.slots =~= s0.1.slots
        &&& s1.1.inv()
    }

    proof fn drop_tracked(self, tracked s: &mut Self::State) {
        let ghost list = s.0.list;
        let ghost n = list.len();
        let ghost old_regions = s.1;

        assert forall|j: int| #![trigger list[j]]
            0 <= j < n implies
                s.1.slot_owners.contains_key(
                    frame_to_index(meta_to_frame(list[j].paddr)))
        by {
            assert(s.0.inv_at(j));
            let paddr = list[j].paddr;
            assert(frame_to_index(meta_to_frame(paddr))
                < max_meta_slots()) by {
                assert(meta_to_frame(paddr) == ((paddr - FRAME_METADATA_RANGE.start)
                    / META_SLOT_SIZE as int * PAGE_SIZE) as usize);
                assert(frame_to_index(meta_to_frame(paddr))
                    == meta_to_frame(paddr) / PAGE_SIZE);
            };
        };

        Self::drop_tracked_helper(list, 0, &old_regions, &mut s.1);

        assert forall|i: int| 0 <= i < n implies s.0.perms.contains_key(i)
        by {
            assert(s.0.list.len() == n);
            assert(s.0.inv_at(i));
        };
        Self::drain_list(&mut s.0, n as int);

        assert forall|i: usize|
            #[trigger] s.1.slot_owners.contains_key(i)
            implies s.1.slot_owners[i].inv()
        by {
            if forall|j: int| #![trigger list[j]]
                0 <= j < n ==> i != frame_to_index(meta_to_frame(list[j].paddr))
            {
                assert(s.1.slot_owners[i] == old_regions.slot_owners[i]);
            }
        };
        assert(s.1.inv());
    }

}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> LinkedList<M> {
    proof fn drain_list(
        tracked owner: &mut LinkedListOwner<M>,
        n: int,
    )
        requires
            old(owner).list.len() == n,
            n >= 0,
            forall|i: int| 0 <= i < n ==> old(owner).perms.contains_key(i),
        ensures
            final(owner).list.len() == 0,
        decreases n,
    {
        if n <= 0 {
            return;
        }
        // Remove perm first (perms is a Map, uses contains_key from precondition)
        let tracked _perm = owner.perms.tracked_remove(n - 1);
        let tracked _link = owner.list.tracked_remove(n - 1);
        Self::drain_list(owner, n - 1);
    }

    proof fn drop_tracked_helper(
        list: Seq<LinkOwner>,
        k: int,
        old_regions: &MetaRegionOwners,
        tracked regions: &mut MetaRegionOwners,
    )
        requires
            0 <= k <= list.len() as int,
            old_regions.slots =~= old(regions).slots,
            old_regions.slot_owners.dom() =~= old(regions).slot_owners.dom(),
            // Distinct indices
            forall|i: int, j: int|
                #![trigger list[i], list[j]]
                0 <= i < j < list.len() ==>
                    frame_to_index(meta_to_frame(list[i].paddr))
                        != frame_to_index(meta_to_frame(list[j].paddr)),
            // Containment (for the actual index used in tracked operations)
            forall|j: int| #![trigger list[j]]
                0 <= j < list.len() ==>
                    old(regions).slot_owners.contains_key(
                        frame_to_index(meta_to_frame(list[j].paddr))),
            // Already processed [0, k): only raw_count changed
            forall|j: int| #![trigger list[j]]
                0 <= j < k ==> {
                    let idx = frame_to_index(meta_to_frame(list[j].paddr));
                    &&& old(regions).slot_owners[idx].raw_count
                        == old_regions.slot_owners[idx].raw_count - 1
                    &&& old(regions).slot_owners[idx].inner_perms
                        == old_regions.slot_owners[idx].inner_perms
                    &&& old(regions).slot_owners[idx].self_addr
                        == old_regions.slot_owners[idx].self_addr
                    &&& old(regions).slot_owners[idx].usage
                        == old_regions.slot_owners[idx].usage
                    &&& old(regions).slot_owners[idx].paths_in_pt
                        == old_regions.slot_owners[idx].paths_in_pt
                },
            // Not yet processed [k, n)
            forall|j: int| #![trigger list[j]]
                k <= j < list.len() ==> {
                    let idx = frame_to_index(meta_to_frame(list[j].paddr));
                    old(regions).slot_owners[idx]
                        == old_regions.slot_owners[idx]
                },
            // Non-list slots unchanged
            forall|idx: usize| #![trigger old(regions).slot_owners[idx]]
                (forall|j: int| #![trigger list[j]]
                    0 <= j < list.len() ==>
                        idx != frame_to_index(meta_to_frame(list[j].paddr)))
                ==> old(regions).slot_owners[idx] == old_regions.slot_owners[idx],
            old(regions).slots =~= old_regions.slots,
            // raw_count > 0 for unprocessed elements
            forall|j: int| #![trigger list[j]]
                k <= j < list.len() ==>
                    old_regions.slot_owners[frame_to_index(meta_to_frame(list[j].paddr))].raw_count > 0,
        ensures
            // All elements decremented (only raw_count changed)
            forall|j: int| #![trigger list[j]]
                0 <= j < list.len() ==> {
                    let idx = frame_to_index(meta_to_frame(list[j].paddr));
                    &&& final(regions).slot_owners[idx].raw_count
                        == old_regions.slot_owners[idx].raw_count - 1
                    &&& final(regions).slot_owners[idx].inner_perms
                        == old_regions.slot_owners[idx].inner_perms
                    &&& final(regions).slot_owners[idx].self_addr
                        == old_regions.slot_owners[idx].self_addr
                    &&& final(regions).slot_owners[idx].usage
                        == old_regions.slot_owners[idx].usage
                    &&& final(regions).slot_owners[idx].paths_in_pt
                        == old_regions.slot_owners[idx].paths_in_pt
                },
            // Non-list slots unchanged
            forall|idx: usize| #![trigger final(regions).slot_owners[idx]]
                (forall|j: int| #![trigger list[j]]
                    0 <= j < list.len() ==>
                        idx != frame_to_index(meta_to_frame(list[j].paddr)))
                ==> final(regions).slot_owners[idx] == old_regions.slot_owners[idx],
            final(regions).slots =~= old_regions.slots,
            final(regions).slot_owners.dom() =~= old_regions.slot_owners.dom(),
        decreases list.len() - k,
    {
        if k >= list.len() {
            return;
        }

        let ghost idx = frame_to_index(meta_to_frame(list[k].paddr));
        let ghost _trigger_k = list[k as int]; // trigger containment precondition
        let tracked mut slot_own = regions.slot_owners.tracked_remove(idx);
        slot_own.raw_count = (slot_own.raw_count - 1) as usize;
        regions.slot_owners.tracked_insert(idx, slot_own);

        let ghost _trigger_k = list[k as int];
        assert(regions.slot_owners[idx].raw_count == slot_own.raw_count);
        assert(old_regions.slot_owners[idx].raw_count > 0);

        // Non-raw_count fields preserved for all elements [0, k+1)
        assert forall|j: int| #![trigger list[j]]
            0 <= j < k + 1 implies ({
                let jdx = frame_to_index(meta_to_frame(list[j].paddr));
                &&& regions.slot_owners[jdx].inner_perms == old_regions.slot_owners[jdx].inner_perms
                &&& regions.slot_owners[jdx].self_addr == old_regions.slot_owners[jdx].self_addr
                &&& regions.slot_owners[jdx].usage == old_regions.slot_owners[jdx].usage
                &&& regions.slot_owners[jdx].paths_in_pt == old_regions.slot_owners[jdx].paths_in_pt
            })
        by {
            let jdx = frame_to_index(meta_to_frame(list[j].paddr));
            if j < k {
                let ghost _a = list[j as int];
                let ghost _b = list[k as int];
                assert(jdx != idx);
            }
            // j == k: only raw_count changed on slot_own
        };

        // All processed elements [0, k+1) have raw_count decremented
        assert forall|j: int| #![trigger list[j]]
            0 <= j < k + 1 implies ({
                let jdx = frame_to_index(meta_to_frame(list[j].paddr));
                regions.slot_owners[jdx].raw_count
                    == old_regions.slot_owners[jdx].raw_count - 1
            })
        by {
            let jdx = frame_to_index(meta_to_frame(list[j].paddr));
            if j < k {
                let ghost _a = list[j as int];
                let ghost _b = list[k as int];
                assert(jdx != idx);
            }
        };

        Self::drop_tracked_helper(list, k + 1, old_regions, regions);
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> Drop for LinkedList<M> {
    fn drop(self, Tracked(s): Tracked<&mut Self::State>)
    {
        // Pull the tuple components out from behind the `&mut`. We can't
        // move directly (E0507) and `cursor_front_mut` requires owned
        // `LinkedListOwner`. `tracked_take` swaps `s.0` with a fresh-empty
        // `LinkedListOwner`; we'll restore `*s` at the end of the body.
        // `MetaRegionOwners` can't be similarly emptied (its `inv()` requires
        // all valid slot indices), so we re-borrow `&mut s.1` for it.
        proof_decl! {
            let tracked mut list_own: LinkedListOwner<M>;
        }
        proof {
            list_own = LinkedListOwner::<M>::tracked_take(&mut s.0);
        }
        let tracked regions: &mut MetaRegionOwners = &mut s.1;
        let ghost original_list = list_own.list;
        let ghost original_regions = *regions;
        let ghost n = original_list.len();
        let mut this = self;

        #[verus_spec(with Tracked(list_own))]
        let cursor_pair = this.cursor_front_mut();
        let (mut cursor, Tracked(mut cursor_own)) = cursor_pair;

        let ghost mut k: int = 0;

        loop
            invariant_except_break
                cursor.wf(cursor_own),
                cursor.current.is_some() <==> k < n,
            invariant
                cursor_own.inv(),
                cursor_own.index == 0,
                regions.inv(),
                cursor_own.list_own.list.len() == n - k,
                0 <= k <= n,
                // The remaining list is a suffix of the original
                forall|j: int| #![trigger cursor_own.list_own.list[j]]
                    0 <= j < n - k ==>
                        cursor_own.list_own.list[j] == original_list[j + k],
                // Elements already taken have raw_count decremented
                forall|j: int| #![trigger original_list[j]]
                    0 <= j < k ==> {
                        let idx = frame_to_index(meta_to_frame(original_list[j].paddr));
                        regions.slot_owners[idx].raw_count
                            == original_regions.slot_owners[idx].raw_count - 1
                    },
                // Slots not in the original list are unchanged
                forall|idx: usize| #![trigger regions.slot_owners[idx]]
                    (forall|j: int| #![trigger original_list[j]]
                        0 <= j < n ==>
                            idx != frame_to_index(meta_to_frame(original_list[j].paddr)))
                    ==> regions.slot_owners[idx] == original_regions.slot_owners[idx],
                regions.slots =~= original_regions.slots,
                // Elements not yet processed have original raw_count
                forall|j: int| #![trigger original_list[j]]
                    k <= j < n ==> {
                        let idx = frame_to_index(meta_to_frame(original_list[j].paddr));
                        regions.slot_owners[idx].raw_count
                            == original_regions.slot_owners[idx].raw_count
                    },
                // Each remaining element's slot is in slot_owners
                forall|j: int| #![trigger original_list[j]]
                    k <= j < n ==>
                        regions.slot_owners.contains_key(frame_to_index(original_list[j].paddr)),
                // Distinct slot indices in original list (from drop_requires)
                forall|i: int, j: int|
                    #![trigger original_list[i], original_list[j]]
                    0 <= i < j < n ==>
                        frame_to_index(meta_to_frame(original_list[i].paddr))
                            != frame_to_index(meta_to_frame(original_list[j].paddr)),
            ensures
                k == n,
                cursor_own.list_own.list.len() == 0,
            decreases n - k,
        {
            proof {
                if cursor.current.is_some() {
                    assert(cursor_own.length() > 0);
                    // cursor.current.addr() == list[0].paddr == original_list[k].paddr
                    // from the slot containment invariant, this key is in slot_owners
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
                    assert(cur_addr == original_list[k].paddr);
                    assert(cur_idx == frame_to_index(meta_to_frame(original_list[k].paddr)));
                }

                // Drop the frame, returning its slot to regions
                #[verus_spec(with Tracked(frame_own), Tracked(regions))]
                frame.drop();

                proof {
                    assert forall|j: int| #![trigger cursor_own.list_own.list[j]]
                        0 <= j < n - k - 1 implies
                            cursor_own.list_own.list[j] == original_list[j + k + 1]
                    by {};

                    assert forall|j: int| #![trigger original_list[j]]
                        0 <= j < k implies ({
                            let idx = frame_to_index(meta_to_frame(original_list[j].paddr));
                            regions.slot_owners[idx].raw_count
                                == original_regions.slot_owners[idx].raw_count - 1
                        })
                    by {
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
            // `final_list_own` now holds the placeholder put in by
            // `tracked_take` at function entry — empty list/perms, so we can
            // discard it via the destroy axiom below.
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
impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> AnyFrameMeta for Link<M>
{
    fn on_drop(&mut self, reader: &mut crate::mm::VmReader<crate::mm::Infallible>) {
        self.meta.on_drop(reader);
    }

    fn is_untyped(&self) -> bool {
        self.meta.is_untyped()
    }

    uninterp spec fn vtable_ptr(&self) -> usize;
}

} // verus!
