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
use vstd_extra::ownership::*;
use vstd_extra::ptr_extra::*;

use crate::mm::frame::meta::mapping::frame_to_meta;
use crate::mm::frame::{UniqueFrame, UniqueFrameOwner};
use crate::mm::{Paddr, PagingLevel, Vaddr};
use crate::specs::arch::mm::{MAX_NR_PAGES, MAX_PADDR, PAGE_SIZE};
use crate::specs::mm::frame::linked_list::{CursorOwner, LinkedListOwner};
use crate::specs::mm::frame::meta_owners::MetaSlotOwner;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;

use core::borrow::BorrowMut;
use core::{
    ops::{Deref, DerefMut},
    ptr::NonNull,
    sync::atomic::{AtomicU64, Ordering},
};

use crate::specs::*;

use crate::mm::frame::meta::mapping::{frame_to_index, meta_addr, meta_to_frame};
use crate::mm::frame::meta::{get_slot, AnyFrameMeta, MetaSlot};

verus! {

/// A link in the linked list.
pub struct Link<M: AnyFrameMeta + Repr<MetaSlot>> {
    pub next: Option<ReprPtr<MetaSlot, Link<M>>>,
    pub prev: Option<ReprPtr<MetaSlot, Link<M>>>,
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
/// The linked list is abstractly represented by a
/// [`LinkedListOwner`](crate::specs::mm::frame::linked_list::linked_list_owners::LinkedListOwner)
/// which is a sequence of [`LinkOwner`](crate::specs::mm::frame::linked_list::linked_list_owners::LinkOwner)
/// objects. Each [`LinkOwner`] uniquely owns the frame metadata of a link.
/// ## Invariant
/// The linked list uniquely owns the raw frames that it contains, so they cannot be used by other
/// data structures. The frame metadata field `in_list` is equal to `list_id` for all links in the list.
/// ## Safety
/// A given linked list can only have one cursor at a time, so there are no data races.
/// The `prev` and `next` fields of the metadata for each link always points to valid
/// links in the list, so the structure is memory safe (will not read or write invalid memory).
pub struct LinkedList<M: AnyFrameMeta + Repr<MetaSlot>> {
    pub front: Option<ReprPtr<MetaSlot, Link<M>>>,
    pub back: Option<ReprPtr<MetaSlot, Link<M>>>,
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
pub struct CursorMut<M: AnyFrameMeta + Repr<MetaSlot>> {
    pub list: PPtr<LinkedList<M>>,
    pub current: Option<ReprPtr<MetaSlot, Link<M>>>,
}

impl<M: AnyFrameMeta + Repr<MetaSlot>> LinkedList<M> {
    /// Creates a new linked list.
    pub const fn new() -> Self {
        Self { front: None, back: None, size: 0, list_id: 0 }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlot>> Default for LinkedList<M> {
    fn default() -> Self {
        Self::new()
    }
}

/// Representation of a link as stored in the metadata slot.
pub struct StoredLink {
    pub next: Option<Paddr>,
    pub prev: Option<Paddr>,
    pub slot: MetaSlot,
}

impl<M: AnyFrameMeta + Repr<MetaSlot>> Repr<MetaSlot> for Link<M> {
    uninterp spec fn wf(r: MetaSlot) -> bool;

    uninterp spec fn to_repr_spec(self) -> MetaSlot;

    #[verifier::external_body]
    fn to_repr(self) -> MetaSlot {
        unimplemented!()
    }

    uninterp spec fn from_repr_spec(r: MetaSlot) -> Self;

    #[verifier::external_body]
    fn from_repr(r: MetaSlot) -> Self {
        unimplemented!()
    }

    #[verifier::external_body]
    fn from_borrowed<'a>(r: &'a MetaSlot) -> &'a Self {
        unimplemented!()
    }

    proof fn from_to_repr(self)
        ensures
            Self::from_repr(self.to_repr()) == self,
    {
        admit();
    }

    proof fn to_from_repr(r: MetaSlot)
        ensures
            Self::from_repr(r).to_repr() == r,
    {
        admit();
    }

    proof fn to_repr_wf(self)
        ensures
            <Self as Repr<MetaSlot>>::wf(self.to_repr()),
    {
        admit();
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlot>> AnyFrameMeta for Link<M> {
    fn on_drop(&mut self) {
    }

    fn is_untyped(&self) -> bool {
        false
    }

    uninterp spec fn vtable_ptr(&self) -> usize;
}

// SAFETY: Only the pointers are not `Send` and `Sync`. But our interfaces
// enforces that only with `&mut` references can we access with the pointers.
//unsafe impl<M> Send for LinkedList<M> where Link<M>: AnyFrameMeta {}
//unsafe impl<M> Sync for LinkedList<M> where Link<M>: AnyFrameMeta {}
#[verus_verify]
impl<M: AnyFrameMeta + Repr<MetaSlot>> LinkedList<M> {
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
            Tracked(perm): Tracked<vstd::simple_pptr::PointsTo<LinkedList<M>>>,
            Tracked(frame_own): Tracked<&mut UniqueFrameOwner<Link<M>>>,
        requires
            perm.pptr() == ptr,
            perm.is_init(),
            perm.mem_contents().value().wf(*old(owner)),
            old(owner).inv(),
            old(owner).list_id != 0,
            old(frame_own).inv(),
            old(frame_own).global_inv(*old(regions)),
            frame.wf(*old(frame_own)),
            old(frame_own).frame_link_inv(),
            old(owner).list.len() < usize::MAX,
            old(regions).inv(),
            old(regions).slots.contains_key(old(frame_own).slot_index),
            old(regions).slot_owners[old(frame_own).slot_index].in_list.is_for(
                old(regions).slots[old(frame_own).slot_index].value().in_list,
            ),
        ensures
            owner.inv(),
            owner.list == old(owner).list.insert(0, old(frame_own).meta_own),
            owner.list_id == old(owner).list_id,
    )]
    pub fn push_front(ptr: PPtr<Self>, frame: UniqueFrame<Link<M>>) {
        let ll = ptr.borrow(Tracked(&perm));
        let current = ll.front;
        let tracked mut cursor_own = CursorOwner::front_owner(*owner, perm);
        let mut cursor = CursorMut { list: ptr, current };

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
            Tracked(perm): Tracked<vstd::simple_pptr::PointsTo<LinkedList<M>>>,
            Tracked(owner): Tracked<LinkedListOwner<M>>,
            Tracked(frame_own): Tracked<UniqueFrameOwner<Link<M>>>,
        requires
            old(regions).inv(),
            perm.pptr() == ptr,
            perm.is_init(),
            perm.value().wf(owner),
            owner.inv(),
            old(regions).slots.contains_key(frame_to_index(owner.list[0].paddr)),
        ensures
            owner.list.len() == 0 ==> r.is_none(),
            r.is_some() ==> r.unwrap().0.model(r.unwrap().1@).meta == owner.list[0]@,
            r.is_some() ==> r.unwrap().1@.frame_link_inv(),
    )]
    pub fn pop_front(ptr: PPtr<Self>) -> Option<(UniqueFrame<Link<M>>, Tracked<UniqueFrameOwner<Link<M>>>)> {
        assert(owner.list.len() > 0 ==> owner.inv_at(0));

        proof_with!(Tracked(owner), Tracked(perm) => Tracked(cursor_own));
        let cursor = Self::cursor_front_mut(ptr);
        let mut cursor = cursor;
        let tracked mut cursor_own = cursor_own;

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
    /// The new frame is inserted at the back of the list, and the cursor is moved to the new frame.
    /// The list invariants are preserved.
    /// ## Safety
    /// See [`insert_before`] for the safety guarantees.
    #[verus_spec(
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(owner): Tracked<&mut LinkedListOwner<M>>,
            Tracked(perm): Tracked<vstd::simple_pptr::PointsTo<LinkedList<M>>>,
            Tracked(frame_own): Tracked<&mut UniqueFrameOwner<Link<M>>>,
        requires
            perm.pptr() == ptr,
            perm.is_init(),
            perm.mem_contents().value().wf(*old(owner)),
            old(owner).inv(),
            old(owner).list_id != 0,
            old(frame_own).inv(),
            old(frame_own).global_inv(*old(regions)),
            frame.wf(*old(frame_own)),
            old(frame_own).frame_link_inv(),
            old(owner).list.len() < usize::MAX,
            old(regions).inv(),
            old(regions).slots.contains_key(old(frame_own).slot_index),
            old(regions).slot_owners[old(frame_own).slot_index].in_list.is_for(
                old(regions).slots[old(frame_own).slot_index].value().in_list,
            ),
        ensures
            owner.inv(),
            old(owner).list.len() > 0 ==> owner.list == old(owner).list.insert(
                old(owner).list.len() as int - 1, old(frame_own).meta_own),
            old(owner).list.len() == 0 ==> owner.list == old(owner).list.insert(
                0, old(frame_own).meta_own),
            owner.list_id == old(owner).list_id,
    )]
    pub fn push_back(ptr: PPtr<Self>, frame: UniqueFrame<Link<M>>) {
        let ll = ptr.borrow(Tracked(&perm));
        let current = ll.back;
        let tracked mut cursor_own = CursorOwner::back_owner(*owner, perm);
        let mut cursor = CursorMut { list: ptr, current };

        #[verus_spec(with Tracked(regions), Tracked(&mut cursor_own), Tracked(frame_own))]
        cursor.insert_before(frame);

        proof {
            *owner = cursor_own.list_own;
        }
    }

    /// Pops a frame from the back of the linked list.
    /// # Verified Properties
    /// ## Preconditions
    /// The list must be well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects. The list must be non-empty, so that the
    /// current frame is valid.
    /// ## Postconditions
    /// The back frame is removed from the list, and the cursor is moved to the "ghost" non-element.
    /// The list invariants are preserved.
    /// ## Safety
    /// See [`take_current`] for the safety guarantees.
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(perm): Tracked<vstd::simple_pptr::PointsTo<LinkedList<M>>>,
            Tracked(owner): Tracked<LinkedListOwner<M>>,
            Tracked(frame_own): Tracked<UniqueFrameOwner<Link<M>>>,
        requires
            old(regions).inv(),
            perm.pptr() == ptr,
            perm.is_init(),
            perm.mem_contents().value().wf(owner),
            owner.inv(),
            old(regions).slots.contains_key(frame_to_index(owner.list[owner.list.len() - 1].paddr)),
        ensures
            owner.list.len() == 0 ==> r.is_none(),
            r.is_some() ==> r.unwrap().0.model(r.unwrap().1@).meta == owner.list[owner.list.len() - 1]@,
            r.is_some() ==> r.unwrap().1@.frame_link_inv(),
    )]
    pub fn pop_back(ptr: PPtr<Self>) -> Option<(UniqueFrame<Link<M>>, Tracked<UniqueFrameOwner<Link<M>>>)> {
        assert(owner.list.len() > 0 ==> owner.inv_at(owner.list.len() - 1));

        #[verus_spec(with Tracked(owner), Tracked(perm))]
        let (cursor, cursor_own) = Self::cursor_back_mut(ptr);
        let mut cursor = cursor;
        let mut cursor_own = cursor_own;

        #[verus_spec(with Tracked(regions), Tracked(cursor_own.borrow_mut()))]
        cursor.take_current()
    }

    /// Tells if a frame is in the list.
    /// # Verified Properties
    /// ## Preconditions
    /// The list must be well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects. The frame must be a valid, active frame.
    /// ## Postconditions
    /// The function returns `true` if the frame is in the list, `false` otherwise.
    /// ## Safety
    /// `lazy_get_id` uses atomic memory accesses, so there are no data races. We
    /// assume that the ID allocator has an available ID if the list previously didn't have one,
    /// but the consequence if that is not the case is a panic.
    /// Everything else conforms to the safe interface.
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(slot_own): Tracked<&MetaSlotOwner>,
            Tracked(owner): Tracked<&mut LinkedListOwner<M>>,
        requires
            slot_own.inv(),
            slot_own.self_addr == frame_to_meta(frame),
            old(regions).inv(),
            old(regions).slots.contains_key(frame_to_index(frame)),
            old(regions).slots[frame_to_index(frame)].is_init(),
            old(regions).slot_owners.contains_key(frame_to_index(frame)),
            old(regions).slot_owners[frame_to_index(frame)].in_list.is_for(
                old(regions).slots[frame_to_index(frame)].mem_contents().value().in_list,
            ),
        ensures
            old(owner).list_id != 0 ==> *owner == *old(owner),
    )]
    pub fn contains(ptr: PPtr<Self>, frame: Paddr) -> bool {
        let Ok(slot_ptr) = get_slot(frame, Tracked(slot_own)) else {
            return false;
        };

        let tracked mut slot_perm = regions.slots.tracked_remove(frame_to_index(frame));
        let tracked mut slot_own = regions.slot_owners.tracked_remove(frame_to_index(frame));

        let slot = slot_ptr.take(Tracked(&mut slot_perm));
        let in_list = slot.in_list.load(Tracked(&mut slot_own.in_list));
        slot_ptr.put(Tracked(&mut slot_perm), slot);

        proof {
            regions.slot_owners.tracked_insert(frame_to_index(frame), slot_own);
            regions.slots.tracked_insert(frame_to_index(frame), slot_perm);
        }

        in_list == #[verus_spec(with Tracked(owner))]
        Self::lazy_get_id(ptr)
    }

    /// Gets a cursor at the specified frame if the frame is in the list.
    ///
    /// This method fails if the frame is not in the list.
    /// # Verified Properties
    /// ## Preconditions
    /// The list must be well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects. The frame must be a valid, active frame.
    /// ## Postconditions
    /// The cursor is well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects. The list invariants are preserved.
    /// ## Safety
    /// `lazy_get_id` uses atomic memory accesses, so there are no data races. We
    /// assume that the ID allocator has an available ID if the list previously didn't have one,
    /// but the consequence if that is not the case is a panic.
    /// Everything else conforms to the safe interface.
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(owner): Tracked<&mut LinkedListOwner<M>>,
        requires
            old(regions).inv(),
            frame < MAX_PADDR,
            frame % PAGE_SIZE == 0,
            old(regions).slots.contains_key(frame_to_index(frame)),
            old(regions).slots[frame_to_index(frame)].is_init(),
            old(regions).slot_owners.contains_key(frame_to_index(frame)),
            old(regions).slot_owners[frame_to_index(frame)].in_list.is_for(
                old(regions).slots[frame_to_index(frame)].mem_contents().value().in_list,
            ),
        ensures
            old(owner).list_id != 0 ==> *owner == *old(owner),
    )]
    pub fn cursor_mut_at(ptr: PPtr<Self>, frame: Paddr) -> Option<CursorMut<M>>
    {
        let tracked mut slot_perm = regions.slots.tracked_remove(frame_to_index(frame));
        let tracked mut slot_own = regions.slot_owners.tracked_remove(frame_to_index(frame));

        let Ok(slot_ptr) = get_slot(frame, Tracked(&slot_own)) else {
            return None;
        };

        let slot = slot_ptr.borrow(Tracked(&slot_perm));
        let in_list = slot.in_list.load(Tracked(&mut slot_own.in_list));
        let contains = in_list == #[verus_spec(with Tracked(owner))]
        Self::lazy_get_id(ptr);

        #[verus_spec(with Tracked(&slot_perm))]
        let meta_ptr = slot.as_meta_ptr::<Link<M>>();

        let res = if contains {
            Some(CursorMut { list: ptr, current: Some(meta_ptr) })
        } else {
            None
        };

        proof {
            regions.slots.tracked_insert(frame_to_index(frame), slot_perm);
            regions.slot_owners.tracked_insert(frame_to_index(frame), slot_own);
        }

        res
    }

    /// Gets a cursor at the front that can mutate the linked list links.
    ///
    /// If the list is empty, the cursor points to the "ghost" non-element.
    /// # Verified Properties
    /// ## Preconditions
    /// The list must be well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects.
    /// ## Postconditions
    /// The cursor is well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects. The list invariants are preserved.
    /// See [`CursorOwner::front_owner_spec`] for the precise specification.
    /// ## Safety
    /// This function only uses the list permission, so there are no illegal memory accesses.
    /// No data races are possible.
    #[verus_spec(r =>
        with
            Tracked(owner): Tracked<LinkedListOwner<M>>,
            Tracked(perm): Tracked<vstd::simple_pptr::PointsTo<LinkedList<M>>>,
                    -> r_perm: Tracked<CursorOwner<M>>,
        requires
            perm.pptr() == ptr,
            perm.is_init(),
            perm.mem_contents().value().wf(owner),
            owner.inv(),
        ensures
            r.wf(r_perm@),
            r_perm@.inv(),
            r_perm@ == CursorOwner::front_owner_spec(owner, perm),
    )]
    pub fn cursor_front_mut(ptr: PPtr<Self>) -> CursorMut<M> {
        let ll = ptr.borrow(Tracked(&perm));
        let current = ll.front;

        proof_with!(|= Tracked(CursorOwner::front_owner(owner, perm)));
        CursorMut { list: ptr, current }
    }

    /// Gets a cursor at the back that can mutate the linked list links.
    ///
    /// If the list is empty, the cursor points to the "ghost" non-element.
    /// # Verified Properties
    /// ## Preconditions
    /// The list must be well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects.
    /// ## Postconditions
    /// The cursor is well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects. The list invariants are preserved.
    /// See [`CursorOwner::back_owner_spec`] for the precise specification.
    /// ## Safety
    /// This function only uses the list permission, so there are no illegal memory accesses.
    /// No data races are possible.
    #[verus_spec(
        with
            Tracked(owner): Tracked<LinkedListOwner<M>>,
            Tracked(perm): Tracked<vstd::simple_pptr::PointsTo<LinkedList<M>>>
    )]
    pub fn cursor_back_mut(ptr: PPtr<Self>) -> (res: (CursorMut<M>, Tracked<CursorOwner<M>>))
        requires
            perm.pptr() == ptr,
            perm.is_init(),
            perm.mem_contents().value().wf(owner),
            owner.inv(),
        ensures
            res.0.wf(res.1@),
            res.1@.inv(),
            res.1@ == CursorOwner::back_owner_spec(owner, perm),
    {
        let ll = ptr.borrow(Tracked(&perm));
        let current = ll.back;

        (CursorMut { list: ptr, current }, Tracked(CursorOwner::back_owner(owner, perm)))
    }

    /// Gets a cursor at the "ghost" non-element that can mutate the linked list links.
    #[verus_spec(
        with Tracked(owner): Tracked<&mut LinkedListOwner<M>>
    )]
    fn cursor_at_ghost_mut(ptr: PPtr<Self>) -> CursorMut<M> {
        CursorMut { list: ptr, current: None }
    }

    /// # Verification Assumption
    /// We assume that there is an available ID for `lazy_get_id` to return.
    /// This is safe because it will panic if the ID allocator is exhausted.
    #[verifier::external_body]
    #[verus_spec(
        with Tracked(owner): Tracked<&mut LinkedListOwner<M>>
    )]
    fn lazy_get_id(ptr: PPtr<Self>) -> (id: u64)
        ensures
            old(owner).list_id != 0 ==> id == old(owner).list_id && *owner == *old(owner),
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

impl<M: AnyFrameMeta + Repr<MetaSlot>> CursorMut<M> {
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
            self.model(owner.move_next_owner_spec()) == old(self).model(owner).move_next_spec(),
            owner.move_next_owner_spec().inv(),
            self.wf(owner.move_next_owner_spec()),
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
            Some(current) => *borrow_field!(& current => next, owner.list_own.perms.tracked_borrow(owner.index)),
            None => borrow_field!(self.list => front, &owner.list_perm),
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
            self.model(owner.move_prev_owner_spec()) == old(self).model(owner).move_prev_spec(),
            owner.move_prev_owner_spec().inv(),
            self.wf(owner.move_prev_owner_spec()),
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
            Some(current) => *borrow_field!(& current => prev, owner.list_own.perms.tracked_borrow(owner.index)),
            None => borrow_field!(self.list => back, &owner.list_perm),
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

    /*
    /// Gets the mutable reference to the current frame's metadata.
    pub fn current_meta(&mut self) -> Option<&mut M> {
        self.current.map(|current| {
            // SAFETY: `&mut self` ensures we have exclusive access to the
            // frame metadata.
            let link_mut = unsafe { &mut *current.as_ptr() };
            // We should not allow `&mut Link<M>` to modify the original links,
            // which would break the linked list. So we just return the
            // inner metadata `M`.
            &mut link_mut.meta
        })
    }
    */

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
            res.is_some() ==> res.unwrap().0.model(res.unwrap().1@).meta == old(
                owner,
            ).list_own.list[old(owner).index]@,
            res.is_some() ==> self.model(*owner) == old(self).model(*old(owner)).remove(),
            res.is_some() ==> res.unwrap().1@.frame_link_inv(),
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

        #[verus_spec(with Tracked(&regions.slots.tracked_borrow(frame_to_index(paddr))))]
        let frame_meta = frame.meta_mut();

        let opt_prev = borrow_field!(frame_meta => prev, &frame_own.meta_perm);

        if let Some(prev) = opt_prev {
            // SAFETY: We own the previous node by `&mut self` and the node is
            // initialized.
            update_field!(prev => next <- next_ptr; owner.list_own.perms, owner.index-1);

            assert(owner.index > 0);
        } else {
            update_field!(self.list => front <- next_ptr; owner.list_perm);
        }

        let prev_ptr = frame.meta().prev;

        #[verus_spec(with Tracked(&regions.slots.tracked_borrow(frame_to_index(paddr))))]
        let frame_meta = frame.meta_mut();
        let opt_next = frame_meta.borrow(Tracked(&frame_own.meta_perm)).next;

        if let Some(next) = opt_next {
            // SAFETY: We own the next node by `&mut self` and the node is
            // initialized.
            update_field!(next => prev <- prev_ptr; owner.list_own.perms, owner.index+1);

            self.current = Some(next);
        } else {
            update_field!(self.list => back <- prev_ptr; owner.list_perm);

            self.current = None;
        }

        #[verus_spec(with Tracked(&regions.slots.tracked_borrow(frame_to_index(paddr))))]
        let frame_meta = frame.meta_mut();

        update_field!(frame_meta => next <- None; frame_own.meta_perm);
        update_field!(frame_meta => prev <- None; frame_own.meta_perm);

        let tracked mut slot_own = regions.slot_owners.tracked_remove(frame_to_index(paddr));

        frame.slot().in_list.store(Tracked(&mut slot_own.in_list), 0);

        proof {
            regions.slot_owners.tracked_insert(frame_to_index(paddr), slot_own);
        }

        update_field!(self.list => size -= 1; owner.list_perm);

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
    /// The cursor must be well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects. The new frame must be active, so that it is
    /// valid to call `into_raw` on it.
    /// ## Postconditions
    /// The new frame is inserted into the list, immediately before the current index.
    /// The list invariants are preserved.
    /// ## Safety
    /// This function calls `into_raw` on the frame, so the caller must ensure that the frame is active and
    /// has not been forgotten already to avoid a memory leak. If the caller attempts to insert a forgotten frame,
    /// the invariant around `into_raw` and `from_raw` will be violated. But, it is the safe failure case in that
    /// it will not cause a double-free.
    #[verus_spec(
        with Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(owner): Tracked<&mut CursorOwner<M>>,
            Tracked(frame_own): Tracked<&mut UniqueFrameOwner<Link<M>>>
    )]
    #[verusfmt::skip]
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
            old(regions).slot_owners[old(frame_own).slot_index].in_list.is_for(
                old(regions).slots[old(frame_own).slot_index].value().in_list,
            ),
            old(frame_own).meta_perm.addr() == frame.ptr.addr(),
            old(frame_own).frame_link_inv(),
        ensures
            self.model(*owner) == old(self).model(*old(owner)).insert(frame_own.meta_own@),
            self.wf(*owner),
            owner.inv(),
            owner.list_own.list == old(owner).list_own.list.insert(old(owner).index, old(frame_own).meta_own),
            owner.list_own.list_id == old(owner).list_own.list_id,
    {
        let ghost owner0 = *owner;
        // The frame can't possibly be in any linked lists since the list will
        // own the frame so there can't be any unique pointers to it.
        assert(meta_addr(frame_own.slot_index) == frame.ptr.addr()) by { admit() };

        assert(regions.slot_owners.contains_key(frame_own.slot_index));
        let tracked slot_own = regions.slot_owners.tracked_borrow(frame_own.slot_index);

        #[verus_spec(with Tracked(&regions.slots.tracked_borrow(frame_own.slot_index)))]
        let frame_ptr = frame.meta_mut();
        assert(frame_ptr.addr() == frame.ptr.addr());

        if let Some(current) = self.current {
            assert(owner.list_own.inv_at(owner.index));
            assert(owner.index > 0 ==> owner.list_own.inv_at(owner.index - 1));
            assert(owner.index < owner.length() - 1 ==> owner.list_own.inv_at(owner.index + 1));

            // SAFETY: We own the current node by `&mut self` and the node is
            // initialized.
            let tracked mut cur_perm = owner.list_own.perms.tracked_remove(owner.index);
            let opt_prev = borrow_field!(current => prev, &cur_perm);
            proof {
                owner.list_own.perms.tracked_insert(owner.index, cur_perm);
            }

            if let Some(prev) = opt_prev {
                // SAFETY: We own the previous node by `&mut self` and the node
                // is initialized.
                update_field!(prev => next <- Some(frame_ptr); owner.list_own.perms, owner.index-1);

                update_field!(frame_ptr => prev <- Some(prev); frame_own.meta_perm);
                update_field!(frame_ptr => next <- Some(prev); frame_own.meta_perm);

                update_field!(current => prev <- Some(frame_ptr); owner.list_own.perms, owner.index);
            } else {
                update_field!(frame_ptr => next <- Some(current); frame_own.meta_perm);

                update_field!(current => prev <- Some(frame_ptr); owner.list_own.perms, owner.index);

                update_field!(self.list => front <- Some(frame_ptr); owner.list_perm);
            }
        } else {
            assert(0 < owner.length() ==> owner.list_own.inv_at(owner.index - 1));

            if let Some(back) = borrow_field!(self.list => back, &owner.list_perm) {
                assert(owner.index == owner.length());

                // SAFETY: We have ownership of the links via `&mut self`.
                //                    debug_assert!(back.as_mut().next.is_none());
                update_field!(back => next <- Some(frame_ptr); owner.list_own.perms, owner.length()-1);

                update_field!(frame_ptr => prev <- Some(back); frame_own.meta_perm);

                update_field!(self.list => back <- Some(frame_ptr); owner.list_perm);
            } else {
                //                debug_assert_eq!(self.list.front, None);
                update_field!(self.list => front <- Some(frame_ptr); owner.list_perm);
                update_field!(self.list => back <- Some(frame_ptr); owner.list_perm);
            }
        }

        #[verus_spec(with Tracked(&regions.slots.tracked_borrow(frame_own.slot_index)))]
        let slot = frame.slot();

        assert(regions.slot_owners.contains_key(frame_to_index(meta_to_frame(frame.ptr.addr()))));
        let tracked mut slot_own = regions.slot_owners.tracked_remove(
            frame_to_index(meta_to_frame(frame.ptr.addr())),
        );

        #[verusfmt::skip]
        slot.in_list.store(
            Tracked(&mut slot_own.in_list),
            #[verus_spec(with Tracked(&mut owner.list_own))]
            LinkedList::<M>::lazy_get_id(self.list)
        );

        proof {
            regions.slot_owners.tracked_insert(
                frame_to_index(meta_to_frame(frame.ptr.addr())),
                slot_own
            )
        }

        assert(regions.inv()) by { admit() };

        // Forget the frame to transfer the ownership to the list.
        #[verus_spec(with Tracked(regions))]
        let _ = frame.into_raw();

        update_field!(self.list => size += 1; owner.list_perm);

        // TODO: these broke, figure out why (it's related to meta-frame conversions)
        assert(forall|i: int| 0 <= i < owner.index - 1 ==> owner0.list_own.inv_at(i) ==> owner.list_own.inv_at(i)) by {};
        assert(forall|i: int| owner.index <= i < owner.length() ==> owner0.list_own.inv_at(i - 1) == owner.list_own.inv_at(i)) by { admit() };

        proof {
            // TODO: likewise
            assert(owner.list_own.list == owner0.list_own.list.insert(owner0.index, frame_own.meta_own)) by { admit() };
            owner0.insert_owner_spec_implies_model_spec(frame_own.meta_own, *owner);
        }
    }

    /// Provides a reference to the linked list.
    #[rustc_allow_incoherent_impl]
    pub fn as_list(&self) -> PPtr<LinkedList<M>> {
        self.list
    }
}

/*impl Drop for LinkedList
{
    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    fn drop(&mut self) {
        unimplemented!()
//        let mut cursor = self.cursor_front_mut();
//        while cursor.take_current().is_some() {}
    }
}*/

/*
impl Deref for Link {
    type Target = FrameMeta;

    #[rustc_allow_incoherent_impl]
    fn deref(&self) -> &Self::Target {
        &self.meta
    }
}

impl DerefMut for Link {
    #[rustc_allow_incoherent_impl]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.meta
    }
}
*/

impl<M: AnyFrameMeta + Repr<MetaSlot>> Link<M> {
    #[rustc_allow_incoherent_impl]
    /// Creates a new linked list metadata.
    pub const fn new(meta: M) -> Self {
        Self { next: None, prev: None, meta }
    }
}

// SAFETY: If `M::on_drop` reads the page using the provided `VmReader`,
// the safety is upheld by the one who implements `AnyFrameMeta` for `M`.
/*unsafe impl<M> AnyFrameMeta for Link<M>
where
    M: AnyFrameMeta,
{
    fn on_drop(&mut self, reader: &mut crate::mm::VmReader<crate::mm::Infallible>) {
        self.meta.on_drop(reader);
    }

    fn is_untyped(&self) -> bool {
        self.meta.is_untyped()
    }
}
*/
} // verus!
