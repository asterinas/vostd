// SPDX-License-Identifier: MPL-2.0
//! Enabling linked lists of frames without heap allocation.
//!
//! This module leverages the customizability of the metadata system (see
//! [super::meta]) to allow any type of frame to be used in a linked list.
use vstd::prelude::*;

use vstd::seq_lib::*;
use vstd::simple_pptr::*;

use vstd_extra::cast_ptr::*;
use vstd_extra::drop_tracking::{Drop, DropObligation, TrackDrop};
use vstd_extra::ownership::*;

use crate::mm::frame::meta::{
    META_SLOT_SIZE, REF_COUNT_UNIQUE,
    mapping::{frame_to_meta, meta_to_frame},
};
use crate::mm::kspace::FRAME_METADATA_RANGE;
use crate::specs::arch::*;
use crate::specs::mm::frame::{
    linked_list::linked_list_owners::*,
    mapping::{frame_to_index, group_page_meta, max_meta_slots, index_to_meta},
    meta_owners::{MetaSlotOwner, Metadata},
    meta_region_owners::MetaRegionOwners,
    unique::UniqueFrameOwner,
};

use super::{
    MetaSlot, mapping,
    meta::{AnyFrameMeta, get_slot},
    unique::UniqueFrame,
};
use crate::{
    arch::mm::PagingConsts,
    mm::{Paddr, Vaddr},
    //panic::abort,
};
use core::{
    ops::{Deref, DerefMut},
    ptr::NonNull,
    sync::atomic::{AtomicU64, Ordering},
};

verus! {

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
///
/// # Example
///
/// To create metadata types that allows linked list links, wrap the metadata
/// type in [`Link`]:
///
/// ```rust
/// use ostd::{
///     mm::{frame::{linked_list::{Link, LinkedList}, Frame}, FrameAllocOptions},
///     impl_untyped_frame_meta_for,
/// };
///
/// #[derive(Debug)]
/// struct MyMeta { mark: usize }
///
/// type MyFrame = Frame<Link<MyMeta>>;
///
/// impl_untyped_frame_meta_for!(MyMeta);
///
/// let alloc_options = FrameAllocOptions::new();
/// let frame1 = alloc_options.alloc_frame_with(Link::new(MyMeta { mark: 1 })).unwrap();
/// let frame2 = alloc_options.alloc_frame_with(Link::new(MyMeta { mark: 2 })).unwrap();
///
/// let mut list = LinkedList::new();
/// list.push_front(frame1.try_into().unwrap());
/// list.push_front(frame2.try_into().unwrap());
///
/// let mut cursor = list.cursor_front_mut();
/// assert_eq!(cursor.current_meta().unwrap().mark, 2);
/// cursor.move_next();
/// assert_eq!(cursor.current_meta().unwrap().mark, 1);
/// ```
///
/// [`from_in_use`]: super::Frame::from_in_use
///
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
/// [`CursorOwner::wf_with_region`] and [`CursorMut::wf_region`].
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
            s == owner@.list.len(),
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
            old(frame_own).inv(),
            old(frame_own).global_inv(*old(regions)),
            frame.wf(*old(frame_own)),
            old(frame_own).frame_link_inv(*old(regions)),
            old(regions).inv(),
        ensures
            final(owner).relate_region(*final(regions)),
            final(regions).inv(),
            final(owner).list == old(owner).list.insert(0, final(frame_own).meta_own),
            old(owner).list_id != 0 ==> final(owner).list_id == old(owner).list_id,
            final(owner).list_id != 0,
            final(frame_own).meta_own.paddr == old(frame_own).meta_own.paddr,
            final(frame_own).meta_own.in_list == final(owner).list_id,
    )]
    pub fn push_front(&mut self, frame: UniqueFrame<Link<M>>) {
        let current = self.front;
        let tracked owner0 = LinkedListOwner::tracked_take(owner);
        let tracked mut cursor_own = CursorOwner::tracked_front_owner(owner0);
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
            r.is_some() ==> (r->0).1@@.meta == owner.list[0]@,
            r.is_some() ==> (r->0).1@.frame_link_inv(*final(regions)),
    )]
    pub fn pop_front(&mut self) -> Option<
        (UniqueFrame<Link<M>>, Tracked<UniqueFrameOwner<Link<M>>>),
    > {
        let tracked mut cursor_own = CursorOwner::tracked_front_owner(owner);
        let current = self.front;
        let mut cursor = CursorMut { list: self, current };

        proof {
            if owner.list.len() > 0 {
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
            old(frame_own).inv(),
            old(frame_own).global_inv(*old(regions)),
            frame.wf(*old(frame_own)),
            old(frame_own).frame_link_inv(*old(regions)),
            old(regions).inv(),
        ensures
            final(owner).relate_region(*final(regions)),
            final(regions).inv(),
            old(owner).list.len() > 0 ==> final(owner).list == old(owner).list.insert(
                old(owner).list.len() - 1, final(frame_own).meta_own),
            old(owner).list.len() == 0 ==> final(owner).list == old(owner).list.insert(
                0, final(frame_own).meta_own),
            // Id preserved when already minted; a fresh (empty) list adopts a
            // non-zero id.
            old(owner).list_id != 0 ==> final(owner).list_id == old(owner).list_id,
            final(owner).list_id != 0,
            final(frame_own).meta_own.paddr == old(frame_own).meta_own.paddr,
            final(frame_own).meta_own.in_list == final(owner).list_id,
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
            r.is_some() ==> (r->0).1@@.meta == owner.list[owner.list.len() - 1]@,
            r.is_some() ==> (r->0).1@.frame_link_inv(*final(regions)),
    )]
    pub fn pop_back(&mut self) -> Option<
        (UniqueFrame<Link<M>>, Tracked<UniqueFrameOwner<Link<M>>>),
    > {
        let current = self.back;
        let tracked mut cursor_own = CursorOwner::tracked_back_owner(owner);
        let mut cursor = CursorMut { list: self, current };

        proof {
            if owner.list.len() > 0 {
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
        ensures
            old(owner).list_id != 0 ==> *final(owner) == *old(owner),
    )]
    pub fn contains(&mut self, frame: Paddr) -> bool {
        let Ok(slot_ptr) = get_slot(frame) else {
            return false;
        };

        proof {
            // `get_slot` returned `Ok`, so `has_safe_slot(frame)` holds; with
            // `regions.inv()` that pins the slot in the region maps, its
            // metadata as init, and its `in_list` permission as governing the
            // slot's atomic — the same facts `cursor_mut_at` derives in-body.
            broadcast use group_page_meta;

            let idx = frame_to_index(frame);
            assert(regions.slot_owners.contains_key(idx));
            assert(regions.slots.contains_key(idx));
            assert(regions.slots[idx].is_init());
            assert(regions.slot_owners[idx].inner_perms.in_list.is_for(
                regions.slots[idx].value().in_list,
            ));
        }

        let tracked mut slot_perm = regions.slots.tracked_remove(frame_to_index(frame));
        let tracked mut slot_own = regions.slot_owners.tracked_remove(frame_to_index(frame));

        let slot = slot_ptr.take(Tracked(&mut slot_perm));

        let tracked mut inner_perms = slot_own.tracked_borrow_mut_inner_perms();

        let in_list = slot.in_list.load(Tracked(&mut inner_perms.in_list));
        slot_ptr.put(Tracked(&mut slot_perm), slot);

        proof {
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
                broadcast use group_page_meta;

                assert(regions.slot_owners.contains_key(idx));
                assert(regions.slots.contains_key(idx));
            }
            let tracked slot_perm = regions.slots.tracked_borrow(idx);
            let tracked mut slot_own = regions.slot_owners.tracked_remove(idx);
            let tracked mut inner_perms = slot_own.tracked_borrow_mut_inner_perms();

            let slot = slot_ptr.borrow(Tracked(slot_perm));

            let in_list = slot.in_list.load(Tracked(&mut inner_perms.in_list));

            let contains = in_list == #[verus_spec(with Tracked(&owner))]
            self.lazy_get_id();

            #[verus_spec(with Tracked(slot_perm))]
            let meta_ptr = slot.as_meta_ptr::<Link<M>>();

            proof {
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
            id != 0,
            final(self).list_id == id,
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
            owner.wf_with_region(*regions),
            old(self).wf_region(owner, *regions),
        ensures
            owner.move_next_owner_spec()@ == owner@.move_next_spec(),
            owner.move_next_owner_spec().wf_with_region(*regions),
            final(self).wf_region(owner.move_next_owner_spec(), *regions),
    {
        let ghost old_self = *self;

        proof {
            if self.current is Some {
                owner.list_own.relate_region_at_facts(*regions, owner.index);
            }
            if owner.index < owner.length() - 1 {
                owner.list_own.relate_region_at_facts(*regions, owner.index + 1);
            }
        }

        self.current = match self.current {
            // SAFETY: The cursor is pointing to a valid element.
            Some(current) => {
                let current_md = MetadataAsLink::cast_to_metadata(current);
                let ghost idx = frame_to_index(meta_to_frame(current.addr()));

                proof {
                    assert(idx == owner.list_own.slot_index_at(owner.index));
                    assert(regions.slots.contains_key(idx));
                    assert(regions.slot_owners.contains_key(idx));
                }

                let tracked meta_perm = regions.borrow_typed_perm::<Link<M>>(idx);

                current_md.borrow(Tracked(meta_perm)).metadata.next
            },
            None => self.list.front,
        };

        proof {
            LinkedListOwner::<M>::view_preserves_len(owner.list_own.list);
            assert(owner.move_next_owner_spec()@.fore == owner@.move_next_spec().fore);
            assert(owner.move_next_owner_spec()@.rear == owner@.move_next_spec().rear);
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
            owner.wf_with_region(*regions),
            old(self).wf_region(owner, *regions),
        ensures
            owner.move_prev_owner_spec()@ == owner@.move_prev_spec(),
            owner.move_prev_owner_spec().wf_with_region(*regions),
            final(self).wf_region(owner.move_prev_owner_spec(), *regions),
    {
        let ghost old_self = *self;

        proof {
            if self.current is Some {
                owner.list_own.relate_region_at_facts(*regions, owner.index);
            }
            if 0 < owner.index {
                owner.list_own.relate_region_at_facts(*regions, owner.index - 1);
            }
        }

        self.current = match self.current {
            // SAFETY: The cursor is pointing to a valid element.
            Some(current) => {
                let current_md = MetadataAsLink::cast_to_metadata(current);
                let ghost idx = frame_to_index(meta_to_frame(current.addr()));

                proof {
                    assert(idx == owner.list_own.slot_index_at(owner.index));
                    assert(regions.slots.contains_key(idx));
                    assert(regions.slot_owners.contains_key(idx));
                }

                let tracked meta_perm = regions.borrow_typed_perm::<Link<M>>(idx);

                current_md.borrow(Tracked(meta_perm)).metadata.prev
            },
            None => self.list.back,
        };

        proof {
            LinkedListOwner::<M>::view_preserves_len(owner.list_own.list);

            if owner@.list_model.list.len() > 0 {
                if owner@.fore.len() > 0 {
                    assert(owner.move_prev_owner_spec()@.fore == owner@.move_prev_spec().fore);
                    assert(owner.move_prev_owner_spec()@.rear == owner@.move_prev_spec().rear);
                    if owner@.rear.len() > 0 {
                        owner.list_own.relate_region_at_facts(*regions, owner.index);
                    }
                } else {
                    owner.list_own.relate_region_at_facts(*regions, owner.index);
                    assert(owner.move_prev_owner_spec()@.rear == owner@.move_prev_spec().rear);
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
            old(owner).wf_with_region(*old(regions)),
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
                    owner.list_own.relate_region_at_facts(*regions, owner.index);
                }
                let current_md = MetadataAsLink::cast_to_metadata(current);
                let ghost idx = frame_to_index(meta_to_frame(current.addr()));
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
            None => None,
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
    #[verifier::spinoff_prover]
    pub fn take_current(&mut self) -> (res: Option<
        (UniqueFrame<Link<M>>, Tracked<UniqueFrameOwner<Link<M>>>),
    >)
        requires
            old(self).wf_region(*old(owner), *old(regions)),
            old(owner).wf_with_region(*old(regions)),
            old(regions).inv(),
        ensures
            old(owner).length() == 0 ==> res.is_none(),
            old(self).current.is_some() ==> res.is_some(),
            res.is_some() ==> (res->0).1@@.meta == old(owner).list_own.list[old(owner).index]@,
            res.is_some() ==> final(owner)@ == old(owner)@.remove(),
            res.is_some() ==> (res->0).1@.frame_link_inv(*final(regions)),
            // Invariant preservation
            res.is_some() ==> final(owner).wf_with_region(*final(regions)),
            res.is_some() ==> final(self).wf_region(*final(owner), *final(regions)),
            res.is_none() ==> *final(owner) == *old(owner),
            final(regions).inv(),
            // Structural: remove_owner_spec
            res.is_some() ==> final(owner).index == old(owner).index,
            res.is_some() ==> final(owner).list_own.list == old(owner).list_own.list.remove(
                old(owner).index,
            ),
            final(owner).list_own.list_id == old(owner).list_own.list_id,
            res.is_some() ==> {
                let paddr = old(self).current->0.addr();
                let idx = frame_to_index(meta_to_frame(paddr));
                &&& final(regions).slots.dom() == old(regions).slots.dom()
                &&& final(regions).slot_owners[idx].inner_perms.ref_count.value()
                    == REF_COUNT_UNIQUE
                &&& final(regions).slot_owners[idx].inner_perms.in_list.value() == 0
                &&& final(regions).slot_owners[idx].inner_perms.storage.is_init()
                &&& final(regions).slot_owners[idx].inner_perms.vtable_ptr.is_init()
                &&& final(regions).slot_owners[idx].slot_vaddr == index_to_meta(idx)
                &&& final(regions).slot_owners[idx].paths_in_pt == old(
                    regions,
                ).slot_owners[idx].paths_in_pt
            },
            res.is_some() ==> forall|j: usize|
                #![trigger final(regions).slot_owners[j]]
                j != frame_to_index(meta_to_frame(old(self).current->0.addr())) ==> {
                    &&& final(regions).slot_owners[j].usage == old(regions).slot_owners[j].usage
                    &&& final(regions).slot_owners[j].slot_vaddr == old(
                        regions,
                    ).slot_owners[j].slot_vaddr
                    &&& final(regions).slot_owners[j].paths_in_pt == old(
                        regions,
                    ).slot_owners[j].paths_in_pt
                },
            res.is_none() ==> *final(regions) == *old(regions),
            // Properties of the returned frame needed for UniqueFrame::drop
            res.is_some() ==> (res->0).0.wf((res->0).1@),
            res.is_some() ==> (res->0).1@.inv(),
            res.is_some() ==> (res->0).1@.slot_index == frame_to_index(
                meta_to_frame(old(self).current->0.addr()),
            ),
            res.is_some() ==> (res->0).0.ptr.addr() == old(self).current->0.addr(),
            res.is_some() ==> final(regions).frame_obligations == old(
                regions,
            ).frame_obligations.insert(frame_to_index(meta_to_frame(old(self).current->0.addr()))),
    {
        let ghost owner0 = *owner;
        let ghost regions0 = *regions;

        let current = self.current?;
        let current_md = MetadataAsLink::cast_to_metadata(current);

        proof {
            owner.list_own.relate_region_at_facts(*regions, owner.index);
            if owner.index > 0 {
                owner.list_own.relate_region_at_facts(*regions, owner.index - 1);
            }
            if owner.index < owner.list_own.list.len() - 1 {
                owner.list_own.relate_region_at_facts(*regions, owner.index + 1);
            }
        }

        let meta_ptr = current.addr();
        let paddr = meta_to_frame(meta_ptr);
        let ghost idx = frame_to_index(paddr);

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
            assert(regions.slots.dom() == regions0.slots.dom());
            assert forall|j: usize| #![trigger regions0.slot_owners[j]] j != idx implies {
                &&& regions.slot_owners[j].usage == regions0.slot_owners[j].usage
                &&& regions.slot_owners[j].slot_vaddr == regions0.slot_owners[j].slot_vaddr
                &&& regions.slot_owners[j].paths_in_pt == regions0.slot_owners[j].paths_in_pt
            } by {}
        }

        let tracked tp = regions.borrow_typed_perm::<Link<M>>(idx);
        proof {
            assert(*tp == owner0.list_own.meta_perm_of(regions0, owner0.index));
        }
        let next_ptr = current_md.borrow(Tracked(tp)).metadata.next;
        let prev_ptr = current_md.borrow(Tracked(tp)).metadata.prev;

        if let Some(prev_link) = prev_ptr {
            let prev = MetadataAsLink::cast_to_metadata(prev_link);
            proof {
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
            prev.borrow_mut(Tracked(prev_perm)).metadata.next = next_ptr;

            proof {
                assert(regions.inv());
                assert(regions.slots.dom() == regions0.slots.dom());
                assert forall|j: usize| #![trigger regions0.slot_owners[j]] j != idx implies {
                    &&& regions.slot_owners[j].usage == regions0.slot_owners[j].usage
                    &&& regions.slot_owners[j].slot_vaddr == regions0.slot_owners[j].slot_vaddr
                    &&& regions.slot_owners[j].paths_in_pt == regions0.slot_owners[j].paths_in_pt
                } by {
                    if j == frame_to_index(meta_to_frame(prev.addr())) {
                    }
                }
            }

        } else {
            self.list.front = next_ptr;
            proof {
                assert(regions.slots.dom() == regions0.slots.dom());
                assert forall|j: usize| #![trigger regions0.slot_owners[j]] j != idx implies {
                    &&& regions.slot_owners[j].usage == regions0.slot_owners[j].usage
                    &&& regions.slot_owners[j].slot_vaddr == regions0.slot_owners[j].slot_vaddr
                    &&& regions.slot_owners[j].paths_in_pt == regions0.slot_owners[j].paths_in_pt
                } by {}
            }
        }

        if let Some(next_link) = next_ptr {
            let next = MetadataAsLink::cast_to_metadata(next_link);
            proof {
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
            next.borrow_mut(Tracked(next_perm)).metadata.prev = prev_ptr;

            proof {
                assert(regions.inv());
                assert(regions.slots.dom() == regions0.slots.dom());
                assert forall|j: usize| #![trigger regions0.slot_owners[j]] j != idx implies {
                    &&& regions.slot_owners[j].usage == regions0.slot_owners[j].usage
                    &&& regions.slot_owners[j].slot_vaddr == regions0.slot_owners[j].slot_vaddr
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
                assert(regions.slots.dom() == regions0.slots.dom());
                assert forall|j: usize| #![trigger regions0.slot_owners[j]] j != idx implies {
                    &&& regions.slot_owners[j].usage == regions0.slot_owners[j].usage
                    &&& regions.slot_owners[j].slot_vaddr == regions0.slot_owners[j].slot_vaddr
                    &&& regions.slot_owners[j].paths_in_pt == regions0.slot_owners[j].paths_in_pt
                } by {}
            }
        }

        let tracked frame_perm = regions.borrow_mut_typed_perm::<Link<M>>(idx);
        current_md.borrow_mut(Tracked(frame_perm)).metadata.next = None;

        let tracked frame_perm = regions.borrow_mut_typed_perm::<Link<M>>(idx);
        current_md.borrow_mut(Tracked(frame_perm)).metadata.prev = None;

        let tracked frame_outer = regions.slots.tracked_remove(idx);
        let tracked mut frame_so = regions.slot_owners.tracked_remove(idx);
        let tracked mut fip = frame_so.tracked_borrow_mut_inner_perms();
        #[verus_spec(with Tracked(&frame_outer))]
        let slot = frame.slot();
        slot.in_list.store(Tracked(&mut fip.in_list), 0);
        proof {
            regions.slots.tracked_insert(idx, frame_outer);
            regions.slot_owners.tracked_insert(idx, frame_so);
            assert(regions.inv());
            assert(regions.slots.dom() == regions0.slots.dom());
            assert(regions.slot_owners[idx].paths_in_pt == regions0.slot_owners[idx].paths_in_pt);
            assert forall|j: usize| #![trigger regions0.slot_owners[j]] j != idx implies {
                &&& regions.slot_owners[j].usage == regions0.slot_owners[j].usage
                &&& regions.slot_owners[j].slot_vaddr == regions0.slot_owners[j].slot_vaddr
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
                &&& fp.inner_perms.ref_count.value() == REF_COUNT_UNIQUE
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
                oldl.relate_region_at_facts(regions0, p);
                oldl.relate_region_at_facts(regions0, nn);
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
    #[verifier::spinoff_prover]
    pub fn insert_before(&mut self, mut frame: UniqueFrame<Link<M>>)
        requires
            old(self).wf_region(*old(owner), *old(regions)),
            old(owner).wf_with_region(*old(regions)),
            old(regions).inv(),
            old(frame_own).inv(),
            old(frame_own).global_inv(*old(regions)),
            frame.wf(*old(frame_own)),
            old(frame_own).frame_link_inv(*old(regions)),
        ensures
            final(owner).wf_with_region(*final(regions)),
            final(self).wf_region(*final(owner), *final(regions)),
            final(regions).inv(),
            final(owner).list_own.list == old(owner).list_own.list.insert(
                old(owner).index,
                final(frame_own).meta_own,
            ),
            // The id is preserved when it was already minted; a `list_id == 0`
            // (necessarily empty) list adopts a freshly-minted non-zero id.
            old(owner).list_own.list_id != 0 ==> final(owner).list_own.list_id == old(
                owner,
            ).list_own.list_id,
            final(owner).list_own.list_id != 0,
            final(owner).index == old(owner).index + 1,
            final(frame_own).meta_own.paddr == old(frame_own).meta_own.paddr,
            final(frame_own).meta_own.in_list == final(owner).list_own.list_id,
            final(owner)@ == old(owner)@.insert(final(frame_own).meta_own@),
    {
        let ghost owner0 = *owner;
        let ghost regions0 = *regions;
        let ghost nn = owner.index as int;

        proof {
            owner0.list_own.length_lt_usize_max(regions0);
            if nn > 0 {
                owner.list_own.relate_region_at_facts(*regions, nn - 1);
            }
            if nn < owner.list_own.list.len() {
                owner.list_own.relate_region_at_facts(*regions, nn);
            }
        }

        let frame_ptr = ReprPtr::<MetaSlot, Metadata<Link<M>>>::from_pptr(frame.ptr);
        let frame_ptr_as_link = MetadataAsLink::cast_from_metadata(frame_ptr);

        let ghost frame_idx_g: usize = frame_own.slot_index;

        if let Some(current) = self.current {
            let current_md = MetadataAsLink::cast_to_metadata(current);

            // Read current's prev pointer.
            let opt_prev_link: Option<ReprPtr<MetaSlot, MetadataAsLink<M>>>;

            let tracked tp = regions.borrow_typed_perm::<Link<M>>(
                frame_to_index(meta_to_frame(current.addr())),
            );
            opt_prev_link = current_md.borrow(Tracked(tp)).metadata.prev;

            if let Some(prev_link) = opt_prev_link {
                let prev = MetadataAsLink::cast_to_metadata(prev_link);

                let tracked perm = regions.borrow_mut_typed_perm::<Link<M>>(
                    frame_to_index(meta_to_frame(prev.addr())),
                );
                prev.borrow_mut(Tracked(perm)).metadata.next = Some(frame_ptr_as_link);

                let tracked perm = regions.borrow_mut_typed_perm::<Link<M>>(frame_idx_g);
                frame_ptr.borrow_mut(Tracked(perm)).metadata.prev = Some(prev_link);

                let tracked perm = regions.borrow_mut_typed_perm::<Link<M>>(frame_idx_g);
                frame_ptr.borrow_mut(Tracked(perm)).metadata.next = Some(current);

                let tracked perm = regions.borrow_mut_typed_perm::<Link<M>>(
                    frame_to_index(meta_to_frame(current.addr())),
                );
                current_md.borrow_mut(Tracked(perm)).metadata.prev = Some(frame_ptr_as_link);

                proof {
                    let fpn_local = vstd_extra::cast_ptr::PointsTo::<
                        MetaSlot,
                        Metadata<Link<M>>,
                    >::new_spec(
                        regions.slots[frame_idx_g],
                        regions.slot_owners[frame_idx_g].inner_perms,
                    );
                    assert(fpn_local.value().metadata.prev.unwrap().addr()
                        == owner0.list_own.list[nn - 1].paddr);
                    assert(fpn_local.value().metadata.prev.unwrap().ptr
                        == regions0.slots[owner0.list_own.slot_index_at(nn - 1)].pptr());
                    assert(fpn_local.value().metadata.next.unwrap().addr()
                        == owner0.list_own.list[nn].paddr);
                    assert(fpn_local.value().metadata.next.unwrap().ptr
                        == regions0.slots[owner0.list_own.slot_index_at(nn)].pptr());
                }
            } else {
                let tracked perm = regions.borrow_mut_typed_perm::<Link<M>>(frame_idx_g);
                frame_ptr.borrow_mut(Tracked(perm)).metadata.next = Some(current);

                let tracked perm = regions.borrow_mut_typed_perm::<Link<M>>(
                    frame_to_index(meta_to_frame(current.addr())),
                );
                current_md.borrow_mut(Tracked(perm)).metadata.prev = Some(frame_ptr_as_link);

                self.list.front = Some(frame_ptr_as_link);
            }
        } else {
            if let Some(back) = self.list.back {
                let back_md = MetadataAsLink::cast_to_metadata(back);

                let tracked perm = regions.borrow_mut_typed_perm::<Link<M>>(
                    frame_to_index(meta_to_frame(back.addr())),
                );
                back_md.borrow_mut(Tracked(perm)).metadata.next = Some(frame_ptr_as_link);

                let tracked perm = regions.borrow_mut_typed_perm::<Link<M>>(frame_idx_g);
                frame_ptr.borrow_mut(Tracked(perm)).metadata.prev = Some(back);

                self.list.back = Some(frame_ptr_as_link);
            } else {
                // EMPTY list: just point both ends at the inserted frame.
                self.list.front = Some(frame_ptr_as_link);
                self.list.back = Some(frame_ptr_as_link);
            }
        }

        #[verus_spec(with Tracked(&owner.list_own))]
        let list_id = self.list.lazy_get_id();

        proof {
            assert(regions.slots.contains_key(frame_idx_g));
        }
        let tracked frame_outer = regions.slots.tracked_remove(frame_idx_g);
        let tracked mut frame_so = regions.slot_owners.tracked_remove(frame_idx_g);
        let tracked mut fip = frame_so.tracked_borrow_mut_inner_perms();
        #[verus_spec(with Tracked(&frame_outer))]
        let slot = frame.slot();
        slot.in_list.store(Tracked(&mut fip.in_list), list_id);
        proof {
            regions.slots.tracked_insert(frame_idx_g, frame_outer);
            regions.slot_owners.tracked_insert(frame_idx_g, frame_so);
            assert(regions.inv());
        }

        #[verus_spec(with Tracked(&*frame_own), Tracked(regions))]
        let _ = frame.into_raw();

        self.list.size = self.list.size + 1;

        proof {
            CursorOwner::<M>::tracked_list_insert(owner, &mut frame_own.meta_own, list_id);

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
                &&& fp.inner_perms.ref_count.value() == REF_COUNT_UNIQUE
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
                oldl.relate_region_at_facts(regions0, p);
                if nn - 1 >= 0 && nn - 1 < oldl.list.len() {
                    oldl.relate_region_at_facts(regions0, nn - 1);
                }
                if nn >= 0 && nn < oldl.list.len() {
                    oldl.relate_region_at_facts(regions0, nn);
                }
            }

            let fpn = vstd_extra::cast_ptr::PointsTo::<MetaSlot, Metadata<Link<M>>>::new_spec(
                regions.slots[ins],
                regions.slot_owners[ins].inner_perms,
            );
            assert(regions.slots.contains_key(ins));
            assert(regions.slot_owners.contains_key(ins));

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

    /// Real key: the list's `list_id`. The token carries the identity of
    /// the list it belongs to, so a token forged for one list can't be
    /// used to discharge another (the `consume_requires` key match
    /// refuses the mismatch). A multiset ledger over `list_id` is not
    /// added because every live `LinkedList` already has a unique
    /// `LinkedListOwner` in scope — the per-instance discipline is
    /// state-side, not ledger-side.
    type Obligation = DropObligation<u64>;

    open spec fn tracked_redeem_requires(self, s: Self::State) -> bool {
        true
    }

    open spec fn tracked_redeem_ensures(
        self,
        s0: Self::State,
        s1: Self::State,
        obl: Self::Obligation,
    ) -> bool {
        &&& s0 =~= s1
        &&& obl.value() == self.list_id
    }

    proof fn tracked_redeem(self, tracked s: &mut Self::State) -> (tracked obl: Self::Obligation) {
        DropObligation::tracked_mint(self.list_id)
    }

    open spec fn drop_requires(self, s: Self::State, obl: Self::Obligation) -> bool {
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
                s.1.slot_owners[idx].inner_perms.ref_count.value() == REF_COUNT_UNIQUE
            }
        &&& forall|i: int|
            #![trigger s.0.list[i]]
            0 <= i < s.0.list.len() ==> {
                let idx = frame_to_index(meta_to_frame(s.0.list[i].paddr));
                s.1.frame_obligations.count(idx) == 0
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
        &&& obl.value() == self.list_id
    }

    open spec fn drop_ensures(
        self,
        s0: Self::State,
        s1: Self::State,
        obl: Self::Obligation,
    ) -> bool {
        &&& s1.0.list.len() == 0
        &&& forall|i: int|
            #![trigger s0.0.list[i]]
            0 <= i < s0.0.list.len() ==> {
                let idx = frame_to_index(meta_to_frame(s0.0.list[i].paddr));
                s1.1.frame_obligations.count(idx) == s0.1.frame_obligations.count(idx)
            }
        &&& forall|idx: usize|
            #![trigger s1.1.slot_owners[idx]]
            (forall|i: int|
                #![trigger s0.0.list[i]]
                0 <= i < s0.0.list.len() ==> idx != frame_to_index(
                    meta_to_frame(s0.0.list[i].paddr),
                )) ==> {
                &&& s1.1.frame_obligations.count(idx) == s0.1.frame_obligations.count(idx)
                &&& s1.1.slot_owners[idx].usage == s0.1.slot_owners[idx].usage
                &&& s1.1.slot_owners[idx].slot_vaddr == s0.1.slot_owners[idx].slot_vaddr
                &&& s1.1.slot_owners[idx].paths_in_pt == s0.1.slot_owners[idx].paths_in_pt
            }
        &&& s1.1.slots.dom() =~= s0.1.slots.dom()
        &&& s1.1.inv()
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> Drop for LinkedList<M> {
    #[verifier::spinoff_prover]
    fn drop(
        self,
        Tracked(s): Tracked<&mut Self::State>,
        Tracked(obl): Tracked<DropObligation<u64>>,
    ) {
        proof_decl! {
            let tracked mut list_own: LinkedListOwner<M>;
        }
        let ghost original_list = s.0.list;
        let ghost original_list_id = s.0.list_id;
        let ghost n = original_list.len();
        let ghost original_regions = s.1;
        proof {
            list_own = LinkedListOwner::<M>::tracked_take(&mut s.0);
        }
        let tracked regions: &mut MetaRegionOwners = &mut s.1;
        let mut this = self;

        #[verus_spec(with Tracked(list_own))]
        let cursor_pair = this.cursor_front_mut();
        let (mut cursor, Tracked(mut cursor_own)) = cursor_pair;

        proof {
            if n > 0 {
                cursor_own.list_own.relate_region_at_facts(*regions, 0);
                cursor_own.list_own.relate_region_at_facts(*regions, n - 1);
            }
        }

        let ghost mut k: int = 0;

        loop
            invariant_except_break
                cursor.wf_region(cursor_own, *regions),
                cursor.current.is_some() <==> k < n,
            invariant
                cursor_own.wf_with_region(*regions),
                cursor_own.list_own.list_id == original_list_id,
                cursor_own.index == 0,
                regions.inv(),
                cursor_own.list_own.list.len() == n - k,
                0 <= k <= n,
                // The remaining list is a suffix of the original
                forall|j: int|
                    #![trigger cursor_own.list_own.list[j]]
                    0 <= j < n - k ==> cursor_own.list_own.list[j] == original_list[j + k],
                // Elements already taken have their in-list obligation redeemed (count 0)
                forall|j: int|
                    #![trigger original_list[j]]
                    0 <= j < k ==> {
                        let idx = frame_to_index(meta_to_frame(original_list[j].paddr));
                        regions.frame_obligations.count(idx) == 0
                    },
                // slots values inside the original_list.
                forall|idx: usize|
                    #![trigger regions.slot_owners[idx]]
                    (forall|j: int|
                        #![trigger original_list[j]]
                        0 <= j < n ==> idx != frame_to_index(meta_to_frame(original_list[j].paddr)))
                        ==> {
                        &&& regions.frame_obligations.count(idx)
                            == original_regions.frame_obligations.count(idx)
                        &&& regions.slot_owners[idx].usage
                            == original_regions.slot_owners[idx].usage
                        &&& regions.slot_owners[idx].slot_vaddr
                            == original_regions.slot_owners[idx].slot_vaddr
                        &&& regions.slot_owners[idx].paths_in_pt
                            == original_regions.slot_owners[idx].paths_in_pt
                    },
                regions.slots.dom() == original_regions.slots.dom(),
                // `paths_in_pt.is_empty()` precondition).
                forall|j: int|
                    #![trigger original_list[j]]
                    k <= j < n ==> {
                        let idx = frame_to_index(meta_to_frame(original_list[j].paddr));
                        &&& regions.frame_obligations.count(idx)
                            == original_regions.frame_obligations.count(idx)
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
                        &&& original_regions.frame_obligations.count(idx) == 0
                        &&& original_regions.slot_owners[idx].paths_in_pt.is_empty()
                        &&& original_regions.slot_owners[idx].inner_perms.ref_count.value()
                            == REF_COUNT_UNIQUE
                    },
            ensures
                k == n,
                cursor_own.list_own.list.len() == 0,
            decreases n - k,
        {
            #[verus_spec(with Tracked(regions), Tracked(&mut cursor_own))]
            let entry = cursor.take_current();

            if let Some(current) = entry {
                let (mut frame, frame_own_tracked) = current;
                let tracked frame_own = frame_own_tracked.get();
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
                        &&& regions.frame_obligations.count(idx)
                            == regions_pre_drop.frame_obligations.count(idx)
                    }) by {
                        let idx = cursor_own.list_own.slot_index_at(i);
                        let ghost _trig_k = original_list[k as int];
                        let ghost _trig_ik = original_list[i + k + 1];
                        assert(cursor_own.list_own.list[i] == original_list[i + k + 1]);

                        cursor_own.list_own.relate_region_at_facts(regions_pre_drop, i);
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
                        regions.frame_obligations.count(idx) == 0
                    }) by {
                        let ghost _a = original_list[j as int];
                        let ghost _b = original_list[k as int];
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

// SAFETY: `Link<M>` is `Send` and `Sync` if `M` is `Send` and `Sync` because
// we only access these unsafe cells when the frame is not shared. This is
// enforced by `UniqueFrame`.
// #[verifier::external]
// unsafe impl<M> Send for LinkedList<M> where Link<M>: AnyFrameMeta {}
// #[verifier::external]
// unsafe impl<M> Sync for LinkedList<M> where Link<M>: AnyFrameMeta {}
/// A link in the linked list.
pub struct Link<M: AnyFrameMeta + Repr<MetaSlotSmall>> {
    pub next: Option<ReprPtr<MetaSlot, MetadataAsLink<M>>>,
    pub prev: Option<ReprPtr<MetaSlot, MetadataAsLink<M>>>,
    pub meta: M,
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
