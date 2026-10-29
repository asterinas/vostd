// SPDX-License-Identifier: MPL-2.0
//! Enabling linked lists of frames without heap allocation.
//!
//! This module leverages the customizability of the metadata system (see
//! [super::meta]) to allow any type of frame to be used in a linked list.
use vstd::{prelude::*, seq_lib::*, simple_pptr::*};
use vstd_extra::{cast_ptr::*, ownership::*};

use crate::specs::{
    arch::*,
    mm::embedding::list_store::list_registry_ok,
    mm::frame::{
        linked_list::linked_list_owners::*, mapping::*, meta_owners::*,
        meta_region_owners::MetaRegionOwners, unique::UniqueFrameOwner,
    },
};

use super::{MetaSlot, mapping, meta::AnyFrameMeta, unique::UniqueFrame};
use crate::mm::frame::meta::{
    META_SLOT_SIZE, REF_COUNT_UNIQUE,
    mapping::{frame_to_meta, meta_to_frame},
};
use crate::mm::kspace::FRAME_METADATA_RANGE;
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
/// The raw slot and storage permissions for each link are parked in the global
/// [`MetaRegionOwners`], while [`LinkedListOwner`] owns the corresponding
/// type-specific `Link<M>::ReprPerm`. Cursor accessors borrow these independent
/// components together when projecting a `Link<M>`.
/// ## Invariant
/// The linked list uniquely owns the raw frames that it contains, so they cannot be used by other
/// data structures. The frame metadata field `in_list` is equal to `list_id` for all links in the list.
/// The per-link well-formedness against the region (pointer/permission wiring,
/// `next`/`prev` pointer chain) is captured by
/// [`LinkedListOwner::relate_region`] (opaque, with per-position
/// [`LinkedListOwner::relate_region_at`]). The cursor exposes this via
/// [`CursorOwner::wf_with_region`] and [`CursorMut::wf_region`].
/// ## Safety
/// A given linked list can only have one cursor at a time, so there are no data races.
/// The `prev` and `next` fields of the metadata for each link always points to valid
/// links in the list, so the structure is memory safe (will not read or write invalid memory).
pub struct LinkedList<M: AnyFrameMeta + Repr<MetaSlotSmall>> {
    pub front: Option<ReprPtr<MetaSlotStorage, Link<M>>>,
    pub back: Option<ReprPtr<MetaSlotStorage, Link<M>>>,
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
    pub current: Option<ReprPtr<MetaSlotStorage, Link<M>>>,
}

#[verifier::spinoff_prover]
proof fn lemma_meta_region_inv_at(regions: MetaRegionOwners, i: int)
    requires
        regions.inv(),
        regions.contains(i),
    ensures
        regions.slot_owners[i].inv(),
        regions.slots[i].is_init(),
        regions.slots[i].addr() == index_to_meta(i),
        regions.slots[i].value().wf(regions.slot_owners[i]),
        regions.slot_owners[i].slot_vaddr == regions.slots[i].addr(),
{
}

/// Localizes the "no existing slot aliases the inserted frame" universal fact
/// into its own prover query, so the `MetaRegionOwners::inv` and map-insert
/// quantifiers do not get over-instantiated inside `insert_before`'s body.
#[verifier::spinoff_prover]
proof fn lemma_insert_before_slot_distinct<M: AnyFrameMeta + Repr<MetaSlotSmall>>(
    owner0: LinkedListOwner<M>,
    regions0: MetaRegionOwners,
    frame_idx: int,
    nn: int,
)
    requires
        owner0.relate_region(regions0),
        regions0.inv(),
        regions0.contains(frame_idx),
        regions0.slot_owners[frame_idx].in_list_perm.value() == 0,
        0 <= nn <= owner0.list.len() as int,
    ensures
        forall|p: int|
            #![trigger regions0.slot_owners[meta_to_index(owner0.list[p].slot_vaddr)]]
            (0 <= p < owner0.list.len() as int) ==> frame_idx != meta_to_index(
                owner0.list[p].slot_vaddr,
            ),
{
    owner0.lemma_relate_region_shape(regions0);
    assert forall|p: int|
        #![trigger regions0.slot_owners[meta_to_index(owner0.list[p].slot_vaddr)]]
        0 <= p < owner0.list.len() as int implies frame_idx != meta_to_index(
        owner0.list[p].slot_vaddr,
    ) by {
        owner0.lemma_relate_region_at_index(regions0, p);
        owner0.lemma_relate_region_at_facts(regions0, p);
        if frame_idx == meta_to_index(owner0.list[p].slot_vaddr) {
            assert(regions0.slot_owners[meta_to_index(
                owner0.list[p].slot_vaddr,
            )].in_list_perm.value() == owner0.list_id);
        }
    }
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
    /// The new frame is inserted at the front of the list.
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
            frame.inv(),
            old(frame_own).inv(),
            frame.wf_with_region(*old(frame_own), *old(regions)),
            frame.frame_link_inv(*old(frame_own), *old(regions)),
            old(regions).inv(),
        ensures
            final(self).wf_region(*final(owner), *final(regions)),
            final(owner).inv(),
            final(owner).relate_region(*final(regions)),
            final(regions).inv(),
            final(owner).list == old(owner).list.insert(0, final(frame_own).meta_own),
            old(owner).list_id != 0 ==> final(owner).list_id == old(owner).list_id,
            final(owner).list_id != 0,
            final(frame_own).meta_own.slot_vaddr == old(frame_own).meta_own.slot_vaddr,
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
            owner.lemma_relate_region_implies_inv(*regions);
        }
    }

    /// Pops a frame from the front of the linked list.
    /// # Verified Properties
    /// ## Preconditions
    /// The list must be well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects.
    /// ## Postconditions
    /// - The list invariants are preserved.
    /// - Returns the front frame and its owner, or `None` if the list is empty.
    /// ## Safety
    /// See [`take_current`] for the safety guarantees.
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(owner): Tracked<&mut LinkedListOwner<M>>,
            -> frame_owner: Tracked<Option<UniqueFrameOwner<Link<M>>>>,
        requires
            old(regions).inv(),
            old(self).wf_region(*old(owner), *old(regions)),
            old(owner).relate_region(*old(regions)),
        ensures
            final(regions).inv(),
            final(owner).inv(),
            final(owner).relate_region(*final(regions)),
            final(self).wf_region(*final(owner), *final(regions)),
            final(owner).list_id == old(owner).list_id,
            r is Some == (old(owner).list.len() > 0),
            r is Some == frame_owner@ is Some,
            r matches Some(frame) ==> (frame_owner@ matches Some(fo) ==> {
                &&& final(owner).list == old(owner).list.remove(0)
                &&& fo.meta_own@ == old(owner).list[0]@
                &&& frame.inv()
                &&& fo.inv()
                &&& frame.wf(fo)
                &&& frame.wf_with_region(fo, *final(regions))
                &&& frame.frame_link_inv(fo, *final(regions))
            }),
            r is None ==> *final(owner) == *old(owner)
                && *final(self) == *old(self) && *final(regions) == *old(regions),
    )]
    pub fn pop_front(&mut self) -> Option<UniqueFrame<Link<M>>> {
        let tracked owner0 = LinkedListOwner::tracked_take(owner);
        let tracked mut cursor_own = CursorOwner::tracked_front_owner(owner0);
        let tracked mut returned_owner: Option<UniqueFrameOwner<Link<M>>>;

        /* Restore the tracked list owner after the cursor call.
         * Origin Rust: self.cursor_front_mut().take_current()
         */
        #[verus_spec(with Tracked(regions), Tracked(&mut cursor_own) => Tracked(returned_owner))]
        let frame = self.cursor_front_mut().take_current();
        proof! {
            *owner = cursor_own.list_own;
            owner.lemma_relate_region_implies_inv(*regions);
        }
        proof_with!(|= Tracked(returned_owner));
        frame
    }

    /// Pushes a frame to the back of the linked list.
    /// # Verified Properties
    /// ## Preconditions
    /// The list must be well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects. The new frame must be active, so that it is
    /// valid to call `into_raw` on it inside of `insert_before`.
    /// ## Postconditions
    /// - The new frame is inserted at the back of the list.
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
            frame.inv(),
            old(frame_own).inv(),
            frame.wf_with_region(*old(frame_own), *old(regions)),
            frame.frame_link_inv(*old(frame_own), *old(regions)),
            old(regions).inv(),
        ensures
            final(self).wf_region(*final(owner), *final(regions)),
            final(owner).inv(),
            final(owner).relate_region(*final(regions)),
            final(regions).inv(),
            final(owner).list == old(owner).list.insert(
                old(owner).list.len() as int, final(frame_own).meta_own),
            // Id preserved when already minted; a fresh (empty) list adopts a
            // non-zero id.
            old(owner).list_id != 0 ==> final(owner).list_id == old(owner).list_id,
            final(owner).list_id != 0,
            final(frame_own).meta_own.slot_vaddr == old(frame_own).meta_own.slot_vaddr,
            final(frame_own).meta_own.in_list == final(owner).list_id,
    )]
    pub fn push_back(&mut self, frame: UniqueFrame<Link<M>>) {
        let tracked owner0 = LinkedListOwner::tracked_take(owner);
        let tracked mut cursor_own = CursorOwner::tracked_cursor_mut_at_owner(
            owner0,
            owner0.list.len() as int,
        );

        #[verus_spec(with Tracked(regions), Tracked(&mut cursor_own), Tracked(frame_own))]
        self.cursor_at_ghost_mut().insert_before(frame);

        proof {
            *owner = cursor_own.list_own;
            owner.lemma_relate_region_implies_inv(*regions);
            assert(self.wf_region(*owner, *regions));
        }
    }

    /// Pops a frame from the back of the linked list.
    /// # Verified Properties
    /// ## Preconditions
    /// - The list must be well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects.
    /// ## Postconditions
    /// - Returns the back frame and its owner, or `None` if the list is empty.
    /// - The list invariants are preserved.
    /// ## Safety
    /// See [`take_current`] for the safety guarantees.
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(owner): Tracked<&mut LinkedListOwner<M>>,
            -> frame_owner: Tracked<Option<UniqueFrameOwner<Link<M>>>>,
        requires
            old(regions).inv(),
            old(self).wf_region(*old(owner), *old(regions)),
            old(owner).relate_region(*old(regions)),
        ensures
            final(regions).inv(),
            final(owner).inv(),
            final(owner).relate_region(*final(regions)),
            final(self).wf_region(*final(owner), *final(regions)),
            final(owner).list_id == old(owner).list_id,
            (r is Some) == (old(owner).list.len() > 0),
            (r is Some) == (frame_owner@ is Some),
            r matches Some(frame) ==> (frame_owner@ matches Some(fo) ==> {
                &&& final(owner).list == old(owner).list.remove(old(owner).list.len() - 1)
                &&& fo.meta_own@ == old(owner).list[old(owner).list.len() - 1]@
                &&& frame.inv()
                &&& fo.inv()
                &&& frame.wf(fo)
                &&& frame.wf_with_region(fo, *final(regions))
                &&& frame.frame_link_inv(fo, *final(regions))
            }),
            r is None ==> *final(owner) == *old(owner)
                && *final(self) == *old(self) && *final(regions) == *old(regions),
    )]
    pub fn pop_back(&mut self) -> Option<UniqueFrame<Link<M>>> {
        let tracked owner0 = LinkedListOwner::tracked_take(owner);
        let tracked mut cursor_own = CursorOwner::tracked_back_owner(owner0);
        let tracked mut returned_owner: Option<UniqueFrameOwner<Link<M>>>;

        /* Restore the tracked list owner after the cursor call.
         * Origin Rust: self.cursor_back_mut().take_current()
         */
        #[verus_spec(with Tracked(regions), Tracked(&mut cursor_own) => Tracked(returned_owner))]
        let frame = self.cursor_back_mut().take_current();
        proof! {
            *owner = cursor_own.list_own;
            owner.lemma_relate_region_implies_inv(*regions);
        }
        proof_with!(|= Tracked(returned_owner));
        frame
    }

    /// Tells if a frame is in the list.
    /// # Verified Properties
    /// ## Preconditions
    /// - The list must be well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects.
    /// - The list owner must relate its links to the region permissions.
    /// ## Postconditions
    /// - The result is `true` exactly when the frame address is valid and its
    /// region-owned `in_list` tag equals the list's ID after lazy initialization.
    /// - A valid frame in the owner's list always returns `true`.
    /// ## Safety
    /// - `lazy_get_id` uses atomic memory accesses, so there are no data races.
    /// - We assume that the ID allocator has an available ID if the list previously didn't have one,
    /// but the consequence if that is not the case is a failsafe panic.
    /// - Everything else conforms to the safe interface.
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&MetaRegionOwners>,
            Tracked(owner): Tracked<&LinkedListOwner<M>>,
        requires
            regions.inv(),
            old(self).wf(*owner),
            owner.relate_region(*regions),
        ensures
            (valid_frame_paddr(frame) && exists|i: int| 0 <= i < owner.list.len()
                && #[trigger] meta_to_index(owner.list[i].slot_vaddr) == frame_to_index(frame))
                ==> r,
        returns
            valid_frame_paddr(frame)
                && regions.slot_owners[frame_to_index(frame)].in_list_perm.value()
                    == final(self).list_id,
    )]
    pub fn contains(&mut self, frame: Paddr) -> bool {
        proof_decl! {
        let ghost idx = frame_to_index(frame);
            if valid_frame_paddr(frame) {
                regions.lemma_contains_valid_frame_paddr(frame);
                if exists|i: int| 0 <= i < owner.list.len()
                    && #[trigger] meta_to_index(owner.list[i].slot_vaddr) == idx {
                    let i = choose|i: int| 0 <= i < owner.list.len()
                        && #[trigger] meta_to_index(owner.list[i].slot_vaddr) == idx;
                    owner.lemma_relate_region_shape(*regions);
                    owner.lemma_relate_region_at_index(*regions, i);
                    owner.lemma_relate_region_at_facts(*regions, i);
                }
            }
        let tracked slot_perm = if valid_frame_paddr(frame) {
            Some(*regions.slots.tracked_borrow(idx))
        } else {
            None
        };
        }
        let Ok(slot) = (#[verus_spec(with Tracked(slot_perm))]
        crate::mm::frame::meta::get_slot(frame)) else {
            return false;
        };

        let tracked slot_own = regions.slot_owners.tracked_borrow(idx);

        slot.in_list.load(Tracked(&slot_own.in_list_perm)) == #[verus_spec(with Tracked(owner))]
        self.lazy_get_id()
    }

    /// Gets a cursor at the specified frame if the frame is in the list.
    ///
    /// This method fails if the frame is not in the list.
    /// # Verified Properties
    /// ## Preconditions
    /// - The list must be well-formed, with the pointers to its links' metadata slots
    /// matching the tracked permission objects.
    /// - The list owner must match the list and region permissions, and its
    /// membership registry must be consistent with the region's `in_list` tags.
    /// - The list must already have a non-zero ID: `lazy_get_id` does not yet
    /// model freshness against the region's `in_list` tags for a fresh list.
    /// ## Postconditions
    /// - A cursor is returned exactly when the valid frame belongs to the list.
    /// Its owner has an in-range index matching the frame, and the cursor is
    /// well-formed with the region permissions.
    /// - The returned cursor and its tracked owner are either both present or both absent.
    /// ## Safety
    /// - `lazy_get_id` uses atomic memory accesses, so there are no data races.
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&MetaRegionOwners>,
            Tracked(owner): Tracked<&mut LinkedListOwner<M>>,
            -> cursor_owner: Tracked<Option<CursorOwner<M>>>,
        requires
            regions.inv(),
            old(self).wf_region(*old(owner), *regions),
            old(owner).relate_region(*regions),
            list_registry_ok(*regions, *old(owner)),
            old(owner).list_id != 0,
        ensures
            !valid_frame_paddr(frame) ==> r is None,
            r is Some == cursor_owner@ is Some,
            (r is Some) == (valid_frame_paddr(frame)
                && exists|i: int| 0 <= i < old(owner).list.len()
                    && #[trigger] meta_to_index(old(owner).list[i].slot_vaddr) == frame_to_index(frame)),
            r is None ==> {
                &&& *final(owner) == *old(owner)
                &&& *final(self) == *old(self)
                &&& final(self).wf_region(*final(owner), *regions)
                &&& final(owner).inv()
            },
            r matches Some(cursor) ==> (cursor_owner@ matches Some(co) ==> {
                &&& co.list_own == *old(owner)
                &&& 0 <= co.index < co.list_own.list.len()
                &&& meta_to_index(co.list_own.list[co.index].slot_vaddr) == frame_to_index(frame)
                &&& cursor.wf_region(co, *regions)
                &&& co.wf_with_region(*regions)
                &&& cursor.wf(co)
                &&& co.inv()
                &&& *cursor.list == *old(self)
                &&& *final(self) == *final(cursor.list)
            }),
    )]
    pub fn cursor_mut_at(&mut self, frame: Paddr) -> Option<CursorMut<'_, M>> {
        proof_decl! {
            owner.lemma_relate_region_implies_inv(*regions);
            let ghost idx = frame_to_index(frame);
            if valid_frame_paddr(frame) {
                regions.lemma_contains_valid_frame_paddr(frame);
            }

            let tracked slot_perm = if valid_frame_paddr(frame) {
                Some(*regions.slots.tracked_borrow(idx))
            } else {
                None
            };
        }
        let Ok(slot) = (#[verus_spec(with Tracked(slot_perm))]
        crate::mm::frame::meta::get_slot(frame)) else {
            return {
                proof_with!(|= Tracked(None));
                None
            };
        };

        let tracked slot_own = regions.slot_owners.tracked_borrow(idx);

        let contains = slot.in_list.load(Tracked(&slot_own.in_list_perm))
            == #[verus_spec(with Tracked(&*owner))]
        self.lazy_get_id();

        if contains {
            proof_decl!{
                let ghost index = choose|i: int| 0 <= i < owner.list.len()
                    && #[trigger] meta_to_index(owner.list[i].slot_vaddr) == frame_to_index(frame);
                owner.lemma_relate_region_at_index(*regions, index);
                owner.lemma_relate_region_at_facts(*regions, index);
                lemma_meta_region_inv_at(*regions, idx);
                let tracked list_owner = LinkedListOwner::tracked_take(owner);
                let tracked cursor_owner = CursorOwner::tracked_cursor_mut_at_owner(list_owner, index);
            }

            let meta_ptr = ReprPtr::<MetaSlotStorage, Link<M>>::from_pptr(
                PPtr::<MetaSlotStorage>::from_addr(frame_to_meta(frame)),
            );
            proof_with!(|= Tracked(Some(cursor_owner)));
            Some(CursorMut { list: self, current: Some(meta_ptr) })
        } else {
            proof_with!(|= Tracked(None));
            None
        }
    }

    /// Gets a cursor at the front that can mutate the linked list links.
    ///
    /// If the list is empty, the cursor points to the "ghost" non-element.
    /// # Verified Properties
    /// ## Safety
    /// This function is written in safe Rust and there is no undefined behavior.
    #[verus_spec(r =>
        ensures
            r.current == old(self).front,
            *r.list == *old(self),
            *final(self) == *final(r.list),
    )]
    pub fn cursor_front_mut(&mut self) -> CursorMut<'_, M> {
        let current = self.front;
        CursorMut { list: self, current }
    }

    /// Gets a cursor at the back that can mutate the linked list links.
    ///
    /// If the list is empty, the cursor points to the "ghost" non-element.
    /// # Verified Properties
    /// ## Safety
    /// This function is written in safe Rust and there is no undefined behavior.
    #[verus_spec(r =>
        ensures
            r.current == old(self).back,
            *r.list == *old(self),
            *final(self) == *final(r.list),
    )]
    pub fn cursor_back_mut(&mut self) -> CursorMut<'_, M> {
        let current = self.back;
        CursorMut { list: self, current }
    }

    /// Gets a cursor at the "ghost" non-element that can mutate the linked list links.
    /// # Verified Properties
    /// ## Safety
    /// This function is written in safe Rust and there is no undefined behavior.
    #[verus_spec(r =>
        ensures
            r.current.is_none(),
            *r.list == *old(self),
            *final(self) == *final(r.list),
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
        proof {
            owner.list_own.lemma_relate_region_shape(*regions);
            if self.current is Some {
                owner.list_own.lemma_relate_region_at_index(*regions, owner.index);
                owner.list_own.lemma_relate_region_at_facts(*regions, owner.index);
            }
            if owner.index < owner.length() - 1 {
                owner.list_own.lemma_relate_region_at_index(*regions, owner.index + 1);
                owner.list_own.lemma_relate_region_at_facts(*regions, owner.index + 1);
            }
        }

        self.current = match self.current {
            // SAFETY: The cursor is pointing to a valid element.
            Some(current) => {
                proof_decl!{
                    let ghost idx = meta_to_index(current.addr());
                    let tracked points_to = regions.slots.tracked_borrow(idx);
                    let tracked metadata_perms =
                        owner.list_own.metadata_perms.tracked_borrow(owner.index);
                    let tracked repr_perm = owner.list_own.repr_perms.tracked_borrow(owner.index);
                }
                proof {
                    assert(regions.contains(idx));
                }
                let link = borrow_meta(
                    current,
                    Tracked(points_to),
                    Tracked(metadata_perms),
                    Tracked(repr_perm),
                );
                link.next
            },
            None => self.list.front,
        };

        proof {
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
        proof {
            owner.list_own.lemma_relate_region_shape(*regions);
            if self.current is Some {
                owner.list_own.lemma_relate_region_at_index(*regions, owner.index);
                owner.list_own.lemma_relate_region_at_facts(*regions, owner.index);
            }
            if 0 < owner.index {
                owner.list_own.lemma_relate_region_at_index(*regions, owner.index - 1);
                owner.list_own.lemma_relate_region_at_facts(*regions, owner.index - 1);
            }
        }

        self.current = match self.current {
            // SAFETY: The cursor is pointing to a valid element.
            Some(current) => {
                proof_decl!{
                    let ghost idx = meta_to_index(current.addr());
                    let tracked points_to = regions.slots.tracked_borrow(idx);
                    let tracked metadata_perms =
                        owner.list_own.metadata_perms.tracked_borrow(owner.index);
                    let tracked repr_perm = owner.list_own.repr_perms.tracked_borrow(owner.index);
                }
                proof {
                    assert(regions.contains(idx));
                }

                let link = borrow_meta(
                    current,
                    Tracked(points_to),
                    Tracked(metadata_perms),
                    Tracked(repr_perm),
                );
                link.prev
            },
            None => self.list.back,
        };

        proof {
            if owner@.list_model.list.len() > 0 {
                if owner@.fore.len() > 0 {
                    assert(owner.move_prev_owner_spec()@.fore == owner@.move_prev_spec().fore);
                    assert(owner.move_prev_owner_spec()@.rear == owner@.move_prev_spec().rear);
                    if owner@.rear.len() > 0 {
                        owner.list_own.lemma_relate_region_at_index(*regions, owner.index);
                        owner.list_own.lemma_relate_region_at_facts(*regions, owner.index);
                    }
                } else {
                    owner.list_own.lemma_relate_region_at_index(*regions, owner.index);
                    owner.list_own.lemma_relate_region_at_facts(*regions, owner.index);
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
                    owner.list_own.lemma_relate_region_shape(*regions);
                    owner.list_own.lemma_relate_region_at_index(*regions, owner.index);
                    owner.list_own.lemma_relate_region_at_facts(*regions, owner.index);
                }
                let ghost idx = meta_to_index(current.addr());
                proof {
                    assert(regions.contains(idx));
                }
                let tracked points_to = regions.slots.tracked_borrow(idx);
                let tracked repr_perm = owner.list_own.repr_perms.tracked_borrow_mut(owner.index);
                let tracked metadata_perms = owner.list_own.metadata_perms.tracked_borrow_mut(
                    owner.index,
                );
                Some(
                    &mut borrow_meta_mut(
                        current,
                        Tracked(points_to),
                        Tracked(metadata_perms),
                        Tracked(repr_perm),
                    ).meta,
                )
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
    /// matching the tracked permission objects.
    /// ## Postconditions
    /// At an element, returns the frame, transfers its owner through the tracked output,
    /// and moves the cursor to the next frame. At the ghost non-element, returns `None`
    /// without changing the cursor, list owner, or region permissions.
    /// ## Safety
    /// This function calls `from_raw` on the frame, but we guarantee that the frame is forgotten
    /// if it is in the list. So, double-free will not occur. All loads and stores are through track
    /// tracked permissions, so there are no illegal memory accesses. No data races are possible.
    #[verus_spec(res =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(owner): Tracked<&mut CursorOwner<M>>,
            -> returned_owner: Tracked<Option<UniqueFrameOwner<Link<M>>>>,

        requires
            old(self).wf_region(*old(owner), *old(regions)),
            old(owner).wf_with_region(*old(regions)),
            old(regions).inv(),
        ensures
            (res is Some) == (returned_owner@ is Some),
            old(owner).length() == 0 ==> res.is_none(),
            old(self).current.is_some() ==> res.is_some(),
            final(owner).wf_with_region(*final(regions)),
            final(self).wf_region(*final(owner), *final(regions)),
            *final(final(self).list) == *final(old(self).list),
            final(regions).inv(),
            final(owner).list_own.list_id == old(owner).list_own.list_id,
            res is None ==> {
                &&& *final(self) == *old(self)
                &&& *final(owner) == *old(owner)
                &&& *final(regions) == *old(regions)
            },
            res matches Some(unique) ==> {
                let paddr = meta_to_frame(old(self).current->0.addr());
                let idx = frame_to_index(paddr);
                let metadata_perm = unique.tracked_metadata_perm@->0;
                &&& final(owner)@ == old(owner)@.remove()
                &&& final(owner).index == old(owner).index
                &&& final(owner).list_own.list == old(owner).list_own.list.remove(old(owner).index)
                &&& final(regions).slots.dom() == old(regions).slots.dom()
                &&& final(regions).ref_count(idx) == REF_COUNT_UNIQUE
                &&& final(regions).slot_owners[idx].in_list_perm.value() == 0
                &&& metadata_perm.storage_perm.is_init()
                &&& metadata_perm.vtable_ptr_perm.is_init()
                &&& final(regions).slot_owners[idx].slot_vaddr == index_to_meta(idx)
                &&& final(regions).slot_owners[idx].paths_in_pt == old(regions).slot_owners[idx].paths_in_pt
                &&& *final(regions) == old(regions).insert_slot_owner(
                    paddr, final(regions).slot_owners[idx],
                )
                &&& unique.inv()
                &&& unique.ptr.addr() == old(self).current->0.addr()
                &&& returned_owner@ matches Some(unique_owner) ==> {
                    &&& unique_owner.meta_own@ == old(owner).list_own.list[old(owner).index]@
                    &&& unique.frame_link_inv(unique_owner, *final(regions))
                    &&& unique.wf(unique_owner)
                    &&& unique_owner.inv()
                    &&& unique.wf_with_region(unique_owner, *final(regions))
                    &&& unique_owner.slot_index == idx
                }
            },
    )]
    #[verifier::spinoff_prover]
    #[verifier::rlimit(250)]
    pub fn take_current(&mut self) -> Option<UniqueFrame<Link<M>>> {
        hide(MetaSlotOwner::storage_perm);
        hide(MetaSlotOwner::vtable_ptr_perm);
        hide(<MetaRegionOwners as Inv>::inv);
        let ghost owner0 = *owner;
        let ghost regions0 = *regions;

        /* Ghost returns need an explicit owner on the early-return path.
         * Origin Rust: let current = self.current?;
         */
        let current = match self.current {
            Some(current) => current,
            None => return {
                proof_with!(|= Tracked(None));
                None
            },
        };

        proof {
            owner.list_own.lemma_relate_region_shape(*regions);
            owner.list_own.lemma_relate_region_at_index(*regions, owner.index);
            owner.list_own.lemma_relate_region_at_facts(*regions, owner.index);
            if owner.index > 0 {
                owner.list_own.lemma_relate_region_at_index(*regions, owner.index - 1);
                owner.list_own.lemma_relate_region_at_facts(*regions, owner.index - 1);
            }
            if owner.index < owner.list_own.list.len() - 1 {
                owner.list_own.lemma_relate_region_at_index(*regions, owner.index + 1);
                owner.list_own.lemma_relate_region_at_facts(*regions, owner.index + 1);
            }
        }

        let meta_ptr = current.addr();
        let paddr = meta_to_frame(meta_ptr);
        let ghost idx = frame_to_index(paddr);

        proof {
            lemma_meta_region_inv_at(regions0, idx);
        }

        let tracked mut cur_own = owner.list_own.list.tracked_remove(owner.index);
        let tracked cur_repr_perm = owner.list_own.repr_perms.tracked_remove(owner.index);
        let tracked cur_metadata_perm = owner.list_own.metadata_perms.tracked_remove(owner.index);

        proof_decl! {
            let tracked mut frame_own: UniqueFrameOwner<Link<M>>;
        }
        let mut frame = unsafe {
            // SAFETY: The frame was forgotten when inserted into the linked list.
            #[verus_spec(with
                Tracked(regions.tracked_borrow_slot(paddr)),
                Tracked(cur_own),
                Tracked(cur_repr_perm),
                Tracked(cur_metadata_perm) => Tracked(frame_own)
            )]
            UniqueFrame::<Link<M>>::from_raw(paddr)
        };

        proof {
            assert(regions.slots.dom() == regions0.slots.dom());
        }

        let next_ptr = (#[verus_spec(with Tracked(&frame_own))]
        frame.meta()).next;
        let prev_ptr = (#[verus_spec(with Tracked(&frame_own))]
        frame.meta()).prev;

        if let Some(prev) = prev_ptr {
            let ghost prev_idx = meta_to_index(owner.list_own.list[owner.index - 1].slot_vaddr);
            proof {
                lemma_meta_region_inv_at(*regions, prev_idx);
            }
            let tracked prev_points_to = regions.slots.tracked_borrow(prev_idx);
            let tracked prev_repr_perm = owner.list_own.repr_perms.tracked_borrow_mut(
                owner.index - 1,
            );
            let tracked prev_metadata_perm = owner.list_own.metadata_perms.tracked_borrow_mut(
                owner.index - 1,
            );
            let prev_meta = borrow_meta_mut(
                prev,
                Tracked(prev_points_to),
                Tracked(prev_metadata_perm),
                Tracked(prev_repr_perm),
            );
            prev_meta.next = next_ptr;

        } else {
            self.list.front = next_ptr;
        }

        if let Some(next) = next_ptr {
            let ghost next_idx = meta_to_index(owner.list_own.list[owner.index].slot_vaddr);
            proof {
                lemma_meta_region_inv_at(*regions, next_idx);
            }
            let tracked next_points_to = regions.slots.tracked_borrow(next_idx);
            let tracked next_repr_perm = owner.list_own.repr_perms.tracked_borrow_mut(owner.index);
            let tracked next_metadata_perm = owner.list_own.metadata_perms.tracked_borrow_mut(
                owner.index,
            );
            let next_meta = borrow_meta_mut(
                next,
                Tracked(next_points_to),
                Tracked(next_metadata_perm),
                Tracked(next_repr_perm),
            );
            next_meta.prev = prev_ptr;

            self.current = Some(next);
        } else {
            self.list.back = prev_ptr;

            self.current = None;
        }

        (#[verus_spec(with Tracked(&mut frame_own))]
        frame.meta_mut()).next = None;
        (#[verus_spec(with Tracked(&mut frame_own))]
        frame.meta_mut()).prev = None;

        let tracked mut frame_so = regions.slot_owners.tracked_borrow_mut(idx);
        let tracked mut fip = &mut frame_so;
        let slot = frame.slot();
        slot.in_list.store(Tracked(&mut fip.in_list_perm), 0);
        proof {
            assert(regions.inv()) by {
                reveal(MetaSlotOwner::storage_perm);
                reveal(MetaSlotOwner::vtable_ptr_perm);
                reveal(<MetaRegionOwners as Inv>::inv);
            };
            assert(regions.slots.dom() == regions0.slots.dom());
        }

        self.list.size -= 1;

        proof {
            owner0.remove_owner_spec_implies_model_spec(*owner);
            let ghost oldl = owner0.list_own;
            let ghost nn = owner0.index as int;
            assert forall|p: int|
                #![trigger meta_to_index(oldl.list[p].slot_vaddr)]
                (0 <= p < oldl.list.len() && p != nn) implies ({
                let i = meta_to_index(oldl.list[p].slot_vaddr);
                let np = if p < nn {
                    p
                } else {
                    p - 1
                };
                let fp = owner.list_own.meta_value_at(*regions, np);
                &&& regions.contains(i)
                &&& regions.slots[i].addr() == oldl.list[p].slot_vaddr
                &&& regions.slots[i].pptr() == regions0.slots[i].pptr()
                &&& regions.ref_count(i) == REF_COUNT_UNIQUE
                &&& regions.slot_owners[i].metadata_perm.is_resource_vacant()
                &&& owner.list_own.metadata_perms[np].storage_perm.id()
                    == regions.slots[i].value().storage.id()
                &&& owner.list_own.metadata_perms[np].vtable_ptr_perm.pptr()
                    == regions.slots[i].value().vtable_ptr
                &&& owner.list_own.metadata_perms[np].vtable_ptr_perm.is_init()
                &&& regions.slot_owners[i].usage is Frame
                &&& regions.slot_owners[i].in_list_perm.value() == owner.list_own.list_id
                &&& owner.list_own.meta_wf_at(*regions, np)
                &&& regions.slots[i].addr() % META_SLOT_SIZE == 0
                &&& FRAME_METADATA_RANGE.start <= regions.slots[i].addr()
                    < FRAME_METADATA_RANGE.start + MAX_NR_PAGES * META_SLOT_SIZE
                &&& (p == nn - 1 ==> fp.next == oldl.meta_value_at(regions0, nn).next)
                &&& (p != nn - 1 ==> fp.next == oldl.meta_value_at(regions0, p).next)
                &&& (p == nn + 1 ==> fp.prev == oldl.meta_value_at(regions0, nn).prev)
                &&& (p != nn + 1 ==> fp.prev == oldl.meta_value_at(regions0, p).prev)
            }) by {
                let i = meta_to_index(oldl.list[p].slot_vaddr);
                let np = if p < nn {
                    p
                } else {
                    p - 1
                };
                let fp = owner.list_own.meta_value_at(*regions, np);
                oldl.lemma_relate_region_at_index(regions0, p);
                oldl.lemma_relate_region_at_index(regions0, nn);
                oldl.lemma_relate_region_indices_distinct(regions0, p, nn);
                oldl.lemma_relate_region_at_facts(regions0, p);
                oldl.lemma_relate_region_at_facts(regions0, nn);
                assert(regions.contains(i));
            }
            LinkedListOwner::lemma_pop_preserves_relate_region(
                oldl,
                regions0,
                owner.list_own,
                *regions,
                nn,
            );
        }
        proof_with!(|= Tracked(Some(frame_own)));
        Some(frame)
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
    #[verifier::rlimit(200)]
    pub fn insert_before(&mut self, mut frame: UniqueFrame<Link<M>>)
        requires
            old(self).wf_region(*old(owner), *old(regions)),
            old(owner).wf_with_region(*old(regions)),
            old(regions).inv(),
            frame.inv(),
            old(frame_own).inv(),
            frame.wf_with_region(*old(frame_own), *old(regions)),
            frame.frame_link_inv(*old(frame_own), *old(regions)),
        ensures
            final(owner).wf_with_region(*final(regions)),
            final(self).wf_region(*final(owner), *final(regions)),
            *final(final(self).list) == *final(old(self).list),
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
            final(frame_own).meta_own.slot_vaddr == old(frame_own).meta_own.slot_vaddr,
            final(frame_own).meta_own.in_list == final(owner).list_own.list_id,
            final(owner)@ == old(owner)@.insert(final(frame_own).meta_own@),
    {
        hide(<MetaRegionOwners as Inv>::inv);
        let ghost owner0 = *owner;
        let ghost regions0 = *regions;
        let ghost nn = owner.index as int;

        proof {
            assert(owner0.list_own.repr_perms.len() == owner0.list_own.list.len()) by {
                reveal(LinkedListOwner::relate_region);
            };
            assert(owner0.list_own.metadata_perms.len() == owner0.list_own.list.len()) by {
                reveal(LinkedListOwner::relate_region);
            };
            assert(owner0.list_own.list.len() > 0 ==> owner0.list_own.list_id != 0) by {
                reveal(LinkedListOwner::relate_region);
            };
            lemma_meta_region_inv_at(regions0, frame_own.slot_index);
            owner0.list_own.lemma_length_lt_usize_max(regions0);
            if nn > 0 {
                assert(owner0.list_own.relate_region_at(regions0, nn - 1)) by {
                    reveal(LinkedListOwner::relate_region);
                };
                owner.list_own.lemma_relate_region_at_facts(*regions, nn - 1);
                lemma_meta_region_inv_at(
                    regions0,
                    meta_to_index(owner0.list_own.list[nn - 1].slot_vaddr),
                );
            }
            if nn < owner.list_own.list.len() {
                assert(owner0.list_own.relate_region_at(regions0, nn)) by {
                    reveal(LinkedListOwner::relate_region);
                };
                owner.list_own.lemma_relate_region_at_facts(*regions, nn);
                lemma_meta_region_inv_at(
                    regions0,
                    meta_to_index(owner0.list_own.list[nn].slot_vaddr),
                );
            }
            assert forall|p: int|
                #![trigger
                    regions0.slot_owners[meta_to_index(owner0.list_own.list[p].slot_vaddr)]]
                0 <= p < owner0.list_own.list.len() implies frame_own.slot_index != meta_to_index(
                owner0.list_own.list[p].slot_vaddr,
            ) by {
                lemma_insert_before_slot_distinct(
                    owner0.list_own,
                    regions0,
                    frame_own.slot_index,
                    nn,
                );
            }
        }

        let frame_ptr = ReprPtr::<MetaSlotStorage, Link<M>>::from_pptr(
            PPtr::<MetaSlotStorage>::from_addr(frame.ptr.addr()),
        );

        if let Some(current) = self.current {
            proof_decl!{
                let ghost idx = meta_to_index(current.addr());
                let tracked points_to = regions.slots.tracked_borrow(idx);
                let tracked metadata_perms =
                    owner.list_own.metadata_perms.tracked_borrow(owner.index);
                let tracked repr_perm = owner.list_own.repr_perms.tracked_borrow(owner.index);
            }

            // Read current's prev pointer.
            let opt_prev_link: Option<ReprPtr<MetaSlotStorage, Link<M>>> = borrow_meta(
                current,
                Tracked(points_to),
                Tracked(metadata_perms),
                Tracked(repr_perm),
            ).prev;

            if let Some(prev_link) = opt_prev_link {
                let prev = prev_link;

                (#[verus_spec(with Tracked(frame_own))]
                frame.meta_mut()).prev = Some(prev_link);
                (#[verus_spec(with Tracked(frame_own))]
                frame.meta_mut()).next = Some(current);

                let ghost prev_idx = meta_to_index(owner.list_own.list[nn - 1].slot_vaddr);
                proof {
                    assert(prev_idx != idx) by {
                        reveal(LinkedListOwner::relate_region);
                    };
                }
                let tracked prev_points_to = regions.slots.tracked_borrow(prev_idx);
                let tracked prev_repr_perm = owner.list_own.repr_perms.tracked_borrow_mut(nn - 1);
                let tracked prev_metadata_perm = owner.list_own.metadata_perms.tracked_borrow_mut(
                    nn - 1,
                );
                let prev_meta = borrow_meta_mut(
                    prev,
                    Tracked(prev_points_to),
                    Tracked(prev_metadata_perm),
                    Tracked(prev_repr_perm),
                );
                prev_meta.next = Some(frame_ptr);

                let ghost current_idx = meta_to_index(owner.list_own.list[nn].slot_vaddr);
                let tracked current_points_to = regions.slots.tracked_borrow(current_idx);
                let tracked current_repr_perm = owner.list_own.repr_perms.tracked_borrow_mut(nn);
                let tracked current_metadata_perm =
                    owner.list_own.metadata_perms.tracked_borrow_mut(nn);
                let current_meta = borrow_meta_mut(
                    current,
                    Tracked(current_points_to),
                    Tracked(current_metadata_perm),
                    Tracked(current_repr_perm),
                );
                current_meta.prev = Some(frame_ptr);
            } else {
                (#[verus_spec(with Tracked(frame_own))]
                frame.meta_mut()).next = Some(current);

                let ghost current_idx = meta_to_index(owner.list_own.list[nn].slot_vaddr);
                let tracked current_points_to = regions.slots.tracked_borrow(current_idx);
                let tracked current_repr_perm = owner.list_own.repr_perms.tracked_borrow_mut(nn);
                let tracked current_metadata_perm =
                    owner.list_own.metadata_perms.tracked_borrow_mut(nn);
                let current_meta = borrow_meta_mut(
                    current,
                    Tracked(current_points_to),
                    Tracked(current_metadata_perm),
                    Tracked(current_repr_perm),
                );
                current_meta.prev = Some(frame_ptr);
                self.list.front = Some(frame_ptr);
            }
        } else {
            if let Some(back) = self.list.back {
                (#[verus_spec(with Tracked(frame_own))]
                frame.meta_mut()).prev = Some(back);

                let ghost back_idx = meta_to_index(owner.list_own.list[nn - 1].slot_vaddr);
                proof {
                    assert(0 <= nn - 1 < owner.list_own.repr_perms.len());
                }
                let tracked back_points_to = regions.slots.tracked_borrow(back_idx);
                let tracked back_repr_perm = owner.list_own.repr_perms.tracked_borrow_mut(nn - 1);
                let tracked back_metadata_perm = owner.list_own.metadata_perms.tracked_borrow_mut(
                    nn - 1,
                );
                let back_meta = borrow_meta_mut(
                    back,
                    Tracked(back_points_to),
                    Tracked(back_metadata_perm),
                    Tracked(back_repr_perm),
                );
                back_meta.next = Some(frame_ptr);
                self.list.back = Some(frame_ptr);
            } else {
                // EMPTY list: just point both ends at the inserted frame.
                self.list.front = Some(frame_ptr);
                self.list.back = Some(frame_ptr);
            }
        }

        #[verus_spec(with Tracked(&owner.list_own))]
        let list_id = self.list.lazy_get_id();

        proof {
            assert(owner0.list_own.list.len() > 0 ==> list_id == owner0.list_own.list_id);
        }
        let tracked mut frame_so = regions.slot_owners.tracked_borrow_mut(frame_own.slot_index);
        let tracked mut fip = &mut frame_so;
        let slot = frame.slot();
        slot.in_list.store(Tracked(&mut fip.in_list_perm), list_id);
        proof {
            assert(regions.inv()) by {
                reveal(<MetaRegionOwners as Inv>::inv);
            };
            assert(frame.wf_with_region(*frame_own, *regions));
        }

        #[verus_spec(with
            => Tracked(frame_metadata_perm)
        )]
        let _ = frame.into_raw();

        self.list.size += 1;

        proof {
            let tracked frame_repr_perm = frame_own.repr_perm.tracked_take();
            let ghost insert_index = owner.index;
            let ghost slot_vaddr = frame_own.meta_own.slot_vaddr;
            let tracked list_entry = LinkOwner { slot_vaddr, in_list: list_id };
            owner.list_own.list.tracked_insert(insert_index, list_entry);
            owner.list_own.repr_perms.tracked_insert(insert_index, frame_repr_perm);
            owner.list_own.metadata_perms.tracked_insert(insert_index, frame_metadata_perm);
            owner.list_own.list_id = list_id;
            owner.index = insert_index + 1;
            frame_own.meta_own = LinkOwner { slot_vaddr, in_list: list_id };
            let oldl = owner0.list_own;
            let nn = owner0.index as int;
            let flink = frame_own.meta_own;
            let ins = frame_own.slot_index;

            assert(owner.list_own.relate_region(*regions)) by {
                assert forall|p: int|
                    #![trigger
                        owner.list_own.insert_old_slot_post_at(
                            *regions,
                            oldl,
                            regions0,
                            nn,
                            flink,
                            p,
                        )]
                    (0 <= p < oldl.list.len()) implies owner.list_own.insert_old_slot_post_at(
                    *regions,
                    oldl,
                    regions0,
                    nn,
                    flink,
                    p,
                ) by {
                    reveal(LinkedListOwner::insert_old_slot_post_at);
                    assert(oldl.relate_region_at(regions0, p)) by {
                        reveal(LinkedListOwner::relate_region);
                    };
                    oldl.lemma_relate_region_at_facts(regions0, p);
                    if nn - 1 >= 0 && nn - 1 < oldl.list.len() && p != nn - 1 {
                        assert(meta_to_index(oldl.list[p].slot_vaddr) != meta_to_index(
                            oldl.list[nn - 1].slot_vaddr,
                        )) by {
                            reveal(LinkedListOwner::relate_region);
                        };
                    }
                    if nn >= 0 && nn < oldl.list.len() && p != nn {
                        assert(meta_to_index(oldl.list[p].slot_vaddr) != meta_to_index(
                            oldl.list[nn].slot_vaddr,
                        )) by {
                            reveal(LinkedListOwner::relate_region);
                        };
                    }
                }

                LinkedListOwner::lemma_insert_preserves_relate_region(
                    oldl,
                    regions0,
                    owner.list_own,
                    *regions,
                    nn,
                    flink,
                );
            };

            owner0.insert_owner_spec_implies_model_spec(flink, *owner);
        }
    }

    /// Provides a reference to the linked list.
    pub fn as_list(&self) -> &LinkedList<M> {
        self.list
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> LinkedList<M> {
    /// Releases every frame owned by the list.
    ///
    /// # Verified Properties
    /// Requires matching list ownership and region permissions, with every list
    /// frame uniquely owned and absent from page tables.
    /// Empties the list owner, preserves the region invariant, and leaves unrelated
    /// frames' usage, metadata addresses, and page-table ownership unchanged.
    #[verifier::spinoff_prover]
    pub fn drop(
        mut self,
        Tracked(owner): Tracked<&mut LinkedListOwner<M>>,
        Tracked(regions): Tracked<&mut MetaRegionOwners>,
    )
        requires
            self.wf(*old(owner)),
            old(owner).inv(),
            old(regions).inv(),
            forall|i: int|
                #![trigger old(owner).list[i]]
                0 <= i < old(owner).list.len() ==> {
                    let idx = meta_to_index(old(owner).list[i].slot_vaddr);
                    &&& old(regions).contains(idx)
                    &&& old(regions).ref_count(idx) == REF_COUNT_UNIQUE
                    &&& old(regions).slot_owners[idx].paths_in_pt.is_empty()
                },
            forall|i: int, j: int|
                #![trigger old(owner).list[i], old(owner).list[j]]
                0 <= i < j < old(owner).list.len() ==> meta_to_index(old(owner).list[i].slot_vaddr)
                    != meta_to_index(old(owner).list[j].slot_vaddr),
            old(owner).relate_region(*old(regions)),
        ensures
            final(owner).list.len() == 0,
            forall|idx: int|
                #![trigger final(regions).slot_owners[idx]]
                (forall|i: int|
                    #![trigger old(owner).list[i]]
                    0 <= i < old(owner).list.len() ==> idx != meta_to_index(
                        old(owner).list[i].slot_vaddr,
                    )) ==> {
                    &&& final(regions).slot_owners[idx].usage == old(regions).slot_owners[idx].usage
                    &&& final(regions).slot_owners[idx].slot_vaddr == old(
                        regions,
                    ).slot_owners[idx].slot_vaddr
                    &&& final(regions).slot_owners[idx].paths_in_pt == old(
                        regions,
                    ).slot_owners[idx].paths_in_pt
                },
            final(regions).slots.dom() =~= old(regions).slots.dom(),
            final(regions).inv(),
    {
        proof_decl! {
            let tracked mut list_own: LinkedListOwner<M>;
        }
        let ghost original_list = owner.list;
        let ghost original_list_id = owner.list_id;
        let ghost n = original_list.len();
        let ghost original_regions = *regions;
        proof {
            list_own = LinkedListOwner::<M>::tracked_take(owner);
        }

        let tracked mut cursor_own = CursorOwner::tracked_front_owner(list_own);
        let mut cursor = self.cursor_front_mut();

        proof {
            if n > 0 {
                cursor_own.list_own.lemma_relate_region_at_index(*regions, 0);
                cursor_own.list_own.lemma_relate_region_at_index(*regions, n - 1);
                cursor_own.list_own.lemma_relate_region_at_facts(*regions, 0);
                cursor_own.list_own.lemma_relate_region_at_facts(*regions, n - 1);
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
                // slots values inside the original_list.
                forall|idx: int|
                    #![trigger regions.slot_owners[idx]]
                    (forall|j: int|
                        #![trigger original_list[j]]
                        0 <= j < n ==> idx != meta_to_index(original_list[j].slot_vaddr)) ==> {
                        &&& regions.slot_owners[idx].usage
                            == original_regions.slot_owners[idx].usage
                        &&& regions.slot_owners[idx].slot_vaddr
                            == original_regions.slot_owners[idx].slot_vaddr
                        &&& regions.slot_owners[idx].paths_in_pt
                            == original_regions.slot_owners[idx].paths_in_pt
                    },
                regions.slots.dom() == original_regions.slots.dom(),
                forall|j: int|
                    #![trigger original_list[j]]
                    k <= j < n ==> {
                        let idx = meta_to_index(original_list[j].slot_vaddr);
                        &&& regions.slot_owners[idx].paths_in_pt
                            == original_regions.slot_owners[idx].paths_in_pt
                    },
                // Each remaining element's slot is in slot_owners
                forall|j: int|
                    #![trigger original_list[j]]
                    k <= j < n ==> regions.contains(meta_to_index(original_list[j].slot_vaddr)),
                forall|i: int, j: int|
                    #![trigger original_list[i], original_list[j]]
                    0 <= i < j < n ==> meta_to_index(original_list[i].slot_vaddr) != meta_to_index(
                        original_list[j].slot_vaddr,
                    ),
                forall|j: int|
                    #![trigger original_list[j]]
                    0 <= j < n ==> {
                        let idx = meta_to_index(original_list[j].slot_vaddr);
                        &&& original_regions.contains(idx)
                        &&& original_regions.slot_owners[idx].paths_in_pt.is_empty()
                        &&& original_regions.ref_count(idx) == REF_COUNT_UNIQUE
                    },
            ensures
                k == n,
                cursor_own.list_own.list.len() == 0,
            decreases n - k,
        {
            #[verus_spec(with Tracked(regions), Tracked(&mut cursor_own) => Tracked(returned_owner))]
            let entry = cursor.take_current();

            if let Some(current) = entry {
                let mut frame = current;
                let tracked frame_own = returned_owner.tracked_unwrap();
                let ghost regions_pre_drop = *regions;

                // Drop the frame, returning its slot to regions
                #[verus_spec(with Tracked(frame_own), Tracked(regions))]
                frame.drop();

                proof {
                    assert forall|i: int|
                        #![trigger cursor_own.list_own.list[i]]
                        0 <= i < cursor_own.list_own.list.len() implies ({
                        let idx = meta_to_index(cursor_own.list_own.list[i].slot_vaddr);
                        &&& regions.contains(idx)
                        &&& regions.slot_owners[idx] == regions_pre_drop.slot_owners[idx]
                    }) by {
                        let idx = meta_to_index(cursor_own.list_own.list[i].slot_vaddr);
                        assert(cursor_own.list_own.list[i] == original_list[i + k + 1]);

                        cursor_own.list_own.lemma_relate_region_at_index(regions_pre_drop, i);
                        cursor_own.list_own.lemma_relate_region_at_facts(regions_pre_drop, i);
                    };
                    cursor_own.list_own.lemma_relate_region_preserved_external_change(
                        regions_pre_drop,
                        *regions,
                    );

                    assert forall|j: int|
                        #![trigger cursor_own.list_own.list[j]]
                        0 <= j < n - k - 1 implies cursor_own.list_own.list[j] == original_list[j
                        + k + 1] by {};

                    k = k + 1;
                }
            } else {
                break;
            }
        }

        // Restore the list owner from the cursor's final (empty) list.
        proof {
            let tracked mut final_list_own = cursor_own.list_own;
            vstd::modes::tracked_swap(owner, &mut final_list_own);
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
    pub next: Option<ReprPtr<MetaSlotStorage, Link<M>>>,
    pub prev: Option<ReprPtr<MetaSlotStorage, Link<M>>>,
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
        regions: MetaRegionOwners,
        vm_io_owner: crate::specs::mm::io::VmIoOwner,
    ) -> bool {
        self.meta.on_drop_pre(reader, regions, vm_io_owner)
    }

    fn on_drop(
        &mut self,
        reader: &mut crate::mm::VmReader<crate::mm::Infallible>,
        regions: Tracked<&mut MetaRegionOwners>,
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
