// SPDX-License-Identifier: MPL-2.0
//! This module defines page table node abstractions and the handle.
//!
//! The page table node is also frequently referred to as a page table in many architectural
//! documentations. It is essentially a page that contains page table entries (PTEs) that map
//! to child page tables nodes or mapped pages.
//!
//! This module leverages the page metadata to manage the page table pages, which makes it
//! easier to provide the following guarantees:
//!
//! The page table node is not freed when it is still in use by:
//!    - a parent page table node,
//!    - or a handle to a page table node,
//!    - or a processor.
//!
//! This is implemented by using a reference counter in the page metadata. If the above
//! conditions are not met, the page table node is ensured to be freed upon dropping the last
//! reference.
//!
//! One can acquire exclusive access to a page table node using merely the physical address of
//! the page table node. This is implemented by a lock in the page metadata. Here the
//! exclusiveness is only ensured for kernel code, and the processor's MMU is able to access the
//! page table node while a lock is held. So the modification to the PTEs should be done after
//! the initialization of the entity that the PTE points to. This is taken care in this module.
//!
mod child;
mod entry;

#[path = "../../../../specs/mm/page_table/node/child.rs"]
mod child_specs;
#[path = "../../../../specs/mm/page_table/node/entry.rs"]
mod entry_specs;

pub use crate::specs::mm::page_table::node::{entry_owners::*, owners::*};
pub use child::*;
pub use entry::*;

use vstd::cell::pcell_maybe_uninit;
use vstd::prelude::*;
use vstd::simple_pptr::PPtr;

use vstd::atomic::PAtomicU8;
use vstd_extra::array_ptr;
use vstd_extra::cast_ptr::*;
use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;

use crate::mm::frame::{
    allocator::FrameAllocOptions,
    meta::{
        META_SLOT_SIZE, MetaSlot, REF_COUNT_MAX, REF_COUNT_UNUSED,
        mapping::{frame_to_meta, meta_to_frame},
    },
};

use crate::mm::page_table::*;
use crate::mm::{Paddr, Vaddr};
use crate::specs::mm::{
    frame::{
        mapping::{frame_to_index, lemma_frame_to_index_injective, meta_to_index},
        meta_owners::{
            FracMetadataPerm, MetaSlotOwner, MetadataPerm, typed_meta_value, typed_meta_wf,
        },
        meta_region_owners::MetaRegionOwners,
    },
    page_table::node::owners::*,
};

use core::{marker::PhantomData, ops::Deref, sync::atomic::Ordering};

use super::{PageTableConfig, PageTableEntryTrait, nr_subpage_per_huge};

use crate::{
    mm::{
        PagingConstsTrait,
        PagingLevel,
        //        FrameAllocOptions, Infallible,
        //        VmReader,
        frame::{Frame, FrameRef, meta::AnyFrameMeta},
        paddr_to_vaddr,
        page_table::{load_pte, store_pte},
    },
    specs::task::InAtomicMode,
};

verus! {

/// The metadata of any kinds of page table pages.
/// Make sure the the generic parameters don't effect the memory layout.
pub struct PageTablePageMeta<C: PageTableConfig> {
    /// The number of valid PTEs. It is mutable if the lock is held.
    pub nr_children: pcell_maybe_uninit::PCell<u16>,
    /// If the page table is detached from its parent.
    ///
    /// A page table can be detached from its parent while still being accessed,
    /// since we use a RCU scheme to recycle page tables. If this flag is set,
    /// it means that the parent is recycling the page table.
    pub stray: pcell_maybe_uninit::PCell<bool>,
    /// The level of the page table page. A page table page cannot be
    /// referenced by page tables of different levels.
    pub level: PagingLevel,
    /// The lock for the page table page.
    pub lock: PAtomicU8,
    pub _phantom: core::marker::PhantomData<C>,
}

/// A smart pointer to a page table node.
///
/// This smart pointer is an owner of a page table node. Thus creating and
/// dropping it will affect the reference count of the page table node. If
/// dropped it as the last reference, the page table node and subsequent
/// children will be freed.
///
/// [`PageTableNode`] is read-only. To modify the page table node, lock and use
/// [`PageTableGuard`].
pub type PageTableNode<C> = Frame<PageTablePageMeta<C>>;

unsafe impl<C: PageTableConfig> AnyFrameMeta for PageTablePageMeta<C> {
    /// Caller invariants the PT-node `on_drop` body relies on:
    /// - Reader well-formedness + `vm_io_owner` matching + read view
    ///   initialized + at least `PAGE_SIZE` bytes remaining for the
    ///   PT-node walk.
    /// - Global region table invariant.
    /// - Embedding ([`child_perms_embedding`]): for every paddr in
    ///   `child_perms.dom()`, the slot and perm match `from_raw` /
    ///   `VerifiedDrop::drop`'s expected shape.
    /// - Walk coverage ([`walk_coverage_from_view`]): for every present
    ///   non-last PTE in the page bytes, `frame_to_index(pte.paddr()) ∈
    ///   child_perms.dom()`.
    /// - Walk uniqueness ([`walk_uniqueness_from_view`]): distinct PTE
    ///   positions with present non-last PTEs have distinct paddrs.
    ///
    /// Coverage and uniqueness retain the memory-safety premises needed by the
    /// trusted destructor body, without storing item permissions in
    /// [`VmIoOwner`](crate::specs::mm::io::VmIoOwner).
    open spec fn on_drop_pre(
        &self,
        reader: crate::mm::VmReader<'_, crate::mm::Infallible>,
        regions: crate::specs::mm::frame::meta_region_owners::MetaRegionOwners,
        vm_io_owner: crate::specs::mm::io::VmIoOwner,
    ) -> bool {
        &&& reader.inv()
        &&& reader.wf(vm_io_owner)
        &&& reader.remain_spec() >= crate::specs::arch::PAGE_SIZE
        &&& reader.cursor.vaddr % core::mem::align_of::<C::E>() == 0
        &&& vm_io_owner.inv()
        &&& vm_io_owner.read_view_initialized()
        &&& regions.inv()
        &&& Self::child_perms_embedding(regions, vstd::set::Set::empty())
        &&& self.walk_coverage_from_view(reader, vm_io_owner.read_view_of(), regions.slots.dom())
        &&& self.walk_uniqueness_from_view(reader, vm_io_owner.read_view_of())
    }

    /// Drops the children of a page-table node.
    ///
    /// The permission handoff for recursively destroying page-table entries is
    /// not modeled yet. Keep that trusted boundary local to this destructor;
    /// `VmIoOwner` only supplies the memory view used by `reader`.
    #[verifier::external_body]
    fn on_drop(
        &mut self,
        reader: &mut crate::mm::VmReader<'_, crate::mm::Infallible>,
        Tracked(regions): Tracked<
            &mut crate::specs::mm::frame::meta_region_owners::MetaRegionOwners,
        >,
        Tracked(_vm_io_owner): Tracked<&mut crate::specs::mm::io::VmIoOwner>,
    ) {
        let level = self.level;
        let range = if level == C::NR_LEVELS() {
            C::TOP_LEVEL_INDEX_RANGE()
        } else {
            0..nr_subpage_per_huge::<C>()
        };

        reader.skip_in_place(range.start * core::mem::size_of::<C::E>());

        let mut i = range.start;
        while i < range.end {
            // Non-atomic read is OK because we have mutable access.
            let pte = reader.read_once::<C::E>().unwrap();
            if pte.is_present() {
                let paddr = pte.paddr();
                // As a fast path, we can ensure that the type of the child frame
                // is `Self` if the PTE points to a child page table. Then we don't
                // need to check the vtable for the drop method.
                if !pte.is_last(level) {
                    // SAFETY: The PTE points to a page table node. The ownership
                    // of the child is transferred to the child then dropped.
                    let frame = unsafe { Frame::<Self>::from_raw(paddr) };
                    frame.drop(Tracked(regions));
                } else {
                    proof_decl! {
                        let tracked item_perm: Option<C::Perm>;
                    }
                    // SAFETY: The PTE points to a mapped item. The ownership
                    // of the item is transferred here then dropped.
                    let _item = unsafe {
                        C::item_from_raw(paddr, level, pte.prop(), Tracked(item_perm))
                    };
                }
            }
            i += 1;
        }
    }

    fn is_untyped(&self) -> bool {
        false
    }

    uninterp spec fn vtable_ptr(&self) -> usize;
}

#[verus_verify]
impl<C: PageTableConfig> PageTableNode<C> {
    /// Gets the level of a page table node.
    /// # Verified Properties
    /// ## Preconditions
    /// - The node must be well-formed, and the caller must provide a permission token for its metadata.
    /// ## Postconditions
    /// - Returns the level of the node.
    /// ## Safety
    /// - We require the caller to provide a permission token to ensure that this function is only called on a valid page table node.
    #[verus_spec(
        with
            Tracked(owner): Tracked<&NodeOwner<C>>,
            Tracked(regions): Tracked<&MetaRegionOwners>
    )]
    pub(super) fn level(&self) -> PagingLevel
        requires
            self.ptr.addr() == regions.slots[owner.slot_index].addr(),
            owner.metaregion_sound_node(*regions),
        returns
            owner.level,
    {
        let tracked points_to = regions.slots.tracked_borrow(owner.slot_index);
        #[verus_spec(with
            Tracked(points_to),
            Tracked(owner.tracked_borrow_metadata_perm()),
            Tracked(&())
        )]
        let meta = self.meta();
        meta.level
    }

    /// Allocates a new empty page table node.
    #[verus_spec(res =>
        with Tracked(parent_owner): Tracked<&mut NodeOwner<C>>,
             Tracked(regions): Tracked<&mut MetaRegionOwners>,
             Tracked(guards): Tracked<&Guards>,
             Ghost(idx): Ghost<usize>,
                 -> owner: Tracked<OwnerSubtree<C>>,
        requires
            1 <= level < NR_LEVELS,
            idx < NR_ENTRIES,
            old(regions).inv(),
            old(parent_owner).inv(),
        ensures
            final(regions).inv(),
            final(parent_owner).inv(),
            allocated_empty_node_owner(owner@, level),
            allocated_empty_node_grandchildren_none(owner@),
            res.ptr.addr() == owner@.value().node().meta_vaddr(),
            res.inv(),
            res.wf_with_region(*final(regions)),
            guards.unlocked(owner@.value().node().meta_vaddr()),
            MetaSlot::get_node_from_unused_spec(meta_to_frame(owner@.value().node().meta_vaddr()), *old(regions), *final(regions)),
            MetaSlot::slot_perm_reparked_spec(meta_to_frame(owner@.value().node().meta_vaddr()), *old(regions), *final(regions)),

            old(regions).contains(meta_to_index(owner@.value().node().meta_vaddr())),

            !crate::specs::mm::frame::meta_owners::is_mmio_paddr(
                meta_to_frame(owner@.value().node().meta_vaddr())),
            owner@.value().metaregion_sound(*final(regions)),
            forall|i: int|
                #[trigger] old(regions).ref_count(i) != REF_COUNT_UNUSED
                ==> i != meta_to_index(owner@.value().node().meta_vaddr()),
            owner@.value().match_pte(C::E::new_pt_spec(meta_to_frame(owner@.value().node().meta_vaddr())), level as PagingLevel),
            final(parent_owner).meta_own == old(parent_owner).meta_own,
            final(parent_owner).frame_permission == old(parent_owner).frame_permission,
            final(parent_owner).slot_index == old(parent_owner).slot_index,
            final(parent_owner).level == old(parent_owner).level,
            final(parent_owner).tree_level == old(parent_owner).tree_level,
            final(parent_owner).children_perm.addr() == old(parent_owner).children_perm.addr(),
            final(parent_owner).children_perm.value() == old(parent_owner).children_perm.value().update(
                idx as int,
                C::E::new_pt_spec(meta_to_frame(owner@.value().node().meta_vaddr())),
            ),
            final(regions).contains(owner@.value().node().slot_index),
            owner@.value().node().metaregion_sound_node(*final(regions)),
    )]
    #[verifier::external_body]
    pub fn alloc<'rcu>(level: PagingLevel) -> Self {
        let tracked entry_owner = EntryOwner::tracked_new_absent(
            TreePath::new(Seq::empty()),
            level,
        );

        let tracked mut owner = OwnerSubtree::<C>::tracked_new_val(entry_owner, level as nat);
        let meta = PageTablePageMeta::new(level);
        let mut frame = FrameAllocOptions::new();
        frame.zeroed(true);
        let allocated_frame = frame.alloc_frame_with(meta).expect(
            "Failed to allocate a page table node",
        );
        // The allocated frame is zeroed. Make sure zero is absent PTE.
        //debug_assert_eq!(C::E::new_absent().as_usize(), 0);

        proof_with!(|= Tracked(owner));

        allocated_frame
    }/*
    /// Activates the page table assuming it is a root page table.
    ///
    /// Here we ensure not dropping an active page table by making a
    /// processor a page table owner. When activating a page table, the
    /// reference count of the last activated page table is decremented.
    /// And that of the current page table is incremented.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the page table to be activated has
    /// proper mappings for the kernel and has the correct const parameters
    /// matching the current CPU.
    ///
    /// # Panics
    ///
    /// Only top-level page tables can be activated using this function.
    pub(crate) unsafe fn activate(&self) {
        use crate::{
            arch::mm::{activate_page_table, current_page_table_paddr},
            mm::page_prop::CachePolicy,
        };

        #[cfg(feature = "allow_panic")]
        assert_eq!(self.level(), C::NR_LEVELS());

        let last_activated_paddr = current_page_table_paddr();
        if last_activated_paddr == self.start_paddr() {
            return;
        }

        // SAFETY: The safety is upheld by the caller.
        unsafe { activate_page_table(self.clone().into_raw(), CachePolicy::Writeback) };

        // Restore and drop the last activated page table.
        // SAFETY: The physical address is valid and points to a forgotten page table node.
        drop(unsafe { Self::from_raw(last_activated_paddr) });
    }

    /// Activates the (root) page table assuming it is the first activation.
    ///
    /// It will not try dropping the last activate page table. It is the same
    /// with [`Self::activate()`] in other senses.
    pub(super) unsafe fn first_activate(&self) {
        use crate::{arch::mm::activate_page_table, mm::page_prop::CachePolicy};

        // SAFETY: The safety is upheld by the caller.
        unsafe { activate_page_table(self.clone().into_raw(), CachePolicy::Writeback) };
    }*/

}

#[verus_verify]
impl<'a, C: PageTableConfig> PageTableNodeRef<'a, C> {
    pub open spec fn locks_preserved_except<'rcu>(
        addr: usize,
        guards0: Guards,
        guards1: Guards,
    ) -> bool {
        &&& OwnerSubtree::implies(
            CursorOwner::<'rcu, C>::node_unlocked(guards0),
            CursorOwner::<'rcu, C>::node_unlocked_except(guards1, addr),
        )
        &&& forall|i: usize| guards0.lock_held(i) ==> guards1.lock_held(i)
        &&& forall|i: usize| guards0.unlocked(i) && i != addr ==> guards1.unlocked(i)
    }

    /// Locks the page table node.
    ///
    /// An atomic mode guard is required to
    ///  1. prevent deadlocks;
    ///  2. provide a lifetime (`'rcu`) that the nodes are guaranteed to outlive.
    /// # Verification Design
    /// As of when we verified this library, we didn't have a spin lock implementation, so we axiomatize
    /// what happens when it's successful.
    #[verifier::external_body]
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&NodeOwner<C>>,
            Tracked(guards): Tracked<&mut Guards>
        requires
            self.inner@.invariants(*owner),
            old(guards).unlocked(owner.meta_vaddr()),
        ensures
            final(guards).lock_held(owner.meta_vaddr()),
            Self::locks_preserved_except(owner.meta_vaddr(), *old(guards), *final(guards)),
            owner.relate_guard(res),
    )]
    pub fn lock<'rcu, A: InAtomicMode>(self, _guard: &'rcu A) -> PageTableGuard<'rcu, C> where
        'a: 'rcu,
     {
        unimplemented!()
    }

    /// Creates a new [`PageTableGuard`] without checking if the page table lock is held.
    ///
    /// # Safety
    ///
    /// This function must be called if this task logically holds the lock.
    ///
    /// Calling this function when a guard is already created is undefined behavior
    /// unless that guard was already forgotten.
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&NodeOwner<C>>,
             Tracked(guards): Tracked<&mut Guards>,
        requires
            self.inner@.invariants(*owner),
            old(guards).unlocked(owner.meta_vaddr()),
        ensures
            final(guards).lock_held(owner.meta_vaddr()),
            Self::locks_preserved_except(owner.meta_vaddr(), *old(guards), *final(guards)),
            owner.relate_guard(res),
    )]
    pub unsafe fn make_guard_unchecked<'rcu, A: InAtomicMode>(
        self,
        _guard: &'rcu A,
    ) -> PageTableGuard<'rcu, C> where 'a: 'rcu {
        let guard = PageTableGuard { inner: self };

        proof {
            let ghost guards0 = *guards;
            guards.guards = guards.guards.insert(owner.meta_vaddr());

        }

        guard
    }
}

impl<'rcu, C: PageTableConfig> PageTableGuard<'rcu, C> {
    /// Borrows an entry in the node at a given index.
    ///
    /// # Panics
    ///
    /// Panics if the index is not within the bound of
    /// [`nr_subpage_per_huge<C>`].
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&NodeOwner<C>>,
             Tracked(child_owner): Tracked<&EntryOwner<C>>,
             Tracked(regions): Tracked<&MetaRegionOwners>,
        requires
            owner.inv(),
            child_owner.inv(),
            owner.relate_guard(*old(self)),
            child_owner.match_pte(
                owner.children_perm.value()[idx as int],
                child_owner.parent_level,
            ),
            regions.inv(),
            regions.contains(owner.slot_index),
            // Panic condition
            idx < NR_ENTRIES,
        ensures
            res.wf(*child_owner),
            res.idx == idx,
            *res.node == *old(self),
            *final(self) == *final(res.node),
            owner.relate_guard(*res.node),
    )]
    pub fn entry<'a>(&'a mut self, idx: usize) -> Entry<'a, 'rcu, C> {
        #[cfg(feature = "allow_panic")]
        assert!(idx < nr_subpage_per_huge::<C>());
        // SAFETY: The index is within the bound. `Entry::new_at` returns an
        // entry whose node is the guard value we were handed.
        unsafe {
            #[verus_spec(with Tracked(child_owner), Tracked(owner), Tracked(regions))]
            Entry::new_at(self, idx)
        }
    }

    /// Gets the number of valid PTEs in a page table node.
    /// # Verified Properties
    /// ## Preconditions
    /// - The node must be well-formed.
    /// ## Postconditions
    /// - Returns the number of valid PTEs in the node.
    /// ## Safety
    /// - We require the caller to provide a permission token to ensure that this function is only called on a valid page table node.
    #[verus_spec(nr =>
        with Tracked(owner) : Tracked<&NodeOwner<C>>,
             Tracked(regions): Tracked<&MetaRegionOwners>,
        requires
            self.inner.inner@.invariants(*owner),
            regions.inv(),
            owner.metaregion_sound_node(*regions),
        returns
            owner.meta_own.nr_children.value(),
    )]
    pub fn nr_children(&self) -> u16 {
        let tracked points_to = regions.slots.tracked_borrow(owner.slot_index);
        #[verus_spec(with
            Tracked(points_to),
            Tracked(owner.tracked_borrow_metadata_perm()),
            Tracked(&())
        )]
        let meta = self.meta();

        *meta.nr_children.borrow(Tracked(&owner.meta_own.nr_children))
    }

    /// Returns if the page table node is detached from its parent.
    #[verus_spec(res =>
        with
            Tracked(points_to): Tracked<&'a vstd::simple_pptr::PointsTo<MetaSlot>>,
            Tracked(metadata_perms): Tracked<&'a MetadataPerm>,
            Tracked(repr_perm): Tracked<&'a ()>,
            Ghost(stray_id): Ghost<vstd::cell::CellId>,
        requires
            old(self).inner.inner@.ptr.addr() == points_to.addr(),
            typed_meta_wf::<PageTablePageMeta<C>>(
                *points_to,
                *metadata_perms,
                *repr_perm,
            ),
            typed_meta_value::<PageTablePageMeta<C>>(
                *metadata_perms,
                *repr_perm,
            ).stray.id()
                == stray_id,
        ensures
            res.id() == stray_id,
            *final(self) == *old(self),
    )]
    pub(super) fn stray_mut<'a>(&'a mut self) -> &'a pcell_maybe_uninit::PCell<bool> {
        // SAFETY: The lock is held so we have an exclusive access.
        #[verus_spec(with
            Tracked(points_to),
            Tracked(metadata_perms),
            Tracked(repr_perm)
        )]
        let meta = self.meta();
        &meta.stray
    }

    /// Reads a non-owning PTE at the given index.
    ///
    /// A non-owning PTE means that it does not account for a reference count
    /// of the a page if the PTE points to a page. The original PTE still owns
    /// the child page.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the index is within the bound.
    #[verus_spec(pte =>
        with Tracked(owner): Tracked<&NodeOwner<C>>,
             Tracked(regions): Tracked<&MetaRegionOwners>,
        requires
            self.inner.inner@.invariants(*owner),
            regions.inv(),
            regions.contains(owner.slot_index),
            idx < NR_ENTRIES,
        ensures
            pte == owner.children_perm.value()[idx as int],
    )]
    pub unsafe fn read_pte(&self, idx: usize) -> C::E {
        // debug_assert!(idx < nr_subpage_per_huge::<C>());
        let ptr = vstd_extra::array_ptr::ArrayPtr::<C::E, NR_ENTRIES>::from_addr(
            paddr_to_vaddr(self.start_paddr()),
        );

        // SAFETY:
        // - The page table node is alive. The index is inside the bound, so the page table entry is valid.
        // - All page table entries are aligned and accessed with atomic operations only.
        unsafe {
            #[verus_spec(with Tracked(&owner.children_perm))]
            load_pte(ptr.add(idx), Ordering::Relaxed)
        }
    }

    /// Writes a page table entry at a given index.
    ///
    /// This operation will leak the old child if the old PTE is present.
    ///
    /// # Safety
    ///
    /// The caller must ensure that:
    ///  1. The index must be within the bound;
    ///  2. The PTE must represent a valid [`Child`] whose level is compatible
    ///     with the page table node.
    ///  3. The page table node will have the ownership of the [`Child`]
    ///     after this method.
    #[verus_spec(
        with Tracked(owner): Tracked<&mut NodeOwner<C>>,
             Tracked(regions): Tracked<&MetaRegionOwners>,
        requires
            old(self).inner.inner@.invariants(*old(owner)),
            regions.inv(),
            regions.contains(old(owner).slot_index),
            idx < NR_ENTRIES,
        ensures
            final(owner).inv(),
            final(owner).level == old(owner).level,
            final(owner).meta_own == old(owner).meta_own,
            final(owner).frame_permission == old(owner).frame_permission,
            final(owner).slot_index == old(owner).slot_index,
            final(owner).children_perm.value() == old(owner).children_perm.value().update(
                idx as int,
                pte,
            ),
            *final(self) == *old(self),
    )]
    pub unsafe fn write_pte(&mut self, idx: usize, pte: C::E) {
        // debug_assert!(idx < nr_subpage_per_huge::<C>());
        #[verusfmt::skip]
        let ptr = vstd_extra::array_ptr::ArrayPtr::<C::E, NR_ENTRIES>::from_addr(
            paddr_to_vaddr(self.start_paddr())
        );

        // SAFETY:
        // - The page table node is alive. The index is inside the bound, so the page table entry is valid.
        // - All page table entries are aligned and accessed with atomic operations only.
        unsafe {
            #[verus_spec(with Tracked(&mut owner.children_perm))]
            store_pte(ptr.add(idx), pte, Ordering::Release)
        }
        proof {
            assert(owner.children_perm.wf());
        }
    }

    /// Gets the mutable reference to the number of valid PTEs in the node.
    #[verus_spec(res =>
        with
            Tracked(points_to): Tracked<&'a vstd::simple_pptr::PointsTo<MetaSlot>>,
            Tracked(metadata_perms): Tracked<&'a MetadataPerm>,
            Ghost(nr_children_id): Ghost<vstd::cell::CellId>,
        requires
            old(self).inner.inner@.ptr.addr() == points_to.addr(),
            typed_meta_wf::<PageTablePageMeta<C>>(*points_to, *metadata_perms, ()),
            typed_meta_value::<PageTablePageMeta<C>>(
                *metadata_perms,
                (),
            ).nr_children.id()
                == nr_children_id,
        ensures
            res.id() == nr_children_id,
            *final(self) == *old(self),
    )]
    fn nr_children_mut<'a>(&'a mut self) -> &'a pcell_maybe_uninit::PCell<u16> {
        // SAFETY: The lock is held so we have an exclusive access.
        #[verus_spec(with
            Tracked(points_to),
            Tracked(metadata_perms),
            Tracked(&())
        )]
        let meta = self.meta();
        &meta.nr_children
    }
}

/*impl<C: PageTableConfig> Drop for PageTableGuard<'_, C> {
    fn drop(&mut self) {
        self.inner.meta().lock.store(0, Ordering::Release);
    }
}*/

impl<C: PageTableConfig> PageTablePageMeta<C> {
    pub fn new(level: PagingLevel) -> Self {
        Self {
            nr_children: pcell_maybe_uninit::PCell::new(0).0,
            stray: pcell_maybe_uninit::PCell::new(false).0,
            level,
            lock: PAtomicU8::new(0).0,
            _phantom: PhantomData,
        }
    }

    /// The PTE value that `read_once::<C::E>` would produce at cursor `c`
    /// against the given memory view. Linked to `read_once` via
    /// `pod_bytes(v) == read_view.read_bytes(...)` (strengthened ensures)
    /// + [`lemma_decode_pod_inverse`].
    pub open spec fn walk_pte_at_view(view: crate::specs::mm::virt_mem::MemView, c: usize) -> C::E {
        ostd_pod::decode_pod::<C::E>(view.read_bytes(c, core::mem::size_of::<C::E>()))
    }

    /// Single-cursor projection of [`walk_coverage_from_view`]. Extracting
    /// the forall body to a named predicate lets the body invoke
    /// [`lemma_coverage_at`] for one specific `c` instead of relying on
    /// auto-trigger matching across the loop invariant's `forall|c|`.
    pub open spec fn walk_coverage_at(
        self,
        view: crate::specs::mm::virt_mem::MemView,
        dom: vstd::set::Set<int>,
        c: usize,
    ) -> bool {
        let pte = Self::walk_pte_at_view(view, c);
        pte.is_present() && !pte.is_last(self.level) ==> dom.contains(frame_to_index(pte.paddr()))
    }

    /// Instantiate [`walk_coverage_from_view`]'s forall at one cursor.
    pub proof fn lemma_coverage_at(
        self,
        reader: crate::mm::VmReader<'_, crate::mm::Infallible>,
        view: crate::specs::mm::virt_mem::MemView,
        dom: vstd::set::Set<int>,
        c: usize,
    )
        requires
            self.walk_coverage_from_view(reader, view, dom),
            reader.cursor.vaddr <= c,
            c + core::mem::size_of::<C::E>() <= reader.cursor.vaddr + reader.remain_spec(),
            (c - reader.cursor.vaddr) % core::mem::size_of::<C::E>() as int == 0,
        ensures
            self.walk_coverage_at(view, dom, c),
    {
    }

    /// Instantiate [`walk_uniqueness_from_view`]'s forall at one cursor pair.
    pub proof fn lemma_uniqueness_at_pair(
        self,
        reader: crate::mm::VmReader<'_, crate::mm::Infallible>,
        view: crate::specs::mm::virt_mem::MemView,
        c1: usize,
        c2: usize,
    )
        requires
            self.walk_uniqueness_from_view(reader, view),
            reader.cursor.vaddr <= c1,
            c1 + core::mem::size_of::<C::E>() <= reader.cursor.vaddr + reader.remain_spec(),
            (c1 - reader.cursor.vaddr) % core::mem::size_of::<C::E>() as int == 0,
            reader.cursor.vaddr <= c2,
            c2 + core::mem::size_of::<C::E>() <= reader.cursor.vaddr + reader.remain_spec(),
            (c2 - reader.cursor.vaddr) % core::mem::size_of::<C::E>() as int == 0,
            c1 != c2,
            Self::walk_pte_at_view(view, c1).is_present(),
            !Self::walk_pte_at_view(view, c1).is_last(self.level),
            Self::walk_pte_at_view(view, c2).is_present(),
            !Self::walk_pte_at_view(view, c2).is_last(self.level),
        ensures
            Self::walk_pte_at_view(view, c1).paddr() != Self::walk_pte_at_view(view, c2).paddr(),
    {
    }

    /// Caller-side dom-membership obligation: every present non-last PTE
    /// position in the walk (over `view`) has its child-frame index in
    /// `dom`. Phrased over a frozen `(view, dom)` pair so the body can
    /// carry it as a loop invariant against an entry-state snapshot
    /// while `vm_io_owner` advances per iteration.
    pub open spec fn walk_coverage_from_view(
        self,
        reader: crate::mm::VmReader<'_, crate::mm::Infallible>,
        view: crate::specs::mm::virt_mem::MemView,
        dom: vstd::set::Set<int>,
    ) -> bool {
        forall|c: usize|
            #![trigger Self::walk_pte_at_view(view, c)]
            reader.cursor.vaddr <= c && c + core::mem::size_of::<C::E>() <= reader.cursor.vaddr
                + reader.remain_spec() && (c - reader.cursor.vaddr) % core::mem::size_of::<
                C::E,
            >() as int == 0 ==> {
                let pte = Self::walk_pte_at_view(view, c);
                pte.is_present() && !pte.is_last(self.level) ==> dom.contains(
                    frame_to_index(pte.paddr()),
                )
            }
    }

    /// Caller-side uniqueness obligation: distinct cursor positions with
    /// present non-last PTEs (in `view`) map to distinct paddrs.
    pub open spec fn walk_uniqueness_from_view(
        self,
        reader: crate::mm::VmReader<'_, crate::mm::Infallible>,
        view: crate::specs::mm::virt_mem::MemView,
    ) -> bool {
        forall|c1: usize, c2: usize|
            #![trigger Self::walk_pte_at_view(view, c1), Self::walk_pte_at_view(view, c2)]
            reader.cursor.vaddr <= c1 && c1 + core::mem::size_of::<C::E>() <= reader.cursor.vaddr
                + reader.remain_spec() && (c1 - reader.cursor.vaddr) % core::mem::size_of::<
                C::E,
            >() as int == 0 && reader.cursor.vaddr <= c2 && c2 + core::mem::size_of::<C::E>()
                <= reader.cursor.vaddr + reader.remain_spec() && (c2 - reader.cursor.vaddr)
                % core::mem::size_of::<C::E>() as int == 0 && c1 != c2 ==> {
                let pte1 = Self::walk_pte_at_view(view, c1);
                let pte2 = Self::walk_pte_at_view(view, c2);
                pte1.is_present() && !pte1.is_last(self.level) && pte2.is_present()
                    && !pte2.is_last(self.level) ==> pte1.paddr() != pte2.paddr()
            }
    }

    /// Caller-side shape obligation: every paddr in `child_perms.dom()`
    /// has a slot perm matching the shape `from_raw` + `VerifiedDrop::drop`
    /// expect (init, alignment, refcount within bounds, last-reference
    /// shape when refcount == 1).
    pub open spec fn child_perms_embedding(
        regions: crate::specs::mm::frame::meta_region_owners::MetaRegionOwners,
        excluded: vstd::set::Set<int>,
    ) -> bool {
        forall|paddr: crate::mm::Paddr|
            #![trigger regions.slot_owner(paddr)]
            regions.slots.dom().contains(frame_to_index(paddr)) && !excluded.contains(
                frame_to_index(paddr),
            ) ==> {
                let idx = frame_to_index(paddr);
                let so = regions.slot_owners[idx];
                &&& <Frame<Self>>::from_raw_requires(regions, paddr)
                &&& 0 < so.ref_count() <= REF_COUNT_MAX
                &&& so.storage_perm().is_init()
                &&& so.ref_count() == 1 ==> {
                    &&& so.in_list_perm.value() == 0
                    &&& so.paths_in_pt.is_empty()
                }
            }
    }
}

} // verus!
