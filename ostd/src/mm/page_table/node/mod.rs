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

use vstd::atomic::PAtomicU8;

use vstd_extra::array_ptr;
use vstd_extra::cast_ptr::*;
use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;

use crate::mm::frame::allocator::FrameAllocOptions;
use crate::mm::frame::meta::MetaSlot;
use crate::mm::frame::{frame_to_index, AnyFrameMeta, Frame};
use crate::mm::kspace::VMALLOC_BASE_VADDR;
use crate::mm::page_table::*;
use crate::mm::{kspace::LINEAR_MAPPING_BASE_VADDR, paddr_to_vaddr, Paddr, Vaddr};
use crate::specs::arch::kspace::FRAME_METADATA_RANGE;
use crate::specs::mm::frame::mapping::{meta_to_frame, META_SLOT_SIZE};
use crate::specs::mm::frame::meta_owners::{
    MetaSlotOwner, MetaSlotStorage, Metadata, REF_COUNT_UNUSED,
};
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::page_table::node::owners::*;

use core::{marker::PhantomData, ops::Deref, sync::atomic::Ordering};

use super::nr_subpage_per_huge;

use crate::{
    mm::{
        page_table::{load_pte, store_pte},
        //        FrameAllocOptions, Infallible,
        //        VmReader,
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

impl<C: PageTableConfig> AnyFrameMeta for PageTablePageMeta<C> {
    fn on_drop(&mut self, _reader: &mut crate::mm::VmReader<'_, crate::mm::Infallible>) {
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
        with Tracked(perm) : Tracked<&PointsTo<MetaSlot, Metadata<PageTablePageMeta<C>>>>
    )]
    pub(super) fn level(&self) -> PagingLevel
        requires
            self.ptr.addr() == perm.addr(),
            self.ptr.addr() == perm.points_to.addr(),
            perm.is_init(),
            perm.wf(&perm.inner_perms),
        returns
            perm.value().metadata.level,
    {
        #[verus_spec(with Tracked(perm))]
        let meta = self.meta();
        meta.level
    }

    /// Allocates a new empty page table node.
    #[verus_spec(res =>
        with Tracked(parent_owner): Tracked<&mut NodeOwner<C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&Guards<'rcu, C>>,
            Ghost(idx): Ghost<usize>,
        -> owner: Tracked<OwnerSubtree<C>>
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
            res.ptr.addr() == owner@.value.node.unwrap().meta_perm.addr(),
            guards.unlocked(owner@.value.node.unwrap().meta_perm.addr()),
            MetaSlot::get_from_unused_spec(meta_to_frame(owner@.value.node.unwrap().meta_perm.addr()), false, *old(regions), *final(regions)),
            old(regions).slots.contains_key(frame_to_index(meta_to_frame(owner@.value.node.unwrap().meta_perm.addr()))),
            // Allocator trust boundary: PT-node allocations come from the regular
            // RAM pool, never from MMIO ranges. Used by `alloc_if_none_metaregion_sound_preserved`
            // to rule out untracked-frame collisions at the freshly-allocated idx.
            !crate::specs::mm::frame::meta_owners::is_mmio_paddr(
                meta_to_frame(owner@.value.node.unwrap().meta_perm.addr())),
            owner@.value.metaregion_sound(*final(regions)),
            // Note: `owner@.value.in_scope` was previously asserted here, but
            // `allocated_empty_node_owner` already requires `owner.inv()`, which
            // through `EntryOwner::inv` forces `!in_scope`. Asserting both was
            // an unsoundness that allowed `assert(false)` post-alloc.
            //
            // Disjointness: the alloc'd slot's idx is different from any
            // previously-active slot's idx. Derived from the unused pre-state
            // (`pre.slot_owners[new_alloc_idx].ref_count == UNUSED` per
            // `get_from_unused_spec`). Stated as an explicit ensures so it's
            // easy to trigger from split/alloc_if_none loop invariants.
            forall|i: usize|
                #[trigger] old(regions).slot_owners[i].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                ==> i != frame_to_index(meta_to_frame(owner@.value.node.unwrap().meta_perm.addr())),
            owner@.value.match_pte(C::E::new_pt_spec(meta_to_frame(owner@.value.node.unwrap().meta_perm.addr())), level as PagingLevel),
            *final(parent_owner) == old(parent_owner).set_children_perm(idx, C::E::new_pt_spec(meta_to_frame(owner@.value.node.unwrap().meta_perm.addr()))),
    )]
    #[verifier::external_body]
    pub fn alloc<'rcu>(level: PagingLevel) -> Self {
        let tracked entry_owner = EntryOwner::new_absent(TreePath::new(Seq::empty()), level);

        let tracked mut owner = OwnerSubtree::<C>::new_val_tracked(entry_owner, level as nat);
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
        guards0: Guards<'rcu, C>,
        guards1: Guards<'rcu, C>,
    ) -> bool {
        &&& OwnerSubtree::implies(
            CursorOwner::node_unlocked(guards0),
            CursorOwner::node_unlocked_except(guards1, addr),
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
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            self.inner@.invariants(*owner),
            old(guards).unlocked(owner.meta_perm.addr()),
        ensures
            final(guards).lock_held(owner.meta_perm.addr()),
            Self::locks_preserved_except(owner.meta_perm.addr(), *old(guards), *final(guards)),
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
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            self.inner@.invariants(*owner),
            old(guards).unlocked(owner.meta_perm.addr()),
        ensures
            final(guards).lock_held(owner.meta_perm.addr()),
            Self::locks_preserved_except(owner.meta_perm.addr(), *old(guards), *final(guards)),
            owner.relate_guard(res),
    )]
    pub fn make_guard_unchecked<'rcu, A: InAtomicMode>(self, _guard: &'rcu A) -> PageTableGuard<
        'rcu,
        C,
    > where 'a: 'rcu {
        let guard = PageTableGuard { inner: self };

        proof {
            let ghost guards0 = *guards;
            guards.guards.tracked_insert(owner.meta_perm.addr(), None);
            assert(owner.relate_guard(guard));

            assert(forall|other: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                owner.inv() && CursorOwner::node_unlocked(guards0)(other, path)
                    ==> #[trigger] CursorOwner::node_unlocked_except(
                    *guards,
                    owner.meta_perm.addr(),
                )(other, path));
        }

        guard
    }
}

//}
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
    )]
    pub fn entry<'a>(&'a mut self, idx: usize) -> (res: Entry<'a, 'rcu, C>)
        requires
            owner.inv(),
            !child_owner.in_scope,
            child_owner.inv(),
            owner.relate_guard(*old(self)),
            child_owner.match_pte(
                owner.children_perm.value()[idx as int],
                child_owner.parent_level,
            ),
            // Panic condition
            idx < NR_ENTRIES,
        ensures
            res.wf(*child_owner),
            res.idx == idx,
            owner.relate_guard(*res.node),
            *final(self) == *old(self),
    {
        #[cfg(feature = "allow_panic")]
        assert!(idx < nr_subpage_per_huge::<C>());
        // SAFETY: The index is within the bound. `*self` is unchanged because
        // Entry::new_at's `*res.node == *old(guard)` ensures says the wrapped
        // node equals the input guard's value, and the reborrow makes
        // `*final(self) == *res.node`.
        #[verus_spec(with Tracked(child_owner), Tracked(owner))]
        Entry::new_at(self, idx)
    }

    /// Gets the number of valid PTEs in a page table node.
    /// # Verified Properties
    /// ## Preconditions
    /// - The node must be well-formed.
    /// ## Postconditions
    /// - Returns the number of valid PTEs in the node.
    /// ## Safety
    /// - We require the caller to provide a permission token to ensure that this function is only called on a valid page table node.
    #[verus_spec(
        with Tracked(owner) : Tracked<&NodeOwner<C>>
    )]
    pub fn nr_children(&self) -> (nr: u16)
        requires
    // Node invariants: owner well-formedness and node-owner consistency

            self.inner.inner@.invariants(*owner),
        returns
            owner.meta_own.nr_children.value(),
    {
        // SAFETY: The lock is held so we have an exclusive access.
        #[verus_spec(with Tracked(&owner.meta_perm))]
        let meta = self.meta();

        *meta.nr_children.borrow(Tracked(&owner.meta_own.nr_children))
    }

    /// Returns if the page table node is detached from its parent.
    #[verus_spec(
        with Tracked(meta_perm): Tracked<&'a PointsTo<MetaSlot, Metadata<PageTablePageMeta<C>>>>
    )]
    pub(super) fn stray_mut<'a>(&'a mut self) -> (res: &'a pcell_maybe_uninit::PCell<bool>)
        requires
            old(self).inner.inner@.ptr.addr() == meta_perm.addr(),
            old(self).inner.inner@.ptr.addr() == meta_perm.points_to.addr(),
            meta_perm.is_init(),
            meta_perm.wf(&meta_perm.inner_perms),
        ensures
            res.id() == meta_perm.value().metadata.stray.id(),
            *final(self) == *old(self),
    {
        // SAFETY: The lock is held so we have an exclusive access.
        #[verus_spec(with Tracked(meta_perm))]
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
    #[verus_spec(
        with Tracked(owner): Tracked<&NodeOwner<C>>
    )]
    pub fn read_pte(&self, idx: usize) -> (pte: C::E)
        requires
            self.inner.inner@.invariants(*owner),
            idx < NR_ENTRIES,
        ensures
            pte == owner.children_perm.value()[idx as int],
    {
        // debug_assert!(idx < nr_subpage_per_huge::<C>());
        let ptr = vstd_extra::array_ptr::ArrayPtr::<C::E, NR_ENTRIES>::from_addr(
            paddr_to_vaddr(
                #[verus_spec(with Tracked(&owner.meta_perm.points_to))]
                self.start_paddr(),
            ),
        );

        // SAFETY:
        // - The page table node is alive. The index is inside the bound, so the page table entry is valid.
        // - All page table entries are aligned and accessed with atomic operations only.
        #[verus_spec(with Tracked(&owner.children_perm))]
        load_pte(ptr.add(idx), Ordering::Relaxed)
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
        with Tracked(owner): Tracked<&mut NodeOwner<C>>
    )]
    pub fn write_pte(&mut self, idx: usize, pte: C::E)
        requires
            old(self).inner.inner@.invariants(*old(owner)),
            idx < NR_ENTRIES,
        ensures
            final(owner).inv(),
            final(owner).meta_perm.addr() == old(owner).meta_perm.addr(),
            final(owner).level == old(owner).level,
            final(owner).meta_own == old(owner).meta_own,
            final(owner).meta_perm.points_to == old(owner).meta_perm.points_to,
            final(owner).meta_perm.inner_perms == old(owner).meta_perm.inner_perms,
            final(owner).children_perm.value() == old(owner).children_perm.value().update(
                idx as int,
                pte,
            ),
            *final(self) == *old(self),
    {
        // debug_assert!(idx < nr_subpage_per_huge::<C>());
        #[verusfmt::skip]
        let ptr = vstd_extra::array_ptr::ArrayPtr::<C::E, NR_ENTRIES>::from_addr(
            paddr_to_vaddr(
                #[verus_spec(with Tracked(&owner.meta_perm.points_to))]
                self.start_paddr()
            ),
        );

        // SAFETY:
        // - The page table node is alive. The index is inside the bound, so the page table entry is valid.
        // - All page table entries are aligned and accessed with atomic operations only.
        #[verus_spec(with Tracked(&mut owner.children_perm))]
        store_pte(ptr.add(idx), pte, Ordering::Release)
    }

    /// Gets the mutable reference to the number of valid PTEs in the node.
    #[verus_spec(
        with Tracked(meta_perm): Tracked<&'a PointsTo<MetaSlot, Metadata<PageTablePageMeta<C>>>>
    )]
    fn nr_children_mut<'a>(&'a mut self) -> (res: &'a pcell_maybe_uninit::PCell<u16>)
        requires
            old(self).inner.inner@.ptr.addr() == meta_perm.addr(),
            old(self).inner.inner@.ptr.addr() == meta_perm.points_to.addr(),
            meta_perm.is_init(),
            meta_perm.wf(&meta_perm.inner_perms),
        ensures
            res.id() == meta_perm.value().metadata.nr_children.id(),
            *final(self) == *old(self),
    {
        // SAFETY: The lock is held so we have an exclusive access.
        #[verus_spec(with Tracked(meta_perm))]
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
}

} // verus!
/* TODO: Come back after VMReader
// FIXME: The safe APIs in the `page_table/node` module allow `Child::Frame`s with
// arbitrary addresses to be stored in the page table nodes. Therefore, they may not
// be valid `C::Item`s. The soundness of the following `on_drop` implementation must
// be reasoned in conjunction with the `page_table/cursor` implementation.
unsafe impl<C: PageTableConfig> AnyFrameMeta for PageTablePageMeta<C> {
    fn on_drop(&mut self, reader: &mut VmReader<Infallible>) {
        let nr_children = self.nr_children.get_mut();
        if *nr_children == 0 {
            return;
        }

        let level = self.level;
        let range = if level == C::NR_LEVELS() {
            C::TOP_LEVEL_INDEX_RANGE.clone()
        } else {
            0..nr_subpage_per_huge::<C>()
        };

        // Drop the children.
        reader.skip(range.start * size_of::<C::E>());
        for _ in range {
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
                    drop(unsafe { Frame::<Self>::from_raw(paddr) });
                } else {
                    // SAFETY: The PTE points to a mapped item. The ownership
                    // of the item is transferred here then dropped.
                    drop(unsafe { C::item_from_raw(paddr, level, pte.prop()) });
                }
            }
        }
    }
}*/
