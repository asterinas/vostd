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

pub use crate::specs::mm::page_table::node::{entry_owners::*, entry_view::*, owners::*};
pub use child::*;
pub use entry::*;

use vstd::prelude::*;

use vstd::atomic::PAtomicU8;
use vstd::cell::PCell;
use vstd::simple_pptr::{self, PPtr};

use vstd_extra::array_ptr;
use vstd_extra::cast_ptr::*;
use vstd_extra::ownership::*;

use crate::mm::frame::meta::MetaSlot;
use crate::mm::frame::{AnyFrameMeta, Frame, StoredPageTablePageMeta};
use crate::mm::page_table::*;
use crate::mm::{kspace::LINEAR_MAPPING_BASE_VADDR, paddr_to_vaddr, Paddr, Vaddr};
use crate::specs::arch::kspace::FRAME_METADATA_RANGE;
use crate::specs::arch::kspace::VMALLOC_BASE_VADDR;
use crate::specs::mm::frame::mapping::{meta_to_frame, META_SLOT_SIZE};
use crate::specs::mm::frame::meta_owners::MetaSlotOwner;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;

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
#[rustc_has_incoherent_inherent_impls]
pub struct PageTablePageMeta<C: PageTableConfig> {
    /// The number of valid PTEs. It is mutable if the lock is held.
    pub nr_children: PCell<u16>,
    /// If the page table is detached from its parent.
    ///
    /// A page table can be detached from its parent while still being accessed,
    /// since we use a RCU scheme to recycle page tables. If this flag is set,
    /// it means that the parent is recycling the page table.
    pub stray: PCell<bool>,
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

impl<C: PageTableConfig> PageTablePageMeta<C> {
    #[verifier::external_body]
    pub fn get_stray(&self) -> PCell<bool>
        returns
            self.stray,
    {
        unimplemented!()
    }

    pub open spec fn into_spec(self) -> StoredPageTablePageMeta {
        StoredPageTablePageMeta {
            nr_children: self.nr_children,
            stray: self.stray,
            level: self.level,
            lock: self.lock,
        }
    }

    #[verifier::when_used_as_spec(into_spec)]
    pub fn into(self) -> (res: StoredPageTablePageMeta)
        ensures
            res == self.into_spec(),
    {
        StoredPageTablePageMeta {
            nr_children: self.nr_children,
            stray: self.stray,
            level: self.level,
            lock: self.lock,
        }
    }
}

impl StoredPageTablePageMeta {
    pub open spec fn into_spec<C: PageTableConfig>(self) -> PageTablePageMeta<C> {
        PageTablePageMeta::<C> {
            nr_children: self.nr_children,
            stray: self.stray,
            level: self.level,
            lock: self.lock,
            _phantom: PhantomData,
        }
    }

    #[verifier::when_used_as_spec(into_spec)]
    pub fn into<C: PageTableConfig>(self) -> (res: PageTablePageMeta<C>)
        ensures
            res == self.into_spec::<C>(),
    {
        PageTablePageMeta::<C> {
            nr_children: self.nr_children,
            stray: self.stray,
            level: self.level,
            lock: self.lock,
            _phantom: PhantomData,
        }
    }
}

uninterp spec fn drop_tree_spec<C: PageTableConfig>(_page: Frame<PageTablePageMeta<C>>) -> Frame<
    PageTablePageMeta<C>,
>;

#[verifier::external_body]
extern "C" fn drop_tree<C: PageTableConfig>(_page: &mut Frame<PageTablePageMeta<C>>)
    ensures
        _page == drop_tree_spec::<C>(*old(_page)),
;

impl<C: PageTableConfig> Repr<MetaSlot> for PageTablePageMeta<C> {
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

    proof fn from_to_repr(self) {
        admit()
    }

    proof fn to_from_repr(r: MetaSlot) {
        admit()
    }

    proof fn to_repr_wf(self) {
        admit()
    }
}

impl<C: PageTableConfig> AnyFrameMeta for PageTablePageMeta<C> {
    fn on_drop(&mut self) {
    }

    fn is_untyped(&self) -> bool {
        false
    }

    uninterp spec fn vtable_ptr(&self) -> usize;
}

impl<C: PageTableConfig> PageTableNode<C> {
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(perm) : Tracked<&PointsTo<MetaSlot, PageTablePageMeta<C>>>
    )]
    pub fn level(&self) -> PagingLevel
        requires
            self.ptr.addr() == perm.addr(),
            self.ptr.addr() == perm.points_to.addr(),
            perm.is_init(),
            perm.wf(),
    {
        #[verus_spec(with Tracked(perm))]
        let meta = self.meta();
        meta.level
    }

    /// Allocates a new empty page table node.
    #[verifier::external_body]
    #[verus_spec(r =>
        with Tracked(regions): Tracked<&mut MetaRegionOwners>
        -> owner: NodeOwner<C>
    )]
    pub(super) fn alloc(level: PagingLevel) -> Self {
        unimplemented!()/*
        let meta = PageTablePageMeta::new(level);
        let frame = FrameAllocOptions::new()
            .zeroed(true)
            .alloc_frame_with(meta)
            .expect("Failed to allocate a page table node");
        // The allocated frame is zeroed. Make sure zero is absent PTE.
        //debug_assert_eq!(C::E::new_absent().as_usize(), 0);

        frame*/

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

        assert_eq!(self.level(), C::NR_LEVELS);

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

impl<'a, C: PageTableConfig> PageTableNodeRef<'a, C> {
    /// Locks the page table node.
    ///
    /// An atomic mode guard is required to
    ///  1. prevent deadlocks;
    ///  2. provide a lifetime (`'rcu`) that the nodes are guaranteed to outlive.
    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    #[verusfmt::skip]
    pub fn lock<'rcu, A: InAtomicMode>(self, _guard: &'rcu A) -> PPtr<PageTableGuard<'rcu, C>>
        where 'a: 'rcu {
        unimplemented!()
        // TODO: axiomatize locks
        /*        while self
            .meta()
            .lock
            .compare_exchange(0, 1, Ordering::Acquire, Ordering::Relaxed)
            .is_err()
        {
            core::hint::spin_loop();
        }
*/
        //        PageTableGuard::<'rcu, C> { inner: self }

    }

    /// Creates a new [`PageTableGuard`] without checking if the page table lock is held.
    ///
    /// # Safety
    ///
    /// This function must be called if this task logically holds the lock.
    ///
    /// Calling this function when a guard is already created is undefined behavior
    /// unless that guard was already forgotten.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&NodeOwner<C>>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            owner.inv(),
            self.inner@.wf(*owner),
            !old(guards).guards.contains_key(owner.meta_perm.addr()),
        ensures
            guards.guards.contains_key(owner.meta_perm.addr()),
            guards.guards[owner.meta_perm.addr()] is Some,
            res.addr() == guards.guards[owner.meta_perm.addr()].unwrap().addr(),
            owner.relate_guard_perm(guards.guards[owner.meta_perm.addr()].unwrap()),
    )]
    pub fn make_guard_unchecked<'rcu, A: InAtomicMode>(self, _guard: &'rcu A) -> (res: PPtr<PageTableGuard<'rcu, C>>) where 'a: 'rcu
    {
        let guard = PageTableGuard { inner: self };
        let (ptr, guard_perm) = PPtr::<PageTableGuard<C>>::new(guard);
        proof {
            guards.guards.tracked_insert(owner.meta_perm.addr(), Some(guard_perm.get()));
            assert(owner.relate_guard_perm(guards.guards[owner.meta_perm.addr()].unwrap()));
        }

        ptr
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
            Tracked(guard_perm): Tracked<&GuardPerm<'rcu, C>>,
    )]
    pub fn entry(guard: PPtr<Self>, idx: usize) -> (res: Entry<'rcu, C>)
        requires
            owner.inv(),
            child_owner.inv(),
            owner.relate_guard_perm(*guard_perm),
            guard_perm.addr() == guard.addr(),
            idx < NR_ENTRIES(), // NR_ENTRIES == nr_subpage_per_huge::<C>()
        ensures
            res.wf(*child_owner),
            res.node.addr() == guard_perm.addr(),
    {
        //        assert!(idx < nr_subpage_per_huge::<C>());
        // SAFETY: The index is within the bound.
        #[verus_spec(with Tracked(child_owner), Tracked(owner), Tracked(guard_perm))]
        Entry::new_at(guard, idx);
    }

    /// Gets the number of valid PTEs in the node.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner) : Tracked<&mut NodeOwner<C>>
    )]
    pub fn nr_children(&self) -> (nr: u16)
        requires
            self.inner.inner@.ptr.addr() == old(owner).meta_perm.addr(),
            self.inner.inner@.ptr.addr() == old(owner).meta_perm.points_to.addr(),
            old(owner).inv(),
        ensures
            owner == old(owner),
    {
        // SAFETY: The lock is held so we have an exclusive access.
        #[verus_spec(with Tracked(&owner.meta_perm))]
        let meta = self.meta();

        *meta.nr_children.borrow(Tracked(&owner.meta_own.nr_children))
    }

    /// Returns if the page table node is detached from its parent.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner) : Tracked<EntryOwner<C>>
    )]
    pub fn stray_mut(&mut self) -> PCell<bool>
        requires
            owner.is_node(),
            old(self).inner.inner@.ptr.addr() == owner.node.unwrap().meta_perm.addr(),
            old(self).inner.inner@.ptr.addr() == owner.node.unwrap().meta_perm.points_to.addr(),
            owner.inv(),
    {
        let tracked node_owner = owner.node.tracked_borrow();

        // SAFETY: The lock is held so we have an exclusive access.
        #[verus_spec(with Tracked(&node_owner.meta_perm))]
        let meta = self.meta();

        meta.get_stray()
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
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner): Tracked<&NodeOwner<C>>
    )]
    pub fn read_pte(&self, idx: usize) -> C::E
        requires
            self.inner.inner@.ptr.addr() == owner.meta_perm.addr(),
            self.inner.inner@.ptr.addr() == owner.meta_perm.points_to.addr(),
            owner.inv(),
            meta_to_frame(owner.meta_perm.addr) < VMALLOC_BASE_VADDR()
                - LINEAR_MAPPING_BASE_VADDR(),
            FRAME_METADATA_RANGE().start <= owner.meta_perm.addr < FRAME_METADATA_RANGE().end,
            owner.meta_perm.addr % META_SLOT_SIZE() == 0,
            idx < NR_ENTRIES(),
    {
        // debug_assert!(idx < nr_subpage_per_huge::<C>());
        let ptr = vstd_extra::array_ptr::ArrayPtr::<C::E, CONST_NR_ENTRIES>::from_addr(
            #[verusfmt::skip]
            paddr_to_vaddr(
                #[verus_spec(with Tracked(&owner.meta_perm.points_to))]
                self.start_paddr()
            ),
        );

        // SAFETY:
        // - The page table node is alive. The index is inside the bound, so the page table entry is valid.
        // - All page table entries are aligned and accessed with atomic operations only.
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
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner): Tracked<&mut NodeOwner<C>>
    )]
    #[verifier::external_body]
    pub fn write_pte(&mut self, idx: usize, pte: C::E)
        requires
            old(owner).inv(),
            meta_to_frame(old(owner).meta_perm.addr) < VMALLOC_BASE_VADDR()
                - LINEAR_MAPPING_BASE_VADDR(),
            idx < NR_ENTRIES(),
        ensures
            owner.inv(),
            owner.meta_perm.addr() == old(owner).meta_perm.addr(),
            owner.meta_own == old(owner).meta_own,
            owner.meta_perm.points_to == old(owner).meta_perm.points_to,
            *self == *old(self),
    {
        // debug_assert!(idx < nr_subpage_per_huge::<C>());
        #[verusfmt::skip]
        let ptr = vstd_extra::array_ptr::ArrayPtr::<C::E, CONST_NR_ENTRIES>::from_addr(
            paddr_to_vaddr(
                #[verus_spec(with Tracked(&owner.meta_perm.points_to))]
                self.start_paddr()
            ),
        );

        // SAFETY:
        // - The page table node is alive. The index is inside the bound, so the page table entry is valid.
        // - All page table entries are aligned and accessed with atomic operations only.
        store_pte(ptr.add(idx), pte, Ordering::Release)
    }

    /// Gets the mutable reference to the number of valid PTEs in the node.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(meta_perm): Tracked<&'a PointsTo<MetaSlot, PageTablePageMeta<C>>>
    )]
    fn nr_children_mut<'a>(&'a mut self) -> (res: &'a PCell<u16>)
        requires
            old(self).inner.inner@.ptr.addr() == meta_perm.addr(),
            old(self).inner.inner@.ptr.addr() == meta_perm.points_to.addr(),
            meta_perm.is_init(),
            meta_perm.wf(),
        ensures
            res.id() == meta_perm.value().nr_children.id(),
            *self == *old(self),
    {
        // SAFETY: The lock is held so we have an exclusive access.
        #[verus_spec(with Tracked(meta_perm))]
        let meta = self.meta();
        &meta.nr_children
    }
}

} // verus!
/*impl<C: PageTableConfig> Drop for PageTableGuard<'_, C> {
    fn drop(&mut self) {
        self.inner.meta().lock.store(0, Ordering::Release);
    }
}*/
impl<C: PageTableConfig> PageTablePageMeta<C> {
    #[rustc_allow_incoherent_impl]
    pub fn new(level: PagingLevel) -> Self {
        Self {
            nr_children: PCell::new(0).0,
            stray: PCell::new(false).0,
            level,
            lock: PAtomicU8::new(0).0,
            _phantom: PhantomData,
        }
    }
}

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
        let range = if level == C::NR_LEVELS {
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
