// SPDX-License-Identifier: MPL-2.0
//! This module provides accessors to the page table entries in a node.
use vstd::prelude::*;

use vstd::simple_pptr::{self, PPtr, PointsTo};

use vstd_extra::cast_ptr;
use vstd_extra::ownership::*;

use crate::mm::frame::meta::mapping::{frame_to_index, meta_to_frame};
use crate::mm::frame::{Frame, FrameRef};
use crate::mm::page_table::*;
use crate::mm::{Paddr, PagingConstsTrait, PagingLevel, Vaddr};
use crate::specs::arch::mm::{NR_ENTRIES, NR_LEVELS, PAGE_SIZE};
use crate::specs::arch::paging_consts::PagingConsts;
use crate::specs::mm::frame::meta_owners::MetaSlotOwner;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::task::InAtomicMode;

use core::marker::PhantomData;
use core::mem::ManuallyDrop;

use crate::{
    mm::{nr_subpage_per_huge, page_prop::PageProperty},
    //    sync::RcuDrop,
    //    task::atomic_mode::InAtomicMode,
};

use super::*;

verus! {

/// A reference to a page table node.
pub type PageTableNodeRef<'a, C> = FrameRef<'a, PageTablePageMeta<C>>;

/// A guard that holds the lock of a page table node.
#[rustc_has_incoherent_inherent_impls]
pub struct PageTableGuard<'rcu, C: PageTableConfig> {
    pub inner: PageTableNodeRef<'rcu, C>,
}

impl<'rcu, C: PageTableConfig> core::ops::Deref for PageTableGuard<'rcu, C> {
    type Target = PageTableNodeRef<'rcu, C>;

    #[verus_spec(ensures returns self.inner)]
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

#[rustc_has_incoherent_inherent_impls]
pub struct Entry<'rcu, C: PageTableConfig> {
    /// The page table entry.
    ///
    /// We store the page table entry here to optimize the number of reads from
    /// the node. We cannot hold a `&mut E` reference to the entry because that
    /// other CPUs may modify the memory location for accessed/dirty bits. Such
    /// accesses will violate the aliasing rules of Rust and cause undefined
    /// behaviors.
    pub pte: C::E,
    /// The index of the entry in the node.
    pub idx: usize,
    /// The node that contains the entry.
    pub node: PPtr<PageTableGuard<'rcu, C>>,
}

impl<'rcu, C: PageTableConfig> Entry<'rcu, C> {
    pub open spec fn new_spec(pte: C::E, idx: usize, node: PPtr<PageTableGuard<'rcu, C>>) -> Self {
        Self { pte, idx, node }
    }

    #[verifier::when_used_as_spec(new_spec)]
    pub fn new(pte: C::E, idx: usize, node: PPtr<PageTableGuard<'rcu, C>>) -> Self {
        Self { pte, idx, node }
    }
}

impl<'a, 'rcu, C: PageTableConfig> Entry<'rcu, C> {
    /// Returns if the entry does not map to anything.
    #[rustc_allow_incoherent_impl]
    #[verus_spec]
    pub fn is_none(&self) -> bool {
        !self.pte.is_present()
    }

    /// Returns if the entry maps to a page table node.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner): Tracked<EntryOwner<C>>,
            Tracked(parent_owner): Tracked<&NodeOwner<C>>,
            Tracked(guard_perm): Tracked<&GuardPerm<'rcu, C>>
    )]
    pub fn is_node(&self) -> bool
        requires
            owner.inv(),
            self.wf(owner),
            guard_perm.addr() == self.node.addr(),
            parent_owner.relate_guard_perm(*guard_perm),
            parent_owner.inv(),
    {
        let guard = self.node.borrow(Tracked(guard_perm));

        self.pte.is_present() && !self.pte.is_last(
            #[verus_spec(with Tracked(&parent_owner.meta_perm))]
            guard.level(),
        )
    }

    /// Gets a reference to the child.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner): Tracked<&EntryOwner<C>>,
            Tracked(parent_owner): Tracked<&NodeOwner<C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guard_perm): Tracked<&GuardPerm<'rcu, C>>
    )]
    pub fn to_ref(&self) -> (res: ChildRef<'rcu, C>)
        requires
            self.wf(*owner),
            owner.inv(),
            old(regions).inv(),
            guard_perm.addr() == self.node.addr(),
            guard_perm.is_init(),
            guard_perm.value().inner.inner@.ptr.addr() == parent_owner.meta_perm.addr(),
            guard_perm.value().inner.inner@.ptr.addr() == parent_owner.meta_perm.points_to.addr(),
            guard_perm.value().inner.inner@.wf(*parent_owner),
            parent_owner.meta_perm.is_init(),
            parent_owner.meta_perm.wf(),
            old(regions).dropped_slots.contains_key(frame_to_index(self.pte.paddr())),
            !old(regions).slots.contains_key(frame_to_index(self.pte.paddr())),
            parent_owner.inv(),
        ensures
            regions.inv(),
            res.wf(*owner),
    {
        let guard = self.node.borrow(Tracked(guard_perm));

        assert(regions.slot_owners.contains_key(frame_to_index(self.pte.paddr())));

        #[verus_spec(with Tracked(&parent_owner.meta_perm))]
        let level = guard.level();

        // SAFETY:
        //  - The PTE outlives the reference (since we have `&self`).
        //  - The level matches the current node.
        #[verus_spec(with Tracked(regions), Tracked(owner))]
        ChildRef::from_pte(&self.pte, level)
    }

    /// Operates on the mapping properties of the entry.
    ///
    /// It only modifies the properties if the entry is present.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner) : Tracked<&mut EntryOwner<C>>,
            Tracked(parent_owner): Tracked<&mut NodeOwner<C>>,
            Tracked(guard_perm): Tracked<&mut GuardPerm<'rcu, C>>,
            Tracked(slot_own) : Tracked<&MetaSlotOwner>
    )]
    pub fn protect(&mut self, op: impl FnOnce(PageProperty) -> PageProperty)
        requires
            old(owner).inv(),
            old(self).wf(*old(owner)),
            old(owner).is_node(),
            old(self).node.addr() == old(guard_perm).addr(),
            old(parent_owner).relate_guard_perm(*old(guard_perm)),
            op.requires((old(self).pte.prop(),)),
    {
        if !self.pte.is_present() {
            return ;
        }
        let prop = self.pte.prop();
        let new_prop = op(prop);

        /* if prop == new_prop {
            return;
        }*/

        self.pte.set_prop(new_prop);

        let mut guard = self.node.take(Tracked(guard_perm));

        // SAFETY:
        //  1. The index is within the bounds.
        //  2. We replace the PTE with a new one, which differs only in
        //     `PageProperty`, so the level still matches the current
        //     page table node.
        #[verus_spec(with Tracked(parent_owner))]
        guard.write_pte(self.idx, self.pte);

        self.node.put(Tracked(guard_perm), guard);
    }

    /// Replaces the entry with a new child.
    ///
    /// The old child is returned.
    ///
    /// # Panics
    ///
    /// The method panics if the level of the new child does not match the
    /// current node.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(regions) : Tracked<&mut MetaRegionOwners>,
            Tracked(owner): Tracked<&EntryOwner<C>>,
            Tracked(new_owner): Tracked<&mut EntryOwner<C>>,
            Tracked(parent_owner): Tracked<&mut NodeOwner<C>>,
            Tracked(guard_perm): Tracked<&mut GuardPerm<'rcu, C>>
    )]
    pub fn replace(&mut self, new_child: Child<C>) -> (res: Child<C>)
        requires
            old(self).wf(*owner),
            owner.inv(),
            old(new_owner).inv(),
            old(parent_owner).inv(),
            old(regions).inv(),
            !old(regions).slots.contains_key(frame_to_index(old(self).pte.paddr())),
            old(regions).dropped_slots.contains_key(frame_to_index(old(self).pte.paddr())),
            old(guard_perm).addr() == old(self).node.addr(),
            old(guard_perm).is_init(),
            old(guard_perm).value().inner.inner@.ptr.addr() == old(parent_owner).meta_perm.addr(),
            old(guard_perm).value().inner.inner@.ptr.addr() == old(parent_owner).meta_perm.points_to.addr(),
            old(guard_perm).value().inner.inner@.wf(*old(parent_owner)),
            old(parent_owner).meta_perm.is_init(),
            old(parent_owner).meta_perm.wf(),

        ensures
            parent_owner.inv(),
            regions.inv(),
            self.wf(*new_owner),
            res.wf(*owner),
    {
        /* match &new_child {
            Child::PageTable(node) => {
                assert_eq!(node.level(), self.node.level() - 1);
            }
            Child::Frame(_, level, _) => {
                assert_eq!(*level, self.node.level());
            }
            Child::None => {}
        }*/
        let mut guard = self.node.take(Tracked(guard_perm));

        // SAFETY:
        //  - The PTE is not referenced by other `ChildRef`s (since we have `&mut self`).
        //  - The level matches the current node.
        #[verus_spec(with Tracked(&parent_owner.meta_perm))]
        let level = guard.level();

        #[verus_spec(with Tracked(regions), Tracked(owner))]
        let old_child = Child::from_pte(self.pte, level);

        if old_child.is_none() && !new_child.is_none() {
            #[verus_spec(with Tracked(&parent_owner.meta_perm))]
            let nr_children = guard.nr_children_mut();
            let _tmp = nr_children.take(Tracked(&mut parent_owner.meta_own.nr_children));
            assert(_tmp < usize::MAX) by { admit() };
            nr_children.put(Tracked(&mut parent_owner.meta_own.nr_children), _tmp + 1);
        } else if !old_child.is_none() && new_child.is_none() {
            #[verus_spec(with Tracked(&parent_owner.meta_perm))]
            let nr_children = guard.nr_children_mut();
            let _tmp = nr_children.take(Tracked(&mut parent_owner.meta_own.nr_children));
            assert(_tmp > 0) by { admit() };
            nr_children.put(Tracked(&mut parent_owner.meta_own.nr_children), _tmp - 1);
        }
        assert(regions.slot_owners[frame_to_index(self.pte.paddr())]@.inv()) by { admit() };
        assert(new_child.wf(*new_owner)) by { admit() };

        #[verus_spec(with Tracked(new_owner), Tracked(regions))]
        let new_pte = new_child.into_pte();

        // SAFETY:
        //  1. The index is within the bounds.
        //  2. The new PTE is a valid child whose level matches the current page table node.
        //  3. The ownership of the child is passed to the page table node.
        #[verus_spec(with Tracked(parent_owner))]
        guard.write_pte(self.idx, new_pte);

        self.node.put(Tracked(guard_perm), guard);

        self.pte = new_pte;

        assert(regions.inv()) by { admit() };
        assert(parent_owner.inv()) by { admit() };
        assert(self.wf(*new_owner)) by { admit() };
        assert(owner.inv()) by { admit() };
        assert(old_child.wf(*owner)) by { admit() };

        //        proof {
        //           new_owner.base_addr = parent_owner.guard_perm.mem_contents().value().inner.inner.0.ptr.addr();
        //       }

        old_child
    }

    /// Allocates a new child page table node and replaces the entry with it.
    ///
    /// If the old entry is not none, the operation will fail and return `None`.
    /// Otherwise, the lock guard of the new child page table node is returned.
    #[verifier::external_body]
    #[rustc_allow_incoherent_impl]
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&mut OwnerSubtree<C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
            -> guard_perm: Tracked<Option<GuardPerm<'rcu, C>>>
        requires
            old(owner).inv(),
            old(self).wf(old(owner).value),
            old(regions).inv(),
        ensures
            old(owner).value.is_absent() ==> {
                &&& res is Some
                &&& owner.value.is_node()
                &&& guard_perm@ is Some
                &&& guard_perm@.unwrap().addr() == res.unwrap().addr()
                &&& owner.level == old(owner).level
            },
            !old(owner).value.is_absent() ==> {
                &&& res is None
                &&& owner == old(owner)
            },
            owner.inv(),
            regions.inv(),
    )]
    pub fn alloc_if_none<A: InAtomicMode>(&mut self, guard: &'rcu A) -> (res: Option<PPtr<PageTableGuard<'rcu, C>>>)
    {
        proof_with!{|= Tracked(None)};
        None

        /*        if !(self.is_none() && self.node.level() > 1) {
            return None;
        }

        let level = self.node.level();
        let new_page = RcuDrop::new(PageTableNode::<C>::alloc(level - 1));

        let paddr = new_page.start_paddr();
        // SAFETY: The page table won't be dropped before the RCU grace period
        // ends, so it outlives `'rcu`.
        let pt_ref = unsafe { PageTableNodeRef::borrow_paddr(paddr) };

        // Lock before writing the PTE, so no one else can operate on it.
        let pt_lock_guard = pt_ref.lock(guard);

        self.pte = Child::PageTable(new_page).into_pte();

        // SAFETY:
        //  1. The index is within the bounds.
        //  2. The new PTE is a child in `C` and at the correct paging level.
        //  3. The ownership of the child is passed to the page table node.
        unsafe { self.node.write_pte(self.idx, self.pte) };

        *self.node.nr_children_mut() += 1;

        Some(pt_lock_guard) */

    }

    /// Splits the entry to smaller pages if it maps to a huge page.
    ///
    /// If the entry does map to a huge page, it is split into smaller pages
    /// mapped by a child page table node. The new child page table node
    /// is returned.
    ///
    /// If the entry does not map to a untracked huge page, the method returns
    /// `None`.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(res =>
        with Tracked(owner) : Tracked<&mut OwnerSubtree<C>>,
            Tracked(parent_owner): Tracked<&mut NodeOwner<C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>,
            Tracked(guard_perm): Tracked<&mut GuardPerm<'rcu, C>>
        requires
            old(regions).inv(),
            old(owner).inv(),
            old(self).wf(old(owner).value),
            old(self).node.addr() == old(guard_perm).addr(),
            old(guard_perm).is_init(),
            old(guard_perm).value().inner.inner@.ptr.addr() == old(parent_owner).meta_perm.addr(),
            old(guard_perm).value().inner.inner@.ptr.addr() == old(parent_owner).meta_perm.points_to.addr(),
            old(guard_perm).value().inner.inner@.wf(*old(parent_owner)),
            old(parent_owner).meta_perm.is_init(),
            old(parent_owner).meta_perm.wf(),
        ensures
            old(owner).value.is_frame() ==> {
                &&& res is Some
                &&& owner.value.is_node()
                &&& owner.level == old(owner).level
                &&& parent_owner.relate_guard_perm(*guard_perm)
                &&& guard_perm.addr() == res.unwrap().addr()
            },
            !old(owner).value.is_frame() ==> {
                &&& res is None
                &&& owner == old(owner)
            },
            owner.inv(),
            regions.inv(),
            parent_owner.inv(),
    )]
    #[verifier::external_body]
    pub fn split_if_mapped_huge<A: InAtomicMode>(&mut self, guard: &'rcu A) -> (res: Option<PPtr<PageTableGuard<'rcu, C>>>)
    {
        let mut node_guard = self.node.take(Tracked(guard_perm));

        #[verus_spec(with Tracked(&mut parent_owner.meta_perm))]
        let level = node_guard.level();

        if !(self.pte.is_last(level) && level > 1) {
            assert(!owner.value.is_frame()) by { admit() };
            return None;
        }
        //        #[verus_spec(with Tracked(&mut parent_owner.as_node.meta_perm))]

        let pa = self.pte.paddr();
        let prop = self.pte.prop();

        let new_page =   /*RcuDrop::new(*/
        PageTableNode::<C>::alloc(level - 1)  /*)*/
        ;

        assert(new_page.ptr.addr() == parent_owner.meta_perm.points_to.addr())
            by { admit() };
        assert(FRAME_METADATA_RANGE().start <= new_page.ptr.addr() < FRAME_METADATA_RANGE().end)
            by { admit() };
        assert(new_page.ptr.addr() % META_SLOT_SIZE() == 0) by { admit() };

        #[verus_spec(with Tracked(&mut parent_owner.meta_perm.points_to))]
        let paddr = new_page.start_paddr();

        assert(paddr < MAX_PADDR()) by { admit() };
        assert(!old(regions).slots.contains_key(frame_to_index(paddr))) by { admit() };
        assert(old(regions).dropped_slots.contains_key(frame_to_index(paddr))) by { admit() };

        // SAFETY: The page table won't be dropped before the RCU grace period
        // ends, so it outlives `'rcu`.
        let pt_ref = PageTableNodeRef::borrow_paddr(paddr);

        // Lock before writing the PTE, so no one else can operate on it.
        let mut pt_lock_guard = pt_ref.lock(guard);

        assert(1 < level < NR_LEVELS()) by { admit() };

        for i in 0..nr_subpage_per_huge::<C>()
            invariant
                1 < level < NR_LEVELS(),
        {
            assert(pa + i * page_size((level - 1) as u8) < MAX_PADDR()) by { admit() };
            let small_pa = pa + i * page_size(level - 1);
            //            #[verus_spec(with Tracked())]
            let mut entry = PageTableGuard::entry(pt_lock_guard, i);
            let old = entry.replace(Child::Frame(small_pa, level - 1, prop));
            //debug_assert!(old.is_none());
        }

        self.pte = Child::PageTable(new_page).into_pte();

        let tracked mut node_owner = owner.value.node.tracked_take();

        // SAFETY:
        //  1. The index is within the bounds.
        //  2. The new PTE is a child in `C` and at the correct paging level.
        //  3. The ownership of the child is passed to the page table node.
        #[verus_spec(with Tracked(&mut node_owner))]
        node_guard.write_pte(self.idx, self.pte);

        proof {
            owner.value.node = Some(node_owner);
            admit();
        }

        self.node.put(Tracked(guard_perm), node_guard);

        Some(pt_lock_guard)
    }

    /// Create a new entry at the node with guard.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the index is within the bounds of the node.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner): Tracked<&OwnerSubtree<C>>,
            Tracked(guard_perm): Tracked<&mut PointsTo<PageTableGuard<'rcu, C>>>
    )]
    #[verifier::external_body]
    pub fn new_at(guard: PPtr<PageTableGuard<'rcu, C>>, idx: usize) -> (res: Self)
        requires
            owner.inv(),
            owner.value.is_node(),
            old(guard_perm).pptr() == guard,
        ensures
            res.wf(owner.children[idx as int].unwrap().value),
    {
        // SAFETY: The index is within the bound.
        #[verus_spec(with Tracked(owner.value.node.tracked_borrow()))]
        let pte = guard.borrow(Tracked(guard_perm)).read_pte(idx);
        Self { pte, idx, node: guard }
    }
}

} // verus!
