// SPDX-License-Identifier: MPL-2.0
//! This module provides accessors to the page table entries in a node.
use vstd::prelude::*;

use vstd::simple_pptr::*;

use vstd_extra::cast_ptr;
use vstd_extra::ownership::*;

use aster_common::prelude::frame::*;
use aster_common::prelude::page_table::*;
use aster_common::prelude::*;

use core::marker::PhantomData;
use core::mem::ManuallyDrop;

use crate::{
    mm::{nr_subpage_per_huge, page_prop::PageProperty, page_table::PageTableNodeRef},
    //    sync::RcuDrop,
    //    task::atomic_mode::InAtomicMode,
};

use super::ChildRef;

verus! {

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
            Tracked(parent_owner): Tracked<&NodeEntryOwner<C>>,
    )]
    pub fn is_node(&self) -> bool
        requires
            owner.inv(),
            self.wf(owner),
            owner.relate_parent_guard_perm(parent_owner.guard_perm),
            parent_owner.inv(),
    {
        let guard = self.node.borrow(Tracked(&parent_owner.guard_perm));

        self.pte.is_present() && !self.pte.is_last(#[verus_spec(with Tracked(&parent_owner.as_node.meta_perm))] guard.level())
    }

    /// Gets a reference to the child.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner): Tracked<&EntryOwner<C>>,
            Tracked(parent_owner): Tracked<&NodeEntryOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
    )]
    pub fn to_ref(&self) -> (res: ChildRef<'rcu, C>)
        requires
            self.wf(*owner),
            owner.inv(),
            old(regions).inv(),
            owner.relate_parent_guard_perm(parent_owner.guard_perm),
            old(regions).dropped_slots.contains_key(frame_to_index(self.pte.paddr())),
            !old(regions).slots.contains_key(frame_to_index(self.pte.paddr())),
            parent_owner.inv(),
        ensures
            regions.inv(),
            res.wf(*owner)
    {
        let guard = self.node.borrow(Tracked(&parent_owner.guard_perm));

        assert(regions.slot_owners.contains_key(frame_to_index(self.pte.paddr())));

        #[verus_spec(with Tracked(&parent_owner.as_node.meta_perm))]
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
        with Tracked(owner) : Tracked<&mut EntryOwner<'rcu, C>>,
            Tracked(guard_perm): Tracked<&mut PointsTo<PageTableGuard<'rcu, C>>>,
            Tracked(slot_own) : Tracked<&MetaSlotOwner>
    )]
    pub fn protect(&mut self, op: impl FnOnce(PageProperty) -> PageProperty)
        requires
            old(owner).inv(),
            old(self).wf(*old(owner)),
            old(owner).is_node(),
            //            old(owner).node.unwrap().relate_slot_owner(slot_own),
            old(owner).relate_parent_guard_perm(*old(guard_perm)),
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

        let tracked mut node_owner = owner.node.tracked_take();

        // SAFETY:
        //  1. The index is within the bounds.
        //  2. We replace the PTE with a new one, which differs only in
        //     `PageProperty`, so the level still matches the current
        //     page table node.
        #[verus_spec(with Tracked(&mut node_owner.as_node))]
        guard.write_pte(self.idx, self.pte);

        proof {
            owner.node = Some(node_owner);
        }
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
            Tracked(owner): Tracked<&EntryOwner<'rcu, C>>,
            Tracked(new_owner): Tracked<&mut EntryOwner<'rcu, C>>,
            Tracked(parent_owner): Tracked<&mut NodeEntryOwner<'rcu, C>>
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
            old(parent_owner).guard_perm.addr() == old(self).node.addr(),
//            old(new_owner).relate_parent_guard_perm(old(parent_owner).guard_perm),
        ensures
            parent_owner.inv(),
            regions.inv(),
            self.wf(*new_owner),
            res.wf(*owner),
            new_owner == old(new_owner).replace_new_spec(parent_owner.guard_perm.addr()),
            parent_owner.guard_perm.addr() == old(parent_owner).guard_perm.addr(),
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
        let mut guard = self.node.take(Tracked(&mut parent_owner.guard_perm));

        // SAFETY:
        //  - The PTE is not referenced by other `ChildRef`s (since we have `&mut self`).
        //  - The level matches the current node.
        #[verus_spec(with Tracked(&parent_owner.as_node.meta_perm))]
        let level = guard.level();

        #[verus_spec(with Tracked(regions), Tracked(owner))]
        let old_child = Child::from_pte(self.pte, level);

        if old_child.is_none() && !new_child.is_none() {
            #[verus_spec(with Tracked(&parent_owner.as_node.meta_perm))]
            let nr_children = guard.nr_children_mut();
            let _tmp = nr_children.take(Tracked(&mut parent_owner.nr_children_perm));
            assert(_tmp < usize::MAX) by { admit() };
            nr_children.put(Tracked(&mut parent_owner.nr_children_perm), _tmp + 1);
        } else if !old_child.is_none() && new_child.is_none() {
            #[verus_spec(with Tracked(&parent_owner.as_node.meta_perm))]
            let nr_children = guard.nr_children_mut();
            let _tmp = nr_children.take(Tracked(&mut parent_owner.nr_children_perm));
            assert(_tmp > 0) by { admit() };
            nr_children.put(Tracked(&mut parent_owner.nr_children_perm), _tmp - 1);
        }

        assert(regions.slot_owners[frame_to_index(self.pte.paddr())]@.inv()) by { admit() };
        assert(new_child.wf(*new_owner)) by { admit() };

        #[verus_spec(with Tracked(new_owner))]
        let new_pte = new_child.into_pte();

        // SAFETY:
        //  1. The index is within the bounds.
        //  2. The new PTE is a valid child whose level matches the current page table node.
        //  3. The ownership of the child is passed to the page table node.
        #[verus_spec(with Tracked(&mut parent_owner.as_node))]
        guard.write_pte(self.idx, new_pte);

        self.node.put(Tracked(&mut parent_owner.guard_perm), guard);

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
    #[verus_spec(
        with Tracked(owner): Tracked<&mut OwnerSubtree<C>>,
    )]
    pub fn alloc_if_none<A: InAtomicMode>(&mut self, guard: &'rcu A) -> (res: Option<PPtr<PageTableGuard<'rcu, C>>>)
        requires
            old(owner).inv(),
            old(self).wf(old(owner).value),
        ensures
            old(owner).value.is_absent() ==> {
                &&& res is Some
                &&& owner.value.is_node()
                &&& owner.value.node.unwrap().guard_perm.addr() == res.unwrap().addr()
                &&& owner.level == old(owner).level
                &&& owner.value.guard_addr == old(owner).value.guard_addr
            },
            !old(owner).value.is_absent() ==> {
                &&& res is None
                &&& owner == old(owner)
            },
            owner.inv()
    {
        unimplemented!()

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
    #[verus_spec(
        with Tracked(owner) : Tracked<&mut OwnerSubtree<C>>
    )]
    #[verifier::external_body]
    #[verusfmt::skip]
    pub fn split_if_mapped_huge<A: InAtomicMode>(&mut self, guard: &'rcu A) -> (res: Option<PPtr<PageTableGuard<'rcu, C>>>)
        requires
            old(owner).inv(),
            old(self).wf(old(owner).value),
        ensures
            old(owner).value.is_frame() ==> {
                &&& res is Some
                &&& owner.value.is_node()
                &&& owner.value.node.unwrap().guard_perm.addr() == res.unwrap().addr()
                &&& owner.level == old(owner).level
                &&& owner.value.guard_addr == old(owner).value.guard_addr
            },
            !old(owner).value.is_frame() ==> {
                &&& res is None
                &&& owner == old(owner)
            },
            owner.inv()
    {
        unimplemented!()
/*        let guard = self.node.borrow(Tracked(owner.guard_perm.borrow()));

        let level = guard.level();

        if !(self.pte.is_last(level) && level > 1) {
            return None;
        }

        let pa = self.pte.paddr();
        let prop = self.pte.prop();

        let new_page = RcuDrop::new(PageTableNode::<C>::alloc(level - 1));

        let paddr = new_page.start_paddr();
        // SAFETY: The page table won't be dropped before the RCU grace period
        // ends, so it outlives `'rcu`.
        let pt_ref = unsafe { PageTableNodeRef::borrow_paddr(paddr) };

        // Lock before writing the PTE, so no one else can operate on it.
        let mut pt_lock_guard = pt_ref.lock(guard);

        for i in 0..nr_subpage_per_huge::<C>() {
            let small_pa = pa + i * page_size::<C>(level - 1);
            let mut entry = pt_lock_guard.entry(i);
            let old = entry.replace(Child::Frame(small_pa, level - 1, prop));
            debug_assert!(old.is_none());
        }

        self.pte = Child::PageTable(new_page).into_pte();

        // SAFETY:
        //  1. The index is within the bounds.
        //  2. The new PTE is a child in `C` and at the correct paging level.
        //  3. The ownership of the child is passed to the page table node.
        unsafe { self.node.write_pte(self.idx, self.pte) };

        Some(pt_lock_guard) */
    }

    /// Create a new entry at the node with guard.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the index is within the bounds of the node.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner): Tracked<&EntryOwner<C>>,
            Tracked(guard_perm): Tracked<&PointsTo<PageTableGuard<'rcu, C>>>,
            Tracked(slot_own): Tracked<&MetaSlotOwner>
    )]
    #[verifier::external_body]
    pub fn new_at(guard: PPtr<PageTableGuard<'rcu, C>>, idx: usize) -> (res: Self)
        requires
            owner.inv(),
            guard_perm.pptr() == guard,
        ensures
            res.wf(*owner)
    {
        let tracked node_owner = owner.node.tracked_borrow();

        // SAFETY: The index is within the bound.
        #[verus_spec(with Tracked(node_owner.as_node))]
        let pte = guard.borrow(Tracked(guard_perm)).read_pte(idx);
        Self { pte, idx, node: guard }
    }
}

} // verus!
