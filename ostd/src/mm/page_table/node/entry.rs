// SPDX-License-Identifier: MPL-2.0
//! This module provides accessors to the page table entries in a node.
use vstd::prelude::*;

use vstd::simple_pptr::{self, PPtr, PointsTo};

use vstd_extra::cast_ptr;
use vstd_extra::drop_tracking::ManuallyDrop;
use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;

use crate::mm::frame::meta::mapping::{frame_to_index, frame_to_meta, meta_to_frame};
use crate::mm::frame::{Frame, FrameRef};
use crate::mm::page_table::*;
use crate::mm::{Paddr, PagingConstsTrait, PagingLevel, Vaddr};
use crate::specs::arch::mm::{NR_ENTRIES, NR_LEVELS, PAGE_SIZE};
use crate::specs::arch::paging_consts::PagingConsts;
use crate::specs::mm::frame::meta_owners::{MetaSlotOwner, REF_COUNT_UNUSED};
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::page_table::{PageTableOwner, INC_LEVELS};
use crate::specs::task::InAtomicMode;

use core::marker::PhantomData;
use core::ops::Deref;

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
pub struct PageTableGuard<'rcu, C: PageTableConfig> {
    pub inner: PageTableNodeRef<'rcu, C>,
}

impl<'rcu, C: PageTableConfig> Deref for PageTableGuard<'rcu, C> {
    type Target = PageTableNodeRef<'rcu, C>;

    #[verus_spec(ensures returns self.inner)]
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

pub struct Entry<'rcu, C: PageTableConfig> {
    /// The page table entry.
    ///
    /// We store the page table entry here to optimize the number of reads from
    /// the node. We cannot hold a `&mut E` reference to the entry because that
    /// other CPUs may modify the memory location for accessed/dirty bits. Such
    /// accesses will violate the aliasing rules of Rust and cause undefined
    /// behaviors.
    ///
    /// # Verification Design
    /// The concrete value of a PTE is specific to the architecture and the page table configuration,
    /// represented by the type `C::E`. We represent its value as an abstract [`EntryOwner`], which is
    /// connected to the concrete value by `match_pte`. The `EntryOwner` is well-formed with respect to
    /// `Entry` if it is related to the concrete value by `match_pte`.
    ///
    /// An `Entry` can be thought of as a mutable handle to the concrete value of the PTE.
    /// The `node` field points (with a level of indirection) to the node that contains the entry,
    /// `index` provides the offset, and the `pte` is current value. Only one `Entry` can exist for
    /// a given node at any given time.
    pub pte: C::E,
    /// The index of the entry in the node.
    pub idx: usize,
    /// The node that contains the entry. In the original Rust this is a `&mut PageTableGuard`; the PPtr
    /// type is handling the mutable reference because Verus does not yet support storing such a reference
    /// in a struct.
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

#[verus_verify]
impl<'a, 'rcu, C: PageTableConfig> Entry<'rcu, C> {
    /// Returns if the entry does not map to anything.
    #[verus_spec(r =>
        with Tracked(owner): Tracked<&EntryOwner<C>>,
        requires
            self.wf(*owner),
            owner.inv(),
        returns owner.is_absent(),
    )]
    pub(in crate::mm) fn is_none(&self) -> bool {
        !self.pte.is_present()
    }

    /// Returns if the entry maps to a page table node.
    #[verus_spec(
        with Tracked(owner): Tracked<EntryOwner<C>>,
            Tracked(parent_owner): Tracked<&NodeOwner<C>>,
            Tracked(guard_perm): Tracked<&GuardPerm<'rcu, C>>
    )]
    pub(in crate::mm) fn is_node(&self) -> bool
        requires
            owner.inv(),
            self.wf(owner),
            guard_perm.addr() == self.node.addr(),
            parent_owner.relate_guard_perm(*guard_perm),
            parent_owner.inv(),
            parent_owner.level == owner.parent_level,
        returns
            owner.is_node(),
    {
        let guard = self.node.borrow(Tracked(guard_perm));

        self.pte.is_present() && !self.pte.is_last(
            #[verus_spec(with Tracked(&parent_owner.meta_perm))]
            guard.level(),
        )
    }

    /// Gets a reference to the child.
    #[verus_spec(
        with Tracked(owner): Tracked<&EntryOwner<C>>,
            Tracked(parent_owner): Tracked<&NodeOwner<C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guard_perm): Tracked<&GuardPerm<'rcu, C>>
    )]
    pub(in crate::mm) fn to_ref(&self) -> (res: ChildRef<'rcu, C>)
        requires
            self.invariants(*owner, *old(regions)),
            self.node_matching(*owner, *parent_owner, *guard_perm),
            !owner.in_scope,
        ensures
            res.invariants(*owner, *final(regions)),
            final(regions).slot_owners =~= old(regions).slot_owners,
            forall |k: usize| old(regions).slots.contains_key(k) ==> #[trigger] final(regions).slots.contains_key(k),
            forall |k: usize| old(regions).slots.contains_key(k) ==> old(regions).slots[k] == #[trigger] final(regions).slots[k],
            final(regions).inv(),
    {
        let guard = self.node.borrow(Tracked(guard_perm));

        #[verus_spec(with Tracked(&parent_owner.meta_perm))]
        let level = guard.level();

        // SAFETY:
        //  - The PTE outlives the reference (since we have `&self`).
        //  - The level matches the current node.
        #[verus_spec(with Tracked(regions), Tracked(owner))]
        let res = ChildRef::from_pte(&self.pte, level);

        res
    }

    /// Operates on the mapping properties of the entry.
    ///
    /// It only modifies the properties if the entry is present.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: The entry must satisfy the relevant safety invariants.
    /// - **Safety**: The caller must provide a valid guard permission matching `guard_perm`, and it must be guarding the
    /// correct parent node.
    /// - **Safety**: The entry must be a frame.
    /// ## Postconditions
    /// - **Safety Invariants**: The entry continues to satisfy the relevant safety invariants.
    /// - **Safety**: The guard permission is preserved.
    /// - **Correctness**: The entry's permissions are updated by `op`
    /// ## Safety
    /// - The entry is updated in place, only changing its properties, so the metadata is unchanged.
    /// That's why we don't take a `MetaRegionOwners` argument. It means that all invariants will be preserved.
    #[verus_spec(
        with Tracked(owner) : Tracked<&mut EntryOwner<C>>,
            Tracked(parent_owner): Tracked<&mut NodeOwner<C>>,
            Tracked(guard_perm): Tracked<&mut GuardPerm<'rcu, C>>,
    )]
    pub(in crate::mm) fn protect(&mut self, op: impl FnOnce(PageProperty) -> PageProperty)
        requires
            old(owner).inv(),
            old(self).wf(*old(owner)),
            old(self).node_matching(*old(owner), *old(parent_owner), *old(guard_perm)),
            op.requires((old(self).pte.prop(),)),
            old(owner).is_frame(),
        ensures
            final(owner).inv(),
            final(self).wf(*final(owner)),
            final(self).node_matching(*final(owner), *final(parent_owner), *final(guard_perm)),
            final(self).parent_perms_preserved(*old(parent_owner), *final(parent_owner), *old(guard_perm), *final(guard_perm)),
            final(owner).is_frame(),
            final(owner).frame.unwrap().mapped_pa == old(owner).frame.unwrap().mapped_pa,
            final(owner).path == old(owner).path,
            final(owner).parent_level == old(owner).parent_level,
            final(owner).in_scope == old(owner).in_scope,
            final(self).idx == old(self).idx,
            old(self).pte.is_present() ==> op.ensures((old(owner).frame.unwrap().prop,), final(owner).frame.unwrap().prop),
    {
        let ghost pte0 = self.pte;

        if !self.pte.is_present() {
            return ;
        }
        let prop = self.pte.prop();
        let new_prop = op(prop);

        /*if prop == new_prop {
            return;
        }*/

        proof {
            self.pte.set_prop_properties(new_prop);
        }
        self.pte.set_prop(new_prop);

        let mut guard = self.node.take(Tracked(guard_perm));

        // SAFETY:
        //  1. The index is within the bounds.
        //  2. We replace the PTE with a new one, which differs only in
        //     `PageProperty`, so the level still matches the current
        //     page table node.
        #[verus_spec(with Tracked(parent_owner))]
        guard.write_pte(self.idx, self.pte);

        proof {
            let tracked mut frame_owner = owner.frame.tracked_take();
            frame_owner.prop = new_prop;
            owner.frame = Some(frame_owner);
        }
        assert(owner.match_pte(self.pte, owner.parent_level));

        self.node.put(Tracked(guard_perm), guard);
    }

    /// Replaces the entry with a new child.
    ///
    /// The old child is returned.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: Both old and new owners must satisfy the respective safety invariants for an [Entry](Entry::invariants)
    /// and a [Child](Child::invariants).
    /// - **Safety**: The caller must provide valid owners for all objects, and for the parent node where the entry
    /// is being replaced. The parent node must have a valid guard permission.
    /// - **Correctness**: The new child must be compatible with the old, for instance by having the same level.
    /// ## Postconditions
    /// - **Safety Invariants**: The old and new owners will satisfy the safety invariants for an [Entry](Entry::invariants)
    /// and a [Child](Child::invariants), but they have changed positions.
    /// - **Safety**: Safety properties that hold across the page table's tree structure are preserved
    /// everywhere except for the entry being replaced.
    /// - **Correctness**: The entry will match the argument, and the returned child will match the entry that was replaced.
    /// ## Safety
    /// - The invariants ensure that the entry is appropriately aligned and its index is within bounds.
    /// - The transformation from child to entry ensures that the tree now owns the updated entry.
    #[verus_spec(
        with Tracked(regions) : Tracked<&mut MetaRegionOwners>,
            Tracked(owner): Tracked<&mut EntryOwner<C>>,
            Tracked(new_owner): Tracked<&mut EntryOwner<C>>,
            Tracked(parent_owner): Tracked<&mut NodeOwner<C>>,
            Tracked(guard_perm): Tracked<&mut GuardPerm<'rcu, C>>,
            Ghost(write_path): Ghost<bool>
    )]
    pub(in crate::mm) fn replace(&mut self, new_child: Child<C>) -> (res: Child<C>)
        requires
            old(self).invariants(*old(owner), *old(regions)),
            new_child.invariants(*old(new_owner), *old(regions)),
            old(self).node_matching(*old(owner), *old(parent_owner), *old(guard_perm)),
            old(self).new_owner_compatible(new_child, *old(owner), *old(new_owner), *old(regions)),
            !old(owner).in_scope,
            Self::replace_panic_condition(*old(parent_owner), *old(new_owner)),
        ensures
            final(self).invariants(*final(new_owner), *final(regions)),
            res.invariants(*final(owner), *final(regions)),
            final(self).node_matching(*final(new_owner), *final(parent_owner), *final(guard_perm)),
            final(self).idx == old(self).idx,
            *final(owner) == old(owner).from_pte_owner_spec(),
            *final(new_owner) == old(new_owner).into_pte_owner_spec(),
            Self::metaregion_sound_neq_preserved(*old(owner), *final(new_owner), *old(regions), *final(regions)),
            // When the new child is not a node and path_if_in_pt is not written:
            // metaregion_sound is preserved with only paddr_neq(old_child).
            (!final(new_owner).is_node() && !write_path) ==>
                Self::metaregion_sound_neq_old_preserved(*old(owner), *old(regions), *final(regions)),
            // When BOTH old and new are not nodes AND path_if_in_pt was None at new_idx
            // (from item_not_mapped), metaregion_sound is fully preserved:
            // no node had metaregion_sound at new_idx (requires path_if_in_pt == Some),
            // and frames don't check path_if_in_pt.
            // When path_if_in_pt is NOT written (!write_path && !is_node): metaregion_sound fully preserved.
            (!old(owner).is_node() && !final(new_owner).is_node() && !write_path) ==>
                Self::metaregion_sound_preserved(*old(regions), *final(regions)),
            // path_tracked_pred for new owner when path_if_in_pt is written (node or write_path).
            (final(new_owner).is_node() || write_path) && !final(new_owner).is_absent() ==>
                PageTableOwner::<C>::path_tracked_pred(*final(regions))(*final(new_owner), final(new_owner).path),
            final(self).parent_perms_preserved(*old(parent_owner), *final(parent_owner), *final(guard_perm), *old(guard_perm)),
            // path_if_in_pt changes when new owner is a node OR write_path; preserved otherwise.
            forall|idx: usize| #![trigger final(regions).slot_owners[idx].path_if_in_pt]
                (!(final(new_owner).is_node() || write_path) || final(new_owner).is_absent()
                    || idx != frame_to_index(final(new_owner).meta_slot_paddr().unwrap()))
                    ==> final(regions).slot_owners[idx].path_if_in_pt == old(regions).slot_owners[idx].path_if_in_pt,
            // slots: monotonic (from_pte may add; into_pte doesn't remove for non-nodes).
            forall|k: usize| old(regions).slots.contains_key(k)
                ==> #[trigger] final(regions).slots.contains_key(k),
            // When both old and new are not nodes: from_pte/into_pte are identity.
            (!old(owner).is_node() && !final(new_owner).is_node()) ==> {
                &&& final(regions).slots == old(regions).slots
                &&& forall|i: usize| #![trigger final(regions).slot_owners[i]]
                    (!(final(new_owner).is_node() || write_path) || final(new_owner).is_absent()
                        || i != frame_to_index(final(new_owner).meta_slot_paddr().unwrap()))
                    ==> final(regions).slot_owners[i] == old(regions).slot_owners[i]
            },
            // When old child is absent and new child is not a node: slots values unchanged.
            (old(owner).is_absent() && !final(new_owner).is_node()) ==>
                forall|k: usize| old(regions).slots.contains_key(k)
                    ==> old(regions).slots[k] == #[trigger] final(regions).slots[k],
    {
        let ghost new_idx = frame_to_index(new_owner.meta_slot_paddr().unwrap());
        let ghost old_idx = frame_to_index(owner.meta_slot_paddr().unwrap());

        let mut guard = self.node.take(Tracked(guard_perm));

        /*
        match &new_child {
            Child::PageTable(node) => {
                assert(node.level() == guard.level() - 1);
            }
            Child::Frame(_, level, _) => {
                assert(*level == guard.level());
            }
            Child::None => {}
        }
        */

        // SAFETY:
        //  - The PTE is not referenced by other `ChildRef`s (since we have `&mut self`).
        //  - The level matches the current node.
        #[verus_spec(with Tracked(&parent_owner.meta_perm))]
        let level = guard.level();

        #[verus_spec(with Tracked(regions), Tracked(owner))]
        let old_child = Child::from_pte(self.pte, level);

        let ghost regions_after_from = *regions;

        assert(new_owner.is_node() ==> regions.slots.contains_key(frame_to_index(new_owner.meta_slot_paddr().unwrap())));

        if old_child.is_none() && !new_child.is_none() {
            #[verus_spec(with Tracked(&parent_owner.meta_perm))]
            let nr_children = guard.nr_children_mut();
            let _tmp = nr_children.read(Tracked(&parent_owner.meta_own.nr_children));
            assume(_tmp < NR_ENTRIES);
            nr_children.write(Tracked(&mut parent_owner.meta_own.nr_children), _tmp + 1);
        } else if !old_child.is_none() && new_child.is_none() {
            #[verus_spec(with Tracked(&parent_owner.meta_perm))]
            let nr_children = guard.nr_children_mut();
            let _tmp = nr_children.read(Tracked(&parent_owner.meta_own.nr_children));
            assume(_tmp > 0);
            nr_children.write(Tracked(&mut parent_owner.meta_own.nr_children), _tmp - 1);
        }
        proof {
            assert(owner.metaregion_sound(*regions));
        }

        #[verus_spec(with Tracked(new_owner), Tracked(regions))]
        let new_pte = new_child.into_pte();

        let ghost regions_after_into = *regions;

        proof {
            assert(owner.metaregion_sound(*regions));
        }

        // SAFETY:
        //  1. The index is within the bounds.
        //  2. The new PTE is a valid child whose level matches the current page table node.
        //  3. The ownership of the child is passed to the page table node.
        #[verus_spec(with Tracked(parent_owner))]
        guard.write_pte(self.idx, new_pte);

        self.node.put(Tracked(guard_perm), guard);

        self.pte = new_pte;

        proof {
            if new_owner.is_node() || (write_path && !new_owner.is_absent()) {
                let paddr = new_owner.meta_slot_paddr().unwrap();
                regions.inv_implies_correct_addr(paddr);

                let tracked mut new_meta_slot = regions.slot_owners.tracked_remove(new_idx);
                new_meta_slot.path_if_in_pt = Some(new_owner.get_path());
                regions.slot_owners.tracked_insert(new_idx, new_meta_slot);
            }
            owner.in_scope = true;
        }

        assert(Self::metaregion_sound_neq_preserved(*old(owner), *new_owner, *old(regions), *regions));

        proof {
            // When both old and new are not nodes and path_if_in_pt is not written:
            // from_pte/into_pte are identity, no slot_owners change. Regions unchanged.
            if !old(owner).is_node() && !new_owner.is_node() && !write_path {
                // slot_owners and slots are identical → metaregion_sound trivially preserved.
            }
        }

        proof {
            if new_owner.is_node() || new_owner.is_frame() {
                let paddr = new_owner.meta_slot_paddr().unwrap();
                regions.inv_implies_correct_addr(paddr);
            }
            // Sub-page validity for new_owner (if a huge frame): preserved because
            // replace only modifies slots/path_if_in_pt at new_owner's own slot, not
            // at sub-page slots (which have different indices for j > 0).
            if new_owner.is_frame() && new_owner.parent_level > 1 {
                assert(new_owner.frame_sub_pages_valid(*regions));
            }
            if owner.is_frame() && owner.parent_level > 1 {
                assert(owner.frame_sub_pages_valid(*regions));
            }
        }

        old_child
    }

    /// Allocates a new child page table node and replaces the entry with it.
    ///
    /// If the old entry is not none, the operation will fail and return `None`.
    /// Otherwise, the lock guard of the new child page table node is returned.
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: The old node's root must satisfy the safety invariants for an [Entry](Entry::invariants)
    /// and the caller must provide its parent node owner.
    /// ## Postconditions
    /// - **Safety Invariants**: If a new node is allocated, it will satisfy the safety invariants.
    /// - **Safety**: If a new node is allocated, all other nodes have their invariants preserved.
    /// - **Correctness**: A new node is allocated if and only if the old node is absent.
    /// - **Correctness**: If the old node is present, the function retuns `None` and the state is unchanged.
    /// ## Safety
    /// - The invariants ensure that the entry is appropriately aligned and its index is within bounds.
    /// - The invariants of the entire page table are preserved in both cases.
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&mut OwnerSubtree<C>>,
            Tracked(parent_owner): Tracked<&mut NodeOwner<C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>,
            Tracked(parent_guard_perm): Tracked<&mut GuardPerm<'rcu, C>>
            -> guard_perm: Tracked<Option<GuardPerm<'rcu, C>>>
        requires
            old(self).invariants(old(owner).value, *old(regions)),
            old(owner).inv(),
            old(self).node_matching(old(owner).value, *old(parent_owner), *old(parent_guard_perm)),
            old(owner).level < INC_LEVELS - 1,
        ensures
            final(self).invariants(final(owner).value, *final(regions)),
            final(self).parent_perms_preserved(*old(parent_owner), *final(parent_owner), *old(parent_guard_perm), *final(parent_guard_perm)),
            final(self).idx == old(self).idx,
            old(owner).value.is_absent() && old(parent_owner).level > 1 ==> {
                // node_matching preserved: parent_owner still matches the child after allocation.
                &&& final(self).node_matching(final(owner).value, *final(parent_owner), *final(parent_guard_perm))
                // OwnerSubtree inv (recursive tree invariant, not just value.inv()).
                &&& final(owner).inv()
                // After into_pte, the entry has in_scope == false.
                &&& !final(owner).value.in_scope
            },
            old(owner).value.is_absent() && old(parent_owner).level > 1 ==> {
                &&& res is Some
                &&& final(owner).value.is_node()
                &&& guard_perm@ is Some
                &&& guard_perm@.unwrap().addr() == res.unwrap().addr()
                &&& final(owner).level == old(owner).level
                &&& final(owner).value.parent_level == old(owner).value.parent_level
                &&& final(owner).value.node.unwrap().relate_guard_perm(guard_perm@.unwrap())
                &&& final(guards).lock_held(final(owner).value.node.unwrap().meta_perm.addr())
                &&& final(owner).value.path == old(owner).value.path
                &&& final(owner).value.metaregion_sound(*final(regions))
                &&& OwnerSubtree::implies(
                    CursorOwner::<'rcu, C>::node_unlocked(*old(guards)),
                    CursorOwner::<'rcu, C>::node_unlocked_except(*final(guards), final(owner).value.node.unwrap().meta_perm.addr()))
                &&& Self::metaregion_sound_neq_preserved(old(owner).value, final(owner).value, *old(regions), *final(regions))
                &&& Self::path_tracked_pred_preserved(*old(regions), *final(regions))
                &&& old(regions).slots.contains_key(frame_to_index(final(owner).value.meta_slot_paddr().unwrap()))
                &&& final(owner).tree_predicate_map(final(owner).value.path,
                    CursorOwner::<'rcu, C>::node_unlocked_except(*final(guards), final(owner).value.node.unwrap().meta_perm.addr()))
                &&& final(owner).tree_predicate_map(final(owner).value.path, PageTableOwner::<C>::metaregion_sound_pred(*final(regions)))
                &&& final(owner).tree_predicate_map(final(owner).value.path, PageTableOwner::<C>::path_tracked_pred(*final(regions)))
                &&& PageTableOwner(*final(owner)).view_rec(final(owner).value.path) =~= set![]
                // All children of the newly allocated node are absent (empty PT node).
                &&& forall|i: int| 0 <= i < NR_ENTRIES ==>
                    #[trigger] final(owner).children[i] is Some && final(owner).children[i].unwrap().value.is_absent()
                // slot_owners unchanged for all indices except the new PT node's index.
                &&& forall|i: usize| i != frame_to_index(final(owner).value.meta_slot_paddr().unwrap()) ==>
                    (#[trigger] final(regions).slot_owners[i]) == old(regions).slot_owners[i]
                // slots keys: the new PT node was removed then re-inserted, so all old keys preserved.
                &&& forall|i: usize| old(regions).slots.contains_key(i)
                    ==> (#[trigger] final(regions).slots.contains_key(i))
                // The new PT node's ref_count is not UNUSED (was set to 1 by get_from_unused).
                &&& final(regions).slot_owners[frame_to_index(final(owner).value.meta_slot_paddr().unwrap())]
                    .inner_perms.ref_count.value() != REF_COUNT_UNUSED
                // The allocated slot had ref_count == UNUSED before allocation (from get_from_unused).
                &&& old(regions).slot_owners[frame_to_index(final(owner).value.meta_slot_paddr().unwrap())]
                    .inner_perms.ref_count.value() == REF_COUNT_UNUSED
            },
            !old(owner).value.is_absent() ==> {
                &&& res is None
                &&& *final(owner) == *old(owner)
            },
            forall |i: usize| old(guards).lock_held(i) ==> final(guards).lock_held(i),
            forall |i: usize| old(guards).unlocked(i) && i != final(owner).value.node.unwrap().meta_perm.addr() ==> final(guards).unlocked(i),
    )]
    pub(in crate::mm) fn alloc_if_none<A: InAtomicMode>(&mut self, guard: &'rcu A)
    -> (res: Option<PPtr<PageTableGuard<'rcu, C>>>) {
        let entry_is_present = self.pte.is_present();

        let mut parent_guard = self.node.take(Tracked(parent_guard_perm));

        #[verus_spec(with Tracked(&parent_owner.meta_perm))]
        let level = parent_guard.level();

        if entry_is_present || level <= 1 {
            self.node.put(Tracked(parent_guard_perm), parent_guard);

            proof_with!{|= Tracked(None)}
            None
        } else {
            let tracked old_path = owner.value.get_path();

            proof_decl! {
                let tracked mut new_node_owner: Tracked<OwnerSubtree<C>>;
            }

            #[verus_spec(with Tracked(parent_owner), Tracked(regions), Tracked(guards), Ghost(self.idx) => Tracked(new_node_owner))]
            let new_page = PageTableNode::<C>::alloc(level - 1);

            proof {
                let pte = C::E::new_pt_spec(meta_to_frame(new_node_owner.value.node.unwrap().meta_perm.addr()));
                old(parent_owner).set_children_perm_axiom(self.idx, pte);
                C::E::new_properties();
                assert(!pte.is_last_spec(level as PagingLevel));
            }

            #[verus_spec(with Tracked(&new_node_owner.value.node.tracked_borrow().meta_perm.points_to))]
            let paddr = new_page.start_paddr();

            assert(new_node_owner.value.metaregion_sound(*regions));

            #[verus_spec(with Tracked(&mut new_node_owner.value), Tracked(regions))]
            let new_pte = Child::PageTable(new_page).into_pte();
            self.pte = new_pte;

            proof {
                assert(new_node_owner.value.pte_invariants(self.pte, *regions));
                assert(new_node_owner.value.match_pte(self.pte, new_node_owner.value.parent_level));
                broadcast use crate::mm::frame::meta::mapping::group_page_meta;
                assert(new_node_owner.value.metaregion_sound(*regions));
                assert(new_node_owner.value.meta_slot_paddr().unwrap() == paddr);
            }

            #[verus_spec(with Tracked(regions), Tracked(&new_node_owner.value.node.tracked_borrow().meta_perm))]
            let pt_ref = PageTableNodeRef::borrow_paddr(paddr);

            proof_decl! {
                let tracked mut guard_perm: Tracked<GuardPerm<'rcu, C>>;
            }

            // Lock before writing the PTE, so no one else can operate on it.
            #[verus_spec(with Tracked(&new_node_owner.value.node.tracked_borrow()), Tracked(guards) => Tracked(guard_perm))]
            let pt_lock_guard = pt_ref.lock(guard);

            // SAFETY:
            //  1. The index is within the bounds.
            //  2. The new PTE is a child in `C` and at the correct paging level.
            //  3. The ownership of the child is passed to the page table node.
            #[verus_spec(with Tracked(parent_owner))]
            parent_guard.write_pte(self.idx, self.pte);

            #[verus_spec(with Tracked(&parent_owner.meta_perm))]
            let nr_children = parent_guard.nr_children_mut();
            let _tmp = nr_children.read(Tracked(&parent_owner.meta_own.nr_children));
            nr_children.write(Tracked(&mut parent_owner.meta_own.nr_children), _tmp + 1);

            self.node.put(Tracked(parent_guard_perm), parent_guard);

            proof {
                owner.value = new_node_owner.value;
                owner.value.parent_level = level as PagingLevel;
                owner.value.path = old_path;
                owner.children = new_node_owner.children;
                // From allocated_empty_node_owner: all children are absent.
                assert(forall|i: int| 0 <= i < NR_ENTRIES ==>
                    (#[trigger] owner.children[i]) is Some && owner.children[i].unwrap().value.is_absent());

                let new_paddr = owner.value.meta_slot_paddr().unwrap();
                assert(old(regions).slots.contains_key(frame_to_index(new_paddr)));
                regions.inv_implies_correct_addr(new_paddr);
                let new_idx = frame_to_index(new_paddr);
                let tracked mut new_meta_slot = regions.slot_owners.tracked_remove(new_idx);
                new_meta_slot.path_if_in_pt = Some(owner.value.get_path());
                regions.slot_owners.tracked_insert(new_idx, new_meta_slot);
            }

            proof_with!{|= Tracked(Some(guard_perm))}
            Some(pt_lock_guard)
        }
    }

    /// Splits the entry to smaller pages if it maps to a huge page.
    ///
    /// If the entry does map to a huge page, it is split into smaller pages
    /// mapped by a child page table node. The new child page table node
    /// is returned.
    ///
    /// If the entry does not map to a untracked huge page, the method returns
    /// `None`.
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: The old node's root must satisfy the safety invariants for an [Entry](Entry::invariants)
    /// and the caller must provide its parent node owner.
    /// ## Postconditions
    /// - **Safety Invariants**: The node allocated in place of the split page satisfies the safety invariants.
    /// - **Safety**: All other nodes have their invariants preserved.
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
            old(parent_owner).relate_guard_perm(*old(guard_perm)),
            old(parent_owner).inv(),
            old(parent_owner).level == old(owner).value.parent_level,
            old(parent_owner).level < NR_LEVELS,
            // For huge-page split: all 4KB sub-pages (j > 0) must be valid.
            // The j = 0 sub-page coincides with the huge frame's own slot, which is
            // already accounted for by the frame's own metaregion_sound.
            // Fine-grained form (over 4KB pages) enables the recursive split case.
            old(owner).value.is_frame() && old(parent_owner).level > 1 ==>
                forall |j: usize| #![trigger frame_to_index(
                    (old(owner).value.frame.unwrap().mapped_pa
                        + j * PAGE_SIZE) as usize)]
                    0 < j < page_size(old(parent_owner).level) / PAGE_SIZE ==> {
                    let sub_idx = frame_to_index(
                        (old(owner).value.frame.unwrap().mapped_pa
                            + j * PAGE_SIZE) as usize);
                    &&& old(regions).slots.contains_key(sub_idx)
                    &&& old(regions).slot_owners[sub_idx].inner_perms.ref_count.value()
                        != REF_COUNT_UNUSED
                },
        ensures
            old(owner).value.is_frame() && old(parent_owner).level > 1 ==> {
                &&& res is Some
                &&& final(owner).value.is_node()
                &&& final(owner).level == old(owner).level
                &&& final(parent_owner).relate_guard_perm(*final(guard_perm))
                &&& final(guards).guards.contains_key(res.unwrap().addr())
                &&& final(guards).guards[res.unwrap().addr()] is Some
                &&& final(guards).guards[res.unwrap().addr()].unwrap().pptr() == res.unwrap()
                &&& final(owner).value.node.unwrap().relate_guard_perm(final(guards).guards[res.unwrap().addr()].unwrap())
                &&& final(owner).value.node.unwrap().meta_perm.addr() == res.unwrap().addr()
                // All children of the new node subtree are frames with the same prop (from the split loop).
                &&& forall |j: int| 0 <= j < NR_ENTRIES ==>
                    (#[trigger] final(owner).children[j]).unwrap().value.is_frame()
                &&& forall |j: int| 0 <= j < NR_ENTRIES ==>
                    (#[trigger] final(owner).children[j]).unwrap().value.frame.unwrap().prop
                        == old(owner).value.frame.unwrap().prop
                &&& final(owner).value.path == old(owner).value.path
                &&& final(owner).value.metaregion_sound(*final(regions))
                &&& OwnerSubtree::implies(
                    CursorOwner::<'rcu, C>::node_unlocked(*old(guards)),
                    CursorOwner::<'rcu, C>::node_unlocked(*final(guards)))
                &&& OwnerSubtree::implies(
                    PageTableOwner::<C>::metaregion_sound_pred(*old(regions)),
                    PageTableOwner::<C>::metaregion_sound_pred(*final(regions)))
                &&& final(owner).tree_predicate_map(final(owner).value.path,
                    CursorOwner::<'rcu, C>::node_unlocked(*final(guards)))
                &&& final(owner).tree_predicate_map(final(owner).value.path,
                    PageTableOwner::<C>::metaregion_sound_pred(*final(regions)))
            },
            !old(owner).value.is_frame() || old(parent_owner).level <= 1 ==> {
                &&& res is None
                &&& *final(owner) == *old(owner)
            },
            final(owner).inv(),
            final(owner).value.parent_level == old(owner).value.parent_level,
            final(self).idx == old(self).idx,
            old(owner).value.is_frame() && old(parent_owner).level > 1 ==> !final(owner).value.in_scope,
            old(owner).value.is_frame() && old(parent_owner).level > 1 ==>
                final(self).node_matching(final(owner).value, *final(parent_owner), *final(guard_perm)),
            final(regions).inv(),
            final(parent_owner).inv(),
            final(parent_owner).level == old(parent_owner).level,
            final(guard_perm).pptr() == old(guard_perm).pptr(),
            final(guard_perm).value().inner.inner@.ptr.addr() == old(guard_perm).value().inner.inner@.ptr.addr(),
            forall |i: usize| old(guards).lock_held(i) ==> final(guards).lock_held(i),
            forall |i: usize| old(guards).unlocked(i) ==> final(guards).unlocked(i),
            // slot_owners unchanged for all indices except the new PT node's index.
            old(owner).value.is_frame() && old(parent_owner).level > 1 ==> {
                &&& forall|i: usize| i != frame_to_index(meta_to_frame(final(owner).value.node.unwrap().meta_perm.addr())) ==>
                    (#[trigger] final(regions).slot_owners[i]) == old(regions).slot_owners[i]
                // slots keys preserved (alloc removes then borrow re-inserts).
                &&& forall|i: usize| old(regions).slots.contains_key(i)
                    ==> (#[trigger] final(regions).slots.contains_key(i))
                // The new PT node's ref_count is not UNUSED.
                &&& final(regions).slot_owners[frame_to_index(meta_to_frame(final(owner).value.node.unwrap().meta_perm.addr()))]
                    .inner_perms.ref_count.value() != REF_COUNT_UNUSED
                // The allocated slot had ref_count == UNUSED before allocation.
                &&& old(regions).slot_owners[frame_to_index(meta_to_frame(final(owner).value.node.unwrap().meta_perm.addr()))]
                    .inner_perms.ref_count.value() == REF_COUNT_UNUSED
            },
    )]
    pub(in crate::mm) fn split_if_mapped_huge<A: InAtomicMode>(&mut self, guard: &'rcu A)
        -> (res: Option<PPtr<PageTableGuard<'rcu, C>>>) {
        let mut node_guard = self.node.take(Tracked(guard_perm));

        #[verus_spec(with Tracked(&parent_owner.meta_perm))]
        let level = node_guard.level();

        if !(self.pte.is_last(level) && level > 1) {
            self.node.put(Tracked(guard_perm), node_guard);

            return None;
        }
        let pa = self.pte.paddr();
        let prop = self.pte.prop();

        proof {
            EntryOwner::last_pte_implies_frame_match(owner.value, self.pte, level);
        }

        proof_decl!{
            let tracked mut new_owner: OwnerSubtree<C>;
        }

        #[verus_spec(with Tracked(parent_owner), Tracked(regions), Tracked(guards), Ghost(self.idx) => Tracked(new_owner))]
        let new_page = PageTableNode::<C>::alloc(level);

        #[verus_spec(with Tracked(&new_owner.value.node.tracked_borrow().meta_perm.points_to))]
        let paddr = new_page.start_paddr();

        proof {
            broadcast use crate::mm::frame::meta::mapping::group_page_meta;
            assert(new_owner.value.metaregion_sound(*regions));
            assert(new_owner.value.meta_slot_paddr().unwrap() == paddr);
        }

        #[verus_spec(with Tracked(regions), Tracked(&new_owner.value.node.tracked_borrow().meta_perm))]
        let pt_ref = PageTableNodeRef::borrow_paddr(paddr);

        proof_decl! {
            let tracked mut new_guard_perm: Tracked<GuardPerm<'rcu, C>>;
        }

        // Lock before writing the PTE, so no one else can operate on it.
        #[verus_spec(with Tracked(&new_owner.value.node.tracked_borrow()), Tracked(guards) => Tracked(new_guard_perm))]
        let pt_lock_guard = pt_ref.lock(guard);

        let ghost children_perm = new_owner.value.node.unwrap().children_perm;
        let ghost new_owner_path = new_owner.value.path;
        let ghost new_owner_meta_addr = new_owner.value.node.unwrap().meta_perm.addr();

        for i in 0..nr_subpage_per_huge::<C>()
            invariant
                1 < level < NR_LEVELS,
                owner.inv(),
                owner.value.is_frame(),
                owner.value.parent_level == level,
                owner.value.frame.unwrap().mapped_pa == pa,
                owner.value.frame.unwrap().prop == prop,
                pa == old(owner).value.frame.unwrap().mapped_pa,
                level == old(parent_owner).level,
                pa % page_size(level) == 0,
                pa + page_size(level) <= MAX_PADDR,
                regions.inv(),
                parent_owner.inv(),
                new_owner.value.is_node(),
                new_owner.inv(),
                new_owner.value.path == new_owner_path,
                new_owner.value.node.unwrap().meta_perm.addr() == new_owner_meta_addr,
                new_owner.value.node.unwrap().relate_guard_perm(new_guard_perm),
                new_owner.value.node.unwrap().level == (level - 1) as PagingLevel,
                pt_lock_guard.addr() == new_guard_perm.addr(),
                forall|j: int|
                    #![auto]
                    0 <= j < NR_ENTRIES ==> {
                        &&& new_owner.children[j] is Some
                        &&& new_owner.children[j].unwrap().value.match_pte(new_owner.value.node.unwrap().children_perm.value()[j], new_owner.value.node.unwrap().level)
                        &&& new_owner.children[j].unwrap().value.parent_level == new_owner.value.node.unwrap().level
                        &&& new_owner.children[j].unwrap().value.inv()
                        &&& new_owner.children[j].unwrap().value.path == new_owner_path.push_tail(j as usize)
                    },
                forall|j: int| #![auto] i <= j < NR_ENTRIES ==> {
                    &&& new_owner.children[j].unwrap().value.is_absent()
                    &&& !new_owner.children[j].unwrap().value.in_scope
                    &&& new_owner.value.node.unwrap().children_perm.value()[j] == C::E::new_absent_spec()
                },
                // Children [0, i) have been replaced with frames.
                forall|j: int| #![auto] 0 <= j < i ==> {
                    new_owner.children[j].unwrap().value.is_frame()
                },
                // Sub-page slots (4KB-grained, j > 0): slots.contains_key and rc != UNUSED preserved.
                // The j = 0 case is handled separately via the frame's own metaregion_sound.
                forall |j: usize| #![trigger frame_to_index(
                    (pa + j * PAGE_SIZE) as usize)]
                    0 < j < page_size(level) / PAGE_SIZE ==> {
                    let sub_idx = frame_to_index((pa + j * PAGE_SIZE) as usize);
                    &&& regions.slots.contains_key(sub_idx)
                    &&& regions.slot_owners[sub_idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                },
                new_page.ptr.addr() == new_owner_meta_addr,
        {
            proof {
                C::axiom_nr_subpage_per_huge_eq_nr_entries();
            }
            assert(i < NR_ENTRIES);

            proof {
                // Prove required facts while we still have new_owner.value.node available.
                let ghost the_node = new_owner.value.node.unwrap();
                assert(0 <= i < NR_ENTRIES);
                assert(new_owner.children[i as int].unwrap().value.match_pte(
                    the_node.children_perm.value()[i as int],
                    new_owner.children[i as int].unwrap().value.parent_level,
                ));
                assert(the_node.relate_guard_perm(new_guard_perm));
                assert(new_guard_perm.addr() == pt_lock_guard.addr());
                assert(new_owner.children[i as int].unwrap().value.parent_level == the_node.level);
                assert(!new_owner.children[i as int].unwrap().value.in_scope);

                OwnerSubtree::child_some_properties(new_owner, i as usize);
            }

            let tracked mut new_owner_node = new_owner.value.node.tracked_take();

            proof {
                let ghost old_children_perm = new_owner_node.children_perm;
            }

            proof {
                EntryOwner::huge_frame_split_child_at(owner.value, *regions, i as usize);
            }

            let small_pa = pa + i * page_size(level - 1);

            assert(small_pa % PAGE_SIZE == 0);

            let tracked child_owner = EntryOwner::new_frame(
                small_pa,
                new_owner.value.path.push_tail(i as usize),
                (level - 1) as PagingLevel,
                prop,
            );

            #[verus_spec(with Tracked(&new_owner_node), Tracked(&new_owner.children.tracked_borrow(i as int).tracked_borrow().value), Tracked(&new_guard_perm))]
            let mut entry = PageTableGuard::entry(pt_lock_guard, i);

            proof {
                assert(entry.idx == i as usize);
                let ghost child_before_remove = new_owner.child(i as usize).unwrap();
                assert(child_before_remove.inv());
            }
            let tracked mut new_owner_child = new_owner.children.tracked_remove(i as int).tracked_unwrap();

            proof {
                assert(new_owner_child.value.match_pte(
                    new_owner_node.children_perm.value()[i as int],
                    new_owner_child.value.parent_level,
                ));

                let idx = frame_to_index(small_pa);
                // Trigger the loop invariant with j = i.
                assert(idx == frame_to_index(
                    (pa + i * page_size((level - 1) as PagingLevel)) as usize));
                // For i > 0: from the j > 0 sub-page precondition (preserved through the loop).
                // For i == 0: small_pa == pa, so idx is the huge frame's own slot index,
                //   which is valid from owner.value.metaregion_sound(*regions) (is_frame branch).
                // TODO: derive both cases — currently still assumed (pre-existing).
                assume(regions.slots.contains_key(idx));
                assume(regions.slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED);

                assert(entry.node_matching(new_owner_child.value, new_owner_node, new_guard_perm)) by {
                    let pte = new_owner_node.children_perm.value()[i as int];
                    assert(pte == C::E::new_absent_spec());
                    crate::specs::arch::PageTableEntry::absent_pte_paddr_ok();
                    EntryOwner::absent_match_pte(
                        new_owner_child.value,
                        pte,
                        new_owner_child.value.parent_level,
                    );
                };

                // For sub-frames at level - 1: if level - 1 > 1, the sub-frame is itself
                // a huge frame and needs sub-sub-page validity. Now derivable since
                // frame_sub_pages_valid is fine-grained (over all 4KB sub-pages):
                // - The original frame at pa has all 4KB slots in [pa, pa + page_size(level)) valid.
                // - The sub-frame child_owner at small_pa = pa + i * page_size(level - 1)
                //   needs its own 4KB slots in [small_pa, small_pa + page_size(level - 1)) valid.
                // - This range is a sub-range of the original [pa, pa + page_size(level)).
                // - For each j' in (0, page_size(level - 1)/PAGE_SIZE), we need
                //   slots.contains_key(small_pa + j' * PAGE_SIZE).
                // - small_pa + j' * PAGE_SIZE = pa + (i * (page_size(level-1)/PAGE_SIZE) + j') * PAGE_SIZE.
                // - Let J = i * (page_size(level-1)/PAGE_SIZE) + j'. J >= j' >= 1, and
                //   J < (i+1) * (page_size(level-1)/PAGE_SIZE) <= NR_ENTRIES * (page_size(level-1)/PAGE_SIZE)
                //   = page_size(level)/PAGE_SIZE. So J is in the original forall's range.
                if level - 1 > 1 {
                    let nr_subpages = page_size((level - 1) as PagingLevel) / PAGE_SIZE;
                    crate::specs::mm::page_table::cursor::page_size_lemmas::
                        lemma_page_size_div_mul_eq((level - 1) as PagingLevel);
                    crate::specs::mm::page_table::cursor::page_size_lemmas::
                        lemma_page_size_div_mul_eq(level);
                    crate::specs::mm::page_table::cursor::page_size_lemmas::
                        lemma_nr_entries_times_sub_page_size(level);
                    assert forall |j_prime: usize|
                        #![trigger frame_to_index((small_pa + j_prime * PAGE_SIZE) as usize)]
                        0 < j_prime < nr_subpages implies {
                        let sub_idx = frame_to_index((small_pa + j_prime * PAGE_SIZE) as usize);
                        &&& regions.slots.contains_key(sub_idx)
                        &&& regions.slot_owners[sub_idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                    } by {
                        let sub_pages_per_subframe = page_size((level - 1) as PagingLevel) / PAGE_SIZE;
                        let big_j_int: int = i as int * sub_pages_per_subframe as int + j_prime as int;
                        // big_j_int > 0: j_prime >= 1, i >= 0, sub_pages_per_subframe > 0.
                        vstd::arithmetic::mul::lemma_mul_nonnegative(
                            i as int, sub_pages_per_subframe as int);
                        assert(big_j_int > 0);
                        // big_j_int < (i+1) * sub_pages_per_subframe <= NR_ENTRIES * sub_pages_per_subframe
                        //   = page_size(level)/PAGE_SIZE
                        assert(i + 1 <= NR_ENTRIES);
                        vstd::arithmetic::mul::lemma_mul_inequality(
                            (i + 1) as int, NR_ENTRIES as int, sub_pages_per_subframe as int);
                        vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(
                            sub_pages_per_subframe as int, i as int, 1int);
                        assert(big_j_int < NR_ENTRIES as int * sub_pages_per_subframe as int);
                        // NR_ENTRIES * sub_pages_per_subframe == page_size(level)/PAGE_SIZE
                        // chained from:
                        //   page_size(level-1) = sub_pages_per_subframe * PAGE_SIZE  (div_mul_eq L-1)
                        //   page_size(level) = NR_ENTRIES * page_size(level-1)  (lemma_nr_entries_times_sub_page_size L)
                        //   page_size(level)/PAGE_SIZE * PAGE_SIZE = page_size(level)  (div_mul_eq L)
                        vstd::arithmetic::mul::lemma_mul_is_associative(
                            NR_ENTRIES as int, sub_pages_per_subframe as int, PAGE_SIZE as int);
                        // From the chain: NR_ENTRIES * sub_pages_per_subframe * PAGE_SIZE == page_size(level)
                        // Since both sides are multiples of PAGE_SIZE > 0, dividing gives equality.
                        vstd::arithmetic::div_mod::lemma_div_by_multiple(
                            NR_ENTRIES as int * sub_pages_per_subframe as int, PAGE_SIZE as int);
                        assert(NR_ENTRIES as int * sub_pages_per_subframe as int
                            == (page_size(level) / PAGE_SIZE) as int);
                        assert(big_j_int < (page_size(level) / PAGE_SIZE) as int);
                        // big_j_int fits in usize (it's < page_size(level)/PAGE_SIZE which fits in usize).
                        let big_j: usize = big_j_int as usize;
                        assert(big_j as int == big_j_int);
                        // small_pa + j_prime * PAGE_SIZE == pa + big_j * PAGE_SIZE
                        // small_pa = pa + i * page_size(level-1)
                        //          = pa + i * sub_pages_per_subframe * PAGE_SIZE
                        // small_pa + j_prime*PAGE_SIZE
                        //   = pa + i * sub_pages_per_subframe * PAGE_SIZE + j_prime * PAGE_SIZE
                        //   = pa + (i * sub_pages_per_subframe + j_prime) * PAGE_SIZE
                        //   = pa + big_j * PAGE_SIZE
                        assert(small_pa as int == pa as int + i as int * page_size((level - 1) as PagingLevel) as int);
                        vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(
                            PAGE_SIZE as int,
                            i as int * sub_pages_per_subframe as int,
                            j_prime as int);
                        vstd::arithmetic::mul::lemma_mul_is_associative(
                            i as int, sub_pages_per_subframe as int, PAGE_SIZE as int);
                        assert((small_pa + j_prime * PAGE_SIZE) as int == (pa + big_j_int * PAGE_SIZE) as int);
                        assert(big_j as int == big_j_int);
                        assert((small_pa + j_prime * PAGE_SIZE) as usize == (pa + big_j * PAGE_SIZE) as usize);
                        let big_sub_idx = frame_to_index((pa + big_j * PAGE_SIZE) as usize);
                        assert(regions.slots.contains_key(big_sub_idx));
                        assert(regions.slot_owners[big_sub_idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED);
                    }
                    assert(child_owner.frame_sub_pages_valid(*regions));
                }
                assert(Child::<C>::Frame(small_pa, (level - 1) as PagingLevel, prop)
                    .invariants(child_owner, *regions));
            }

            #[verus_spec(with Tracked(regions),
                Tracked(&mut new_owner_child.value),
                Tracked(&mut child_owner),
                Tracked(&mut new_owner_node),
                Tracked(&mut new_guard_perm),
                Ghost(false))]
            let old = entry.replace(Child::Frame(small_pa, level - 1, prop));

            proof {
                new_owner.value.node = Some(new_owner_node);
                new_owner_child.value.in_scope = false;
                child_owner.in_scope = false;
                OwnerSubtree::set_value_property(new_owner_child, child_owner);
                new_owner_child.value = child_owner;
                new_owner.children.tracked_insert(i as int, Some(new_owner_child));

                TreePath::push_tail_property_len(new_owner_path, i as usize);
                OwnerSubtree::insert_preserves_inv(new_owner, i as usize, new_owner_child);
            }
        }

        self.pte = (#[verus_spec(with Tracked(&mut new_owner.value), Tracked(regions))]
        Child::PageTable(new_page).into_pte());

        proof {
            new_owner.level = owner.level;
            *owner = new_owner;
        }

        let tracked mut node_owner = owner.value.node.tracked_take();

        // SAFETY:
        //  1. The index is within the bounds.
        //  2. The new PTE is a child in `C` and at the correct paging level.
        //  3. The ownership of the child is passed to the page table node.
        #[verus_spec(with Tracked(&mut node_owner))]
        node_guard.write_pte(self.idx, self.pte);

        proof {
            owner.value.node = Some(node_owner);
        }

        self.node.put(Tracked(guard_perm), node_guard);

        Some(pt_lock_guard)
    }

    /// Create a new entry at the node with guard.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety**: The caller must provide the owner of the entry and the parent node, and the entry
    /// must match the parent node's PTE at the given index.
    /// - **Safety**: The caller must provide a valid guard permission matching `guard`, and it must be guarding the
    /// correct parent.
    /// ## Postconditions
    /// - **Correctness**: The resulting entry matches the owner.
    /// ## Safety
    /// - The precondition ensures that the index is within the bounds of the node.
    /// - This function does not modify the actual entry or any other relevant structure, so it is safe to call.
    /// Because we also require the guard to be correct, it will be safe to use the resulting `Entry` as a handle to the
    /// underlying `PTE`.
    #[verus_spec(
        with Tracked(owner): Tracked<&EntryOwner<C>>,
            Tracked(parent_owner): Tracked<&NodeOwner<C>>,
            Tracked(guard_perm): Tracked<&GuardPerm<'rcu, C>>
    )]
    pub(in crate::mm) fn new_at(guard: PPtr<PageTableGuard<'rcu, C>>, idx: usize) -> (res: Self)
        requires
            owner.inv(),
            !owner.in_scope,
            parent_owner.inv(),
            guard_perm.addr() == guard.addr(),
            parent_owner.relate_guard_perm(*guard_perm),
            idx < NR_ENTRIES,
            owner.match_pte(parent_owner.children_perm.value()[idx as int], owner.parent_level),
        ensures
            res.wf(*owner),
            res.node.addr() == guard_perm.addr(),
            res.idx == idx,
    {
        // SAFETY: The index is within the bound.
        let guard_val = guard.borrow(Tracked(guard_perm));
        #[verus_spec(with Tracked(parent_owner))]
        let pte = guard_val.read_pte(idx);
        Self { pte, idx, node: guard }
    }
}

} // verus!
