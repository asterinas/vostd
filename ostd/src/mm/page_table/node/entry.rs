// SPDX-License-Identifier: MPL-2.0
//! This module provides accessors to the page table entries in a node.
use vstd::prelude::*;


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

pub struct Entry<'a, 'rcu, C: PageTableConfig> {
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
    /// The `node` field is a mutable reference to the guard of the node that contains the entry,
    /// `index` provides the offset, and the `pte` is current value. Only one `Entry` can exist for
    /// a given node at any given time.
    pub pte: C::E,
    /// The index of the entry in the node.
    pub idx: usize,
    /// The node that contains the entry.
    pub node: &'a mut PageTableGuard<'rcu, C>,
}

impl<'a, 'rcu, C: PageTableConfig> Entry<'a, 'rcu, C> {
    pub open spec fn new_spec(pte: C::E, idx: usize, node: &'a mut PageTableGuard<'rcu, C>) -> Self {
        Self { pte, idx, node }
    }

    #[verifier::external_body]
    pub fn new(pte: C::E, idx: usize, node: &'a mut PageTableGuard<'rcu, C>) -> (res: Self)
        ensures
            res == Self::new_spec(pte, idx, node),
            // Move into a struct field doesn't mutate `*node`. Stating this
            // explicitly makes the `*final(self) == *old(self)` chain in
            // `new_at` (and transitively, `entry`) reliably derivable.
            *final(node) == *old(node),
    {
        Self { pte, idx, node }
    }
}

#[verus_verify]
impl<'a, 'rcu, C: PageTableConfig> Entry<'a, 'rcu, C> {
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
    )]
    pub(in crate::mm) fn is_node(&self) -> bool
        requires
            owner.inv(),
            self.wf(owner),
            parent_owner.relate_guard(*self.node),
            parent_owner.inv(),
            parent_owner.level == owner.parent_level,
        returns
            owner.is_node(),
    {
        self.pte.is_present() && !self.pte.is_last(
            #[verus_spec(with Tracked(&parent_owner.meta_perm))]
            self.node.level(),
        )
    }

    /// Gets a reference to the child.
    #[verus_spec(
        with Tracked(owner): Tracked<&EntryOwner<C>>,
            Tracked(parent_owner): Tracked<&NodeOwner<C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
    )]
    pub(in crate::mm) fn to_ref(&self) -> (res: ChildRef<'rcu, C>)
        requires
            self.invariants(*owner, *old(regions)),
            self.node_matching(*owner, *parent_owner, *self.node),
            !owner.in_scope,
        ensures
            res.invariants(*owner, *final(regions)),
            final(regions).slot_owners =~= old(regions).slot_owners,
            forall |k: usize| old(regions).slots.contains_key(k) ==> #[trigger] final(regions).slots.contains_key(k),
            forall |k: usize| old(regions).slots.contains_key(k) ==> old(regions).slots[k] == #[trigger] final(regions).slots[k],
            final(regions).inv(),
    {
        #[verus_spec(with Tracked(&parent_owner.meta_perm))]
        let level = self.node.level();

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
    )]
    pub(in crate::mm) fn protect(&mut self, op: impl FnOnce(PageProperty) -> PageProperty)
        requires
            old(owner).inv(),
            old(self).wf(*old(owner)),
            old(self).node_matching(*old(owner), *old(parent_owner), *old(self).node),
            op.requires((old(self).pte.prop(),)),
            old(owner).is_frame(),
            // POTENTIALLY UNSOUND PATCH: `op` must preserve the trackedness of
            // `item_from_raw_spec(pa, level, _)` across the prop change.
            //
            // `axiom_frame_is_tracked_matches_item` asserts that the entry's recorded
            // `is_tracked` field equals `C::tracked(C::item_from_raw_spec(pa, level, prop))`.
            // `protect` updates `prop = op(old_prop)` but preserves `is_tracked`. If
            // `C::tracked` of the reconstructed item depended on a bit `op` flipped, the
            // axiom would be violated.
            //
            // For `KernelPtConfig`, `C::tracked(item)` reads `prop.flags.AVAIL1`, so this
            // precondition reduces to "op preserves AVAIL1". For `UserPtConfig`,
            // `C::tracked` is constant `true`, so this is trivial.
            //
            // This precondition is a *patch*, not a fix. The underlying issue is that
            // `KernelPtConfig` overloads the PTE's `prop.AVAIL1` to encode tracked-ness,
            // conflating "page property bits the user wants to mutate" with "internal
            // accounting." A clean fix is to track tracked-ness separately from `prop`,
            // or to reformulate `axiom_frame_is_tracked_matches_item` so it doesn't
            // depend on `prop`.
            forall |pa: Paddr, level: PagingLevel, p_in: PageProperty, p_out: PageProperty| #![auto]
                op.ensures((p_in,), p_out) ==>
                    C::tracked(C::item_from_raw_spec(pa, level, p_out))
                    == C::tracked(C::item_from_raw_spec(pa, level, p_in)),
        ensures
            final(owner).inv(),
            final(self).wf(*final(owner)),
            final(self).node_matching(*final(owner), *final(parent_owner), *final(self).node),
            final(self).parent_perms_preserved(*old(parent_owner), *final(parent_owner)),
            final(owner).is_frame(),
            final(owner).frame.unwrap().mapped_pa == old(owner).frame.unwrap().mapped_pa,
            final(owner).frame.unwrap().is_tracked == old(owner).frame.unwrap().is_tracked,
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

        // SAFETY:
        //  1. The index is within the bounds.
        //  2. We replace the PTE with a new one, which differs only in
        //     `PageProperty`, so the level still matches the current
        //     page table node.
        #[verus_spec(with Tracked(parent_owner))]
        self.node.write_pte(self.idx, self.pte);

        proof {
            let tracked mut frame_owner = owner.frame.tracked_take();
            frame_owner.prop = new_prop;
            owner.frame = Some(frame_owner);
        }
        assert(owner.match_pte(self.pte, owner.parent_level));
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
    )]
    pub(in crate::mm) fn replace(&mut self, new_child: Child<C>) -> (res: Child<C>)
        requires
            old(self).invariants(*old(owner), *old(regions)),
            new_child.invariants(*old(new_owner), *old(regions)),
            old(self).node_matching(*old(owner), *old(parent_owner), *old(self).node),
            old(self).new_owner_compatible(new_child, *old(owner), *old(new_owner), *old(regions)),
            !old(owner).in_scope,
        ensures
            final(self).invariants(*final(new_owner), *final(regions)),
            res.invariants(*final(owner), *final(regions)),
            final(self).node_matching(*final(new_owner), *final(parent_owner), *final(self).node),
            final(self).idx == old(self).idx,
            *final(owner) == old(owner).from_pte_owner_spec(),
            *final(new_owner) == old(new_owner).into_pte_owner_spec(),
            Self::metaregion_sound_neq_preserved(*old(owner), *final(new_owner), *old(regions), *final(regions)),
            !final(new_owner).is_node() ==>
                Self::metaregion_sound_neq_old_preserved(*old(owner), *old(regions), *final(regions)),
            (!old(owner).is_node() && !final(new_owner).is_node()) ==>
                Self::metaregion_sound_preserved(*old(regions), *final(regions)),
            final(new_owner).is_node() && !final(new_owner).is_absent() ==>
                PageTableOwner::<C>::path_tracked_pred(*final(regions))(*final(new_owner), final(new_owner).path),
            final(self).parent_perms_preserved(*old(parent_owner), *final(parent_owner)),
            // paths_in_pt changes when new owner is a node; preserved otherwise.
            forall|idx: usize| #![trigger final(regions).slot_owners[idx].paths_in_pt]
                (!final(new_owner).is_node() || final(new_owner).is_absent()
                    || idx != frame_to_index(final(new_owner).meta_slot_paddr().unwrap()))
                    ==> final(regions).slot_owners[idx].paths_in_pt == old(regions).slot_owners[idx].paths_in_pt,
            // slots: monotonic (from_pte may add; into_pte doesn't remove for non-nodes).
            forall|k: usize| old(regions).slots.contains_key(k)
                ==> #[trigger] final(regions).slots.contains_key(k),
            // ref_count is preserved per-slot. `into_pte_regions_spec` and
            // `from_pte_regions_spec` only ever rewrite `raw_count` (and the
            // ghost `paths_in_pt` is touched by the surrounding body, never
            // `inner_perms`); both use the `..old_slot` struct-update form
            // so `inner_perms.ref_count` is preserved across the rewrite.
            forall|idx: usize| #![trigger final(regions).slot_owners[idx].inner_perms.ref_count.value()]
                final(regions).slot_owners[idx].inner_perms.ref_count.value()
                    == old(regions).slot_owners[idx].inner_perms.ref_count.value(),
            // When both old and new are not nodes: from_pte/into_pte are identity.
            (!old(owner).is_node() && !final(new_owner).is_node()) ==> {
                &&& final(regions).slots == old(regions).slots
                &&& forall|i: usize| #![trigger final(regions).slot_owners[i]]
                    final(regions).slot_owners[i] == old(regions).slot_owners[i]
            },
            // When old child is absent and new child is not a node: slots values unchanged.
            (old(owner).is_absent() && !final(new_owner).is_node()) ==>
                forall|k: usize| old(regions).slots.contains_key(k)
                    ==> old(regions).slots[k] == #[trigger] final(regions).slots[k],
            Self::replace_nonpanic_condition(*old(parent_owner), *old(new_owner)),
    {
        let ghost new_idx = frame_to_index(new_owner.meta_slot_paddr().unwrap());
        let ghost old_idx = frame_to_index(owner.meta_slot_paddr().unwrap());

        #[cfg(feature = "allow_panic")]
        {
            let guard_level = self.node.level();
            match &new_child {
                Child::PageTable(node) => {
                    assert!(node.level() == guard_level - 1);
                }
                Child::Frame(_, level, _) => {
                    assert!(*level == guard_level);
                }
                Child::None => {}
            }
        }

        // SAFETY:
        //  - The PTE is not referenced by other `ChildRef`s (since we have `&mut self`).
        //  - The level matches the current node.
        #[verus_spec(with Tracked(&parent_owner.meta_perm))]
        let level = self.node.level();

        #[verus_spec(with Tracked(regions), Tracked(owner))]
        let old_child = Child::from_pte(self.pte, level);

        let ghost regions_after_from = *regions;

        assert(new_owner.is_node() ==> regions.slots.contains_key(frame_to_index(new_owner.meta_slot_paddr().unwrap())));

        if old_child.is_none() && !new_child.is_none() {
            #[verus_spec(with Tracked(&parent_owner.meta_perm))]
            let nr_children = self.node.nr_children_mut();
            let _tmp = nr_children.read(Tracked(&parent_owner.meta_own.nr_children));
            proof {
                parent_owner.nr_children_absent_slot_bound(self.idx);
            }
            nr_children.write(Tracked(&mut parent_owner.meta_own.nr_children), _tmp + 1);
        } else if !old_child.is_none() && new_child.is_none() {
            #[verus_spec(with Tracked(&parent_owner.meta_perm))]
            let nr_children = self.node.nr_children_mut();
            let _tmp = nr_children.read(Tracked(&parent_owner.meta_own.nr_children));
            proof {
                parent_owner.nr_children_present_slot_bound(self.idx);
            }
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
        self.node.write_pte(self.idx, new_pte);

        self.pte = new_pte;

        proof {
            // Install new entry's path into its slot's paths_in_pt.
            // Nodes: singleton overwrite (tree enforces unique node path).
            // Frames: their path is installed by the caller BEFORE calling replace,
            //   so that `new_child.invariants` — which now requires
            //   `paths_in_pt.contains(new.path)` for the frame arm — is satisfied on
            //   entry. See the huge-page split and `replace_cur_entry` caller sites.
            if new_owner.is_node() {
                let paddr = new_owner.meta_slot_paddr().unwrap();
                regions.inv_implies_correct_addr(paddr);

                let tracked mut new_meta_slot = regions.slot_owners.tracked_remove(new_idx);
                new_meta_slot.paths_in_pt = set![new_owner.path];
                regions.slot_owners.tracked_insert(new_idx, new_meta_slot);
            }
            owner.in_scope = true;
        }

        assert(Self::metaregion_sound_neq_preserved(*old(owner), *new_owner, *old(regions), *regions));

        proof {
            // When both old and new are not nodes:
            // from_pte/into_pte are identity, no slot_owners change. Regions unchanged.
            if !old(owner).is_node() && !new_owner.is_node() {
                // slot_owners and slots are identical → metaregion_sound trivially preserved.
            }
        }

        proof {
            if new_owner.is_node() || new_owner.is_frame() {
                let paddr = new_owner.meta_slot_paddr().unwrap();
                regions.inv_implies_correct_addr(paddr);
            }
            // Sub-page validity for new_owner (if a huge frame): preserved because
            // replace only modifies slots/paths_in_pt at new_owner's own slot, not
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
        requires
            old(self).invariants(old(owner).value, *old(regions)),
            old(owner).inv(),
            old(self).node_matching(old(owner).value, *old(parent_owner), *old(self).node),
            old(owner).level < INC_LEVELS - 1,
        ensures
            final(self).invariants(final(owner).value, *final(regions)),
            final(self).parent_perms_preserved(*old(parent_owner), *final(parent_owner)),
            final(self).idx == old(self).idx,
            old(owner).value.is_absent() && old(parent_owner).level > 1 ==> {
                // node_matching preserved: parent_owner still matches the child after allocation.
                &&& final(self).node_matching(final(owner).value, *final(parent_owner), *final(self).node)
                // OwnerSubtree inv (recursive tree invariant, not just value.inv()).
                &&& final(owner).inv()
                // After into_pte, the entry has in_scope == false.
                &&& !final(owner).value.in_scope
            },
            old(owner).value.is_absent() && old(parent_owner).level > 1 ==> {
                &&& res is Some
                &&& final(owner).value.is_node()
                &&& final(owner).level == old(owner).level
                &&& final(owner).value.parent_level == old(owner).value.parent_level
                &&& final(guards).lock_held(final(owner).value.node.unwrap().meta_perm.addr())
                &&& final(owner).value.node.unwrap().relate_guard(res.unwrap())
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
                // Children's paths are rebased onto the cursor path. Required by
                // `pt_edge_at` for the freshly-allocated node, since the bare
                // `allocated_empty_node_owner` from `PageTableNode::alloc` uses
                // an empty parent path and `alloc_if_none` rewrites that path to
                // the cursor path; without rebasing the children, their paths
                // would be `[i]` rather than `cursor_path.push_tail(i)`.
                &&& forall|i: int| 0 <= i < NR_ENTRIES ==>
                    (#[trigger] final(owner).children[i]).unwrap().value.path
                        == final(owner).value.path.push_tail(i as usize)
                // Grandchildren are all None (carried through from
                // `PageTableNode::alloc`'s `allocated_empty_node_grandchildren_none`
                // ensures; the rebase only touches paths).
                &&& crate::specs::mm::page_table::allocated_empty_node_grandchildren_none(*final(owner))
                // Other child fields preserved from `allocated_empty_node_owner`.
                &&& forall|i: int| 0 <= i < NR_ENTRIES ==>
                    (#[trigger] final(owner).children[i]).unwrap().value.parent_level
                        == final(owner).value.node.unwrap().level
                &&& forall|i: int| 0 <= i < NR_ENTRIES ==>
                    (#[trigger] final(owner).children[i]).unwrap().value.match_pte(
                        final(owner).value.node.unwrap().children_perm.value()[i],
                        final(owner).children[i].unwrap().value.parent_level)
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
                // Allocator pool is disjoint from MMIO ranges (from `PageTableNode::alloc`).
                &&& !crate::specs::mm::frame::meta_owners::is_mmio_paddr(
                    final(owner).value.meta_slot_paddr().unwrap())
            },
            !old(owner).value.is_absent() ==> {
                &&& res is None
                &&& *final(owner) == *old(owner)
            },
            forall |i: usize| old(guards).lock_held(i) ==> final(guards).lock_held(i),
            forall |i: usize| old(guards).unlocked(i) && i != final(owner).value.node.unwrap().meta_perm.addr() ==> final(guards).unlocked(i),
    )]
    pub(in crate::mm) fn alloc_if_none<A: InAtomicMode>(&mut self, guard: &'rcu A)
    -> (res: Option<PageTableGuard<'rcu, C>>) {
        let entry_is_present = self.pte.is_present();

        #[verus_spec(with Tracked(&parent_owner.meta_perm))]
        let level = self.node.level();

        if entry_is_present || level <= 1 {
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

            let pt_ref = unsafe {
                #[verus_spec(with Tracked(regions), Tracked(&new_node_owner.value.node.tracked_borrow().meta_perm.points_to))]
                PageTableNodeRef::borrow_paddr(paddr)
            };

            // Lock before writing the PTE, so no one else can operate on it.
            #[verus_spec(with Tracked(&new_node_owner.value.node.tracked_borrow()), Tracked(guards))]
            let mut pt_lock_guard = pt_ref.lock(guard);

            proof {
                parent_owner.nr_children_absent_slot_bound(self.idx);
            }

            // SAFETY:
            //  1. The index is within the bounds.
            //  2. The new PTE is a child in `C` and at the correct paging level.
            //  3. The ownership of the child is passed to the page table node.
            #[verus_spec(with Tracked(parent_owner))]
            self.node.write_pte(self.idx, self.pte);

            #[verus_spec(with Tracked(&parent_owner.meta_perm))]
            let nr_children = self.node.nr_children_mut();
            let _tmp = nr_children.read(Tracked(&parent_owner.meta_own.nr_children));
            nr_children.write(Tracked(&mut parent_owner.meta_own.nr_children), _tmp + 1);

            proof {
                owner.value = new_node_owner.value;
                owner.value.parent_level = level as PagingLevel;
                owner.value.path = old_path;
                owner.children = new_node_owner.children;
                // Rebase children's paths from `[i]` (rooted at empty) onto
                // the cursor path `old_path` so `pt_edge_at`'s
                // `child.path == parent.path.push_tail(i)` holds.
                crate::specs::mm::page_table::rebase_freshly_allocated_children(
                    owner, old_path);
                // From allocated_empty_node_owner: all children are absent.
                assert(forall|i: int| 0 <= i < NR_ENTRIES ==>
                    (#[trigger] owner.children[i]) is Some && owner.children[i].unwrap().value.is_absent());

                let new_paddr = owner.value.meta_slot_paddr().unwrap();
                assert(old(regions).slots.contains_key(frame_to_index(new_paddr)));
                regions.inv_implies_correct_addr(new_paddr);
                let new_idx = frame_to_index(new_paddr);
                let tracked mut new_meta_slot = regions.slot_owners.tracked_remove(new_idx);
                new_meta_slot.paths_in_pt = set![owner.value.path];
                regions.slot_owners.tracked_insert(new_idx, new_meta_slot);
            }

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
    #[verifier::spinoff_prover]
    #[verus_spec(res =>
        with Tracked(owner) : Tracked<&mut OwnerSubtree<C>>,
            Tracked(parent_owner): Tracked<&mut NodeOwner<C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            old(regions).inv(),
            old(owner).inv(),
            old(self).wf(old(owner).value),
            old(parent_owner).relate_guard(*old(self).node),
            old(parent_owner).inv(),
            old(parent_owner).level == old(owner).value.parent_level,
            old(parent_owner).level < NR_LEVELS,
            // Frame entries being split must have `metaregion_sound` for
            // their slot — provides `regions.slots.contains_key(pa_idx)` and
            // ref_count facts at the parent slot itself (j = 0 case in the
            // split loop's invariant). Without this, those facts can't be
            // re-established after alloc.
            old(owner).value.is_frame() && old(parent_owner).level > 1 ==>
                old(owner).value.metaregion_sound(*old(regions)),
            // Sub-page validity for huge-page split: each 4KB sub-page slot must
            // exist; non-MMIO sub-pages must additionally have `rc != UNUSED`.
            // (MMIO sub-pages keep `usage == MMIO` and `rc == UNUSED`.)
            old(owner).value.is_frame() && old(parent_owner).level > 1 ==>
                forall |j: usize| #![trigger frame_to_index(
                    (old(owner).value.frame.unwrap().mapped_pa
                        + j * PAGE_SIZE) as usize)]
                    0 < j < page_size(old(parent_owner).level) / PAGE_SIZE ==> {
                    let sub_idx = frame_to_index(
                        (old(owner).value.frame.unwrap().mapped_pa
                            + j * PAGE_SIZE) as usize);
                    &&& old(regions).slots.contains_key(sub_idx)
                    &&& old(regions).slot_owners[sub_idx].usage
                            != crate::specs::mm::frame::meta_owners::PageUsage::MMIO ==>
                        old(regions).slot_owners[sub_idx].inner_perms.ref_count.value()
                            != REF_COUNT_UNUSED
                },
        ensures
            old(owner).value.is_frame() && old(parent_owner).level > 1 ==> {
                &&& res is Some
                &&& final(owner).value.is_node()
                &&& final(owner).level == old(owner).level
                &&& final(parent_owner).relate_guard(*final(self).node)
                &&& final(owner).value.node.unwrap().relate_guard(res.unwrap())
                &&& final(owner).value.node.unwrap().meta_perm.addr() == res.unwrap().inner.inner@.ptr.addr()
                &&& final(guards).lock_held(res.unwrap().inner.inner@.ptr.addr())
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
                final(self).node_matching(final(owner).value, *final(parent_owner), *final(self).node),
            final(regions).inv(),
            final(parent_owner).inv(),
            final(parent_owner).level == old(parent_owner).level,
            final(self).node.inner.inner@.ptr.addr() == old(self).node.inner.inner@.ptr.addr(),
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
            // Parent's other PTEs are preserved: only the entry at self.idx
            // is overwritten (with the new PT pointer). Lets callers re-derive
            // `inv_children_rel` for the unchanged children when restoring the
            // parent NodeOwner into the cursor's continuation.
            old(owner).value.is_frame() && old(parent_owner).level > 1 ==>
                forall|j: int| 0 <= j < NR_ENTRIES && j != old(self).idx as int ==>
                    #[trigger] final(parent_owner).children_perm.value()[j]
                        == old(parent_owner).children_perm.value()[j],
    )]
    pub(in crate::mm) fn split_if_mapped_huge<A: InAtomicMode>(&mut self, guard: &'rcu A)
        -> (res: Option<PageTableGuard<'rcu, C>>) {
        #[verus_spec(with Tracked(&parent_owner.meta_perm))]
        let level = self.node.level();

        if !(self.pte.is_last(level) && level > 1) {
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

        // alloc takes the NEW NODE level (level - 1, one below the cursor's
        // level which is `level`). Convention: alloc(M) produces node.level=M.
        #[verus_spec(with Tracked(parent_owner), Tracked(regions), Tracked(guards), Ghost(self.idx) => Tracked(new_owner))]
        let new_page = PageTableNode::<C>::alloc(level - 1);

        #[verus_spec(with Tracked(&new_owner.value.node.tracked_borrow().meta_perm.points_to))]
        let paddr = new_page.start_paddr();

        proof {
            broadcast use crate::mm::frame::meta::mapping::group_page_meta;
            assert(new_owner.value.metaregion_sound(*regions));
            assert(new_owner.value.meta_slot_paddr().unwrap() == paddr);
        }

        let pt_ref = unsafe {
            #[verus_spec(with Tracked(regions), Tracked(&new_owner.value.node.tracked_borrow().meta_perm.points_to))]
            PageTableNodeRef::borrow_paddr(paddr)
        };

        // Lock before writing the PTE, so no one else can operate on it.
        #[verus_spec(with Tracked(&new_owner.value.node.tracked_borrow()), Tracked(guards))]
        let mut pt_lock_guard = pt_ref.lock(guard);

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
                new_owner.value.node.unwrap().relate_guard(pt_lock_guard),
                guards.lock_held(new_owner_meta_addr),
                new_owner.value.node.unwrap().level == (level - 1) as PagingLevel,
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
                // Sub-page slots (4KB-grained, j > 0): slots.contains_key is unconditional;
                // rc constraints apply only to non-MMIO sub-pages (MMIO sub-pages keep
                // `usage == MMIO` and `rc == UNUSED`).
                forall |j: usize| #![trigger frame_to_index(
                    (pa + j * PAGE_SIZE) as usize)]
                    0 < j < page_size(level) / PAGE_SIZE ==> {
                    let sub_idx = frame_to_index((pa + j * PAGE_SIZE) as usize);
                    &&& regions.slots.contains_key(sub_idx)
                    &&& regions.slot_owners[sub_idx].usage
                            != crate::specs::mm::frame::meta_owners::PageUsage::MMIO ==> {
                        &&& regions.slot_owners[sub_idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                        &&& regions.slot_owners[sub_idx].inner_perms.ref_count.value() > 0
                    }
                },
                // j = 0: the huge frame's own slot.
                regions.slots.contains_key(frame_to_index(pa)),
                regions.slot_owners[frame_to_index(pa)].usage
                        != crate::specs::mm::frame::meta_owners::PageUsage::MMIO ==> {
                    &&& regions.slot_owners[frame_to_index(pa)].inner_perms.ref_count.value()
                        != crate::specs::mm::frame::meta_owners::REF_COUNT_UNUSED
                    &&& regions.slot_owners[frame_to_index(pa)].inner_perms.ref_count.value() > 0
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
                assert(the_node.relate_guard(pt_lock_guard));
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
                /* is_tracked */ owner.value.frame.unwrap().is_tracked,
            );

            #[verus_spec(with Tracked(&new_owner_node), Tracked(&new_owner.children.tracked_borrow(i as int).tracked_borrow().value))]
            let mut entry = pt_lock_guard.entry(i);

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
                assert(idx == frame_to_index(
                    (pa + i * page_size((level - 1) as PagingLevel)) as usize));
                if i != 0 {
                    let ghost big_j = crate::specs::mm::page_table::cursor::
                        page_size_lemmas::lemma_split_sub_page_big_j(pa, level, i);
                    assert(small_pa == (pa + big_j * PAGE_SIZE) as usize);
                }

                assert(entry.node_matching(new_owner_child.value, new_owner_node, *entry.node)) by {
                    let pte = new_owner_node.children_perm.value()[i as int];
                    assert(pte == C::E::new_absent_spec());
                    crate::specs::arch::PageTableEntry::absent_pte_paddr_ok();
                    EntryOwner::absent_match_pte(
                        new_owner_child.value,
                        pte,
                        new_owner_child.value.parent_level,
                    );
                };

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
                        &&& regions.slot_owners[sub_idx].usage
                                != crate::specs::mm::frame::meta_owners::PageUsage::MMIO ==> {
                            &&& regions.slot_owners[sub_idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                            &&& regions.slot_owners[sub_idx].inner_perms.ref_count.value() > 0
                        }
                    } by {
                        let sub_pages_per_subframe = page_size((level - 1) as PagingLevel) / PAGE_SIZE;
                        let big_j_int: int = i as int * sub_pages_per_subframe as int + j_prime as int;
                        vstd::arithmetic::mul::lemma_mul_nonnegative(
                            i as int, sub_pages_per_subframe as int);
                        vstd::arithmetic::mul::lemma_mul_inequality(
                            (i + 1) as int, NR_ENTRIES as int, sub_pages_per_subframe as int);
                        vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(
                            sub_pages_per_subframe as int, i as int, 1int);
                        vstd::arithmetic::mul::lemma_mul_is_associative(
                            NR_ENTRIES as int, sub_pages_per_subframe as int, PAGE_SIZE as int);
                        vstd::arithmetic::div_mod::lemma_div_by_multiple(
                            NR_ENTRIES as int * sub_pages_per_subframe as int, PAGE_SIZE as int);
                        let big_j: usize = big_j_int as usize;
                        vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(
                            PAGE_SIZE as int,
                            i as int * sub_pages_per_subframe as int,
                            j_prime as int);
                        vstd::arithmetic::mul::lemma_mul_is_associative(
                            i as int, sub_pages_per_subframe as int, PAGE_SIZE as int);
                        assert((small_pa + j_prime * PAGE_SIZE) as usize == (pa + big_j * PAGE_SIZE) as usize);
                    }
                    assert(child_owner.frame_sub_pages_valid(*regions));
                }

                let small_idx = frame_to_index(small_pa);

                // Instantiate the loop invariant's sub-page forall (or the j=0
                // facts) at small_idx. The new invariant only guarantees the
                // ref_count facts under `usage != MMIO`; matches the new
                // metaregion_sound frame arm shape.
                if i == 0 {
                    // small_pa == pa + 0 * page_size(level-1) == pa.
                    assert(i as int * page_size((level - 1) as PagingLevel) as int == 0) by {
                        vstd::arithmetic::mul::lemma_mul_by_zero_is_zero(
                            page_size((level - 1) as PagingLevel) as int);
                    }
                    assert(small_pa == pa);
                } else {
                    let ghost big_j = crate::specs::mm::page_table::cursor::
                        page_size_lemmas::lemma_split_sub_page_big_j(pa, level, i);
                    assert(small_pa == (pa + big_j * PAGE_SIZE) as usize);
                    // Trigger the sub-page forall at j = big_j.
                    assert(regions.slots.contains_key(
                        frame_to_index((pa + big_j * PAGE_SIZE) as usize)));
                }
                assert(regions.slots.contains_key(small_idx));

                // Capture the slot's inner_perms before modification; the
                // tracked_remove/insert below only touches paths_in_pt.
                let ghost orig_inner_perms = regions.slot_owners[small_idx].inner_perms;

                regions.inv_implies_correct_addr(small_pa);
                let tracked mut small_slot = regions.slot_owners.tracked_remove(small_idx);
                small_slot.paths_in_pt = small_slot.paths_in_pt.insert(child_owner.path);
                regions.slot_owners.tracked_insert(small_idx, small_slot);

                // Post-insert: ref_count and slots.contains_key are preserved.
                assert(regions.slot_owners[small_idx].inner_perms == orig_inner_perms);
                assert(regions.slots.contains_key(small_idx));

                if (level - 1) > 1 {
                    assert(child_owner.frame_sub_pages_valid(*regions));
                }

                let ghost target_idx = frame_to_index(small_pa);
                assert(target_idx == small_idx);
                if i != 0 {
                    let ghost big_j = crate::specs::mm::page_table::cursor::
                        page_size_lemmas::lemma_split_sub_page_big_j(pa, level, i);
                    assert(small_pa == (pa + big_j * PAGE_SIZE) as usize);
                    assert(target_idx == frame_to_index((pa + big_j * PAGE_SIZE) as usize));
                    assert(regions.slots.contains_key(target_idx));
                    assert(regions.slot_owners[target_idx].usage
                            != crate::specs::mm::frame::meta_owners::PageUsage::MMIO ==> {
                        &&& regions.slot_owners[target_idx].inner_perms.ref_count.value()
                            != crate::specs::mm::frame::meta_owners::REF_COUNT_UNUSED
                        &&& regions.slot_owners[target_idx].inner_perms.ref_count.value() > 0
                    });
                } else {
                    assert(0 * page_size((level - 1) as PagingLevel) == 0)
                        by (nonlinear_arith);
                    assert(small_pa as int == pa as int);
                    assert(target_idx == frame_to_index(pa));
                }
                assert(child_owner.metaregion_sound(*regions));
                assert(Child::<C>::Frame(small_pa, (level - 1) as PagingLevel, prop)
                    .invariants(child_owner, *regions));
            }

            #[verus_spec(with Tracked(regions),
                Tracked(&mut new_owner_child.value),
                Tracked(&mut child_owner),
                Tracked(&mut new_owner_node))]
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
        self.node.write_pte(self.idx, self.pte);

        proof {
            owner.value.node = Some(node_owner);
        }

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
    )]
    pub(in crate::mm) fn new_at(guard: &'a mut PageTableGuard<'rcu, C>, idx: usize) -> (res: Self)
        requires
            owner.inv(),
            !owner.in_scope,
            parent_owner.inv(),
            parent_owner.relate_guard(*guard),
            idx < NR_ENTRIES,
            owner.match_pte(parent_owner.children_perm.value()[idx as int], owner.parent_level),
        ensures
            res.wf(*owner),
            res.idx == idx,
            parent_owner.relate_guard(*res.node),
            // Pinpoint the reborrow: the Entry's node is exactly the guard
            // we were handed in, so callers get `*res.node == *old(guard)`.
            *res.node == *old(guard),
            // The function reads but does not mutate `*guard`. This propagates
            // the no-mutation fact through the reborrow.
            *final(guard) == *old(guard),
    {
        // SAFETY: The index is within the bound. Routed through `Self::new`
        // (already `external_body`) so the reborrow's spec-level identity is
        // captured by `new_spec`'s definition rather than recomputed here.
        #[verus_spec(with Tracked(parent_owner))]
        let pte = guard.read_pte(idx);
        Self::new(pte, idx, guard)
    }
}

} // verus!
