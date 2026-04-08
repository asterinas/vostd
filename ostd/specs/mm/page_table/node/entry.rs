use vstd::prelude::*;

use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;

use crate::mm::frame::meta::mapping::frame_to_index;
use crate::mm::page_table::*;
use crate::specs::arch::mm::NR_ENTRIES;
use crate::specs::mm::frame::meta_owners::REF_COUNT_UNUSED;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::page_table::*;

verus! {

impl<'rcu, C: PageTableConfig> Entry<'rcu, C> {
    pub open spec fn invariants(self, owner: EntryOwner<C>, regions: MetaRegionOwners) -> bool {
        &&& owner.inv()
        &&& regions.inv()
        &&& self.wf(owner)
        &&& owner.metaregion_sound(regions)
    }

    pub open spec fn node_matching(self, owner: EntryOwner<C>, parent_owner: NodeOwner<C>, guard_perm: GuardPerm<'rcu, C>) -> bool {
        &&& parent_owner.level == owner.parent_level
        &&& parent_owner.inv()
        &&& guard_perm.addr() == self.node.addr()
        &&& guard_perm.is_init()
        &&& guard_perm.value().inner.inner@.ptr.addr() == parent_owner.meta_perm.addr()
        &&& guard_perm.value().inner.inner@.ptr.addr() == parent_owner.meta_perm.points_to.addr()
        &&& guard_perm.value().inner.inner@.wf(parent_owner)
        &&& parent_owner.meta_perm.is_init()
        &&& parent_owner.meta_perm.wf(&parent_owner.meta_perm.inner_perms)
        &&& owner.match_pte(parent_owner.children_perm.value()[self.idx as int], owner.parent_level)
    }

    pub open spec fn metaregion_sound_preserved(regions0: MetaRegionOwners, regions1: MetaRegionOwners) -> bool {
        OwnerSubtree::implies(
            |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>| entry.metaregion_sound(regions0),
            |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>| entry.metaregion_sound(regions1),
        )
    }

    pub open spec fn replace_panic_condition(
        parent_owner: NodeOwner<C>,
        new_owner: EntryOwner<C>,
    ) -> bool {
        if new_owner.is_node() {
            parent_owner.level - 1 == new_owner.node.unwrap().level
        } else if new_owner.is_frame() {
            parent_owner.level == new_owner.parent_level
        } else {
            true
        }
    }

    pub open spec fn metaregion_sound_neq_preserved(
        old_entry_owner: EntryOwner<C>,
        new_entry_owner: EntryOwner<C>,
        regions0: MetaRegionOwners,
        regions1: MetaRegionOwners,
    ) -> bool {
        OwnerSubtree::implies(
            |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                entry.meta_slot_paddr_neq(old_entry_owner)
                && entry.meta_slot_paddr_neq(new_entry_owner)
                && entry.metaregion_sound(regions0),
            |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                entry.metaregion_sound(regions1),
        )
    }

    /// When the new child is NOT a node, `into_pte` doesn't modify `raw_count`.
    /// Only `path_if_in_pt` changes at `new_idx`, which `metaregion_sound` doesn't inspect.
    /// So entries with `paddr_neq(old_child)` preserve `metaregion_sound` — no
    /// `paddr_neq(new_child)` needed.
    pub open spec fn metaregion_sound_neq_old_preserved(
        old_entry_owner: EntryOwner<C>,
        regions0: MetaRegionOwners,
        regions1: MetaRegionOwners,
    ) -> bool {
        OwnerSubtree::implies(
            |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                entry.meta_slot_paddr_neq(old_entry_owner)
                && entry.metaregion_sound(regions0),
            |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                entry.metaregion_sound(regions1),
        )
    }

    /// When `alloc_if_none` allocates a new node from an absent slot, all existing entries'
    /// `metaregion_sound` is preserved in the new regions.
    ///
    /// Justification: `metaregion_sound_neq_preserved` gives preservation for entries whose paddr
    /// differs from both old_child and new_child. Old_child is absent (paddr_neq trivially true).
    /// New_child was freshly allocated from `regions0.slots` (a free slot). By PointsTo
    /// uniqueness (`active_entry_not_in_free_pool`), no existing entry can share its slot index.
    /// With both `paddr_neq` conditions, `metaregion_sound_neq_preserved` yields the result.
    pub proof fn alloc_if_none_metaregion_sound_preserved(
        old_child: EntryOwner<C>,
        new_child: EntryOwner<C>,
        regions0: MetaRegionOwners,
        regions1: MetaRegionOwners,
    )
        requires
            old_child.is_absent(),
            old_child.inv(),
            new_child.is_node(),
            regions0.inv(),
            regions0.slots.contains_key(frame_to_index(new_child.meta_slot_paddr().unwrap())),
            regions0.slot_owners[frame_to_index(new_child.meta_slot_paddr().unwrap())]
                .inner_perms.ref_count.value() == REF_COUNT_UNUSED,
            Self::metaregion_sound_neq_preserved(old_child, new_child, regions0, regions1),
        ensures
            Self::metaregion_sound_preserved(regions0, regions1),
    {
        let new_idx = frame_to_index(new_child.meta_slot_paddr().unwrap());
        // Use metaregion_sound_pred to get spec_fn values whose application covers both variables,
        // satisfying Verus's trigger-coverage requirement.
        let f = PageTableOwner::<C>::metaregion_sound_pred(regions0);
        let g = PageTableOwner::<C>::metaregion_sound_pred(regions1);
        assert(Self::metaregion_sound_preserved(regions0, regions1)) by {
            assert(OwnerSubtree::implies(f, g)) by {
                assert forall |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                    entry.inv() && f(entry, path) implies
                    #[trigger] g(entry, path)
                by {
                    // Part 1: meta_slot_paddr_neq(old_child) — trivial since old_child is absent.
                    // old_child.inv() + is_absent() ==> node is None && frame is None ==> meta_slot_paddr() is None.
                    assert(old_child.meta_slot_paddr() is None) by {
                        assert(!old_child.is_node());
                        assert(!old_child.is_frame());
                    };
                    assert(entry.meta_slot_paddr_neq(old_child));

                    // Part 2: meta_slot_paddr_neq(new_child) — by slot disjointness.
                    // If this entry has a paddr, it can't be the same as new_child's free-pool slot.
                    assert(entry.meta_slot_paddr_neq(new_child)) by {
                        if entry.meta_slot_paddr() is Some {
                            let eidx = frame_to_index(entry.meta_slot_paddr().unwrap());
                            if entry.is_node() {
                                // PointsTo uniqueness: a node's slot can't also be in the free pool.
                                EntryOwner::<C>::active_entry_not_in_free_pool(entry, regions0, new_idx);
                            } else {
                                // Frame: metaregion_sound requires ref_count != UNUSED at eidx.
                                // The free pool slot at new_idx has ref_count == UNUSED (alloc precondition).
                                // So eidx != new_idx by contradiction.
                                assert(regions0.slot_owners[eidx].inner_perms.ref_count.value() != REF_COUNT_UNUSED);
                            }
                            assert(eidx != new_idx);
                            if entry.meta_slot_paddr().unwrap() == new_child.meta_slot_paddr().unwrap() {
                                assert(frame_to_index(entry.meta_slot_paddr().unwrap())
                                    == frame_to_index(new_child.meta_slot_paddr().unwrap()));
                                assert(false);
                            }
                        }
                    };

                    // Part 3: apply metaregion_sound_neq_preserved.
                    // The antecedent f(entry, path) = paddr_neq(old) && paddr_neq(new) && relate(r0)
                    // is fully established; the conclusion g(entry, path) = relate(r1) follows.
                    assert(entry.meta_slot_paddr_neq(old_child)
                        && entry.meta_slot_paddr_neq(new_child)
                        && entry.metaregion_sound(regions0));
                };
            };
        };
    }

    pub open spec fn path_tracked_pred_preserved(regions0: MetaRegionOwners, regions1: MetaRegionOwners) -> bool {
        OwnerSubtree::implies(
            PageTableOwner::<C>::path_tracked_pred(regions0),
            PageTableOwner::<C>::path_tracked_pred(regions1),
        )
    }

    pub open spec fn new_owner_compatible(self,
        new_child: Child<C>,
        old_owner: EntryOwner<C>,
        new_owner: EntryOwner<C>,
        regions: MetaRegionOwners)
    -> bool {
        &&& old_owner.path == new_owner.path
        &&& old_owner.parent_level == new_owner.parent_level
        &&& new_owner.in_scope
        &&& new_owner.is_node() ==> {
            &&& regions.slots.contains_key(frame_to_index(new_owner.meta_slot_paddr().unwrap()))
            &&& regions.slot_owners[frame_to_index(new_owner.meta_slot_paddr().unwrap())].inner_perms.ref_count.value() !=
                REF_COUNT_UNUSED
        }
    }

    pub open spec fn parent_perms_preserved(self,
        parent_owner0: NodeOwner<C>,
        parent_owner1: NodeOwner<C>,
        guard_perm0: GuardPerm<'rcu, C>,
        guard_perm1: GuardPerm<'rcu, C>)
    -> bool {
        &&& guard_perm0.addr() == guard_perm1.addr()
        &&& guard_perm0.value().inner.inner@.ptr.addr() == guard_perm1.value().inner.inner@.ptr.addr()
        &&& forall|i: int| 0 <= i < NR_ENTRIES ==> i != self.idx ==>
            parent_owner0.children_perm.value()[i] == parent_owner1.children_perm.value()[i]
        // meta_perm is unchanged: only children_perm and meta_own are modified by entry operations.
        &&& parent_owner1.meta_perm.addr == parent_owner0.meta_perm.addr
        &&& parent_owner1.meta_perm.points_to == parent_owner0.meta_perm.points_to
        &&& parent_owner1.meta_perm.inner_perms == parent_owner0.meta_perm.inner_perms
    }
}

} // verus!
