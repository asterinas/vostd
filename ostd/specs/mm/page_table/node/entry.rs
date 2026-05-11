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

impl<'a, 'rcu, C: PageTableConfig> Entry<'a, 'rcu, C> {
    pub open spec fn invariants(self, owner: EntryOwner<C>, regions: MetaRegionOwners) -> bool {
        &&& owner.inv()
        &&& regions.inv()
        &&& self.wf(owner)
        &&& owner.metaregion_sound(regions)
    }

    pub open spec fn node_matching(self, owner: EntryOwner<C>, parent_owner: NodeOwner<C>, guard: PageTableGuard<'rcu, C>) -> bool {
        &&& parent_owner.level == owner.parent_level
        &&& parent_owner.inv()
        &&& guard.inner.inner@.ptr.addr() == parent_owner.meta_perm.points_to.addr()
        &&& guard.inner.inner@.wf(parent_owner)
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

    pub open spec fn replace_nonpanic_condition(
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
    /// Only `paths_in_pt` changes at `new_idx`, which `metaregion_sound` doesn't inspect.
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
            // Allocator-pool / MMIO disjointness: the freshly-allocated node's
            // paddr is non-MMIO. Rules out an MMIO-frame entry sitting at the
            // same idx as the new node (delivered by `PageTableNode::alloc`).
            !crate::specs::mm::frame::meta_owners::is_mmio_paddr(
                new_child.meta_slot_paddr().unwrap()),
            Self::metaregion_sound_neq_preserved(old_child, new_child, regions0, regions1),
        ensures
            Self::metaregion_sound_preserved(regions0, regions1),
    {
        broadcast use crate::specs::mm::frame::meta_owners::axiom_mmio_usage_iff_mmio_paddr;
        let new_idx = frame_to_index(new_child.meta_slot_paddr().unwrap());
        let f = PageTableOwner::<C>::metaregion_sound_pred(regions0);
        let g = PageTableOwner::<C>::metaregion_sound_pred(regions1);

        assert(old_child.meta_slot_paddr() is None);

        assert forall |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
            entry.inv() && f(entry, path) implies #[trigger] g(entry, path)
        by {
            if entry.meta_slot_paddr() is Some && entry.is_node() {
                EntryOwner::<C>::active_entry_not_in_free_pool(entry, regions0, new_idx);
            }
            // Frame entries colliding at new_idx are ruled out: either the
            // slot's `usage != MMIO` (then `metaregion_sound` requires
            // `rc != UNUSED`, contradicting the precondition), or the slot's
            // `usage == MMIO` (then by axiom the paddr is MMIO, contradicting
            // the allocator's non-MMIO guarantee).
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
        parent_owner1: NodeOwner<C>)
    -> bool {
        &&& forall|i: int| 0 <= i < NR_ENTRIES ==> i != self.idx ==>
            parent_owner0.children_perm.value()[i] == parent_owner1.children_perm.value()[i]
        // meta_perm is unchanged: only children_perm and meta_own are modified by entry operations.
        &&& parent_owner1.meta_perm.addr() == parent_owner0.meta_perm.addr()
        &&& parent_owner1.meta_perm.points_to == parent_owner0.meta_perm.points_to
        &&& parent_owner1.meta_perm.inner_perms == parent_owner0.meta_perm.inner_perms
    }
}

} // verus!
