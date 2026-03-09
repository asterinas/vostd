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
        &&& owner.relate_region(regions)
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

    pub open spec fn relate_region_preserved(regions0: MetaRegionOwners, regions1: MetaRegionOwners) -> bool {
        OwnerSubtree::implies(
            |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>| entry.relate_region(regions0),
            |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>| entry.relate_region(regions1),
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

    pub open spec fn relate_region_neq_preserved(
        old_entry_owner: EntryOwner<C>,
        new_entry_owner: EntryOwner<C>,
        regions0: MetaRegionOwners,
        regions1: MetaRegionOwners,
    ) -> bool {
        OwnerSubtree::implies(
            |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                entry.meta_slot_paddr_neq(old_entry_owner)
                && entry.meta_slot_paddr_neq(new_entry_owner)
                && entry.relate_region(regions0),
            |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                entry.relate_region(regions1),
        )
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
        &&& old_owner.meta_slot_paddr_neq(new_owner)
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
    }
}

} // verus!
