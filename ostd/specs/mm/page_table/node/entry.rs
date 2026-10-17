use vstd::prelude::*;
use vstd_extra::{ghost_tree::*, ownership::*};

use crate::specs::{
    arch::NR_ENTRIES,
    mm::{
        frame::{mapping::frame_to_index, meta_region_owners::MetaRegionOwners},
        page_table::*,
    },
};

use crate::mm::{frame::meta::REF_COUNT_UNUSED, page_table::*};

verus! {

impl<'a, 'rcu, C: PageTableConfig> Entry<'a, 'rcu, C> {
    /// Claiming one unused slot preserves entries that refer to other slots.
    pub proof fn lemma_allocated_node_preserves_disjoint_entries(
        old_child: EntryOwner<C>,
        new_child: EntryOwner<C>,
        r0: MetaRegionOwners,
        r1: MetaRegionOwners,
    )
        requires
            old_child.is_absent(),
            new_child.is_node(),
            new_child.inv(),
            r0.inv(),
            r1.inv(),
            r0.slots == r1.slots,
            forall|i: int|
                #![trigger r1.slot_owners[i]]
                i != frame_to_index(new_child.meta_slot_paddr()->0) ==> {
                    &&& r1.slot_owners[i].same_permissions(r0.slot_owners[i])
                    &&& r1.slot_owners[i].usage == r0.slot_owners[i].usage
                    &&& r1.slot_owners[i].slot_vaddr == r0.slot_owners[i].slot_vaddr
                    &&& r0.slot_owners[i].paths_in_pt.subset_of(r1.slot_owners[i].paths_in_pt)
                    &&& r0.slot_owners[i].usage is PageTable ==> r1.slot_owners[i].paths_in_pt
                        == r0.slot_owners[i].paths_in_pt
                },
            r1.contains(frame_to_index(new_child.meta_slot_paddr()->0)),
            0 < r1.ref_count(frame_to_index(new_child.meta_slot_paddr()->0))
                <= crate::mm::frame::meta::REF_COUNT_MAX,
        ensures
            Self::metaregion_sound_neq_preserved(old_child, new_child, r0, r1),
    {
        broadcast use crate::specs::mm::frame::mapping::lemma_frame_to_index_injective;

        let idx = frame_to_index(new_child.meta_slot_paddr()->0);
        assert forall|entry: EntryOwner<C>|
            entry.inv() && entry.owned_meta_slot_paddr_neq(new_child) && entry.metaregion_sound(
                r0,
            ) implies #[trigger] entry.metaregion_sound(r1) by {
            let intermediate = r0.insert_slot_owner(
                new_child.meta_slot_paddr()->0,
                r1.slot_owners[idx],
            );
            assert(intermediate.inv());
            entry.lemma_metaregion_sound_one_slot_changed(r0, intermediate, idx);
            entry.lemma_metaregion_sound_frame_paths_changed(intermediate, r1);
        };
    }

    pub open spec fn invariants(self, owner: EntryOwner<C>, regions: MetaRegionOwners) -> bool {
        &&& owner.inv()
        &&& regions.inv()
        &&& self.wf(owner)
        &&& owner.metaregion_sound(regions)
    }

    pub open spec fn node_matching(
        self,
        owner: EntryOwner<C>,
        parent_owner: NodeOwner<C>,
        guard: PageTableGuard<'rcu, C>,
    ) -> bool {
        &&& parent_owner.level() == owner.parent_level
        &&& parent_owner.inv()
        &&& parent_owner.relate_guard(guard)
        &&& owner.match_pte(parent_owner.children_perm.value()[self.idx as int], owner.parent_level)
    }

    pub open spec fn metaregion_sound_preserved(
        regions0: MetaRegionOwners,
        regions1: MetaRegionOwners,
    ) -> bool {
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
            parent_owner.level() - 1 == new_owner.node().level()
        } else if new_owner.is_frame() {
            parent_owner.level() == new_owner.parent_level
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
                entry.owned_meta_slot_paddr_neq(old_entry_owner) && entry.owned_meta_slot_paddr_neq(
                    new_entry_owner,
                ) && entry.metaregion_sound(regions0),
            |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>| entry.metaregion_sound(regions1),
        )
    }

    /// Preservation for entries whose counted slot is disjoint from the old entry.
    /// Untracked physical aliases impose no counted-metadata exclusion.
    pub open spec fn metaregion_sound_neq_old_preserved(
        old_entry_owner: EntryOwner<C>,
        regions0: MetaRegionOwners,
        regions1: MetaRegionOwners,
    ) -> bool {
        OwnerSubtree::implies(
            |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                entry.owned_meta_slot_paddr_neq(old_entry_owner) && entry.metaregion_sound(
                    regions0,
                ),
            |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>| entry.metaregion_sound(regions1),
        )
    }

    /// When `alloc_if_none` allocates a new node from an absent slot, all existing entries'
    /// `metaregion_sound` is preserved in the new regions.
    ///
    /// Counted entries cannot occupy the newly claimed unused slot, and raw
    /// physical aliases impose no counted-metadata exclusion.
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
            regions0.contains(frame_to_index(new_child.meta_slot_paddr()->0)),
            regions0.slot_owner(new_child.meta_slot_paddr()->0).ref_count() == REF_COUNT_UNUSED,
            Self::metaregion_sound_neq_preserved(old_child, new_child, regions0, regions1),
        ensures
            Self::metaregion_sound_preserved(regions0, regions1),
    {
        let new_idx = frame_to_index(new_child.meta_slot_paddr().unwrap());
        let f = PageTableOwner::<C>::metaregion_sound_pred(regions0);
        let g = PageTableOwner::<C>::metaregion_sound_pred(regions1);

        assert(old_child.meta_slot_paddr() is None);

        assert forall|entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
            entry.inv() && f(entry, path) implies #[trigger] g(entry, path) by {
            if entry.meta_slot_paddr() is Some && entry.is_node() {
                EntryOwner::<C>::lemma_active_entry_not_in_free_pool(entry, regions0, new_idx);
            }
        };
    }

    pub open spec fn path_tracked_pred_preserved(
        regions0: MetaRegionOwners,
        regions1: MetaRegionOwners,
    ) -> bool {
        OwnerSubtree::implies(
            PageTableOwner::<C>::path_tracked_pred(regions0),
            PageTableOwner::<C>::path_tracked_pred(regions1),
        )
    }

    pub open spec fn new_owner_compatible(
        self,
        new_child: Child<C>,
        old_owner: EntryOwner<C>,
        new_owner: EntryOwner<C>,
        regions: MetaRegionOwners,
    ) -> bool {
        &&& old_owner.path == new_owner.path
        &&& old_owner.parent_level == new_owner.parent_level
        &&& new_owner.is_node() ==> {
            &&& regions.contains(frame_to_index(new_owner.meta_slot_paddr()->0))
            &&& regions.slot_owner(new_owner.meta_slot_paddr()->0).ref_count() != REF_COUNT_UNUSED
        }
    }

    pub open spec fn parent_perms_preserved(
        self,
        parent_owner0: NodeOwner<C>,
        parent_owner1: NodeOwner<C>,
    ) -> bool {
        &&& forall|i: int|
            0 <= i < NR_ENTRIES ==> i != self.idx ==> parent_owner0.children_perm.value()[i]
                == parent_owner1.children_perm.value()[i]
        &&& parent_owner1.slot_index == parent_owner0.slot_index
        &&& parent_owner1.level() == parent_owner0.level()
        &&& parent_owner1.tree_level == parent_owner0.tree_level
        &&& parent_owner1.meta_own.nr_children.id() == parent_owner0.meta_own.nr_children.id()
        &&& parent_owner1.meta_own.stray == parent_owner0.meta_own.stray
    }
}

} // verus!
