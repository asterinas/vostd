/// CursorOwner-level preservation lemmas for transient `MetaRegionOwners`
/// updates that affect at most one slot. Written as preparation for Phase 3b
/// of the `paths_in_pt` refactor, where map/unmap operations insert or remove
/// a single tree path from a single frame slot and must show that the global
/// `Cursor::invariants` survives the edit.
///
/// Each lemma here lifts [`EntryOwner`]-level preservation facts (from
/// `entry_owners.rs`) over the full cursor tree.
use vstd::prelude::*;

use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;

use crate::mm::frame::meta::mapping::frame_to_index;
use crate::mm::page_table::*;
use crate::specs::arch::mm::{NR_ENTRIES, NR_LEVELS};
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::page_table::cursor::owners::{CursorContinuation, CursorOwner};
use crate::specs::mm::page_table::node::entry_owners::EntryOwner;
use crate::specs::mm::page_table::owners::{OwnerSubtree, PageTableOwner};

verus! {

impl<'rcu, C: PageTableConfig> CursorOwner<'rcu, C> {

    /// Tree-wide predicate: no page-table node in either the cursor's tree
    /// children or its continuation path has metadata slot index `idx`.
    /// Used as the "sanity" precondition of the path-insert preservation
    /// lemma: the only kind of entry it can touch with the new path is a
    /// frame. Callers satisfy it by observing that page-table node metadata
    /// lives in `FRAME_METADATA_RANGE`, which is disjoint from any data-frame
    /// paddr (where `paths_in_pt` inserts happen).
    pub open spec fn no_node_at_idx(self, idx: usize) -> bool {
        &&& self.map_full_tree(
            |e: EntryOwner<C>, _p: TreePath<NR_ENTRIES>|
                e.is_node() && e.meta_slot_paddr() is Some
                    ==> frame_to_index(e.meta_slot_paddr().unwrap()) != idx)
        &&& forall |i: int| #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS ==> {
                let e = self.continuations[i].entry_own;
                e.is_node() && e.meta_slot_paddr() is Some
                    ==> frame_to_index(e.meta_slot_paddr().unwrap()) != idx
            }
    }

    /// Pointwise conjunction of two tree-wide predicates: if `self.map_full_tree(f)`
    /// and `self.map_full_tree(guard)` hold, then `self.map_full_tree(f && guard)`
    /// holds. A thin wrapper around `OwnerSubtree::map_implies_and` applied per
    /// continuation + per child; extracted so callers don't have to re-derive
    /// the same nested `assert forall ... by { map_implies_and(...) }` block.
    pub proof fn and_map_full_tree(
        self,
        f: spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool,
        guard: spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool,
    )
        requires
            self.inv(),
            self.map_full_tree(f),
            self.map_full_tree(guard),
        ensures
            self.map_full_tree(
                |e: EntryOwner<C>, p: TreePath<NR_ENTRIES>| f(e, p) && guard(e, p)),
    {
        let combined = |e: EntryOwner<C>, p: TreePath<NR_ENTRIES>|
            f(e, p) && guard(e, p);
        assert forall |i: int| #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS
        implies
            self.continuations[i].map_children(combined)
        by {
            let cont = self.continuations[i];
            reveal(CursorContinuation::inv_children);
            assert forall |j: int| #![trigger cont.children[j]]
                0 <= j < cont.children.len() && cont.children[j] is Some
            implies
                cont.children[j].unwrap()
                    .tree_predicate_map(cont.path().push_tail(j as usize), combined)
            by {
                cont.inv_children_unroll(j);
                OwnerSubtree::map_implies_and(
                    cont.children[j].unwrap(),
                    cont.path().push_tail(j as usize),
                    f, guard, combined);
            };
        };
    }

    /// Discharge `no_node_at_idx(changed_idx)` from the observation that
    /// `changed_idx` is the index of a slot currently sitting in the free
    /// pool (`regions.slots.contains_key(changed_idx)`). The argument uses
    /// `EntryOwner::active_entry_not_in_free_pool`: an active node's
    /// metadata slot is never simultaneously in the free pool, so any node
    /// in the cursor tree must have a different slot index than
    /// `changed_idx`.
    ///
    /// Callers doing a `paths_in_pt.insert` at a frame's data-slot
    /// (e.g., `map` and the huge-page split) use this helper to
    /// satisfy the precondition of
    /// [`Self::metaregion_preserved_under_path_insert`].
    pub proof fn no_node_at_idx_from_slot_key(
        self,
        regions: MetaRegionOwners,
        changed_idx: usize,
    )
        requires
            self.inv(),
            regions.inv(),
            self.metaregion_sound(regions),
            regions.slots.contains_key(changed_idx),
        ensures
            self.no_node_at_idx(changed_idx),
    {
        let msp = PageTableOwner::<C>::metaregion_sound_pred(regions);
        let target = |e: EntryOwner<C>, _p: TreePath<NR_ENTRIES>|
            e.is_node() && e.meta_slot_paddr() is Some
                ==> frame_to_index(e.meta_slot_paddr().unwrap()) != changed_idx;

        assert(OwnerSubtree::implies(msp, target)) by {
            assert forall |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                entry.inv() && msp(entry, path)
            implies #[trigger] target(entry, path) by {
                if entry.is_node() && entry.meta_slot_paddr() is Some {
                    EntryOwner::<C>::active_entry_not_in_free_pool(
                        entry, regions, changed_idx);
                }
            };
        };
        self.map_children_implies(msp, target);

        assert forall |i: int| #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS
        implies {
            let e = self.continuations[i].entry_own;
            e.is_node() && e.meta_slot_paddr() is Some
                ==> frame_to_index(e.meta_slot_paddr().unwrap()) != changed_idx
        } by {
            let entry = self.continuations[i].entry_own;
            if entry.is_node() && entry.meta_slot_paddr() is Some {
                EntryOwner::<C>::active_entry_not_in_free_pool(
                    entry, regions, changed_idx);
            }
        };
    }

    /// Preservation of the cursor-level metaregion invariants when the only
    /// change to `regions` is the **insertion** of a new path into the
    /// `paths_in_pt` set at a single slot.
    pub proof fn metaregion_preserved_under_path_insert(
        self,
        regions0: MetaRegionOwners,
        regions1: MetaRegionOwners,
        changed_idx: usize,
        new_path: TreePath<NR_ENTRIES>,
    )
        requires
            self.inv(),
            self.metaregion_sound(regions0),
            regions0.inv(),
            regions0.slot_owners.contains_key(changed_idx),
            regions1.slots == regions0.slots,
            regions1.slot_owners.dom() =~= regions0.slot_owners.dom(),
            forall |i: usize| #![trigger regions1.slot_owners[i]]
                i != changed_idx ==> regions0.slot_owners[i] == regions1.slot_owners[i],
            regions1.slot_owners[changed_idx].inner_perms
                == regions0.slot_owners[changed_idx].inner_perms,
            regions1.slot_owners[changed_idx].self_addr
                == regions0.slot_owners[changed_idx].self_addr,
            regions1.slot_owners[changed_idx].raw_count
                == regions0.slot_owners[changed_idx].raw_count,
            regions1.slot_owners[changed_idx].usage
                == regions0.slot_owners[changed_idx].usage,
            regions1.slot_owners[changed_idx].paths_in_pt
                == regions0.slot_owners[changed_idx].paths_in_pt.insert(new_path),
            self.no_node_at_idx(changed_idx),
        ensures
            self.metaregion_sound(regions1),
            self.metaregion_correct(regions0) ==> self.metaregion_correct(regions1),
    {
        let f = PageTableOwner::<C>::metaregion_sound_pred(regions0);
        let g = PageTableOwner::<C>::metaregion_sound_pred(regions1);
        let guard = |entry: EntryOwner<C>, _p: TreePath<NR_ENTRIES>|
            entry.is_node() && entry.meta_slot_paddr() is Some
                ==> frame_to_index(entry.meta_slot_paddr().unwrap()) != changed_idx;
        let f_strong = |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
            f(entry, path) && guard(entry, path);

        assert(OwnerSubtree::implies(f_strong, g)) by {
            assert forall |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                entry.inv() && f_strong(entry, path)
            implies #[trigger] g(entry, path) by {
                if entry.meta_slot_paddr() is Some {
                    let eidx = frame_to_index(entry.meta_slot_paddr().unwrap());
                    if eidx != changed_idx {
                        entry.metaregion_sound_one_slot_changed(
                            regions0, regions1, changed_idx);
                    } else {
                        assert(!entry.is_node());
                        assert(entry.is_frame());
                        if entry.parent_level > 1 {
                            assert(entry.frame_sub_pages_valid(regions1));
                        }
                    }
                }
            };
        };

        self.and_map_full_tree(f, guard);
        self.map_children_implies(f_strong, g);

        assert forall |i: int| #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS
        implies
            self.continuations[i].entry_own.metaregion_sound(regions1)
        by {
            let cont_entry = self.continuations[i].entry_own;
            if cont_entry.meta_slot_paddr() is Some {
                cont_entry.metaregion_sound_one_slot_changed(
                    regions0, regions1, changed_idx);
            }
        };

        if self.metaregion_correct(regions0) {
            let e = PageTableOwner::<C>::path_tracked_pred(regions0);
            let h = PageTableOwner::<C>::path_tracked_pred(regions1);
            let e_strong = |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                e(entry, path) && guard(entry, path);

            assert(OwnerSubtree::implies(e_strong, h)) by {
                assert forall |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                    entry.inv() && e_strong(entry, path)
                implies #[trigger] h(entry, path) by {};
            };

            self.and_map_full_tree(e, guard);
            self.map_children_implies(e_strong, h);

            assert forall |i: int| #![trigger self.continuations[i]]
                self.level - 1 <= i < NR_LEVELS
            implies
                PageTableOwner::<C>::path_tracked_pred(regions1)(
                    self.continuations[i].entry_own,
                    self.continuations[i].path())
            by {};
        }
    }
}

} // verus!
