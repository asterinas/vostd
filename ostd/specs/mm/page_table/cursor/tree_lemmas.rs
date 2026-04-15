/// Tree-predicate lifting, tree entry level constraints, and tree membership
/// lemmas for `CursorContinuation` and `CursorOwner`.
///
/// Themes moved here from `owners.rs`:
/// - **Theme 5**: Tree predicate lifting (`map_children_lift`, `map_children_implies`, etc.)
/// - **Theme 11**: Tree entry level constraints (`cur_entry_node_implies_level_gt_1`, etc.)
/// - **Theme 12**: Tree membership & tracking (`absent_not_in_tree`, `not_in_tree_from_not_mapped`)
use vstd::prelude::*;

use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;

use crate::mm::page_table::*;
use crate::mm::page_prop::PageProperty;
use crate::mm::{Paddr, PagingLevel, Vaddr};
use crate::specs::arch::mm::{NR_ENTRIES, NR_LEVELS, PAGE_SIZE};
use crate::mm::frame::meta::mapping::frame_to_index;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::page_table::cursor::owners::{CursorContinuation, CursorOwner};
use crate::specs::mm::page_table::node::entry_owners::EntryOwner;
use crate::specs::mm::page_table::node::GuardPerm;
use crate::specs::mm::page_table::owners::*;
use crate::specs::mm::page_table::AbstractVaddr;
use crate::specs::mm::page_table::Mapping;

use core::ops::Range;

verus! {

// ─── Tree predicate lifting (CursorContinuation) ───────────────────

impl<'rcu, C: PageTableConfig> CursorContinuation<'rcu, C> {

    /// Lift map_children(f) to map_children(g) when implies(f, g).
    pub proof fn map_children_lift(
        self,
        f: spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool,
        g: spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool,
    )
        requires
            self.inv(),
            self.map_children(f),
            OwnerSubtree::implies(f, g),
        ensures
            self.map_children(g),
    {
        assert forall|j: int|
            #![auto]
            0 <= j < self.children.len()
                && self.children[j] is Some implies
                self.children[j].unwrap().tree_predicate_map(
                    self.path().push_tail(j as usize), g)
        by {
            self.inv_children_unroll(j);
            OwnerSubtree::map_implies(
                self.children[j].unwrap(),
                self.path().push_tail(j as usize),
                f, g,
            );
        };
    }

    /// Lift map_children from f to g when siblings (j != idx) come from
    /// cont0 which had map_children(f), and the child at idx (if present)
    /// already satisfies g.
    pub proof fn map_children_lift_skip_idx(
        self,
        cont0: Self,
        idx: int,
        f: spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool,
        g: spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool,
    )
        requires
            0 <= idx < NR_ENTRIES,
            OwnerSubtree::implies(f, g),
            cont0.inv(),
            cont0.map_children(f),
            self.path() == cont0.path(),
            self.children.len() == cont0.children.len(),
            forall|j: int| #![auto]
                0 <= j < NR_ENTRIES && j != idx ==>
                self.children[j] == cont0.children[j],
            self.children[idx] is Some ==>
                self.children[idx].unwrap().tree_predicate_map(
                    self.path().push_tail(idx as usize), g),
        ensures
            self.map_children(g),
    {
        assert forall|j: int|
            #![auto]
            0 <= j < self.children.len()
                && self.children[j] is Some implies
                self.children[j].unwrap().tree_predicate_map(
                    self.path().push_tail(j as usize), g)
        by {
            if j != idx {
                cont0.inv_children_unroll(j);
                OwnerSubtree::map_implies(
                    cont0.children[j].unwrap(),
                    cont0.path().push_tail(j as usize), f, g);
            }
        };
    }

    pub proof fn as_subtree_restore(self, child: Self)
        requires
            self.inv(),
            child.inv(),
            self.all_but_index_some(),
            child.all_some(),
        ensures
            self.restore_spec(child).0.as_subtree() ==
            self.put_child_spec(child.as_subtree()).as_subtree(),
    {
        assert(self.put_child_spec(child.as_subtree()).children ==
        self.children.update(self.idx as int, Some(child.as_subtree())));
    }
}

// ─── Tree predicate lifting (CursorOwner) ──────────────────────────

impl<'rcu, C: PageTableConfig> CursorOwner<'rcu, C> {

    pub proof fn map_children_implies(
        self,
        f: spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool,
        g: spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool,
    )
    requires
        self.inv(),
        OwnerSubtree::implies(f, g),
        forall|i: int|
            #![trigger self.continuations[i]]
                self.level - 1 <= i < NR_LEVELS ==>
                    self.continuations[i].map_children(f),
    ensures
        forall|i: int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS ==>
                self.continuations[i].map_children(g),
    {
        assert forall|i: int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS implies self.continuations[i].map_children(g) by {
                let cont = self.continuations[i];
                reveal(CursorContinuation::inv_children);
                assert forall|j: int|
                    #![trigger cont.children[j]]
                    0 <= j < cont.children.len() && cont.children[j] is Some
                        implies cont.children[j].unwrap().tree_predicate_map(cont.path().push_tail(j as usize), g) by {
                            cont.inv_children_unroll(j);
                            OwnerSubtree::map_implies(cont.children[j].unwrap(), cont.path().push_tail(j as usize), f, g);
                    }
            }
    }

    // ─── Tree entry level constraints ──────────────────────────

    pub proof fn cur_entry_node_implies_level_gt_1(self)
        requires
            self.inv(),
            self.cur_entry_owner().is_node(),
        ensures
            self.level > 1,
    {
        self.cur_subtree_inv();
        let cont = self.continuations[self.level - 1];
        let child = self.cur_subtree();
        assert(child.level < INC_LEVELS - 1);
        assert(cont.level() == self.level) by {
            if self.level == 1 {} else if self.level == 2 {} else if self.level == 3 {} else {}
        };
    }

    /// A frame entry at the cursor's current level that doesn't fit the aligned range
    /// `[cur_va, end)` must be at level > 1.
    /// Justification: At level 1, `page_size(1) == BASE_PAGE_SIZE`. Since the cursor VA
    /// and `end` are BASE_PAGE_SIZE-aligned and `cur_va < end`, we have
    /// `cur_va + page_size(1) <= end`, so a level-1 frame always fits. Therefore
    /// `!cur_entry_fits_range` implies `level > 1`.
    pub proof fn frame_not_fits_implies_level_gt_1(
        self,
        cur_entry_fits_range: bool,
        cur_va: Vaddr,
        end: Vaddr,
    )
        requires
            self.inv(),
            self.cur_entry_owner().is_frame(),
            !cur_entry_fits_range,
            cur_va < end,
            // cur_va is the cursor's current VA (from the call site: cur_va == self.va).
            cur_va == self.cur_va(),
            // Definition: cur_entry_fits_range iff cur_va is at start of entry AND entry end <= end.
            cur_entry_fits_range == (
                cur_va == self.cur_va_range().start.to_vaddr()
                && self.cur_va_range().end.to_vaddr() <= end),
            // cur_va and end are PAGE_SIZE-aligned
            cur_va as nat % PAGE_SIZE as nat == 0,
            end as nat % PAGE_SIZE as nat == 0,
        ensures
            self.level > 1
    {
        // At level 1, page_size(1) == PAGE_SIZE. cursor inv gives va.offset == 0,
        // so align_down(va, PAGE_SIZE) == va. The range is [va, va + PAGE_SIZE).
        // cur_va == va (precondition) and cur_va + PAGE_SIZE <= end (from alignment
        // and cur_va < end). Hence cur_entry_fits_range == true, contradicting
        // !cur_entry_fits_range.
        if self.level == 1 {
            crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_spec_level1();
            self.va.align_down_concrete(1);
            self.va.align_up_concrete(1);
            self.va.align_diff(1);
        }
    }

    // ─── Tree membership & tracking ────────────────────────────

    pub open spec fn not_in_tree(self, owner: EntryOwner<C>) -> bool {
        self.map_full_tree(|owner0: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
            owner0.meta_slot_paddr_neq(owner))
    }

    pub proof fn absent_not_in_tree(self, owner: EntryOwner<C>)
        requires
            self.inv(),
            owner.inv(),
            owner.is_absent(),
        ensures
            self.not_in_tree(owner),
    {
        let g = |e: EntryOwner<C>, p: TreePath<NR_ENTRIES>| e.meta_slot_paddr_neq(owner);
        let nsp = PageTableOwner::<C>::not_in_scope_pred();
        assert(OwnerSubtree::implies(nsp, g)) by {
            assert forall |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                entry.inv() && !entry.in_scope implies #[trigger] g(entry, path) by {};
        };
        assert forall |i: int| #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS implies self.continuations[i].map_children(g)
        by {
            let cont = self.continuations[i];
            reveal(CursorContinuation::inv_children);
            assert forall |j: int| 0 <= j < NR_ENTRIES
                && #[trigger] cont.children[j] is Some implies
                cont.children[j].unwrap().tree_predicate_map(cont.path().push_tail(j as usize), g)
            by {
                cont.inv_children_unroll(j);
                PageTableOwner::tree_not_in_scope(cont.children[j].unwrap(), cont.path().push_tail(j as usize));
                cont.children[j].unwrap().map_implies(cont.path().push_tail(j as usize), nsp, g);
            };
        };
    }

    /// If the cursor owner's tree satisfies `metaregion_correct(regions)`, and a new entry's
    /// physical address is not currently tracked in the page table (`paths_in_pt.is_empty()`),
    /// then no existing entry in the tree has the same physical address as the new entry.
    ///
    /// This lemma encapsulates the `map_children_implies` proof for `not_in_tree`, factored out
    /// so it runs in its own Z3 context (avoiding rlimit issues when called from large functions).
    /// If `paths_in_pt.is_empty()` at the new entry's slot, then no NODE in the tree
    /// has the same paddr (node metaregion_sound requires a singleton path set).
    /// Frames CAN share paddrs (tracked separately by `paths_in_pt` membership).
    pub proof fn not_in_tree_from_not_mapped(
        self,
        regions: MetaRegionOwners,
        new_entry: EntryOwner<C>,
    )
        requires
            self.inv(),
            self.metaregion_correct(regions),
            new_entry.meta_slot_paddr() is Some,
            regions.slot_owners[
                frame_to_index(new_entry.meta_slot_paddr().unwrap())
            ].paths_in_pt.is_empty(),
        ensures
            // Only guarantees paddr_neq for node entries (frames can share paddrs).
            self.map_full_tree(|e: EntryOwner<C>, p: TreePath<NR_ENTRIES>|
                e.is_node() ==> e.meta_slot_paddr_neq(new_entry)),
    {
        let pa = new_entry.meta_slot_paddr().unwrap();
        let g = |e: EntryOwner<C>, p: TreePath<NR_ENTRIES>|
            e.is_node() ==> e.meta_slot_paddr_neq(new_entry);
        assert(OwnerSubtree::implies(PageTableOwner::<C>::path_tracked_pred(regions), g)) by {
            assert forall |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                PageTableOwner::<C>::path_tracked_pred(regions)(entry, path)
                implies #[trigger] g(entry, path) by {
                if entry.is_node() && entry.meta_slot_paddr() is Some
                    && entry.meta_slot_paddr().unwrap() == pa {
                    // Node: path_tracked_pred gives paths_in_pt == set![entry.path] (non-empty).
                    // But precondition says paths_in_pt.is_empty(). Contradiction.
                    assert(false);
                }
            };
        };
        self.map_children_implies(PageTableOwner::<C>::path_tracked_pred(regions), g);
    }
}

} // verus!
