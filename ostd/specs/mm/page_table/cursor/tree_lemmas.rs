//! Tree-predicate lifting, tree entry level constraints, and tree membership
//! lemmas for `CursorContinuation` and `CursorOwner`.
use vstd::{
    arithmetic::div_mod::{lemma_small_mod, lemma_sub_mod_noop},
    prelude::*,
};
use vstd_extra::{arithmetic::lemma_nat_align_down_sound, ghost_tree::*, ownership::*};

use crate::specs::{
    arch::{NR_ENTRIES, NR_LEVELS, PAGE_SIZE},
    mm::page_table::{
        cursor::owners::{CursorContinuation, CursorOwner},
        node::entry_owners::EntryOwner,
        owners::*,
    },
};

use crate::arch::mm::PagingConsts;
use crate::mm::{Paddr, PagingConstsTrait, PagingLevel, Vaddr, page_prop::PageProperty, page_size, page_table::*};
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
        reveal(CursorContinuation::map_children);
        assert forall|j: int|
            #![auto]
            0 <= j < self.children.len()
                && self.children[j] is Some implies self.children[j].unwrap().subtree_satisfies(
            self.path().push_tail(j),
            g,
        ) by {
            self.lemma_inv_children_unroll(j);
            OwnerSubtree::lemma_subtree_satisfies_implies(
                self.children[j].unwrap(),
                self.path().push_tail(j),
                f,
                g,
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
            forall|j: int|
                #![auto]
                0 <= j < NR_ENTRIES && j != idx ==> self.children[j] == cont0.children[j],
            self.children[idx] is Some ==> self.children[idx]->0.subtree_satisfies(
                self.path().push_tail(idx as int),
                g,
            ),
        ensures
            self.map_children(g),
    {
        reveal(CursorContinuation::map_children);
        assert forall|j: int|
            #![auto]
            0 <= j < self.children.len()
                && self.children[j] is Some implies self.children[j].unwrap().subtree_satisfies(
            self.path().push_tail(j),
            g,
        ) by {
            if j != idx {
                cont0.lemma_inv_children_unroll(j);
                OwnerSubtree::lemma_subtree_satisfies_implies(
                    cont0.children[j].unwrap(),
                    cont0.path().push_tail(j),
                    f,
                    g,
                );
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
            self.restore(child).0.as_subtree() == self.put_child(child.as_subtree()).as_subtree(),
    {
        assert(self.put_child(child.as_subtree()).children == self.children.update(
            self.idx as int,
            Some(child.as_subtree()),
        ));
    }
}

// ─── Tree predicate lifting (CursorOwner) ──────────────────────────
impl<'rcu, C: PageTableConfig> CursorOwner<'rcu, C> {
    /// Initial decomposition retains every raw-node count below the root.
    pub proof fn new_preserves_raw_metadata_coverage(
        subtree: OwnerSubtree<C>,
        idx: usize,
        guard: PageTableGuard<'rcu, C>,
        metadata: NodeMetadataLoans<'rcu>,
    )
        requires
            C::NR_LEVELS() == NR_LEVELS,
            PageTableOwner(subtree).inv(),
            PageTableOwner(subtree).raw_metadata_covers(metadata.permissions()),
        ensures
            Self::new(subtree, idx, guard, metadata).raw_metadata_covers(),
    {
        broadcast use group_ghost_tree_lemmas;
        reveal(CursorContinuation::map_children);
        let next = Self::new(subtree, idx, guard, metadata);
        let f = PageTableOwner::<C>::raw_metadata_pred(metadata.permissions(), subtree.value().path);
        assert(subtree.level() < INC_LEVELS - 1);
        assert forall|j: int| 0 <= j < subtree.children().len()
            && #[trigger] subtree.children()[j] is Some implies
                subtree.child(j).subtree_satisfies(subtree.value().path.push_tail(j), f) by {
            subtree.lemma_subtree_satisfies_unroll_once(subtree.value().path, f, j);
        };
        assert(next.continuations[NR_LEVELS - 1].map_children(f));
    }

    /// The current raw entry is covered even when its ancestors are decomposed.
    pub proof fn lemma_cur_metadata_covered(self)
        requires
            self.inv(),
            self.raw_metadata_covers(),
        ensures
            self.cur_entry_owner().raw_node_token_in_store(self.metadata.permissions()),
    {
        self.lemma_inv_continuation(self.level - 1);
        self.lemma_cur_subtree_inv();
        let cont = self.continuations[self.level - 1];
        let f = PageTableOwner::<C>::raw_metadata_pred(
            self.metadata.permissions(), self.continuations[NR_LEVELS - 1].path(),
        );
        cont.lemma_map_children_unroll(f, cont.idx as int);
        cont.lemma_inv_children_rel_unroll(cont.idx as int);
    }

    /// Decomposing a child into a continuation preserves every tree predicate;
    /// the moved structural owner need not contain the borrowed count.
    pub proof fn push_level_preserves_tree_predicate(
        self,
        guard: PageTableGuard<'rcu, C>,
        f: spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool,
    )
        requires
            self.inv(),
            self.level > 1,
            self.tree_satisfies(f),
        ensures
            self.push_level_owner(guard).tree_satisfies(f),
    {
        reveal(CursorContinuation::map_children);
        self.lemma_inv_continuation(self.level - 1);
        let cont = self.continuations[self.level - 1];
        cont.lemma_inv_children_unroll(cont.idx as int);
        cont.lemma_map_children_unroll(f, cont.idx as int);
        let subtree = cont.child();
        let path = cont.path().push_tail(cont.idx as int);
        let next = self.push_level_owner(guard);
        assert forall|i: int| #![trigger next.continuations[i]]
            next.level - 1 <= i < NR_LEVELS implies
                next.continuations[i].map_children(f) by {
            if i == self.level - 2 {
                assert forall|j: int| #![trigger subtree.children()[j]]
                    0 <= j < subtree.children().len() && subtree.has_child(j) implies
                        subtree.child(j).subtree_satisfies(path.push_tail(j), f) by {
                    subtree.lemma_subtree_satisfies_unroll_once(path, f, j);
                };
            }
        };
    }

    /// Restoring a decomposed node to its parent preserves the same predicate.
    pub proof fn pop_level_preserves_tree_predicate(
        self,
        f: spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool,
    )
        requires
            self.inv(),
            self.level < NR_LEVELS,
            self.tree_satisfies(f),
        ensures
            self.pop_level_owner().0.tree_satisfies(f),
    {
        broadcast use group_ghost_tree_lemmas;
        reveal(CursorContinuation::map_children);
        let child = self.continuations[self.level - 1];
        let parent = self.continuations[self.level as int];
        self.lemma_inv_continuation(self.level - 1);
        child.as_page_table_owner_preserves_view_mappings();
        assert(f(child.entry_own, child.path()));
        assert(child.map_children(f));
        assert forall|j: int| 0 <= j < child.children.len()
            && #[trigger] child.as_subtree().has_child(j) implies
                child.as_subtree().child(j).subtree_satisfies(child.path().push_tail(j), f) by {
            child.lemma_map_children_unroll(f, j);
        };
        assert(child.as_subtree().subtree_satisfies(child.path(), f));
        let next = self.pop_level_owner().0;
        assert forall|i: int| #![trigger next.continuations[i]]
            next.level - 1 <= i < NR_LEVELS implies
                next.continuations[i].map_children(f) by {
        };
    }

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
                self.level - 1 <= i < NR_LEVELS ==> self.continuations[i].map_children(f),
        ensures
            forall|i: int|
                #![trigger self.continuations[i]]
                self.level - 1 <= i < NR_LEVELS ==> self.continuations[i].map_children(g),
    {
        assert forall|i: int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS implies self.continuations[i].map_children(g) by {
            self.lemma_inv_continuation(i);
            self.continuations[i].map_children_lift(f, g);
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
        self.lemma_cur_subtree_inv();
    }

    /// A frame entry at the cursor's current level that doesn't fit the aligned range
    /// `[cur_va, end)` must be at level > 1.
    /// Justification: At level 1, `page_size(1) == BASE_PAGE_SIZE`. Since the cursor VA
    /// and `end` are BASE_PAGE_SIZE-aligned and `cur_va < end`, we have
    /// `cur_va + page_size(1) <= end`, so a level-1 frame always fits. Therefore
    /// `!cur_entry_fits_range` implies `level > 1`.
    #[verifier::spinoff_prover]
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
            cur_entry_fits_range == (cur_va == self.cur_va_range().start && self.cur_va_range().end
                <= end),
            // cur_va and end are PAGE_SIZE-aligned
            cur_va as nat % PAGE_SIZE as nat == 0,
            end as nat % PAGE_SIZE as nat == 0,
        ensures
            self.level > 1,
    {
        if self.level == 1 {
            crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_base::<
                PagingConsts,
            >();
            lemma_nat_align_down_sound(cur_va as nat, PAGE_SIZE as nat);
            lemma_sub_mod_noop(end as int, cur_va as int, PAGE_SIZE as int);
            if end - cur_va < PAGE_SIZE {
                lemma_small_mod((end - cur_va) as nat, PAGE_SIZE as nat);
                assert(false);
            }
        }
    }
}

} // verus!
