//! Cursor function-specific lemmas for `CursorOwner`.
use vstd::{arithmetic::power2::pow2, prelude::*};
use vstd_extra::{ghost_tree::*, ownership::*};

use crate::specs::{
    arch::*,
    mm::{
        frame::meta_region_owners::MetaRegionOwners,
        page_table::{
            cursor::owners::{CursorContinuation, CursorOwner},
            cursor::page_size_lemmas::lemma_page_size_next,
            owners::*,
            *,
        },
    },
};

use crate::mm::{PagingConsts, PagingConstsTrait, PagingLevel, Vaddr, page_size, page_table::*};
use core::ops::Range;

verus! {

broadcast use group_ghost_tree_lemmas;

impl<'rcu, C: PageTableConfig> CursorOwner<'rcu, C> {
    /// Restore a tree predicate after replacing only the current child subtree.
    pub proof fn lemma_replaced_child_preserves_map_full_tree(
        self,
        old: Self,
        f: spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool,
        g: spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool,
    )
        requires
            self.inv(),
            old.inv(),
            self.level == old.level,
            old.map_full_tree(f),
            OwnerSubtree::implies(f, g),
            forall|i: int|
                self.level <= i < NR_LEVELS ==> #[trigger] self.continuations[i]
                    == old.continuations[i],
            self.continuations[self.level - 1].path() == old.continuations[old.level - 1].path(),
            self.index() == old.index(),
            forall|j: int|
                0 <= j < NR_ENTRIES && j != old.index() ==> #[trigger] self.continuations[self.level
                    - 1].children[j] == old.continuations[old.level - 1].children[j],
            self.cur_subtree().subtree_satisfies(self.cur_entry_owner().path, g),
        ensures
            self.map_full_tree(g),
    {
        assert forall|i: int|
            self.level - 1 <= i < NR_LEVELS implies #[trigger] self.continuations[i].map_children(
            g,
        ) by {
            if i == self.level - 1 {
                self.continuations[i].lemma_map_children_lift_skip_idx(
                    old.continuations[i],
                    self.index() as int,
                    f,
                    g,
                );
            } else {
                old.continuations[i].map_children_lift(f, g);
            }
        };
    }

    /// Replace the huge current mapping with the proven view of its split subtree.
    pub proof fn lemma_split_current_mappings(self, old: Self)
        requires
            self.inv(),
            old.inv(),
            self.in_barrier_va(),
            old.in_barrier_va(),
            self.level == old.level,
            self.va == old.va,
            old.cur_entry_owner().is_frame(),
            self.cur_entry_owner().is_node(),
            self.index() == old.index(),
            self.continuations[self.level - 1].path() == old.continuations[old.level - 1].path(),
            forall|i: int|
                self.level <= i < NR_LEVELS ==> #[trigger] self.continuations[i]
                    == old.continuations[i],
            forall|j: int|
                0 <= j < NR_ENTRIES && j != old.index() ==> #[trigger] self.continuations[self.level
                    - 1].children[j] == old.continuations[old.level - 1].children[j],
            1 < old.level < NR_LEVELS,
            PageTableOwner(self.cur_subtree()).view_rec(self.cur_entry_owner().path) == Set::<
                int,
            >::range(0, NR_ENTRIES as int).map(
                |i: int|
                    CursorView::<C>::split_index(
                        PageTableOwner(old.cur_subtree()).view_rec(
                            old.cur_entry_owner().path,
                        ).choose(),
                        page_size::<PagingConsts>((old.level - 1) as PagingLevel),
                        i as usize,
                    ),
            ),
        ensures
            self@ == old@.split_if_mapped_huge_spec(
                page_size::<PagingConsts>((old.level - 1) as PagingLevel),
            ),
            old@.inv(),
            old@.present(),
            old@.query_mapping().page_size == page_size::<PagingConsts>(old.level),
    {
        hide(CursorContinuation::inv_children_rel);
        hide(CursorContinuation::inv_children);
        hide(CursorContinuation::pt_inv_children);
        hide(CursorOwner::view_mappings);
        hide(CursorContinuation::view_mappings);
        broadcast use {CursorContinuation::group_lemmas, CursorOwner::group_lemmas};

        old.lemma_inv_continuation(old.level - 1);
        let old_cont = old.continuations[old.level - 1];
        old_cont.lemma_inv_children_unroll(old_cont.idx as int);
        old_cont.lemma_inv_children_rel_unroll(old_cont.idx as int);
        old_cont.lemma_pt_inv_children_unroll(old_cont.idx as int);
        self.lemma_cur_subtree_inv();
        old.view_preserves_inv();
        old.lemma_cur_subtree_inv();
        old.cur_va_in_subtree_range();
        old.lemma_cur_entry_frame_present();
        let old_subtree = old.cur_subtree();
        let path = old.cur_entry_owner().path;
        let m = old@.query_mapping();
        old.query_mapping_from_subtree(m);
        assert(PageTableOwner(old_subtree).view_rec(path) == set![m]);
        vstd::set::lemma_set_choose_len(set![m]);
        let size = page_size::<PagingConsts>((old.level - 1) as PagingLevel);
        lemma_page_size_next::<PagingConsts>((old.level - 1) as PagingLevel);
        crate::arch::mm::lemma_nr_subpage_per_huge_eq_nr_entries();
        assert(m.page_size / size == NR_ENTRIES) by (nonlinear_arith)
            requires
                size > 0,
                m.page_size == size * NR_ENTRIES,
        ;
        let cont0 = old.continuations[old.level - 1];
        let cont1 = self.continuations[self.level - 1];
        cont1.lemma_inv_children_rel_unroll(cont1.idx as int);
        cont0.view_mappings_take_child();
        cont1.view_mappings_take_child();
        cont0.take_child_preserves_inv();
        cont1.take_child_preserves_inv();
        let siblings0 = cont0.take_child().1;
        let siblings1 = cont1.take_child().1;
        assert(siblings0.view_mappings() == siblings1.view_mappings()) by {
            assert forall|j: int| 0 <= j < NR_ENTRIES implies (#[trigger] siblings0.children[j])
                == siblings1.children[j] by {};
            assert forall|e: Mapping|
                siblings0.view_mappings().contains(e) implies siblings1.view_mappings().contains(
                e,
            ) by {
                let j = choose|j: int|
                    0 <= j < NR_ENTRIES && (#[trigger] siblings0.children[j]) is Some
                        && PageTableOwner(siblings0.children[j]->0).view_rec(
                        siblings0.path().push_tail(j),
                    ).contains(e);
                siblings1.lemma_view_mappings_intro(e, j);
            };
            assert forall|e: Mapping|
                siblings1.view_mappings().contains(e) implies siblings0.view_mappings().contains(
                e,
            ) by {
                let j = choose|j: int|
                    0 <= j < NR_ENTRIES && (#[trigger] siblings1.children[j]) is Some
                        && PageTableOwner(siblings1.children[j]->0).view_rec(
                        siblings1.path().push_tail(j),
                    ).contains(e);
                siblings0.lemma_view_mappings_intro(e, j);
            };
        };
        let new_subtree = self.cur_subtree();
        siblings1.view_mappings_put_child(new_subtree);
        assert(siblings1.put_child(new_subtree).view_mappings() == cont1.view_mappings());
        Self::view_mappings_replace_lowest(old, self, cont0, cont1);
        assert(cont0.view_mappings().subset_of(old.view_mappings())) by {
            assert forall|e: Mapping|
                cont0.view_mappings().contains(e) implies old.view_mappings().contains(e) by {
                old.lemma_view_mappings_intro(e, old.level - 1);
            };
        };
        assert(self.view_mappings() =~= old.view_mappings() - set![m] + PageTableOwner(
            new_subtree,
        ).view_rec(self.cur_entry_owner().path));
    }

    /// Restoring a changed child and parent PTE preserves cursor and metadata invariants.
    pub proof fn lemma_replace_preserves_cursor_inv_metaregion(
        self,
        other: Self,
        regions: MetaRegionOwners,
    )
        requires
            self.inv(),
            self.in_barrier_va(),
            !self.popped_too_high,
            self.metaregion_sound(regions),
            // cursor level and structural fields unchanged
            self.level == other.level,
            self.guard_level == other.guard_level,
            self.va == other.va,
            self.barrier_va == other.barrier_va,
            self.prefix == other.prefix,
            self.popped_too_high == other.popped_too_high,
            // higher-level continuations unchanged
            forall|i: int|
                self.level <= i < NR_LEVELS ==> #[trigger] self.continuations[i]
                    == other.continuations[i],
            // bottom continuation well-formed after protect
            other.continuations[self.level - 1].inv(),
            other.continuations[self.level - 1].all_some(),
            other.continuations[self.level - 1].idx == self.continuations[self.level - 1].idx,
            other.continuations[self.level - 1].entry_own.parent_level
                == self.continuations[self.level - 1].entry_own.parent_level,
            other.continuations[self.level - 1].guard.inner.slot_vaddr()
                == self.continuations[self.level - 1].guard.inner.slot_vaddr(),
            other.continuations[self.level - 1].path() == self.continuations[self.level - 1].path(),
            other.continuations.dom() =~= self.continuations.dom(),
            forall|j: int|
                0 <= j < NR_ENTRIES && j != self.continuations[self.level - 1].idx
                    ==> #[trigger] other.continuations[self.level - 1].children[j]
                    == self.continuations[self.level - 1].children[j],
            ({
                let new_child = other.continuations[self.level
                    - 1].children[other.continuations[self.level - 1].idx as int]->0;
                let new_path = other.continuations[self.level - 1].path().push_tail(
                    other.continuations[self.level - 1].idx as int,
                );
                new_child.subtree_satisfies(
                    new_path,
                    PageTableOwner::<C>::metaregion_sound_pred(regions),
                )
            }),
            other.continuations[self.level - 1].entry_own.metaregion_sound(regions),
        ensures
            other.inv(),
            other.metaregion_sound(regions),
    {
        self.lemma_cur_pte_index();
        other.lemma_map_branch_none_inv_holds(self);

        let f = PageTableOwner::<C>::metaregion_sound_pred(regions);
        let L = self.level as int;
        let idx = self.continuations[L - 1].idx as int;

        assert forall|i: int|
            #![trigger other.continuations[i]]
            other.level - 1 <= i < NR_LEVELS implies other.continuations[i].map_children(f) by {
            reveal(CursorContinuation::map_children);
            if i > L - 1 {
                assert(other.continuations[i] == self.continuations[i]);
                assert(self.continuations[i].map_children(f));
            } else {
                assert(i == L - 1);
                let o_cont = other.continuations[L - 1];
                let s_cont = self.continuations[L - 1];
                reveal(CursorContinuation::inv_children);
                assert forall|j: int|
                    #![trigger o_cont.children[j]]
                    0 <= j < o_cont.children.len()
                        && o_cont.children[j] is Some implies o_cont.children[j].unwrap().subtree_satisfies(
                o_cont.path().push_tail(j), f) by {
                    if j != idx {
                        assert(o_cont.children[j] == s_cont.children[j]);
                        s_cont.lemma_inv_children_unroll(j);
                    }
                };
            }
        };

        reveal(CursorOwner::path_metaregion_sound);
        assert forall|i: int|
            #![trigger other.continuations[i]]
            other.level - 1 <= i
                < NR_LEVELS implies other.continuations[i].entry_own.metaregion_sound(regions) by {
            if i > L - 1 {
                assert(other.continuations[i] == self.continuations[i]);
                self.lemma_inv_continuation(i);
            }
        };
    }

    pub proof fn lemma_map_branch_none_inv_holds(self, owner0: Self)
        requires
            owner0.inv(),
            // The map happens in the locked range and changes only the current
            // continuation's slot at `idx` (a real, in-range slot). With this +
            // "higher continuations unchanged", the root continuation's
            // isolation clauses are preserved.
            self.in_barrier_va(),
            !self.popped_too_high,
            forall|j: int|
                0 <= j < NR_ENTRIES && j != owner0.continuations[owner0.level - 1].idx ==> (
                #[trigger] self.continuations[self.level - 1].children[j])
                    == owner0.continuations[owner0.level - 1].children[j],
            self.level == owner0.level,
            self.va == owner0.va,
            self.barrier_va == owner0.barrier_va,
            self.guard_level == owner0.guard_level,
            self.prefix == owner0.prefix,
            self.popped_too_high == owner0.popped_too_high,
            // Higher-level continuations unchanged
            forall|i: int|
                self.level <= i < NR_LEVELS ==> #[trigger] self.continuations[i]
                    == owner0.continuations[i],
            // Bottom continuation is well-formed
            self.continuations[self.level - 1].inv(),
            self.continuations[self.level - 1].all_some(),
            self.continuations[self.level - 1].idx == owner0.continuations[owner0.level - 1].idx,
            self.continuations[self.level - 1].entry_own.parent_level
                == owner0.continuations[owner0.level - 1].entry_own.parent_level,
            // Guard address preserved (from parent_perms_preserved).
            self.continuations[self.level - 1].guard.inner.slot_vaddr()
                == owner0.continuations[owner0.level - 1].guard.inner.slot_vaddr(),
            self.continuations[self.level - 1].path() == owner0.continuations[owner0.level
                - 1].path(),
            pte_index_spec::<C>(self.cur_va(), self.level as PagingLevel)
                == self.continuations[self.level - 1].idx,
            // Domain preserved: same keys as owner0.
            self.continuations.dom() =~= owner0.continuations.dom(),
        ensures
            self.inv(),
    {
        let L = self.level as int;
        C::lemma_paging_consts_properties();
        C::axiom_current_paging_consts_hardcoded();
        lemma_pte_index_bound::<C>(self.cur_va(), self.level);
        assert(pte_index_spec::<C>(self.va, self.level as PagingLevel)
            == self.continuations[self.level - 1].idx);
        assert(self.continuations[L - 1].level() == self.level);
        assert(self.continuations.contains_key(L - 1));
        // Isolation clauses for the root continuation (NR_LEVELS-1).
        if self.level < NR_LEVELS {
            // Root is above the current level ⟹ unchanged (higher-unchanged), so
            // both clauses carry verbatim from `owner0.inv()`.
            assert(self.continuations[NR_LEVELS - 1] == owner0.continuations[NR_LEVELS - 1]);
        } else {
            // Root IS the current continuation. The idx clause is vacuous
            // (level == NR_LEVELS). For the outside-(borrowed||absent) clause:
            // the map changed only the in-range slot `idx`, so every outside
            // child keeps `owner0`'s value; `idx` is in-range (top index in
            // [start, end), and `in_barrier_va` rules out the sentinel).
            owner0.lemma_in_barrier_va_top_index_bounds();
            assert(self.continuations[NR_LEVELS - 1].idx == pte_index_spec::<C>(
                self.va,
                NR_LEVELS as PagingLevel,
            ));
            assert(self.continuations[NR_LEVELS - 1].idx == owner0.continuations[owner0.level
                - 1].idx);
            assert(C::TOP_LEVEL_INDEX_RANGE().start <= owner0.continuations[owner0.level - 1].idx
                < C::TOP_LEVEL_INDEX_RANGE().end);
            assert(forall|j: int|
                0 <= j < NR_ENTRIES && !(C::TOP_LEVEL_INDEX_RANGE().start <= j
                    < C::TOP_LEVEL_INDEX_RANGE().end) ==> (#[trigger] self.continuations[NR_LEVELS
                    - 1].children[j]) is Some ==> (self.continuations[NR_LEVELS
                    - 1].children[j].unwrap().value().is_borrowed() || self.continuations[NR_LEVELS
                    - 1].children[j].unwrap().value().is_absent()));
        }
    }

    /// After alloc_if_none (absent->node), `view_mappings` is unchanged (both contribute zero mappings).
    pub proof fn map_branch_none_no_new_mappings(self, owner0: Self)
        requires
            owner0.inv(),
            owner0.in_barrier_va(),
            self.inv(),
            self.in_barrier_va(),
            self.level == owner0.level,
            self.va == owner0.va,
            forall|i: int|
                self.level <= i < NR_LEVELS ==> #[trigger] self.continuations[i]
                    == owner0.continuations[i],
            // child at idx changed from absent to empty node
            owner0.continuations[owner0.level - 1].children[owner0.continuations[owner0.level
                - 1].idx as int] is Some,
            owner0.continuations[owner0.level - 1].children[owner0.continuations[owner0.level
                - 1].idx as int]->0.value().is_absent(),
            self.continuations[self.level - 1].children[self.continuations[self.level
                - 1].idx as int] is Some,
            self.continuations[self.level - 1].children[self.continuations[self.level
                - 1].idx as int]->0.value().is_node(),
            // Non-idx children and path preserved
            self.continuations[self.level - 1].path() == owner0.continuations[owner0.level
                - 1].path(),
            forall|j: int|
                0 <= j < NR_ENTRIES && j != owner0.continuations[owner0.level - 1].idx as int
                    ==> #[trigger] self.continuations[self.level - 1].children[j]
                    == owner0.continuations[owner0.level - 1].children[j],
            // The new node's subtree has empty view_rec (from alloc_if_none postcondition)
            PageTableOwner(
                self.continuations[self.level - 1].children[self.continuations[self.level
                    - 1].idx as int]->0,
            ).view_rec(
                self.continuations[self.level - 1].path().push_tail(
                    self.continuations[self.level - 1].idx as int,
                ),
            ) =~= Set::<Mapping>::empty(),
        ensures
            self.view_mappings() == owner0.view_mappings(),
    {
        broadcast use {CursorContinuation::group_lemmas, CursorOwner::group_lemmas};

        let L = self.level as int;
        let cont = self.continuations[L - 1];
        let cont0 = owner0.continuations[L - 1];
        let idx = cont0.idx as int;

        assert(cont.view_mappings() == cont0.view_mappings()) by {
            cont0.lemma_inv_children_unroll(idx);
            PageTableOwner(cont0.children[idx].unwrap()).lemma_view_rec_absent_empty(
                cont0.path().push_tail(idx as int),
            );
            assert forall|m: Mapping|
                cont.view_mappings().contains(m) implies cont0.view_mappings().contains(m) by {
                let j = choose|j: int|
                    0 <= j < cont.children.len() && #[trigger] cont.children[j] is Some
                        && PageTableOwner(cont.children[j].unwrap()).view_rec(
                        cont.path().push_tail(j),
                    ).contains(m);
                if j == idx {
                    // cont.children[idx]'s view_rec == empty (from precondition)
                    assert(false);
                } else {
                    assert(cont.children[j] == cont0.children[j]);
                }
            };
            assert forall|m: Mapping|
                cont0.view_mappings().contains(m) implies cont.view_mappings().contains(m) by {
                let j = choose|j: int|
                    0 <= j < cont0.children.len() && #[trigger] cont0.children[j] is Some
                        && PageTableOwner(cont0.children[j].unwrap()).view_rec(
                        cont0.path().push_tail(j),
                    ).contains(m);
                if j == idx {
                    // cont0.children[idx] is absent, view_rec is empty
                    assert(false);
                } else {
                    assert(cont0.children[j] == cont.children[j]);
                }
            };
        };
        // Lift cont == cont0 to self.view_mappings() == owner0.view_mappings()
        assert(self.view_mappings() == owner0.view_mappings()) by {
            assert forall|m: Mapping|
                self.view_mappings().contains(m) implies owner0.view_mappings().contains(m) by {
                let i = choose|i: int|
                    self.level - 1 <= i < NR_LEVELS
                        && #[trigger] self.continuations[i].view_mappings().contains(m);
                if i == L - 1 {
                    assert(cont0.view_mappings().contains(m));
                } else {
                    assert(owner0.continuations[i] == self.continuations[i]);
                }
            };
            assert forall|m: Mapping|
                owner0.view_mappings().contains(m) implies self.view_mappings().contains(m) by {
                let i = choose|i: int|
                    owner0.level - 1 <= i < NR_LEVELS
                        && #[trigger] owner0.continuations[i].view_mappings().contains(m);
                if i == L - 1 {
                    assert(cont.view_mappings().contains(m));
                } else {
                    assert(self.continuations[i] == owner0.continuations[i]);
                }
            };
        };
    }
}

} // verus!
