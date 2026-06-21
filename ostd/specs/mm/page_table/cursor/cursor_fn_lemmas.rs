/// Cursor function-specific lemmas for `CursorOwner`.
///
/// Themes moved here from `owners.rs`:
/// - **Theme 7**: PTE & entry modification invariant preservation
///   (`protect_preserves_cursor_inv_metaregion`, `map_branch_none_*`)
/// - **Theme 14**: Cursor path structure & jump utilities
///   (`cursor_path_nesting`, `jump_above_locked_range_va_in_node`,
///    `jump_not_in_node_level_lt_guard_minus_one`)
use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;

use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;

use vstd_extra::arithmetic::{
    lemma_nat_align_down_monotone, lemma_nat_align_down_sound, lemma_nat_align_down_within_block,
    lemma_nat_align_up_sound,
};

use crate::arch::mm::PagingConsts;
use crate::mm::nr_subpage_per_huge;
use crate::mm::page_table::*;
use crate::mm::{PagingConstsTrait, PagingLevel, Vaddr, page_size};
use crate::specs::arch::*;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::page_table::AbstractVaddr;
use crate::specs::mm::page_table::Mapping;
use crate::specs::mm::page_table::cursor::owners::{CursorContinuation, CursorOwner};
use crate::specs::mm::page_table::cursor::page_size_lemmas::{
    lemma_page_size_divides, lemma_page_size_ge_page_size,
};
use crate::specs::mm::page_table::owners::*;
use crate::specs::mm::page_table::{nat_align_down, nat_align_up};

use core::ops::Range;

verus! {

impl<'rcu, C: PageTableConfig> CursorOwner<'rcu, C> {
    pub proof fn protect_preserves_cursor_inv_metaregion(
        self,
        other: Self,
        regions: MetaRegionOwners,
    )
        requires
            self.inv(),
            self.in_locked_range(),
            self.metaregion_sound(regions),
            self.cur_entry_owner().is_frame(),
            other.cur_entry_owner().is_frame(),
            other.cur_entry_owner().inv(),
            // protect preserves PA, path, parent_level
            other.cur_entry_owner().frame().mapped_pa == self.cur_entry_owner().frame().mapped_pa,
            other.cur_entry_owner().path == self.cur_entry_owner().path,
            other.cur_entry_owner().parent_level == self.cur_entry_owner().parent_level,
            // cursor level and structural fields unchanged
            self.level == other.level,
            self.guard_level == other.guard_level,
            self.va == other.va,
            self.prefix == other.prefix,
            self.popped_too_high == other.popped_too_high,
            // higher-level continuations unchanged
            forall|i: int|
                self.level <= i < C::NR_LEVELS() ==> #[trigger] self.continuations[i]
                    == other.continuations[i],
            // bottom continuation well-formed after protect
            other.continuations[self.level - 1].inv(),
            other.continuations[self.level - 1].all_some(),
            other.continuations[self.level - 1].idx == self.continuations[self.level - 1].idx,
            other.continuations[self.level - 1].entry_own.parent_level
                == self.continuations[self.level - 1].entry_own.parent_level,
            other.continuations[self.level - 1].guard.inner.inner@.ptr.addr()
                == self.continuations[self.level - 1].guard.inner.inner@.ptr.addr(),
            other.continuations[self.level - 1].path() == self.continuations[self.level - 1].path(),
            other.continuations.dom() =~= self.continuations.dom(),
            forall|j: int|
                0 <= j < NR_ENTRIES && j != self.continuations[self.level - 1].idx as int
                    ==> #[trigger] other.continuations[self.level - 1].children[j]
                    == self.continuations[self.level - 1].children[j],
            ({
                let new_child = other.continuations[self.level
                    - 1].children[other.continuations[self.level - 1].idx as int]->0;
                let new_path = other.continuations[self.level - 1].path().push_tail(
                    other.continuations[self.level - 1].idx as usize,
                );
                new_child.tree_predicate_map(
                    new_path,
                    PageTableOwner::<C>::metaregion_sound_pred(regions),
                )
            }),
            other.continuations[self.level - 1].entry_own.metaregion_sound(regions),
        ensures
            other.inv(),
            other.metaregion_sound(regions),
    {
        C::lemma_paging_consts_properties();
        let L = self.level as int;
        // Establish the precondition for map_branch_none_inv_holds:
        // other.va.index[other.level - 1] == other.continuations[other.level - 1].idx
        assert(self.continuations.contains_key(L - 1));
        assert(self.va.index[L - 1] == self.continuations[L - 1].idx) by {
            self.inv_continuation(L - 1);
        };
        assert(other.va.index[other.level - 1] == other.continuations[other.level - 1].idx);

        other.map_branch_none_inv_holds(self);

        let f = PageTableOwner::<C>::metaregion_sound_pred(regions);
        let idx = self.continuations[L - 1].idx as int;

        assert forall|i: int|
            #![trigger other.continuations[i]]
            other.level - 1 <= i < C::NR_LEVELS() implies other.continuations[i].map_children(
            f,
        ) by {
            if i > L - 1 {
                assert(other.continuations[i] == self.continuations[i]);
                assert(self.continuations[i].map_children(f));
            } else {
                assert(i == L - 1);
                let o_cont = other.continuations[L - 1];
                let s_cont = self.continuations[L - 1];
                assert(s_cont.inv()) by {
                    assert(self.continuations.contains_key(L - 1));
                };
                assert(s_cont.inv_children());
                assert(s_cont.children.len() == NR_ENTRIES);
                reveal(CursorContinuation::inv_children);
                assert forall|j: int|
                    #![trigger o_cont.children[j]]
                    0 <= j < o_cont.children.len()
                        && o_cont.children[j] is Some implies o_cont.children[j].unwrap().tree_predicate_map(
                o_cont.path().push_tail(j as usize), f) by {
                    if j != idx {
                        assert(o_cont.children[j] == s_cont.children[j]);
                        assert(0 <= j < s_cont.children.len());
                        s_cont.inv_children_unroll(j);
                    }
                };
            }
        };

        assert forall|i: int|
            #![trigger other.continuations[i]]
            other.level - 1 <= i
                < C::NR_LEVELS() implies other.continuations[i].entry_own.metaregion_sound(
            regions,
        ) by {
            if i > L - 1 {
                assert(other.continuations[i] == self.continuations[i]);
                self.inv_continuation(i);
            }
        };
    }

    #[verifier::spinoff_prover]
    pub proof fn map_branch_none_inv_holds(self, owner0: Self)
        requires
            owner0.inv(),
            self.level == owner0.level,
            self.va == owner0.va,
            self.guard_level == owner0.guard_level,
            self.prefix == owner0.prefix,
            self.popped_too_high == owner0.popped_too_high,
            // Higher-level continuations unchanged
            forall|i: int|
                self.level <= i < C::NR_LEVELS() ==> #[trigger] self.continuations[i]
                    == owner0.continuations[i],
            // Bottom continuation is well-formed
            self.continuations[self.level - 1].inv(),
            self.continuations[self.level - 1].all_some(),
            self.continuations[self.level - 1].idx == owner0.continuations[owner0.level - 1].idx,
            self.continuations[self.level - 1].entry_own.parent_level
                == owner0.continuations[owner0.level - 1].entry_own.parent_level,
            // Guard address preserved (from parent_perms_preserved).
            self.continuations[self.level - 1].guard.inner.inner@.ptr.addr()
                == owner0.continuations[owner0.level - 1].guard.inner.inner@.ptr.addr(),
            self.continuations[self.level - 1].path() == owner0.continuations[owner0.level
                - 1].path(),
            self.va.index[self.level - 1] == self.continuations[self.level - 1].idx,
            // Domain preserved: same keys as owner0.
            self.continuations.dom() =~= owner0.continuations.dom(),
        ensures
            self.inv(),
    {
        let L = self.level as int;
        assert(self.continuations.contains_key(L - 1));
        // Most CursorOwner::inv() clauses depend only on fields preserved by
        // the preconditions (va, level, guard_level, prefix, popped_too_high,
        // and continuations at i >= level), plus the explicitly-given
        // well-formedness of self.continuations[L-1]. We discharge the
        // continuation quantifiers by splitting on i == L - 1 vs i > L - 1.
        let s_bot = self.continuations[L - 1];
        let o_bot = owner0.continuations[L - 1];

        // Per-continuation invariant block (lines 765-773 of CursorOwner::inv).
        assert forall|i: int|
            #![trigger self.continuations.contains_key(i)]
            self.level - 1 <= i < C::NR_LEVELS() implies {
            &&& self.continuations.contains_key(i)
            &&& self.continuations[i].inv()
            &&& self.continuations[i].level() == i + 1
            &&& self.continuations[i].entry_own.parent_level == i + 2
            &&& self.in_locked_range() ==> self.va.index[i] == self.continuations[i].idx
        } by {
            assert(owner0.continuations.contains_key(i)) by {
                owner0.inv_continuation(i);
            };
            assert(self.continuations.contains_key(i));
            if i == L - 1 {
                // From preconditions: self.continuations[L-1].inv() and
                // entry_own.parent_level == owner0's, which is L + 1 = i + 2.
                owner0.inv_continuation(L - 1);
                assert(o_bot.entry_own.parent_level == L + 1);
                assert(s_bot.entry_own.parent_level == L + 1);
                // level() == entry_own.node().level == parent_level - 1 (from EntryOwner::inv_base
                // since s_bot.entry_own.is_node() via s_bot.inv()).
                assert(s_bot.entry_own.is_node());
                assert(s_bot.entry_own.parent_level == s_bot.entry_own.node().level + 1);
                assert(s_bot.level() == L);
                assert(self.in_locked_range() ==> self.va.index[L - 1] == s_bot.idx);
            } else {
                assert(i > L - 1);
                assert(self.continuations[i] == owner0.continuations[i]);
                owner0.inv_continuation(i);
                assert(self.in_locked_range() == owner0.in_locked_range());
            }
        };

        // Path / PTE consistency between consecutive continuations (lines 774-792).
        assert forall|i: int|
            #![trigger self.continuations[i].path()]
            self.level - 1 <= i < C::NR_LEVELS() - 1 implies {
            &&& self.continuations[i].path() == self.continuations[i + 1].path().push_tail(
                self.continuations[i + 1].idx as usize,
            )
            &&& self.continuations[i].entry_own.path.len() == self.continuations[i
                + 1].entry_own.node().tree_level + 1
            &&& self.continuations[i].entry_own.match_pte(
                self.continuations[i
                    + 1].entry_own.node().children_perm.value()[self.continuations[i
                    + 1].idx as int],
                self.continuations[i + 1].entry_own.node().level,
            )
            &&& self.continuations[i].entry_own.parent_level == self.continuations[i
                + 1].entry_own.node().level
        } by {
            // For all i in this range, self.continuations[i+1] == owner0.continuations[i+1]
            // (since i + 1 > L - 1, i.e. i + 1 >= L).
            assert(self.continuations[i + 1] == owner0.continuations[i + 1]);
            if i == L - 1 {
                // Bottom continuation's path equals owner0's (precondition).
                assert(s_bot.path() == o_bot.path());
                assert(s_bot.entry_own.parent_level == o_bot.entry_own.parent_level);
                let parent = self.continuations[i + 1];
                // From owner0.inv(): the analogous clauses hold for owner0.
                // The parent continuation is identical (i + 1 >= L).
                assert(parent == owner0.continuations[i + 1]);
                let pte = parent.entry_own.node().children_perm.value()[parent.idx as int];
                let plevel = parent.entry_own.node().level;
                // owner0 gives: o_bot.entry_own.match_pte(pte, plevel)
                assert(o_bot.entry_own.match_pte(pte, plevel));
                // s_bot.inv() ⇒ s_bot.entry_own.is_node() and relate_guard, hence
                // s_bot.entry_own.node().meta_addr_self() == s_bot.guard.addr()
                //                                       == o_bot.guard.addr()
                //                                       == o_bot.entry_own.node().meta_addr_self()
                assert(s_bot.entry_own.is_node());
                owner0.inv_continuation(L - 1);
                assert(o_bot.entry_own.is_node());
                assert(s_bot.entry_own.node().meta_addr_self()
                    == s_bot.guard.inner.inner@.ptr.addr());
                assert(o_bot.entry_own.node().meta_addr_self()
                    == o_bot.guard.inner.inner@.ptr.addr());
                assert(s_bot.entry_own.node().meta_addr_self()
                    == o_bot.entry_own.node().meta_addr_self());
                // Therefore s_bot.entry_own.match_pte(pte, plevel) holds:
                // pte properties (paddr alignment, < MAX_PADDR) come from owner0's match_pte;
                // the kind selection is is_node (matching o_bot's node branch);
                // and meta_to_frame(meta_addr_self) is identical.
                assert(s_bot.entry_own.match_pte(pte, plevel));
                // path.len: path() == entry_own.path, so s_bot.entry_own.path == o_bot.entry_own.path.
                assert(s_bot.entry_own.path == o_bot.entry_own.path);
                assert(o_bot.entry_own.path.len() == parent.entry_own.node().tree_level + 1);
                assert(s_bot.entry_own.path.len() == parent.entry_own.node().tree_level + 1);
            } else {
                assert(self.continuations[i] == owner0.continuations[i]);
            }
        };

        // Guard address distinctness (lines 793-798).
        assert forall|i: int, j: int|
            #![trigger self.continuations[i].guard, self.continuations[j].guard]
            self.level - 1 <= i < j < C::NR_LEVELS() implies {
            self.continuations[i].guard.inner.inner@.ptr.addr()
                != self.continuations[j].guard.inner.inner@.ptr.addr()
        } by {
            // Owner0 has the distinctness; substitute preserved guards.
            let s_i_addr = self.continuations[i].guard.inner.inner@.ptr.addr();
            let s_j_addr = self.continuations[j].guard.inner.inner@.ptr.addr();
            let o_i_addr = owner0.continuations[i].guard.inner.inner@.ptr.addr();
            let o_j_addr = owner0.continuations[j].guard.inner.inner@.ptr.addr();
            if i == L - 1 {
                assert(s_i_addr == o_i_addr);
                assert(self.continuations[j] == owner0.continuations[j]);
                assert(s_j_addr == o_j_addr);
            } else {
                assert(self.continuations[i] == owner0.continuations[i]);
                assert(self.continuations[j] == owner0.continuations[j]);
            }
            assert(o_i_addr != o_j_addr);
        };
    }

    /// After alloc_if_none (absent->node), `view_mappings` is unchanged (both contribute zero mappings).
    pub proof fn map_branch_none_no_new_mappings(self, owner0: Self)
        requires
            owner0.inv(),
            owner0.in_locked_range(),
            self.inv(),
            self.in_locked_range(),
            self.level == owner0.level,
            self.va == owner0.va,
            forall|i: int|
                self.level <= i < C::NR_LEVELS() ==> #[trigger] self.continuations[i]
                    == owner0.continuations[i],
            // child at idx changed from absent to empty node
            owner0.continuations[owner0.level - 1].children[owner0.continuations[owner0.level
                - 1].idx as int] is Some,
            owner0.continuations[owner0.level - 1].children[owner0.continuations[owner0.level
                - 1].idx as int]->0.value.is_absent(),
            self.continuations[self.level - 1].children[self.continuations[self.level
                - 1].idx as int] is Some,
            self.continuations[self.level - 1].children[self.continuations[self.level
                - 1].idx as int]->0.value.is_node(),
            // Non-idx children and path preserved
            self.continuations[self.level - 1].path() == owner0.continuations[owner0.level
                - 1].path(),
            forall|j: int|
                0 <= j < nr_subpage_per_huge::<C>() && j != owner0.continuations[owner0.level
                    - 1].idx as int ==> #[trigger] self.continuations[self.level - 1].children[j]
                    == owner0.continuations[owner0.level - 1].children[j],
            // The new node's subtree has empty view_rec (from alloc_if_none postcondition)
            PageTableOwner(
                self.continuations[self.level - 1].children[self.continuations[self.level
                    - 1].idx as int]->0,
            ).view_rec(
                self.continuations[self.level - 1].path().push_tail(
                    self.continuations[self.level - 1].idx as usize,
                ),
            ) =~= Set::<Mapping>::empty(),
        ensures
            self.view_mappings() == owner0.view_mappings(),
    {
        C::lemma_paging_consts_properties();
        broadcast use {CursorContinuation::group_lemmas, CursorOwner::group_lemmas};

        let L = self.level as int;
        owner0.inv_continuation(L - 1);
        self.inv_continuation(L - 1);
        let cont = self.continuations[L - 1];
        let cont0 = owner0.continuations[L - 1];
        let idx = cont0.idx as int;

        assert(cont0.inv_children());
        assert(cont.inv_children());

        assert(cont.view_mappings() == cont0.view_mappings()) by {
            cont0.inv_children_unroll(idx);
            PageTableOwner(cont0.children[idx].unwrap()).view_rec_absent_empty(
                cont0.path().push_tail(idx as usize),
            );
            assert forall|m: Mapping|
                cont.view_mappings().contains(m) implies cont0.view_mappings().contains(m) by {
                let j = choose|j: int|
                    0 <= j < cont.children.len() && #[trigger] cont.children[j] is Some
                        && PageTableOwner(cont.children[j].unwrap()).view_rec(
                        cont.path().push_tail(j as usize),
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
                        cont0.path().push_tail(j as usize),
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
                    self.level - 1 <= i < C::NR_LEVELS()
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
                    owner0.level - 1 <= i < C::NR_LEVELS()
                        && #[trigger] owner0.continuations[i].view_mappings().contains(m);
                if i == L - 1 {
                    assert(cont.view_mappings().contains(m));
                } else {
                    assert(self.continuations[i] == owner0.continuations[i]);
                }
            };
        };
    }

    /// After `map_branch_none` (alloc_if_none + push_level), the current entry is absent.
    ///
    /// Proof: `alloc_if_none` creates an empty PT node where all children are absent
    /// (`allocated_empty_node_owner` line 172). `push_level` enters one of these children,
    /// so `cur_entry_owner().is_absent()` holds.
    pub proof fn map_branch_none_cur_entry_absent(self)
        requires
            self.inv(),
            // All children of the current continuation are absent (from the empty node)
            forall|i: int|
                0 <= i < nr_subpage_per_huge::<C>() ==> #[trigger] self.continuations[self.level
                    - 1].children[i] is Some && self.continuations[self.level
                    - 1].children[i]->0.value.is_absent(),
        ensures
            self.cur_entry_owner().is_absent(),
    {
        C::lemma_paging_consts_properties();
        self.inv_continuation(self.level - 1);
        let idx = self.continuations[self.level - 1].idx as int;
        assert(0 <= idx < NR_ENTRIES);
        assert(0 <= idx < nr_subpage_per_huge::<C>());
        assert(self.continuations[self.level - 1].children[idx] is Some);
        assert(self.continuations[self.level - 1].children[idx]->0.value.is_absent());
    }

    pub proof fn cursor_path_nesting(self, i: int, j: int)
        requires
            self.inv(),
            self.level - 1 <= j < i < C::NR_LEVELS(),
        ensures
            self.continuations[j].path().len() as int > self.continuations[i].path().len() as int,
            self.continuations[j].path().index(self.continuations[i].path().len() as int)
                == self.continuations[i].idx,
    {
        C::lemma_paging_consts_properties();
        assert(nr_subpage_per_huge::<C>() == NR_ENTRIES);
        // Explicitly instantiate continuation invariants for all indices
        // that the case branches use. inv_continuation(k) requires
        // self.level - 1 <= k <= C::NR_LEVELS() - 1, which holds for
        // all k in [j, i] since self.level - 1 <= j < i < C::NR_LEVELS().
        self.inv_continuation(i);
        self.inv_continuation(j);
        // Also instantiate for intermediate indices used in the i==3,j==0
        // and i==2,j==0 branches (they access continuations[1] and [2]).
        if j < i - 1 {
            // There's at least one index between j and i
            self.inv_continuation(j + 1);
            if j + 2 < i {
                self.inv_continuation(j + 2);
            }
        }
        if i == 3 && j == 2 {
            self.continuations[3].path().push_tail_property_index(
                self.continuations[3].idx as usize,
            );
            self.continuations[3].path().push_tail_property_len(self.continuations[3].idx as usize);
        } else if i == 3 && j == 1 {
            let p3 = self.continuations[3].path();
            let p2 = self.continuations[2].path();
            let idx3 = self.continuations[3].idx as usize;
            let idx2 = self.continuations[2].idx as usize;
            p3.push_tail_property_index(idx3);
            p3.push_tail_property_len(idx3);
            p2.push_tail_property_index(idx2);
            p2.push_tail_property_len(idx2);
            assert(p3.len() < p2.len());
            assert(self.continuations[1].path() == p2.push_tail(idx2));
            assert(p2.push_tail(idx2).index(p3.len() as int) == p2.index(p3.len() as int));
        } else if i == 3 && j == 0 {
            let p3 = self.continuations[3].path();
            let p2 = self.continuations[2].path();
            let p1 = self.continuations[1].path();
            let idx3 = self.continuations[3].idx as usize;
            let idx2 = self.continuations[2].idx as usize;
            let idx1 = self.continuations[1].idx as usize;
            p3.push_tail_property_index(idx3);
            p3.push_tail_property_len(idx3);
            p2.push_tail_property_index(idx2);
            p2.push_tail_property_len(idx2);
            p1.push_tail_property_index(idx1);
            p1.push_tail_property_len(idx1);
            assert(p3.len() < p2.len());
            assert(p3.len() < p1.len());
            assert(p1.push_tail(idx1).index(p3.len() as int) == p1.index(p3.len() as int));
            assert(p2.push_tail(idx2).index(p3.len() as int) == p2.index(p3.len() as int));
        } else if i == 2 && j == 1 {
            self.continuations[2].path().push_tail_property_index(
                self.continuations[2].idx as usize,
            );
            self.continuations[2].path().push_tail_property_len(self.continuations[2].idx as usize);
        } else if i == 2 && j == 0 {
            let p2 = self.continuations[2].path();
            let p1 = self.continuations[1].path();
            let idx2 = self.continuations[2].idx as usize;
            let idx1 = self.continuations[1].idx as usize;
            p2.push_tail_property_index(idx2);
            p2.push_tail_property_len(idx2);
            p1.push_tail_property_index(idx1);
            p1.push_tail_property_len(idx1);
            assert(p2.len() < p1.len());
            assert(self.continuations[0].path() == p1.push_tail(idx1));
            assert(p1.push_tail(idx1).index(p2.len() as int) == p1.index(p2.len() as int));
            assert(p1 == p2.push_tail(idx2));
            assert(p2.push_tail(idx2).index(p2.len() as int) == idx2);
        } else if i == 1 && j == 0 {
            self.continuations[1].path().push_tail_property_index(
                self.continuations[1].idx as usize,
            );
            self.continuations[1].path().push_tail_property_len(self.continuations[1].idx as usize);
        }
    }

    pub proof fn lemma_page_size_spec_5_eq_pow2_48()
        ensures
            page_size::<PagingConsts>(5) == pow2(48nat) as usize,
    {
        crate::arch::mm::lemma_nr_subpage_per_huge_eq_nr_entries();
        vstd_extra::external::ilog2::lemma_usize_ilog2_to32();
        vstd::arithmetic::power2::lemma2_to64();
        vstd::arithmetic::power2::lemma2_to64_rest();
        vstd::arithmetic::power2::lemma_pow2_adds(12nat, 36nat);
    }

    pub proof fn jump_not_in_node_level_lt_guard_minus_one(
        self,
        level: PagingLevel,
        va: Vaddr,
        node_start: Vaddr,
    )
        requires
            self.inv(),
            self.locked_range().start <= va < self.locked_range().end,
            1 <= level,
            level + 1 <= self.guard_level,
            self.locked_range().start <= node_start,
            node_start + page_size::<C>((level + 1) as PagingLevel) <= self.locked_range().end,
            !(node_start <= va && va < node_start + page_size::<C>((level + 1) as PagingLevel)),
        ensures
            level + 1 < self.guard_level,
    {
        if level + 1 == self.guard_level {
            let pv = self.prefix.to_vaddr() as nat;
            let ps = page_size::<C>(self.guard_level as PagingLevel) as nat;
            self.prefix.align_down_concrete(self.guard_level as int);
            self.prefix_aligned_to_guard_level();
            self.prefix_plus_ps_no_overflow();
            self.prefix.aligned_align_up_advances(self.guard_level as int);
            AbstractVaddr::<C>::from_vaddr_to_vaddr_roundtrip(nat_align_down(pv, ps) as Vaddr);
        }
    }
}

} // verus!
