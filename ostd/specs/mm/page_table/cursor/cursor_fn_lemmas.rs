//! Cursor function-specific lemmas for `CursorOwner`.
use vstd::{
    prelude::*,
    arithmetic::power2::pow2,
};

use vstd_extra::{
    ghost_tree::*,
    ownership::*,
};

use crate::specs::{
    arch::*,
    mm::{
        frame::meta_region_owners::MetaRegionOwners,
        page_table::{
            AbstractVaddr,
            Mapping,
            cursor::owners::{
                CursorContinuation,
                CursorOwner,
            },
            nat_align_down,
            owners::*,
        },
    },
};

use core::ops::Range;
use crate::mm::{PagingLevel, Vaddr, page_size, page_table::*};

verus! {

broadcast use group_ghost_tree_lemmas;

impl<'rcu, C: PageTableConfig> CursorOwner<'rcu, C> {
    pub proof fn protect_preserves_cursor_inv_metaregion(
        self,
        other: Self,
        regions: MetaRegionOwners,
    )
        requires
            self.inv(),
            self.in_locked_range(),
            !self.popped_too_high,
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
                self.level <= i < NR_LEVELS ==> #[trigger] self.continuations[i]
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
        other.map_branch_none_inv_holds(self);

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

    pub proof fn map_branch_none_inv_holds(self, owner0: Self)
        requires
            owner0.inv(),
            // The map happens in the locked range and changes only the current
            // continuation's slot at `idx` (a real, in-range slot). With this +
            // "higher continuations unchanged", the root continuation's
            // isolation clauses are preserved.
            self.in_locked_range(),
            !self.popped_too_high,
            forall|j: int|
                0 <= j < NR_ENTRIES && j != owner0.continuations[owner0.level - 1].idx ==> (
                #[trigger] self.continuations[self.level - 1].children[j])
                    == owner0.continuations[owner0.level - 1].children[j],
            self.level == owner0.level,
            self.va == owner0.va,
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
            // [start, end), and `in_locked_range` rules out the sentinel).
            owner0.lemma_in_locked_range_top_index_lt_top_end();
            assert(self.continuations[NR_LEVELS - 1].idx == self.va.index[NR_LEVELS - 1]);
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
            owner0.in_locked_range(),
            self.inv(),
            self.in_locked_range(),
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
            PageTableOwner(cont0.children[idx].unwrap()).view_rec_absent_empty(
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
