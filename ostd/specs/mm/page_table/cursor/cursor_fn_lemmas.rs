/// Cursor function-specific lemmas for `CursorOwner`.
///
/// Themes moved here from `owners.rs`:
/// - **Theme 7**: PTE & entry modification invariant preservation
///   (`protect_preserves_cursor_inv_metaregion`, `map_branch_none_*`)
/// - **Theme 14**: Cursor path structure & jump utilities
///   (`cursor_path_nesting`, `jump_above_locked_range_va_in_node`,
///    `jump_not_in_node_level_lt_guard_minus_one`, `lemma_page_size_spec_5_eq_pow2_48`)
use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;

use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;

use vstd_extra::arithmetic::{
    lemma_nat_align_down_monotone, lemma_nat_align_down_sound, lemma_nat_align_down_within_block,
    lemma_nat_align_up_sound,
};

use crate::mm::page_table::*;
use crate::mm::{PagingLevel, Vaddr};
use crate::specs::arch::mm::{NR_ENTRIES, NR_LEVELS};
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::page_table::cursor::owners::{CursorOwner, CursorContinuation};
use crate::specs::mm::page_table::cursor::page_size_lemmas::{
    lemma_page_size_divides, lemma_page_size_ge_page_size,
};
use crate::specs::mm::page_table::owners::*;
use crate::specs::mm::page_table::AbstractVaddr;
use crate::specs::mm::page_table::Mapping;
use crate::specs::mm::page_table::{nat_align_down, nat_align_up};

use core::ops::Range;

verus! {

impl<'rcu, C: PageTableConfig> CursorOwner<'rcu, C> {

    // ─── Theme 7: PTE & entry modification invariant preservation ────────

    pub proof fn protect_preserves_cursor_inv_metaregion(
        self,
        other: Self,
        regions: MetaRegionOwners,
    )
        requires
            self.inv(),
            self.metaregion_sound(regions),
            self.cur_entry_owner().is_frame(),
            other.cur_entry_owner().is_frame(),
            other.cur_entry_owner().inv(),
            // protect preserves PA, path, parent_level
            other.cur_entry_owner().frame.unwrap().mapped_pa == self.cur_entry_owner().frame.unwrap().mapped_pa,
            other.cur_entry_owner().path == self.cur_entry_owner().path,
            other.cur_entry_owner().parent_level == self.cur_entry_owner().parent_level,
            // cursor level and structural fields unchanged
            self.level == other.level,
            self.guard_level == other.guard_level,
            self.va == other.va,
            self.prefix == other.prefix,
            self.popped_too_high == other.popped_too_high,
            // higher-level continuations unchanged
            forall|i: int| self.level <= i < NR_LEVELS ==>
                #[trigger] self.continuations[i] == other.continuations[i],
            // bottom continuation well-formed after protect
            other.continuations[self.level - 1].inv(),
            other.continuations[self.level - 1].all_some(),
            other.continuations[self.level - 1].idx == self.continuations[self.level - 1].idx,
            other.continuations[self.level - 1].entry_own.parent_level
                == self.continuations[self.level - 1].entry_own.parent_level,
            other.continuations[self.level - 1].guard_perm.value().inner.inner@.ptr.addr()
                == self.continuations[self.level - 1].guard_perm.value().inner.inner@.ptr.addr(),
            other.continuations[self.level - 1].path()
                == self.continuations[self.level - 1].path(),
            other.continuations.dom() =~= self.continuations.dom(),
            forall |j: int| 0 <= j < NR_ENTRIES
                && j != self.continuations[self.level - 1].idx as int ==>
                #[trigger] other.continuations[self.level - 1].children[j]
                    == self.continuations[self.level - 1].children[j],
            ({
                let new_child = other.continuations[self.level - 1].children[
                    other.continuations[self.level - 1].idx as int].unwrap();
                let new_path = other.continuations[self.level - 1].path()
                    .push_tail(other.continuations[self.level - 1].idx as usize);
                new_child.tree_predicate_map(new_path,
                    PageTableOwner::<C>::metaregion_sound_pred(regions))
            }),
            other.continuations[self.level - 1].entry_own.metaregion_sound(regions),
            // For `metaregion_correct` transfer (only needed in the correct branch).
            self.metaregion_correct(regions) ==> ({
                let new_child = other.continuations[self.level - 1].children[
                    other.continuations[self.level - 1].idx as int].unwrap();
                let new_path = other.continuations[self.level - 1].path()
                    .push_tail(other.continuations[self.level - 1].idx as usize);
                new_child.tree_predicate_map(new_path,
                    PageTableOwner::<C>::path_tracked_pred(regions))
            }),
            self.metaregion_correct(regions) ==>
                PageTableOwner::<C>::path_tracked_pred(regions)(
                    other.continuations[self.level - 1].entry_own,
                    other.continuations[self.level - 1].path()),
        ensures
            other.inv(),
            other.metaregion_sound(regions),
            self.metaregion_correct(regions) ==> other.metaregion_correct(regions),
    {
        other.map_branch_none_inv_holds(self);

        let f = PageTableOwner::<C>::metaregion_sound_pred(regions);
        let h = PageTableOwner::<C>::path_tracked_pred(regions);
        let L = self.level as int;
        let idx = self.continuations[L - 1].idx as int;

        assert forall |i: int| #![trigger other.continuations[i]]
            other.level - 1 <= i < NR_LEVELS
        implies
            other.continuations[i].map_children(f)
        by {
            if i > L - 1 {
                assert(other.continuations[i] == self.continuations[i]);
                assert(self.continuations[i].map_children(f));
            } else {
                assert(i == L - 1);
                let o_cont = other.continuations[L - 1];
                let s_cont = self.continuations[L - 1];
                reveal(CursorContinuation::inv_children);
                assert forall |j: int| #![trigger o_cont.children[j]]
                    0 <= j < o_cont.children.len() && o_cont.children[j] is Some
                implies
                    o_cont.children[j].unwrap()
                        .tree_predicate_map(o_cont.path().push_tail(j as usize), f)
                by {
                    if j != idx {
                        assert(o_cont.children[j] == s_cont.children[j]);
                        s_cont.inv_children_unroll(j);
                    }
                };
            }
        };

        assert forall |i: int| #![trigger other.continuations[i]]
            other.level - 1 <= i < NR_LEVELS
        implies
            other.continuations[i].entry_own.metaregion_sound(regions)
        by {
            if i > L - 1 {
                assert(other.continuations[i] == self.continuations[i]);
                self.inv_continuation(i);
            }
        };

        if self.metaregion_correct(regions) {
            assert forall |i: int| #![trigger other.continuations[i]]
                other.level - 1 <= i < NR_LEVELS
            implies
                other.continuations[i].map_children(h)
            by {
                if i > L - 1 {
                    assert(other.continuations[i] == self.continuations[i]);
                    assert(self.continuations[i].map_children(h));
                } else {
                    assert(i == L - 1);
                    let o_cont = other.continuations[L - 1];
                    let s_cont = self.continuations[L - 1];
                    reveal(CursorContinuation::inv_children);
                    assert forall |j: int| #![trigger o_cont.children[j]]
                        0 <= j < o_cont.children.len() && o_cont.children[j] is Some
                    implies
                        o_cont.children[j].unwrap()
                            .tree_predicate_map(o_cont.path().push_tail(j as usize), h)
                    by {
                        if j != idx {
                            assert(o_cont.children[j] == s_cont.children[j]);
                            s_cont.inv_children_unroll(j);
                        }
                    };
                }
            };

            assert forall |i: int| #![trigger other.continuations[i]]
                other.level - 1 <= i < NR_LEVELS
            implies
                h(other.continuations[i].entry_own, other.continuations[i].path())
            by {
                if i > L - 1 {
                    assert(other.continuations[i] == self.continuations[i]);
                    self.inv_continuation(i);
                }
            };
        }
    }

    pub proof fn map_branch_none_inv_holds(self, owner0: Self)
        requires
            owner0.inv(),
            self.level == owner0.level,
            self.va == owner0.va,
            self.guard_level == owner0.guard_level,
            self.prefix == owner0.prefix,
            self.popped_too_high == owner0.popped_too_high,
            // Higher-level continuations unchanged
            forall|i: int| self.level <= i < NR_LEVELS ==>
                #[trigger] self.continuations[i] == owner0.continuations[i],
            // Bottom continuation is well-formed
            self.continuations[self.level - 1].inv(),
            self.continuations[self.level - 1].all_some(),
            self.continuations[self.level - 1].idx == owner0.continuations[owner0.level - 1].idx,
            self.continuations[self.level - 1].entry_own.parent_level
                == owner0.continuations[owner0.level - 1].entry_own.parent_level,
            // Guard address preserved (from parent_perms_preserved).
            self.continuations[self.level - 1].guard_perm.value().inner.inner@.ptr.addr()
                == owner0.continuations[owner0.level - 1].guard_perm.value().inner.inner@.ptr.addr(),
            self.continuations[self.level - 1].path()
                == owner0.continuations[owner0.level - 1].path(),
            self.va.index[self.level - 1] == self.continuations[self.level - 1].idx,
            // Domain preserved: same keys as owner0.
            self.continuations.dom() =~= owner0.continuations.dom(),
        ensures
            self.inv()
    {
        let L = self.level as int;
        assert(self.continuations[L - 1].level() == self.level) by {
            assert(self.continuations[L - 1].path() == owner0.continuations[L - 1].path());
            if L == 1 {} else if L == 2 {} else if L == 3 {} else {}
        };
        assert(self.continuations.contains_key(L - 1)) by {
            if L == 1 {} else if L == 2 {} else if L == 3 {} else {}
        };
    }

    /// After alloc_if_none (absent->node), `path_tracked_pred` transfers via `map_children_lift`.
    pub proof fn map_branch_none_path_tracked_holds(
        self,
        owner0: Self,
        regions: MetaRegionOwners,
        old_regions: MetaRegionOwners,
    )
        requires
            owner0.metaregion_sound(old_regions) && owner0.metaregion_correct(old_regions),
            self.inv(),
            self.level == owner0.level,
            forall|i: int| self.level <= i < NR_LEVELS ==>
                #[trigger] self.continuations[i] == owner0.continuations[i],
            Entry::<C>::path_tracked_pred_preserved(old_regions, regions),
            // Bottom continuation's children satisfy ptp(regions).
            self.continuations[self.level - 1].map_children(
                PageTableOwner::<C>::path_tracked_pred(regions)),
        ensures
            self.map_full_tree(PageTableOwner::<C>::path_tracked_pred(regions))
    {
        let ptp_old = PageTableOwner::<C>::path_tracked_pred(old_regions);
        let ptp_new = PageTableOwner::<C>::path_tracked_pred(regions);
        assert forall|i: int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS implies
                self.continuations[i].map_children(ptp_new)
        by {
            if i >= self.level as int {
                let cont = owner0.continuations[i];
                assert(cont.map_children(ptp_old));
                cont.map_children_lift(ptp_old, ptp_new);
            }
        };
    }

    /// After alloc_if_none (absent->node), `view_mappings` is unchanged (both contribute zero mappings).
    pub proof fn map_branch_none_no_new_mappings(self, owner0: Self)
        requires
            owner0.inv(),
            self.inv(),
            self.level == owner0.level,
            self.va == owner0.va,
            forall|i: int| self.level <= i < NR_LEVELS ==>
                #[trigger] self.continuations[i] == owner0.continuations[i],
            // child at idx changed from absent to empty node
            owner0.continuations[owner0.level - 1].children[
                owner0.continuations[owner0.level - 1].idx as int] is Some,
            owner0.continuations[owner0.level - 1].children[
                owner0.continuations[owner0.level - 1].idx as int].unwrap().value.is_absent(),
            self.continuations[self.level - 1].children[
                self.continuations[self.level - 1].idx as int] is Some,
            self.continuations[self.level - 1].children[
                self.continuations[self.level - 1].idx as int].unwrap().value.is_node(),
            // Non-idx children and path preserved
            self.continuations[self.level - 1].path()
                == owner0.continuations[owner0.level - 1].path(),
            forall|j: int| 0 <= j < NR_ENTRIES
                && j != owner0.continuations[owner0.level - 1].idx as int ==>
                #[trigger] self.continuations[self.level - 1].children[j]
                    == owner0.continuations[owner0.level - 1].children[j],
            // The new node's subtree has empty view_rec (from alloc_if_none postcondition)
            PageTableOwner(self.continuations[self.level - 1].children[
                self.continuations[self.level - 1].idx as int].unwrap())
                .view_rec(self.continuations[self.level - 1].path()
                    .push_tail(self.continuations[self.level - 1].idx as usize))
                =~= Set::<Mapping>::empty(),
        ensures
            self.view_mappings() =~= owner0.view_mappings()
    {
        let L = self.level as int;
        let cont = self.continuations[L - 1];
        let cont0 = owner0.continuations[L - 1];
        let idx = cont0.idx as int;

        assert(cont.view_mappings() =~= cont0.view_mappings()) by {
            cont0.inv_children_unroll(idx);
            PageTableOwner(cont0.children[idx].unwrap())
                .view_rec_absent_empty(cont0.path().push_tail(idx as usize));
            assert forall |m: Mapping| cont.view_mappings().contains(m)
                implies cont0.view_mappings().contains(m) by {
                let j = choose|j:int| 0 <= j < cont.children.len()
                    && #[trigger] cont.children[j] is Some
                    && PageTableOwner(cont.children[j].unwrap())
                        .view_rec(cont.path().push_tail(j as usize)).contains(m);
                if j != idx { assert(cont.children[j] == cont0.children[j]); }
            };
            assert forall |m: Mapping| cont0.view_mappings().contains(m)
                implies cont.view_mappings().contains(m) by {
                let j = choose|j:int| 0 <= j < cont0.children.len()
                    && #[trigger] cont0.children[j] is Some
                    && PageTableOwner(cont0.children[j].unwrap())
                        .view_rec(cont0.path().push_tail(j as usize)).contains(m);
                if j != idx { assert(cont0.children[j] == cont.children[j]); }
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
            forall|i: int| 0 <= i < NR_ENTRIES ==>
                #[trigger] self.continuations[self.level - 1].children[i] is Some &&
                self.continuations[self.level - 1].children[i].unwrap().value.is_absent(),
        ensures
            self.cur_entry_owner().is_absent(),
    {
    }

    pub proof fn cursor_path_nesting(self, i: int, j: int)
        requires
            self.inv(),
            self.level - 1 <= j < i,
            i < NR_LEVELS,
        ensures
            self.continuations[j].path().len() as int > self.continuations[i].path().len() as int,
            self.continuations[j].path().index(self.continuations[i].path().len() as int)
                == self.continuations[i].idx,
    {
        if i == 3 && j == 2 {
            self.continuations[3].path().push_tail_property_index(self.continuations[3].idx as usize);
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
            self.continuations[2].path().push_tail_property_index(self.continuations[2].idx as usize);
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
            self.continuations[1].path().push_tail_property_index(self.continuations[1].idx as usize);
            self.continuations[1].path().push_tail_property_len(self.continuations[1].idx as usize);
        }
    }

    pub proof fn lemma_page_size_spec_5_eq_pow2_48()
        ensures
            page_size_spec(5) == pow2(48nat) as usize,
    {
        crate::specs::arch::paging_consts::lemma_nr_subpage_per_huge_eq_nr_entries();
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
            node_start + page_size((level + 1) as PagingLevel) <= self.locked_range().end,
            !(node_start <= va && va < node_start + page_size((level + 1) as PagingLevel)),
        ensures
            level + 1 < self.guard_level,
    {
        if level + 1 == self.guard_level {
            let pv = self.prefix.to_vaddr() as nat;
            let ps = page_size(self.guard_level as PagingLevel) as nat;
            self.prefix.align_down_concrete(self.guard_level as int);
            self.prefix.align_up_concrete(self.guard_level as int);
            self.prefix.align_diff(self.guard_level as int);
            AbstractVaddr::from_vaddr_to_vaddr_roundtrip(nat_align_down(pv, ps) as Vaddr);
            AbstractVaddr::from_vaddr_to_vaddr_roundtrip(nat_align_up(pv, ps) as Vaddr);
        }
    }
}

} // verus!
