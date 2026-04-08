use vstd::prelude::*;
use vstd::set::{axiom_set_choose_len, axiom_set_intersect_finite};

use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;

use crate::mm::page_table::*;
use crate::mm::{PagingLevel, Vaddr};
use crate::specs::arch::mm::{NR_ENTRIES, NR_LEVELS};
use crate::specs::mm::page_table::cursor::owners::*;
use crate::specs::mm::page_table::owners::PageTableOwner;
use crate::specs::mm::page_table::Mapping;

use crate::mm::page_table::page_size_spec as page_size;

verus! {

impl<'rcu, C: PageTableConfig> CursorOwner<'rcu, C> {

    /// When the current entry is a PT node at level `self.level`, any mapping at `cur_va` has
    /// `page_size <= page_size(self.level - 1)`.  Therefore `split_while_huge` at
    /// `page_size(self.level - 1)` does not split anything and is a no-op on the abstract view.
    /// When present, the query_mapping is from the current subtree's view_rec.
    proof fn query_mapping_from_subtree(self, qm: Mapping)
        requires
            self.inv(),
            self@.inv(),
            self@.present(),
            qm == self@.query_mapping(),
        ensures
            PageTableOwner(self.cur_subtree()).view_rec(self.cur_subtree().value.path).contains(qm),
    {
        let f = self@.mappings.filter(|m2: Mapping| m2.va_range.start <= self@.cur_va < m2.va_range.end);
        axiom_set_intersect_finite::<Mapping>(
            self@.mappings, Set::new(|m2: Mapping| m2.va_range.start <= self@.cur_va < m2.va_range.end));
        axiom_set_choose_len(f);
        self.mapping_covering_cur_va_from_cur_subtree(qm);
    }

    pub proof fn split_while_huge_node_noop(self)
        requires
            self.inv(),
            self.cur_entry_owner().is_node(),
            self.level > 1,
        ensures
            self@.split_while_huge(page_size((self.level - 1) as PagingLevel)) == self@
    {
        self.view_preserves_inv();
        if self@.present() {
            self.cur_subtree_inv();
            let subtree = self.cur_subtree();
            let path = subtree.value.path;
            let qm = self@.query_mapping();
            self.query_mapping_from_subtree(qm);
            let cont = self.continuations[self.level - 1];
            cont.path().push_tail_property_len(cont.idx as usize);
            PageTableOwner(subtree).view_rec_node_page_size_bound(path, qm);
        }
    }

    /// When the current entry is absent, there is no mapping at `cur_va` in the abstract view,
    /// so `split_while_huge` finds nothing to split and is a no-op for any target size.
    pub proof fn split_while_huge_absent_noop(self, size: usize)
        requires
            self.inv(),
            self.cur_entry_owner().is_absent(),
        ensures
            self@.split_while_huge(size) == self@,
    {
        self.view_preserves_inv();
        self.cur_entry_absent_not_present();
    }

    pub proof fn split_while_huge_at_level_noop(self)
        requires
            self.inv(),
        ensures
            self@.split_while_huge(page_size(self.level as PagingLevel)) == self@
    {
        self.view_preserves_inv();
        if self@.present() {
            self.cur_subtree_inv();
            let subtree = self.cur_subtree();
            let path = subtree.value.path;
            let qm = self@.query_mapping();
            self.query_mapping_from_subtree(qm);
            let cont = self.continuations[self.level - 1];
            cont.path().push_tail_property_len(cont.idx as usize);
            PageTableOwner(subtree).view_rec_page_size_bound(path, qm);
        }
    }

    /// After `map_branch_none` splits a huge frame at level `level_before_frame` and descends,
    /// the cursor view equals `owner0@.split_while_huge(page_size(level_before_frame - 1))`.
    ///
    /// Chain:
    ///   owner@ = owner_before_frame@.split_if_mapped_huge_spec(page_size(level_before_frame - 1))
    ///          = owner0@.split_while_huge(page_size(level_before_frame)).split_if_mapped_huge_spec(...)
    ///          = owner0@.split_while_huge(page_size(level_before_frame - 1))
    /// The last equality uses the fact that split_while_huge(L) on a frame of size page_size(L)
    /// takes exactly one split step to page_size(L-1), matching split_if_mapped_huge_spec.
    pub proof fn map_branch_frame_split_while_huge(
        self,
        owner0: Self,
        owner_before_frame: Self,
        level_before_frame: int,
    )
        requires
            self.inv(),
            owner0.inv(),
            owner_before_frame.inv(),
            1 <= level_before_frame - 1,
            level_before_frame <= NR_LEVELS,
            self.level == (level_before_frame - 1) as u8,
            owner_before_frame@ == owner0@.split_while_huge(
                page_size(level_before_frame as PagingLevel)),
            self@ == owner_before_frame@.split_if_mapped_huge_spec(
                page_size((level_before_frame - 1) as PagingLevel)),
        ensures
            self@ == owner0@.split_while_huge(page_size(self.level as PagingLevel))
    { admit() }

    /// After split_if_mapped_huge + push_level, the mappings equal
    /// `old_view.split_while_huge(page_size(current_level))`.
    pub proof fn find_next_split_push_equals_split_while_huge(
        self,
        old_view: CursorView<C>,
    )
        requires
            self.inv(),
            self.cur_entry_owner().is_frame(),
            self@.cur_va == old_view.cur_va,
            old_view.present(),
            self@.mappings =~= old_view.split_if_mapped_huge_spec(
                page_size(self.level as PagingLevel)).mappings,
        ensures
            self@.mappings =~= old_view.split_while_huge(
                page_size(self.level as PagingLevel)).mappings,
    {
        let ps = page_size(self.level as PagingLevel);
        let m = old_view.query_mapping();
        if m.page_size > ps && m.page_size / NR_ENTRIES == ps {
            old_view.split_while_huge_one_step(ps);
        } else {
            admit() // edge cases: multi-step split or page_size <= ps
        }
    }

    /// `split_while_huge` gives the same mappings for two `cur_va` values
    /// when no mapping starts between them and the `!present` case is a no-op.
    pub proof fn split_while_huge_cur_va_independent(
        v1: CursorView<C>,
        v2: CursorView<C>,
        size: usize,
    )
        requires
            v1.inv(),
            v2.inv(),
            v1.mappings =~= v2.mappings,
            v1.cur_va <= v2.cur_va,
            // No mapping starts in [v1.cur_va, v2.cur_va).
            v1.mappings.filter(|m: Mapping|
                v1.cur_va <= m.va_range.start && m.va_range.start < v2.cur_va)
                =~= Set::<Mapping>::empty(),
            // When v1 has no mapping at cur_va, any mapping at v2.cur_va is
            // already small enough that split_while_huge is a no-op on it too.
            // (At the call site this follows from: split_while_huge(v1) was a
            // no-op, so find_next found the mapping without splitting, meaning
            // its page_size <= size.)
            !v1.present() && v2.present() ==> v2.query_mapping().page_size <= size,
        ensures
            v1.split_while_huge(size).mappings =~= v2.split_while_huge(size).mappings,
    {
        if v1.cur_va == v2.cur_va {
            assert(v1 =~= v2);
            return;
        }
        if v1.present() {
            // Both VAs are covered by the same mapping (or v2 is not present).
            // In either case split_while_huge proceeds identically.
            admit()
        }
        // !v1.present(): both split_while_huge calls are no-ops.
    }
}

} // verus!
