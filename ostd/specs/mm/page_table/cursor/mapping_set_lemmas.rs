use vstd::prelude::*;
use vstd::set::{axiom_set_intersect_finite};

use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;

use crate::mm::page_table::*;
use crate::mm::{PagingLevel, Vaddr};
use crate::specs::arch::mm::{NR_ENTRIES, NR_LEVELS};
use crate::specs::mm::page_table::cursor::owners::*;
use crate::specs::mm::page_table::owners::{
    page_size_monotonic, sibling_paths_disjoint, vaddr, OwnerSubtree, PageTableOwner, INC_LEVELS,
};
use crate::specs::mm::page_table::Mapping;

use crate::mm::page_table::page_size_spec as page_size;

verus! {

// ─── CursorContinuation mapping lemmas ───────────────────────────────────────

impl<'rcu, C: PageTableConfig> CursorContinuation<'rcu, C> {

    pub proof fn as_page_table_owner_preserves_view_mappings(self)
        requires
            self.inv(),
            self.all_some(),
        ensures
            self.as_page_table_owner().view_rec(self.path()) == self.view_mappings(),
    {
        self.inv_children_unroll_all();
    }

    pub proof fn view_mappings_take_child(self)
        requires
            self.inv(),
            self.all_some(),
        ensures
            self.take_child_spec().1.view_mappings() == self.view_mappings() - self.view_mappings_take_child_spec()
    {
        self.inv_children_unroll_all();
        let def = self.take_child_spec().1.view_mappings();
        let diff = self.view_mappings() - self.view_mappings_take_child_spec();
        assert forall |m: Mapping| diff.contains(m) implies def.contains(m) by {
            let i = choose|i: int| 0 <= i < self.children.len() && #[trigger] self.children[i] is Some &&
                PageTableOwner(self.children[i].unwrap()).view_rec(self.path().push_tail(i as usize)).contains(m);
            assert(i != self.idx);
            assert(self.take_child_spec().1.children[i] is Some);
        };
        assert forall |m: Mapping|
        #![trigger def.contains(m)]
        def.contains(m) implies diff.contains(m) by {
            let left = self.take_child_spec().1;
            assert(left.view_mappings().contains(m));
            if self.view_mappings_take_child_spec().contains(m) {
                assert(PageTableOwner(self.children[self.idx as int].unwrap()).view_rec(self.path().push_tail(self.idx as usize)).contains(m));
                let i = choose|i: int| 0 <= i < left.children.len() && #[trigger] left.children[i] is Some &&
                    PageTableOwner(left.children[i].unwrap()).view_rec(left.path().push_tail(i as usize)).contains(m);
                assert(i != self.idx);
                assert(PageTableOwner(left.children[i as int].unwrap()).view_rec(left.path().push_tail(i as usize)).contains(m));

                PageTableOwner(self.children[self.idx as int].unwrap()).view_rec_vaddr_range(self.path().push_tail(self.idx as usize), m);
                PageTableOwner(left.children[i as int].unwrap()).view_rec_vaddr_range(left.path().push_tail(i as usize), m);

                let size = page_size((INC_LEVELS - self.path().len()) as PagingLevel);

                // Sibling paths have disjoint VA ranges
                sibling_paths_disjoint(self.path(), self.idx, i as usize, size);
                page_size_monotonic((INC_LEVELS - self.path().len() - 1) as PagingLevel, (INC_LEVELS - self.path().len()) as PagingLevel);

            }
        };
    }

    pub proof fn view_mappings_put_child(self, child: OwnerSubtree<C>)
        requires
            self.inv(),
            child.inv(),
            self.all_but_index_some(),
        ensures
            self.put_child_spec(child).view_mappings() == self.view_mappings() + PageTableOwner(child).view_rec(self.path().push_tail(self.idx as usize))
    {
        let def = self.put_child_spec(child).view_mappings();
        let sum = self.view_mappings() + PageTableOwner(child).view_rec(self.path().push_tail(self.idx as usize));
        assert forall |m: Mapping| sum.contains(m) implies def.contains(m) by {
            if self.view_mappings().contains(m) {
                let i = choose|i: int| 0 <= i < self.children.len() && #[trigger] self.children[i] is Some &&
                    PageTableOwner(self.children[i].unwrap()).view_rec(self.path().push_tail(i as usize)).contains(m);
                assert(i != self.idx);
                assert(self.put_child_spec(child).children[i] == self.children[i]);
            } else {
                assert(PageTableOwner(child).view_rec(self.path().push_tail(self.idx as usize)).contains(m));
                assert(self.put_child_spec(child).children[self.idx as int] == Some(child));
            }
        };
    }
}

// ─── CursorOwner mapping lemmas ──────────────────────────────────────────────

impl<'rcu, C: PageTableConfig> CursorOwner<'rcu, C> {

    /// The current subtree's mappings equal the filter over [cur_va, cur_va + page_size(level)).
    pub proof fn cur_subtree_eq_filtered_mappings(self)
        requires
            self.inv(),
        ensures
            PageTableOwner(self.cur_subtree())@.mappings ==
                self@.mappings.filter(|m: Mapping| self@.cur_va <= m.va_range.start < self@.cur_va + page_size(self.level)),
    {
        let cur_subtree = self.cur_subtree();
        let cur_path = cur_subtree.value.path;
        let cur_va = self.cur_va();
        let size = page_size(self.level);

        let subtree_mappings = PageTableOwner(cur_subtree)@.mappings;
        let filtered = self@.mappings.filter(|m: Mapping| cur_va <= m.va_range.start < cur_va + size);

        assert forall |m: Mapping| subtree_mappings.contains(m) implies filtered.contains(m) by {
            admit();
        };
        assert forall |m: Mapping| filtered.contains(m) implies subtree_mappings.contains(m) by {
            admit();
        };

        assert(subtree_mappings =~= filtered);
    }

    /// Subtrees at different indices have disjoint VA ranges.
    pub proof fn subtree_va_ranges_disjoint(self, j: int)
        requires
            self.inv(),
            0 <= j < NR_ENTRIES,
            j != self.index(),
            self.continuations[self.level - 1].children[j] is Some,
        ensures
            vaddr(self.continuations[self.level - 1].path().push_tail(j as usize)) + page_size(self.level as PagingLevel) <= self.cur_va()
            || self.cur_va() < vaddr(self.continuations[self.level - 1].path().push_tail(j as usize))
    { admit() }

    /// Children of higher-level continuations have VA ranges that don't include cur_va,
    /// because cur_va's indices at those levels match the path to the current position.
    pub proof fn higher_level_children_disjoint(self, i: int, j: int)
        requires
            self.inv(),
            self.level - 1 < i < NR_LEVELS,
            0 <= j < NR_ENTRIES,
            j != self.continuations[i].idx,
            self.continuations[i].children[j] is Some,
        ensures
            vaddr(self.continuations[i].path().push_tail(j as usize)) + page_size((i + 1) as PagingLevel) <= self.cur_va()
            || self.cur_va() < vaddr(self.continuations[i].path().push_tail(j as usize))
    { admit() }

    /// Any mapping that covers cur_va must come from the current subtree.
    /// This follows from the disjointness of VA ranges and the fact that
    /// cur_va falls within the current subtree's VA range.
    pub proof fn mapping_covering_cur_va_from_cur_subtree(self, m: Mapping)
        requires
            self.inv(),
            self.view_mappings().contains(m),
            m.va_range.start <= self.cur_va() < m.va_range.end,
        ensures
            PageTableOwner(self.cur_subtree()).view_rec(self.cur_subtree().value.path).contains(m),
    {
        let cur_va = self.cur_va();

        // m comes from some continuation level i
        let i = choose|i: int| self.level - 1 <= i < NR_LEVELS
            && #[trigger] self.continuations[i].view_mappings().contains(m);
        self.inv_continuation(i);

        let cont_i = self.continuations[i];
        let j = choose|j: int| #![auto] 0 <= j < NR_ENTRIES
            && cont_i.children[j] is Some
            && PageTableOwner(cont_i.children[j].unwrap())
                .view_rec(cont_i.path().push_tail(j as usize)).contains(m);

        cont_i.inv_children_unroll(j);
        let child_j = cont_i.children[j].unwrap();
        let path_j = cont_i.path().push_tail(j as usize);
        PageTableOwner(child_j).view_rec_vaddr_range(path_j, m);

        if i == self.level - 1 {
            if j as usize != self.index() {
                self.subtree_va_ranges_disjoint(j);
            }
        } else {
            if j as usize != cont_i.idx as usize {
                self.higher_level_children_disjoint(i, j);
            } else {
                assert(cont_i.children[cont_i.idx as int] is None);
                assert(false);
            }
        }
    }

    pub proof fn view_mappings_take_lowest(self, new: Self)
        requires
            self.inv(),
            new.continuations == self.continuations.remove(self.level - 1),
        ensures
            new.view_mappings() == self.view_mappings() - self.continuations[self.level - 1].view_mappings(),
    {
        admit()
    }

    pub proof fn view_mappings_put_lowest(self, new: Self, cont: CursorContinuation<C>)
        requires
            cont.inv(),
            new.inv(),
            new.continuations == self.continuations.insert(self.level - 1, cont),
        ensures
            new.view_mappings() == self.view_mappings() + cont.view_mappings(),
    {
        admit()
    }

    pub proof fn as_page_table_owner_preserves_view_mappings(self)
        requires
            self.inv(),
        ensures
            self.as_page_table_owner().view_rec(self.continuations[3].path()) == self.view_mappings(),
    {
        admit()
    }
}

} // verus!
