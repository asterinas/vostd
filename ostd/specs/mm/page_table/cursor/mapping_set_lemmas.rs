use vstd::prelude::*;
use vstd::set::axiom_set_intersect_finite;

use vstd_extra::arithmetic::{
    lemma_nat_align_down_monotone, lemma_nat_align_down_within_block, nat_align_down,
};
use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;

use crate::mm::page_table::*;
use crate::mm::{PagingLevel, Vaddr};
use crate::specs::arch::mm::{NR_ENTRIES, NR_LEVELS};
use crate::specs::mm::page_table::cursor::owners::*;
use crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_divides;
use crate::specs::mm::page_table::owners::{
    lemma_vaddr_of_eq_int, page_size_monotonic, sibling_paths_disjoint, vaddr, vaddr_of,
    OwnerSubtree, PageTableOwner, INC_LEVELS,
};
use crate::specs::mm::page_table::{AbstractVaddr, Mapping};

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
            self.as_subtree().inv(),
            PageTableOwner(self.as_subtree()).pt_inv(),
    {
        self.inv_children_unroll_all();
        self.as_subtree_inv();
        self.as_page_table_owner_pt_inv();
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
                assert(PageTableOwner(self.children[self.idx as int].unwrap())
                    .view_rec(self.path().push_tail(self.idx as usize)).contains(m));
                let i = choose|i: int|
                    0 <= i < left.children.len() && #[trigger] left.children[i] is Some &&
                    PageTableOwner(left.children[i].unwrap())
                        .view_rec(left.path().push_tail(i as usize)).contains(m);
                assert(i != self.idx);
                assert(PageTableOwner(left.children[i as int].unwrap())
                    .view_rec(left.path().push_tail(i as usize)).contains(m));

                PageTableOwner(self.children[self.idx as int].unwrap())
                    .view_rec_vaddr_range(self.path().push_tail(self.idx as usize), m);
                PageTableOwner(left.children[i as int].unwrap())
                    .view_rec_vaddr_range(left.path().push_tail(i as usize), m);

                let size = page_size((INC_LEVELS - self.path().len() - 1) as PagingLevel);
                // Positional disjointness; shift both sides by LEADING_BITS * 2^48.
                sibling_paths_disjoint::<C>(self.path(), self.idx, i as usize, size);
                lemma_vaddr_of_eq_int::<C>(self.path().push_tail(self.idx as usize));
                lemma_vaddr_of_eq_int::<C>(self.path().push_tail(i as usize));
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

impl<'rcu, C: PageTableConfig> CursorContinuation<'rcu, C> {
    /// When a continuation has all_some and inv, its as_subtree() also has Node::inv().
    proof fn as_subtree_inv(self)
        requires
            self.inv(),
            self.all_some(),
        ensures
            self.as_subtree().inv(),
    {
        self.inv_children_unroll_all();
    }

    proof fn as_page_table_owner_pt_inv(self)
        requires
            self.inv(),
            self.all_some(),
        ensures
            PageTableOwner(self.as_subtree()).pt_inv(),
    {
        self.as_subtree_inv();
        let st = self.as_subtree();
        let depth = (INC_LEVELS - st.level) as nat;
        assert forall |i: int| #![trigger st.children[i]]
            0 <= i < NR_ENTRIES implies
                PageTableOwner::<C>::pt_edge_at(st, i)
                && PageTableOwner(st.children[i].unwrap())
                       .pt_inv_at_depth((depth - 1) as nat)
        by {
            self.inv_children_rel_unroll(i);
            self.pt_inv_children_unroll(i);
        };
    }
}

// ─── CursorOwner mapping lemmas ──────────────────────────────────────────────

impl<'rcu, C: PageTableConfig> CursorOwner<'rcu, C> {

    /// The current subtree's mappings equal the filter over [subtree_va, subtree_va + page_size(level))
    /// where subtree_va = vaddr(cur_subtree path).
    pub proof fn cur_subtree_eq_filtered_mappings_path(self)
        requires
            self.inv(),
            self.in_locked_range(),
        ensures ({
            let subtree_va = vaddr_of::<C>(self.cur_subtree().value.path) as int;
            let size = page_size(self.level) as int;
            PageTableOwner(self.cur_subtree())@.mappings ==
                self@.mappings.filter(|m: Mapping| subtree_va <= m.va_range.start < subtree_va + size)
        }),
    {
        let cur_subtree = self.cur_subtree();
        let cur_path = cur_subtree.value.path;
        let subtree_va = vaddr_of::<C>(cur_path) as int;
        let size = page_size(self.level) as int;

        let subtree_mappings = PageTableOwner(cur_subtree)@.mappings;
        let filtered = self@.mappings.filter(|m: Mapping| subtree_va <= m.va_range.start < subtree_va + size);

        self.cur_subtree_inv();

        let cont = self.continuations[self.level - 1];
        self.inv_continuation(self.level - 1);
        cont.inv_children_rel_unroll(self.index() as int);
        // cur_subtree.value.path == cont.path().push_tail(self.index())

        // Forward: subtree mappings are in the filtered set
        assert forall |m: Mapping| subtree_mappings.contains(m) implies filtered.contains(m) by {
            // m is in the current subtree's view_rec => in cont[level-1].view_mappings() => in self.view_mappings()
            assert(cont.children[self.index() as int] is Some);
            assert(cont.children[self.index() as int].unwrap() == cur_subtree);
            assert(cont.view_mappings().contains(m));
            assert(self.view_mappings().contains(m));

            // view_rec_vaddr_range gives m.va_range.start in
            // [vaddr_of(cur_path), vaddr_of(cur_path) + page_size(level)),
            // which is exactly our filter range.
            PageTableOwner(cur_subtree).view_rec_vaddr_range(cur_path, m);
        };

        // Reverse: filtered mappings are in the subtree
        assert forall |m: Mapping| filtered.contains(m) implies subtree_mappings.contains(m) by {
            // m is in self.view_mappings() and subtree_va <= m.va_range.start < subtree_va + size
            let i = choose|i: int| self.level - 1 <= i < NR_LEVELS
                && #[trigger] self.continuations[i].view_mappings().contains(m);
            self.inv_continuation(i);

            let cont_i = self.continuations[i];
            let j = choose|j: int| #![auto] 0 <= j < NR_ENTRIES
                && cont_i.children[j] is Some
                && PageTableOwner(cont_i.children[j].unwrap())
                    .view_rec(cont_i.path().push_tail(j as usize)).contains(m);

            cont_i.inv_children_unroll(j);
            PageTableOwner(cont_i.children[j].unwrap()).view_rec_vaddr_range(
                cont_i.path().push_tail(j as usize), m);

            if i == self.level - 1 {
                if j as usize == self.index() {
                    // cont_i.children[j] is exactly cur_subtree; m is already
                    // in subtree_mappings via view_rec at the same path.
                    assert(cont_i.children[j] == Some(cur_subtree));
                    assert(cont_i.path().push_tail(j as usize) == cur_path);
                    assert(subtree_mappings == PageTableOwner(cur_subtree).view_rec(cur_path));
                    assert(PageTableOwner(cur_subtree).view_rec(cur_path).contains(m));
                    assert(subtree_mappings.contains(m));
                } else {
                    // Disjointness: sibling j's VA range doesn't overlap [subtree_va, subtree_va + page_size(level))
                    assert(cont.level() == self.level) by {
                        if self.level == 1 {} else if self.level == 2 {} else if self.level == 3 {} else {}
                    };
                    let sib_size = page_size((INC_LEVELS - cont.path().len() - 1) as PagingLevel);
                    sibling_paths_disjoint::<C>(cont.path(), self.index(), j as usize, sib_size);
                    // Lift positional disjointness to canonical by adding
                    // the same leading_bits * 2^48 to both sides.
                    lemma_vaddr_of_eq_int::<C>(cont.path().push_tail(self.index() as usize));
                    lemma_vaddr_of_eq_int::<C>(cont.path().push_tail(j as usize));
                    assert(false);  // contradiction from disjointness + filter
                }
            } else {
                if j as usize != cont_i.idx as usize {
                    // Subtree VA range is contained in ancestor child range
                    self.subtree_va_in_ancestor_range(i);

                    // Sibling j is disjoint from cont_i.idx child
                    assert(cont_i.level() == (i + 1) as PagingLevel) by {
                        if i == 0 {} else if i == 1 {} else if i == 2 {} else {}
                    };
                    let sib_size = page_size((INC_LEVELS - cont_i.path().len() - 1) as PagingLevel);
                    sibling_paths_disjoint::<C>(cont_i.path(), cont_i.idx, j as usize, sib_size);
                    lemma_vaddr_of_eq_int::<C>(cont_i.path().push_tail(cont_i.idx as usize));
                    lemma_vaddr_of_eq_int::<C>(cont_i.path().push_tail(j as usize));
                    lemma_vaddr_of_eq_int::<C>(cur_path);
                    assert(false);  // contradiction
                } else {
                    assert(cont_i.children[cont_i.idx as int] is None);
                    assert(false);  // cont_i.children[j] is Some contradicts
                }
            }
        };

        assert(subtree_mappings =~= filtered);
    }

    /// Version using nat_align_down(cur_va, page_size(level)) in the filter.
    /// Bridge: nat_align_down(cur_va, ps) as int == vaddr(cur_path) + leading_bits * 2^48.
    pub proof fn cur_subtree_eq_filtered_mappings(self)
        requires
            self.inv(),
            self.in_locked_range(),
        ensures ({
            let start = nat_align_down(self@.cur_va as nat, page_size(self.level) as nat) as Vaddr;
            let size = page_size(self.level);
            PageTableOwner(self.cur_subtree())@.mappings ==
                self@.mappings.filter(|m: Mapping| start <= m.va_range.start < start + size)
        }),
    {
        // Bridge: `nat_align_down(cur_va, ps) as Vaddr == vaddr_of::<C>(cur_path)`.
        //   _path version filters on `vaddr_of(cur_path)` (canonical).
        //   to_path_vaddr_concrete + cursor inv + lemma_vaddr_of_eq_int
        //   identify the two boundaries.
        self.cur_subtree_eq_filtered_mappings_path();
        self.cur_va_in_cont_child_range(self.level - 1);
        self.va.to_path_vaddr_concrete(self.level as int - 1);
        let cur_path = self.cur_subtree().value.path;
        let ps = page_size(self.level);
        lemma_vaddr_of_eq_int::<C>(cur_path);
        // Bridge nat_align_down's nat→usize cast (no wrap since
        // nat_align_down(x, _) <= x <= usize::MAX).
        vstd_extra::arithmetic::lemma_nat_align_down_sound(
            self@.cur_va as nat, ps as nat);
        let nad = nat_align_down(self@.cur_va as nat, ps as nat);
        assert(nad <= self@.cur_va as nat);
        assert(nad <= usize::MAX);
        assert((nad as Vaddr) as int == nad as int);
        assert((nad as Vaddr) as int == vaddr_of::<C>(cur_path) as int);
    }

    /// The cursor's VA falls within the canonical VA range of any ancestor
    /// continuation's child that the cursor descended through. Canonical
    /// form: positional `vaddr(path)` plus the `leading_bits * 2^48` shift.
    proof fn cur_va_in_cont_child_range(self, lvl: int)
        requires
            self.inv(),
            self.in_locked_range(),
            self.level - 1 <= lvl < NR_LEVELS,
        ensures
            vaddr(self.continuations[lvl].path().push_tail(self.continuations[lvl].idx as usize)) as int
                + self.va.leading_bits * 0x1_0000_0000_0000int
                <= self.cur_va() as int,
            (self.cur_va() as int)
                < vaddr(self.continuations[lvl].path().push_tail(self.continuations[lvl].idx as usize)) as int
                    + self.va.leading_bits * 0x1_0000_0000_0000int
                    + page_size((lvl + 1) as PagingLevel) as int,
            vaddr(self.continuations[lvl].path().push_tail(self.continuations[lvl].idx as usize))
                == vaddr(self.va.to_path(lvl)),
    {
        let cont = self.continuations[lvl];
        let child_path = cont.path().push_tail(cont.idx as usize);
        let va_path = self.va.to_path(lvl);

        self.va.to_path_len(lvl);
        cont.path().push_tail_property_len(cont.idx as usize);
        assert(cont.level() == (lvl + 1) as PagingLevel) by {
            if lvl == 0 {} else if lvl == 1 {} else if lvl == 2 {} else {}
        };

        assert forall|k: int| 0 <= k < child_path.len() implies
            child_path.index(k) == va_path.index(k) by {
            self.va.to_path_index(lvl, k);
            if lvl == 3 {
                cont.path().push_tail_property_index(cont.idx as usize);
            } else if lvl == 2 {
                cont.path().push_tail_property_index(cont.idx as usize);
                self.continuations[3].path().push_tail_property_index(self.continuations[3].idx as usize);
            } else if lvl == 1 {
                cont.path().push_tail_property_index(cont.idx as usize);
                self.continuations[2].path().push_tail_property_index(self.continuations[2].idx as usize);
                self.continuations[3].path().push_tail_property_index(self.continuations[3].idx as usize);
            } else {
                cont.path().push_tail_property_index(cont.idx as usize);
                self.continuations[1].path().push_tail_property_index(self.continuations[1].idx as usize);
                self.continuations[2].path().push_tail_property_index(self.continuations[2].idx as usize);
                self.continuations[3].path().push_tail_property_index(self.continuations[3].idx as usize);
            }
        };

        self.va.to_path_inv(lvl);
        cont.path().push_tail_preserves_inv(cont.idx as usize);
        AbstractVaddr::rec_vaddr_eq_if_indices_eq(child_path, va_path, 0);
        self.va.vaddr_range_from_path(lvl);
    }

    /// The current subtree's VA range [subtree_va, subtree_va + page_size(level)) is contained
    /// within the VA range of any ancestor continuation's child that the cursor descended through.
    proof fn subtree_va_in_ancestor_range(self, lvl: int)
        requires
            self.inv(),
            self.in_locked_range(),
            self.level - 1 < lvl < NR_LEVELS,
        ensures ({
            let subtree_va = vaddr(self.cur_subtree().value.path);
            let idx_path_va = vaddr(self.continuations[lvl].path().push_tail(self.continuations[lvl].idx as usize));
            &&& idx_path_va <= subtree_va
            &&& subtree_va + page_size(self.level) <= idx_path_va + page_size((lvl + 1) as PagingLevel)
        }),
    {
        let cont = self.continuations[self.level - 1];
        self.inv_continuation(self.level - 1);
        cont.inv_children_rel_unroll(self.index() as int);
        // cur_subtree.value.path == cont.path().push_tail(self.index())

        self.cur_va_in_cont_child_range(self.level - 1);
        self.cur_va_in_cont_child_range(lvl);
        self.va.to_path_vaddr_concrete(self.level as int - 1);
        self.va.to_path_vaddr_concrete(lvl);

        let x = self.cur_va() as nat;
        let fine = page_size(self.level as PagingLevel) as nat;
        let coarse = page_size((lvl + 1) as PagingLevel) as nat;
        let shift = self.va.leading_bits * 0x1_0000_0000_0000int;

        // Explicit chain: subtree_va + shift == nat_align_down(x, fine)
        let subtree_va = vaddr(self.cur_subtree().value.path);
        assert(subtree_va == vaddr(self.va.to_path(self.level as int - 1)));
        assert(subtree_va as int + shift == nat_align_down(x, fine) as int);

        // Explicit chain: idx_path_va + shift == nat_align_down(x, coarse)
        let idx_path_va = vaddr(self.continuations[lvl].path().push_tail(self.continuations[lvl].idx as usize));
        assert(idx_path_va == vaddr(self.va.to_path(lvl)));
        assert(idx_path_va as int + shift == nat_align_down(x, coarse) as int);

        lemma_page_size_divides(self.level as PagingLevel, (lvl + 1) as PagingLevel);
        lemma_nat_align_down_monotone(x, fine, coarse);
        lemma_nat_align_down_within_block(x, fine, coarse);

        // Bridge nat to usize: values fit in usize since they're <= cur_va
        vstd_extra::arithmetic::lemma_nat_align_down_sound(x, fine);
        vstd_extra::arithmetic::lemma_nat_align_down_sound(x, coarse);
    }

    /// Subtrees at different indices have disjoint VA ranges.
    pub proof fn subtree_va_ranges_disjoint(self, j: int)
        requires
            self.inv(),
            self.in_locked_range(),
            0 <= j < NR_ENTRIES,
            j != self.index(),
            self.continuations[self.level - 1].children[j] is Some,
        ensures
            vaddr(self.continuations[self.level - 1].path().push_tail(j as usize)) as int
                + self.va.leading_bits * 0x1_0000_0000_0000int
                + page_size(self.level as PagingLevel) as int
                <= self.cur_va() as int
            || (self.cur_va() as int)
                < vaddr(self.continuations[self.level - 1].path().push_tail(j as usize)) as int
                    + self.va.leading_bits * 0x1_0000_0000_0000int
    {
        let cont = self.continuations[self.level - 1];
        let idx = self.index();

        // Establish cont.level() == self.level via case split
        assert(cont.level() == self.level) by {
            if self.level == 1 {} else if self.level == 2 {} else if self.level == 3 {} else {}
        };

        // cur_va is within the child at cont[level-1].idx
        self.cur_va_in_cont_child_range(self.level - 1);

        // Sibling paths are separated by `page_size(self.level)` (child page size).
        let size = page_size((INC_LEVELS - cont.path().len() - 1) as PagingLevel);
        sibling_paths_disjoint::<C>(cont.path(), idx, j as usize, size);
    }

    /// Children of higher-level continuations have VA ranges that don't include cur_va,
    /// because cur_va's indices at those levels match the path to the current position.
    pub proof fn higher_level_children_disjoint(self, i: int, j: int)
        requires
            self.inv(),
            self.in_locked_range(),
            self.level - 1 < i < NR_LEVELS,
            0 <= j < NR_ENTRIES,
            j != self.continuations[i].idx,
            self.continuations[i].children[j] is Some,
        ensures
            vaddr(self.continuations[i].path().push_tail(j as usize)) as int
                + self.va.leading_bits * 0x1_0000_0000_0000int
                + page_size((i + 1) as PagingLevel) as int
                <= self.cur_va() as int
            || (self.cur_va() as int)
                < vaddr(self.continuations[i].path().push_tail(j as usize)) as int
                    + self.va.leading_bits * 0x1_0000_0000_0000int
    {
        let cont = self.continuations[i];

        // Establish cont.level() == i + 1 via case split
        assert(cont.level() == (i + 1) as PagingLevel) by {
            if i == 0 {} else if i == 1 {} else if i == 2 {} else {}
        };

        // cur_va is within the child at cont[i].idx
        self.cur_va_in_cont_child_range(i);

        // Siblings at this depth are separated by `page_size(i+1)` (child page size).
        let size = page_size((INC_LEVELS - cont.path().len() - 1) as PagingLevel);
        sibling_paths_disjoint::<C>(cont.path(), cont.idx, j as usize, size);
    }

    /// Any mapping that covers cur_va must come from the current subtree.
    /// This follows from the disjointness of VA ranges and the fact that
    /// cur_va falls within the current subtree's VA range.
    pub proof fn mapping_covering_cur_va_from_cur_subtree(self, m: Mapping)
        requires
            self.inv(),
            self.in_locked_range(),
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
        // Bridge view_rec_vaddr_range's canonical bounds to the
        // disjointness lemmas (also canonical after the refactor).
        lemma_vaddr_of_eq_int::<C>(path_j);

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

    /// Combined replace: swap the lowest continuation, relating old and new mapping sets.
    /// Avoids the Map::remove phantom key issue by requiring both old and new to have inv().
    #[verifier::rlimit(60)]
    pub proof fn view_mappings_replace_lowest(
        old_self: Self, new_self: Self,
        old_cont: CursorContinuation<'rcu, C>,
        new_cont: CursorContinuation<'rcu, C>,
    )
        requires
            old_self.inv(),
            old_self.in_locked_range(),
            new_self.inv(),
            old_self.level == new_self.level,
            old_self.continuations[old_self.level - 1] == old_cont,
            new_self.continuations[new_self.level - 1] == new_cont,
            forall|i: int| old_self.level <= i < NR_LEVELS ==>
                old_self.continuations[i] == new_self.continuations[i],
        ensures
            new_self.view_mappings() ==
                (old_self.view_mappings() - old_cont.view_mappings()).union(new_cont.view_mappings()),
    {
        let level = old_self.level;

        assert forall |m: Mapping| new_self.view_mappings().contains(m) implies
            ((old_self.view_mappings().contains(m) && !old_cont.view_mappings().contains(m)) || new_cont.view_mappings().contains(m))
        by {
            let i = choose|i: int| level - 1 <= i < NR_LEVELS
                && #[trigger] new_self.continuations[i].view_mappings().contains(m);
            if i == level - 1 {
                assert(new_cont.view_mappings().contains(m));
            } else {
                assert(old_self.continuations[i] == new_self.continuations[i]);
                assert(old_self.continuations[i].view_mappings().contains(m));
                assert(old_self.view_mappings().contains(m));

                if old_cont.view_mappings().contains(m) {
                    old_self.inv_continuation(i);
                    old_self.inv_continuation(level - 1);
                    let cont_i = old_self.continuations[i];
                    let j = choose|j: int| #![auto] 0 <= j < NR_ENTRIES
                        && cont_i.children[j] is Some
                        && PageTableOwner(cont_i.children[j].unwrap())
                            .view_rec(cont_i.path().push_tail(j as usize)).contains(m);
                    cont_i.inv_children_unroll(j);
                    PageTableOwner(cont_i.children[j].unwrap()).view_rec_vaddr_range(
                        cont_i.path().push_tail(j as usize), m);

                    let k = choose|k: int| #![auto] 0 <= k < NR_ENTRIES
                        && old_cont.children[k] is Some
                        && PageTableOwner(old_cont.children[k].unwrap())
                            .view_rec(old_cont.path().push_tail(k as usize)).contains(m);
                    old_cont.inv_children_unroll(k);
                    PageTableOwner(old_cont.children[k].unwrap()).view_rec_vaddr_range(
                        old_cont.path().push_tail(k as usize), m);

                    if j as usize != cont_i.idx as usize {
                        assert(cont_i.level() == (i + 1) as PagingLevel) by {
                            if i == 0 {} else if i == 1 {} else if i == 2 {} else {}
                        };

                        old_self.cur_va_in_cont_child_range(level as int);
                        old_self.va.to_path_vaddr_concrete(level as int);
                        old_self.cur_va_in_cont_child_range(i);
                        old_self.va.to_path_vaddr_concrete(i);

                        let x = old_self.cur_va() as nat;
                        let ps_node = page_size((level + 1) as PagingLevel) as nat;
                        let ps_anc = page_size((i + 1) as PagingLevel) as nat;

                        crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_ge_page_size((level + 1) as PagingLevel);
                        crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_ge_page_size((i + 1) as PagingLevel);
                        lemma_page_size_divides((level + 1) as PagingLevel, (i + 1) as PagingLevel);

                        lemma_nat_align_down_monotone(x, ps_node, ps_anc);
                        lemma_nat_align_down_within_block(x, ps_node, ps_anc);
                        vstd_extra::arithmetic::lemma_nat_align_down_sound(x, ps_node);
                        vstd_extra::arithmetic::lemma_nat_align_down_sound(x, ps_anc);

                        let sib_size = page_size((INC_LEVELS - cont_i.path().len() - 1) as PagingLevel);
                        sibling_paths_disjoint::<C>(cont_i.path(), cont_i.idx, j as usize, sib_size);
                        // Lift positional disjointness to canonical.
                        lemma_vaddr_of_eq_int::<C>(cont_i.path().push_tail(cont_i.idx as usize));
                        lemma_vaddr_of_eq_int::<C>(cont_i.path().push_tail(j as usize));

                        old_cont.as_subtree_inv();
                        PageTableOwner(old_cont.as_subtree()).view_rec_vaddr_range(old_cont.path(), m);
                    } else {
                        assert(cont_i.children[cont_i.idx as int] is None);
                    }
                }
            }
        };

        assert forall |m: Mapping|
            ((old_self.view_mappings().contains(m) && !old_cont.view_mappings().contains(m)) || new_cont.view_mappings().contains(m))
            implies new_self.view_mappings().contains(m)
        by {
            if new_cont.view_mappings().contains(m) {
                assert(new_self.continuations[level - 1].view_mappings().contains(m));
            } else {
                // m in old.vm() and not in old_cont.vm(), so m in some higher cont
                let i = choose|i: int| level - 1 <= i < NR_LEVELS
                    && #[trigger] old_self.continuations[i].view_mappings().contains(m);
                if i == level - 1 {
                    // contradiction: m in old_cont but we assumed m not in old_cont
                    assert(false);
                } else {
                    assert(new_self.continuations[i] == old_self.continuations[i]);
                    assert(new_self.continuations[i].view_mappings().contains(m));
                }
            }
        };

        assert(new_self.view_mappings() =~=
            (old_self.view_mappings() - old_cont.view_mappings()).union(new_cont.view_mappings()));
    }

    pub proof fn as_page_table_owner_preserves_view_mappings(self)
        requires
            self.inv(),
        ensures
            self.as_page_table_owner().view_rec(self.continuations[3].path()) == self.view_mappings(),
            self.as_page_table_owner().0.inv(),
            self.as_page_table_owner().0.level == self.continuations[3].tree_level,
            self.as_page_table_owner().pt_inv(),
    {
        if self.level == 4 {
            self.continuations[3].as_page_table_owner_preserves_view_mappings();
            assert(self.view_mappings() =~= self.continuations[3].view_mappings());
        } else if self.level == 3 {
            let c2 = self.continuations[2];
            let c3 = self.continuations[3];

            c2.as_page_table_owner_preserves_view_mappings();
            c2.as_subtree_inv();
            c3.view_mappings_put_child(c2.as_subtree());
            c3.as_subtree_restore(c2);

            let l4 = c3.restore_spec(c2).0;
            assert(l4.all_some()) by {
                assert forall |i: int| 0 <= i < NR_ENTRIES implies l4.children[i] is Some by {
                    if i == c3.idx as int {
                    } else {
                        assert(l4.children[i] == c3.children[i]);
                    }
                };
            };

            c2.as_page_table_owner_pt_inv();
            assert(l4.pt_inv_children()) by {
                assert forall |i: int|
                    #![trigger l4.children[i]]
                    !(0 <= i < l4.children.len())
                        || (l4.children[i] is Some ==> PageTableOwner(l4.children[i].unwrap()).pt_inv())
                by {
                    if 0 <= i < l4.children.len() {
                        if i == c3.idx as int {
                            assert(l4.children[i] == Some(c2.as_subtree()));
                        } else {
                            assert(l4.children[i] == c3.children[i]);
                            c3.pt_inv_children_unroll(i);
                        }
                    } else {
                        assert(!(0 <= i < l4.children.len()));
                    }
                };
            };

            c2.inv_children_unroll_all();
            c3.inv_children_unroll_all();
            l4.as_page_table_owner_preserves_view_mappings();

            assert(self.view_mappings() =~= self.continuations[2].view_mappings().union(self.continuations[3].view_mappings())) by {
                assert forall |m: Mapping| #[trigger] self.view_mappings().contains(m) implies
                    self.continuations[2].view_mappings().contains(m) || self.continuations[3].view_mappings().contains(m) by {
                    let i = choose |i: int| 2 <= i < NR_LEVELS && #[trigger] self.continuations[i].view_mappings().contains(m);
                };
            };
        } else if self.level == 2 {
            let c1 = self.continuations[1];
            let c2 = self.continuations[2];
            let c3 = self.continuations[3];

            c1.as_page_table_owner_preserves_view_mappings();
            c1.as_subtree_inv();
            c2.view_mappings_put_child(c1.as_subtree());
            c2.as_subtree_restore(c1);

            let l3 = c2.restore_spec(c1).0;
            assert(l3.all_some()) by {
                assert forall |i: int| 0 <= i < NR_ENTRIES implies l3.children[i] is Some by {
                    if i == c2.idx as int {
                    } else {
                        assert(l3.children[i] == c2.children[i]);
                    }
                };
            };
            c1.as_page_table_owner_pt_inv();
            assert(l3.pt_inv_children()) by {
                assert forall |i: int|
                    #![trigger l3.children[i]]
                    !(0 <= i < l3.children.len())
                        || (l3.children[i] is Some ==> PageTableOwner(l3.children[i].unwrap()).pt_inv())
                by {
                    if 0 <= i < l3.children.len() {
                        if i == c2.idx as int {
                            assert(l3.children[i] == Some(c1.as_subtree()));
                        } else {
                            assert(l3.children[i] == c2.children[i]);
                            c2.pt_inv_children_unroll(i);
                        }
                    } else {
                        assert(!(0 <= i < l3.children.len()));
                    }
                };
            };

            c1.inv_children_unroll_all();
            c2.inv_children_unroll_all();
            l3.as_page_table_owner_preserves_view_mappings();
            l3.as_subtree_inv();
            c3.as_subtree_restore(l3);
            c3.view_mappings_put_child(l3.as_subtree());

            let l4 = c3.restore_spec(l3).0;
            assert(l4.all_some()) by {
                assert forall |i: int| 0 <= i < NR_ENTRIES implies l4.children[i] is Some by {
                    if i == c3.idx as int {
                        assert(l4.children[i] == Some(l3.as_subtree()));
                    } else {
                        assert(l4.children[i] == c3.children[i]);
                    }
                };
            };
            l3.as_page_table_owner_pt_inv();
            assert(l4.pt_inv_children()) by {
                assert forall |i: int|
                    #![trigger l4.children[i]]
                    !(0 <= i < l4.children.len())
                        || (l4.children[i] is Some ==> PageTableOwner(l4.children[i].unwrap()).pt_inv())
                by {
                    if 0 <= i < l4.children.len() {
                        if i == c3.idx as int {
                            assert(l4.children[i] == Some(l3.as_subtree()));
                        } else {
                            assert(l4.children[i] == c3.children[i]);
                            c3.pt_inv_children_unroll(i);
                        }
                    } else {
                        assert(!(0 <= i < l4.children.len()));
                    }
                };
            };

            c3.inv_children_unroll_all();
            l4.as_page_table_owner_preserves_view_mappings();

            assert(self.view_mappings() =~= c1.view_mappings().union(c2.view_mappings()).union(c3.view_mappings())) by {
                assert forall |m: Mapping| self.view_mappings().contains(m) implies
                    (c1.view_mappings().contains(m) || c2.view_mappings().contains(m) || c3.view_mappings().contains(m)) by {
                    let i = choose |i: int| 1 <= i < NR_LEVELS && #[trigger] self.continuations[i].view_mappings().contains(m);
                };
            };
        } else {
            // level == 1
            let c0 = self.continuations[0];
            let c1 = self.continuations[1];
            let c2 = self.continuations[2];
            let c3 = self.continuations[3];

            c0.as_page_table_owner_preserves_view_mappings();
            c0.as_subtree_inv();
            c1.view_mappings_put_child(c0.as_subtree());
            c1.as_subtree_restore(c0);
            let l2 = c1.restore_spec(c0).0;
            assert(l2.all_some()) by {
                assert forall |i: int| 0 <= i < NR_ENTRIES implies l2.children[i] is Some by {
                    if i == c1.idx as int {
                    } else {
                        assert(l2.children[i] == c1.children[i]);
                    }
                };
            };
            c0.as_page_table_owner_pt_inv();
            assert(l2.pt_inv_children()) by {
                assert forall |i: int| #![trigger l2.children[i]]
                    !(0 <= i < l2.children.len())
                        || (l2.children[i] is Some ==> PageTableOwner(l2.children[i].unwrap()).pt_inv())
                by {
                    if 0 <= i < l2.children.len() {
                        if i == c1.idx as int {
                            assert(l2.children[i] == Some(c0.as_subtree()));
                        } else {
                            assert(l2.children[i] == c1.children[i]);
                            c1.pt_inv_children_unroll(i);
                        }
                    } else {
                        assert(!(0 <= i < l2.children.len()));
                    }
                };
            };

            c0.inv_children_unroll_all();
            c1.inv_children_unroll_all();
            l2.as_page_table_owner_preserves_view_mappings();
            l2.as_subtree_inv();
            c2.view_mappings_put_child(l2.as_subtree());
            c2.as_subtree_restore(l2);
            let l3 = c2.restore_spec(l2).0;
            assert(l3.all_some()) by {
                assert forall |i: int| 0 <= i < NR_ENTRIES implies l3.children[i] is Some by {
                    if i == c2.idx as int {
                    } else {
                        assert(l3.children[i] == c2.children[i]);
                    }
                };
            };
            l2.as_page_table_owner_pt_inv();
            assert(l3.pt_inv_children()) by {
                assert forall |i: int| #![trigger l3.children[i]]
                    !(0 <= i < l3.children.len())
                        || (l3.children[i] is Some ==> PageTableOwner(l3.children[i].unwrap()).pt_inv())
                by {
                    if 0 <= i < l3.children.len() {
                        if i == c2.idx as int {
                            assert(l3.children[i] == Some(l2.as_subtree()));
                        } else {
                            assert(l3.children[i] == c2.children[i]);
                            c2.pt_inv_children_unroll(i);
                        }
                    } else {
                        assert(!(0 <= i < l3.children.len()));
                    }
                };
            };

            c2.inv_children_unroll_all();
            l3.as_page_table_owner_preserves_view_mappings();
            l3.as_subtree_inv();
            c3.view_mappings_put_child(l3.as_subtree());
            c3.as_subtree_restore(l3);
            let l4 = c3.restore_spec(l3).0;
            assert(l4.all_some()) by {
                assert forall |i: int| 0 <= i < NR_ENTRIES implies l4.children[i] is Some by {
                    if i == c3.idx as int {
                    } else {
                        assert(l4.children[i] == c3.children[i]);
                    }
                };
            };
            l3.as_page_table_owner_pt_inv();
            assert(l4.pt_inv_children()) by {
                assert forall |i: int| #![trigger l4.children[i]]
                    !(0 <= i < l4.children.len())
                        || (l4.children[i] is Some ==> PageTableOwner(l4.children[i].unwrap()).pt_inv())
                by {
                    if 0 <= i < l4.children.len() {
                        if i == c3.idx as int {
                            assert(l4.children[i] == Some(l3.as_subtree()));
                        } else {
                            assert(l4.children[i] == c3.children[i]);
                            c3.pt_inv_children_unroll(i);
                        }
                    } else {
                        assert(!(0 <= i < l4.children.len()));
                    }
                };
            };

            c3.inv_children_unroll_all();
            l4.as_page_table_owner_preserves_view_mappings();

            assert(self.view_mappings() =~= c0.view_mappings().union(c1.view_mappings()).union(c2.view_mappings()).union(c3.view_mappings())) by {
                assert forall |m: Mapping| self.view_mappings().contains(m) implies
                    (c0.view_mappings().contains(m) || c1.view_mappings().contains(m) || c2.view_mappings().contains(m) || c3.view_mappings().contains(m)) by {
                    let i = choose |i: int| 0 <= i < NR_LEVELS && #[trigger] self.continuations[i].view_mappings().contains(m);
                };
            };
        }
    }

    /// Every mapping in the cursor view satisfies `Mapping::inv()`.
    ///
    /// Collapses the cursor view into a single-root `view_rec` and applies
    /// `view_rec_mapping_inv`. Inherits the latter's two narrow `assume`s
    /// on `vaddr(path)` arithmetic.
    pub proof fn view_mapping_inv(self)
        requires
            self.inv(),
        ensures
            forall |m: Mapping| self.view_mappings().contains(m) ==> #[trigger] m.inv(),
    {
        self.as_page_table_owner_preserves_view_mappings();
        let pto = self.as_page_table_owner();
        let root_path = self.continuations[3].path();
        self.inv_continuation(NR_LEVELS as int - 1);
        pto.view_rec_mapping_inv(root_path);
    }

    /// Every mapping in the cursor view has `page_size ∈ {4K, 2M, 1G}`.
    ///
    /// Uses the standard collapse trick: `view_mappings` equals
    /// `as_page_table_owner().view_rec(continuations[3].path())`, then applies
    /// `view_rec_mapping_page_size`. The root's `parent_level == 5 == INC_LEVELS`
    /// is given by the cursor invariant (continuations[3].entry_own.parent_level == 5).
    pub proof fn view_mapping_page_size_valid(self)
        requires
            self.inv(),
        ensures
            forall |m: Mapping| #[trigger] self.view_mappings().contains(m) ==>
                set![4096usize, 2097152usize, 1073741824usize].contains(m.page_size),
    {
        self.as_page_table_owner_preserves_view_mappings();
        let pto = self.as_page_table_owner();
        let root_path = self.continuations[3].path();
        self.inv_continuation(NR_LEVELS as int - 1);
        // pto.0.level == continuations[3].tree_level == 0
        // pto.0.value.parent_level == continuations[3].entry_own.parent_level == 5
        // == INC_LEVELS == INC_LEVELS - 0 == INC_LEVELS - pto.0.level
        pto.view_rec_mapping_page_size(root_path);
    }

    /// Finiteness of the cursor view.
    ///
    /// Collapses the union-over-continuations `view_mappings` into a single
    /// `view_rec` rooted at the reconstructed root page table, then uses
    /// `view_rec_finite` (bounded depth / branching).
    pub proof fn view_mappings_finite(self)
        requires
            self.inv(),
        ensures
            self.view_mappings().finite(),
    {
        self.as_page_table_owner_preserves_view_mappings();
        let pto = self.as_page_table_owner();
        let root_path = self.continuations[3].path();
        self.inv_continuation(NR_LEVELS as int - 1);
        pto.view_rec_finite(root_path);
    }

    /// Non-overlapping mappings in the cursor view.
    ///
    /// Collapses the union-over-continuations `view_mappings` into a single
    /// `view_rec` rooted at the reconstructed root page table, then applies
    /// `view_rec_disjoint_vaddrs` on that single subtree.
    /// Follows from tree structure alone.
    pub proof fn as_page_table_owner_view_non_overlapping(self)
        requires
            self.inv(),
        ensures
            self@.non_overlapping(),
    {
        self.as_page_table_owner_preserves_view_mappings();
        let pto = self.as_page_table_owner();
        let root_path = self.continuations[3].path();

        assert(root_path.len() == self.continuations[3].tree_level);
        assert(self.continuations[3].tree_level == 0) by {
            self.inv_continuation(NR_LEVELS as int - 1);
            // continuations[3].tree_level == INC_LEVELS - continuations[3].level() - 1
            // and continuations[3].level() == 4 (root).
        };
        assert(root_path.len() == 0);
        assert(pto.0.level == 0);

        assert forall |m: Mapping, n: Mapping|
            #[trigger] self@.mappings.contains(m) && #[trigger] self@.mappings.contains(n) && m != n implies
            m.va_range.end <= n.va_range.start || n.va_range.end <= m.va_range.start
        by {
            assert(self@.mappings == self.view_mappings());
            assert(pto.view_rec(root_path).contains(m));
            assert(pto.view_rec(root_path).contains(n));
            pto.view_rec_disjoint_vaddrs(root_path, m, n);
        };
    }
}

} // verus!
