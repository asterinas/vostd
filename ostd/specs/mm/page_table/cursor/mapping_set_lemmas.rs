use vstd::prelude::*;

use vstd_extra::arithmetic::{
    lemma_nat_align_down_monotone, lemma_nat_align_down_within_block, nat_align_down,
};
use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;

use crate::mm::page_table::*;
use crate::mm::{PagingLevel, Vaddr, page_size};
use crate::specs::arch::{NR_ENTRIES, NR_LEVELS};
use crate::specs::mm::page_table::cursor::owners::*;
use crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_divides;
use crate::specs::mm::page_table::owners::{
    INC_LEVELS, OwnerSubtree, PageTableOwner, lemma_vaddr_of_eq_int, sibling_paths_disjoint, vaddr,
    vaddr_of,
};
use crate::specs::mm::page_table::{AbstractVaddr, Mapping};

verus! {

broadcast use group_ghost_tree_lemmas;
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
        broadcast use {CursorContinuation::group_lemmas, PageTableOwner::group_lemmas};

        self.inv_children_unroll_all();
        self.as_subtree_inv();
        self.as_page_table_owner_pt_inv();
        let pto = self.as_page_table_owner();
        assert(self.as_page_table_owner().view_rec(self.path()) == self.view_mappings()) by {
            assert forall|m: Mapping|
                #![auto]
                self.view_mappings().contains(m) implies pto.view_rec(self.path()).contains(m) by {
                let i = choose|i: int|
                    #![auto]
                    0 <= i < self.children.len() && self.children[i] is Some && PageTableOwner(
                        self.children[i].unwrap(),
                    ).view_rec(self.path().push_tail(i)).contains(m);
                assert(pto.view_rec(self.path()).contains(m));
            };
            assert forall|m: Mapping|
                pto.view_rec(self.path()).contains(
                    m,
                ) implies #[trigger] self.view_mappings().contains(m) by {
                let i = choose|i: int|
                    #![auto]
                    0 <= i < pto.0.children().len() && pto.0.children()[i] is Some
                        && PageTableOwner(pto.0.children()[i].unwrap()).view_rec(
                        self.path().push_tail(i),
                    ).contains(m);
            };
        };
    }

    pub proof fn view_mappings_take_child(self)
        requires
            self.inv(),
            self.all_some(),
        ensures
            self.take_child().1.view_mappings() == self.view_mappings()
                - self.view_mappings_take_child_spec(),
    {
        broadcast use CursorContinuation::group_lemmas;

        self.inv_children_unroll_all();
        let def = self.take_child().1.view_mappings();
        let diff = self.view_mappings() - self.view_mappings_take_child_spec();
        assert forall|m: Mapping| diff.contains(m) implies def.contains(m) by {
            let i = choose|i: int|
                0 <= i < self.children.len() && #[trigger] self.children[i] is Some
                    && PageTableOwner(self.children[i].unwrap()).view_rec(
                    self.path().push_tail(i),
                ).contains(m);
            assert(i != self.idx);
            assert(self.take_child().1.children[i] is Some);
        };
        assert forall|m: Mapping| #![trigger def.contains(m)] def.contains(m) implies diff.contains(
            m,
        ) by {
            let left = self.take_child().1;
            assert(left.view_mappings().contains(m));
            // Establish self.view_mappings().contains(m) from left's child
            let wi = choose|i: int|
                #![auto]
                0 <= i < left.children.len() && left.children[i] is Some && PageTableOwner(
                    left.children[i].unwrap(),
                ).view_rec(left.path().push_tail(i)).contains(m);
            if self.view_mappings_take_child_spec().contains(m) {
                assert(PageTableOwner(self.children[self.idx as int].unwrap()).view_rec(
                    self.path().push_tail(self.idx as int),
                ).contains(m));
                let i = choose|i: int|
                    0 <= i < left.children.len() && #[trigger] left.children[i] is Some
                        && PageTableOwner(left.children[i].unwrap()).view_rec(
                        left.path().push_tail(i),
                    ).contains(m);
                assert(PageTableOwner(left.children[i as int].unwrap()).view_rec(
                    left.path().push_tail(i),
                ).contains(m));

                PageTableOwner(self.children[self.idx as int].unwrap()).view_rec_vaddr_range(
                    self.path().push_tail(self.idx as int),
                    m,
                );
                PageTableOwner(left.children[i as int].unwrap()).view_rec_vaddr_range(
                    left.path().push_tail(i),
                    m,
                );

                let size = page_size((INC_LEVELS - self.path().len() - 1) as PagingLevel);
                // Positional disjointness; shift both sides by LEADING_BITS * 2^48.
                sibling_paths_disjoint::<C>(self.path(), self.idx as int, i, size);
                lemma_vaddr_of_eq_int::<C>(self.path().push_tail(self.idx as int));
                lemma_vaddr_of_eq_int::<C>(self.path().push_tail(i));
            }
        };
    }

    pub proof fn view_mappings_put_child(self, child: OwnerSubtree<C>)
        requires
            self.inv(),
            child.inv(),
            self.all_but_index_some(),
        ensures
            self.put_child(child).view_mappings() == self.view_mappings() + PageTableOwner(
                child,
            ).view_rec(self.path().push_tail(self.idx as int)),
    {
        broadcast use CursorContinuation::group_lemmas;

        let def = self.put_child(child).view_mappings();
        let sum = self.view_mappings() + PageTableOwner(child).view_rec(
            self.path().push_tail(self.idx as int),
        );
        assert forall|m: Mapping| sum.contains(m) implies def.contains(m) by {
            if self.view_mappings().contains(m) {
                let i = choose|i: int|
                    0 <= i < self.children.len() && #[trigger] self.children[i] is Some
                        && PageTableOwner(self.children[i].unwrap()).view_rec(
                        self.path().push_tail(i),
                    ).contains(m);
                assert(self.put_child(child).children[i] == self.children[i]);
                self.put_child(child).lemma_view_mappings_intro(m, i);
            } else {
                assert(PageTableOwner(child).view_rec(
                    self.path().push_tail(self.idx as int),
                ).contains(m));
                assert(self.put_child(child).children[self.idx as int] == Some(child));
                self.put_child(child).lemma_view_mappings_intro(m, self.idx as int);
            }
        };
        assert forall|m: Mapping| def.contains(m) implies sum.contains(m) by {
            let i = choose|i: int|
                0 <= i < self.put_child(child).children.len() && #[trigger] self.put_child(
                    child,
                ).children[i] is Some && PageTableOwner(
                    self.put_child(child).children[i].unwrap(),
                ).view_rec(self.put_child(child).path().push_tail(i)).contains(m);
            if i == self.idx {
            } else {
                assert(self.children[i] == self.put_child(child).children[i]);
            }
        };
    }
}

impl<'rcu, C: PageTableConfig> CursorContinuation<'rcu, C> {
    /// When a continuation has all_some and inv, its as_subtree() also has `TreeNode::inv()`.
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
        let depth = (INC_LEVELS - st.level()) as nat;
        assert forall|i: int|
            #![trigger st.children()[i]]
            0 <= i < NR_ENTRIES implies PageTableOwner::<C>::pt_edge_at(st, i) && PageTableOwner(
            st.children()[i].unwrap(),
        ).pt_inv_at_depth((depth - 1) as nat) by {
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
        ensures
            ({
                let subtree_va = vaddr_of::<C>(self.cur_subtree().value().path) as int;
                let size = page_size(self.level) as int;
                PageTableOwner(self.cur_subtree())@.mappings == self@.mappings.filter(
                    |m: Mapping| subtree_va <= m.va_range.start < subtree_va + size,
                )
            }),
    {
        broadcast use {CursorContinuation::group_lemmas, CursorOwner::group_lemmas};

        let cur_subtree = self.cur_subtree();
        let cur_path = cur_subtree.value().path;
        let subtree_va = vaddr_of::<C>(cur_path) as int;
        let size = page_size(self.level) as int;

        let subtree_mappings = PageTableOwner(cur_subtree)@.mappings;
        let filtered = self@.mappings.filter(
            |m: Mapping| subtree_va <= m.va_range.start < subtree_va + size,
        );

        self.cur_subtree_inv();

        let cont = self.continuations[self.level - 1];
        self.inv_continuation(self.level - 1);
        cont.inv_children_rel_unroll(self.index() as int);
        // cur_subtree.value.path == cont.path().push_tail(self.index())

        // Forward: subtree mappings are in the filtered set
        assert forall|m: Mapping| subtree_mappings.contains(m) implies filtered.contains(m) by {
            // m is in the current subtree's view_rec => in cont[level-1].view_mappings() => in self.view_mappings()
            assert(cont.children[self.index() as int] is Some);
            assert(cont.children[self.index() as int].unwrap() == cur_subtree);

            // view_rec_vaddr_range gives m.va_range.start in
            // [vaddr_of(cur_path), vaddr_of(cur_path) + page_size(level)),
            // which is exactly our filter range.
            PageTableOwner(cur_subtree).view_rec_vaddr_range(cur_path, m);
        };

        // Reverse: filtered mappings are in the subtree
        assert forall|m: Mapping| filtered.contains(m) implies subtree_mappings.contains(m) by {
            // m is in self.view_mappings() and subtree_va <= m.va_range.start < subtree_va + size
            let i = choose|i: int|
                self.level - 1 <= i < NR_LEVELS
                    && #[trigger] self.continuations[i].view_mappings().contains(m);
            self.inv_continuation(i);

            let cont_i = self.continuations[i];
            let j = choose|j: int|
                #![auto]
                0 <= j < NR_ENTRIES && cont_i.children[j] is Some && PageTableOwner(
                    cont_i.children[j].unwrap(),
                ).view_rec(cont_i.path().push_tail(j)).contains(m);

            cont_i.inv_children_unroll(j);
            PageTableOwner(cont_i.children[j].unwrap()).view_rec_vaddr_range(
                cont_i.path().push_tail(j),
                m,
            );

            if i == self.level - 1 {
                if j as usize == self.index() {
                    // cont_i.children[j] is exactly cur_subtree; m is already
                    // in subtree_mappings via view_rec at the same path.
                    assert(cont_i.children[j] == Some(cur_subtree));
                    assert(cont_i.path().push_tail(j) == cur_path);
                    assert(subtree_mappings == PageTableOwner(cur_subtree).view_rec(cur_path));
                    assert(PageTableOwner(cur_subtree).view_rec(cur_path).contains(m));
                    assert(subtree_mappings.contains(m));
                } else {
                    // Disjointness: sibling j's VA range doesn't overlap [subtree_va, subtree_va + page_size(level))
                    let sib_size = page_size((INC_LEVELS - cont.path().len() - 1) as PagingLevel);
                    sibling_paths_disjoint::<C>(cont.path(), self.index() as int, j, sib_size);
                    // Lift positional disjointness to canonical by adding
                    // the same leading_bits * 2^48 to both sides.
                    lemma_vaddr_of_eq_int::<C>(cont.path().push_tail(self.index() as int));
                    lemma_vaddr_of_eq_int::<C>(cont.path().push_tail(j));
                    assert(false);  // contradiction from disjointness + filter
                }
            } else {
                if j as usize != cont_i.idx as int {
                    // Subtree VA range is contained in ancestor child range
                    self.subtree_va_in_ancestor_range(i);

                    // Sibling j is disjoint from cont_i.idx child
                    let sib_size = page_size((INC_LEVELS - cont_i.path().len() - 1) as PagingLevel);
                    sibling_paths_disjoint::<C>(cont_i.path(), cont_i.idx as int, j, sib_size);
                    lemma_vaddr_of_eq_int::<C>(cont_i.path().push_tail(cont_i.idx as int));
                    lemma_vaddr_of_eq_int::<C>(cont_i.path().push_tail(j));
                    lemma_vaddr_of_eq_int::<C>(cur_path);
                    assert(false);  // contradiction
                } else {
                    assert(cont_i.children[cont_i.idx as int] is None);
                    assert(false);  // cont_i.children[j] is Some contradicts
                }
            }
        };

        assert(subtree_mappings == filtered);
    }

    /// Version using nat_align_down(cur_va, page_size(level)) in the filter.
    /// Bridge: nat_align_down(cur_va, ps) == vaddr(cur_path) + leading_bits * 2^48.
    pub proof fn cur_subtree_eq_filtered_mappings(self)
        requires
            self.inv(),
            self.in_locked_range(),
        ensures
            ({
                let start = nat_align_down(
                    self@.cur_va as nat,
                    page_size(self.level) as nat,
                ) as Vaddr;
                let size = page_size(self.level);
                PageTableOwner(self.cur_subtree())@.mappings == self@.mappings.filter(
                    |m: Mapping| start <= m.va_range.start < start + size,
                )
            }),
    {
        // Bridge: `nat_align_down(cur_va, ps) as Vaddr == vaddr_of::<C>(cur_path)`.
        //   _path version filters on `vaddr_of(cur_path)` (canonical).
        //   to_path_vaddr_concrete + cursor inv + lemma_vaddr_of_eq_int
        //   identify the two boundaries.
        self.cur_subtree_eq_filtered_mappings_path();
        self.cur_va_in_cont_child_range(self.level - 1);
        self.va.to_path_vaddr_concrete(self.level - 1);
        let cur_path = self.cur_subtree().value().path;
        let ps = page_size(self.level);
        lemma_vaddr_of_eq_int::<C>(cur_path);
        // Bridge nat_align_down's nat→usize cast (no wrap since
        // nat_align_down(x, _) <= x <= usize::MAX).
        vstd_extra::arithmetic::lemma_nat_align_down_sound(self@.cur_va as nat, ps as nat);
        let nad = nat_align_down(self@.cur_va as nat, ps as nat);
        assert(nad as Vaddr == nad);
        assert(nad as Vaddr == vaddr_of::<C>(cur_path));
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
            vaddr(self.continuations[lvl].path().push_tail(self.continuations[lvl].idx as int))
                + self.va.leading_bits * 0x1_0000_0000_0000int <= self.cur_va(),
            self.cur_va() < vaddr(
                self.continuations[lvl].path().push_tail(self.continuations[lvl].idx as int),
            ) + self.va.leading_bits * 0x1_0000_0000_0000int + page_size((lvl + 1) as PagingLevel),
            vaddr(self.continuations[lvl].path().push_tail(self.continuations[lvl].idx as int))
                == vaddr(self.va.to_path(lvl)),
    {
        let cont = self.continuations[lvl];
        let child_path = cont.path().push_tail(cont.idx as int);
        let va_path = self.va.to_path(lvl);

        self.va.to_path_len(lvl);
        assert forall|k: int| 0 <= k < child_path.len() implies child_path[k] == va_path[k] by {
            self.va.to_path_index(lvl, k);
        };

        self.va.to_path_inv(lvl);
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
        ensures
            ({
                let subtree_va = vaddr(self.cur_subtree().value().path);
                let idx_path_va = vaddr(
                    self.continuations[lvl].path().push_tail(self.continuations[lvl].idx as int),
                );
                &&& idx_path_va <= subtree_va
                &&& subtree_va + page_size(self.level) <= idx_path_va + page_size(
                    (lvl + 1) as PagingLevel,
                )
            }),
    {
        let cont = self.continuations[self.level - 1];
        self.inv_continuation(self.level - 1);
        cont.inv_children_rel_unroll(self.index() as int);
        // cur_subtree.value.path == cont.path().push_tail(self.index())

        self.cur_va_in_cont_child_range(self.level - 1);
        self.cur_va_in_cont_child_range(lvl);
        self.va.to_path_vaddr_concrete(self.level - 1);
        self.va.to_path_vaddr_concrete(lvl);

        let x = self.cur_va() as nat;
        let fine = page_size(self.level as PagingLevel) as nat;
        let coarse = page_size((lvl + 1) as PagingLevel) as nat;
        let shift = self.va.leading_bits * 0x1_0000_0000_0000int;

        // Explicit chain: subtree_va + shift == nat_align_down(x, fine)
        let subtree_va = vaddr(self.cur_subtree().value().path);
        assert(subtree_va == vaddr(self.va.to_path(self.level - 1)));
        assert(subtree_va + shift == nat_align_down(x, fine));

        // Explicit chain: idx_path_va + shift == nat_align_down(x, coarse)
        let idx_path_va = vaddr(
            self.continuations[lvl].path().push_tail(self.continuations[lvl].idx as int),
        );
        assert(idx_path_va == vaddr(self.va.to_path(lvl)));
        assert(idx_path_va + shift == nat_align_down(x, coarse));

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
            vaddr(self.continuations[self.level - 1].path().push_tail(j)) + self.va.leading_bits
                * 0x1_0000_0000_0000int + page_size(self.level as PagingLevel) <= self.cur_va()
                || self.cur_va() < vaddr(self.continuations[self.level - 1].path().push_tail(j))
                + self.va.leading_bits * 0x1_0000_0000_0000int,
    {
        let cont = self.continuations[self.level - 1];
        let idx = self.index();

        // Establish cont.level() == self.level via case split
        // cur_va is within the child at cont[level-1].idx
        self.cur_va_in_cont_child_range(self.level - 1);

        // Sibling paths are separated by `page_size(self.level)` (child page size).
        let size = page_size((INC_LEVELS - cont.path().len() - 1) as PagingLevel);
        sibling_paths_disjoint::<C>(cont.path(), idx as int, j, size);
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
            vaddr(self.continuations[i].path().push_tail(j)) + self.va.leading_bits
                * 0x1_0000_0000_0000int + page_size((i + 1) as PagingLevel) <= self.cur_va()
                || self.cur_va() < vaddr(self.continuations[i].path().push_tail(j))
                + self.va.leading_bits * 0x1_0000_0000_0000int,
    {
        let cont = self.continuations[i];

        // Establish cont.level() == i + 1 via case split
        // cur_va is within the child at cont[i].idx
        self.cur_va_in_cont_child_range(i);

        // Siblings at this depth are separated by `page_size(i+1)` (child page size).
        let size = page_size((INC_LEVELS - cont.path().len() - 1) as PagingLevel);
        sibling_paths_disjoint::<C>(cont.path(), cont.idx as int, j, size);
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
            PageTableOwner(self.cur_subtree()).view_rec(self.cur_subtree().value().path).contains(
                m,
            ),
    {
        broadcast use {CursorContinuation::group_lemmas, CursorOwner::group_lemmas};

        let cur_va = self.cur_va();

        // m comes from some continuation level i
        let i = choose|i: int|
            self.level - 1 <= i < NR_LEVELS
                && #[trigger] self.continuations[i].view_mappings().contains(m);
        self.inv_continuation(i);

        let cont_i = self.continuations[i];
        let j = choose|j: int|
            #![auto]
            0 <= j < NR_ENTRIES && cont_i.children[j] is Some && PageTableOwner(
                cont_i.children[j].unwrap(),
            ).view_rec(cont_i.path().push_tail(j)).contains(m);

        cont_i.inv_children_unroll(j);
        let child_j = cont_i.children[j].unwrap();
        let path_j = cont_i.path().push_tail(j);
        PageTableOwner(child_j).view_rec_vaddr_range(path_j, m);
        // Bridge view_rec_vaddr_range's canonical bounds to the
        // disjointness lemmas (also canonical after the refactor).
        lemma_vaddr_of_eq_int::<C>(path_j);

        if i == self.level - 1 {
            if j as usize != self.index() {
                self.subtree_va_ranges_disjoint(j);
            }
        } else {
            if j as usize != cont_i.idx as int {
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
        old_self: Self,
        new_self: Self,
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
            forall|i: int|
                old_self.level <= i < NR_LEVELS ==> old_self.continuations[i]
                    == new_self.continuations[i],
        ensures
            new_self.view_mappings() == (old_self.view_mappings() - old_cont.view_mappings()).union(
                new_cont.view_mappings(),
            ),
    {
        broadcast use {CursorContinuation::group_lemmas, CursorOwner::group_lemmas};

        let level = old_self.level;

        assert forall|m: Mapping| new_self.view_mappings().contains(m) implies ((
        old_self.view_mappings().contains(m) && !old_cont.view_mappings().contains(m))
            || new_cont.view_mappings().contains(m)) by {
            let i = choose|i: int|
                level - 1 <= i < NR_LEVELS
                    && #[trigger] new_self.continuations[i].view_mappings().contains(m);
            if i == level - 1 {
                assert(new_cont.view_mappings().contains(m));
            } else {
                assert(old_self.continuations[i] == new_self.continuations[i]);
                assert(old_self.continuations[i].view_mappings().contains(m));

                if old_cont.view_mappings().contains(m) {
                    old_self.inv_continuation(i);
                    old_self.inv_continuation(level - 1);
                    let cont_i = old_self.continuations[i];
                    let j = choose|j: int|
                        #![auto]
                        0 <= j < NR_ENTRIES && cont_i.children[j] is Some && PageTableOwner(
                            cont_i.children[j].unwrap(),
                        ).view_rec(cont_i.path().push_tail(j)).contains(m);
                    cont_i.inv_children_unroll(j);
                    PageTableOwner(cont_i.children[j].unwrap()).view_rec_vaddr_range(
                        cont_i.path().push_tail(j),
                        m,
                    );

                    let k = choose|k: int|
                        #![auto]
                        0 <= k < NR_ENTRIES && old_cont.children[k] is Some && PageTableOwner(
                            old_cont.children[k].unwrap(),
                        ).view_rec(old_cont.path().push_tail(k)).contains(m);
                    old_cont.inv_children_unroll(k);
                    PageTableOwner(old_cont.children[k].unwrap()).view_rec_vaddr_range(
                        old_cont.path().push_tail(k),
                        m,
                    );

                    if j as usize != cont_i.idx as int {
                        old_self.cur_va_in_cont_child_range(level as int);
                        old_self.va.to_path_vaddr_concrete(level as int);
                        old_self.cur_va_in_cont_child_range(i);
                        old_self.va.to_path_vaddr_concrete(i);

                        let x = old_self.cur_va() as nat;
                        let ps_node = page_size((level + 1) as PagingLevel) as nat;
                        let ps_anc = page_size((i + 1) as PagingLevel) as nat;

                        crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_ge_page_size(
                        (level + 1) as PagingLevel);
                        crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_ge_page_size(
                        (i + 1) as PagingLevel);
                        lemma_page_size_divides((level + 1) as PagingLevel, (i + 1) as PagingLevel);

                        lemma_nat_align_down_monotone(x, ps_node, ps_anc);
                        lemma_nat_align_down_within_block(x, ps_node, ps_anc);
                        vstd_extra::arithmetic::lemma_nat_align_down_sound(x, ps_node);
                        vstd_extra::arithmetic::lemma_nat_align_down_sound(x, ps_anc);

                        let sib_size = page_size(
                            (INC_LEVELS - cont_i.path().len() - 1) as PagingLevel,
                        );
                        sibling_paths_disjoint::<C>(cont_i.path(), cont_i.idx as int, j, sib_size);
                        // Lift positional disjointness to canonical.
                        lemma_vaddr_of_eq_int::<C>(cont_i.path().push_tail(cont_i.idx as int));
                        lemma_vaddr_of_eq_int::<C>(cont_i.path().push_tail(j));

                        old_cont.as_subtree_inv();
                        old_cont.as_page_table_owner_preserves_view_mappings();
                        PageTableOwner(old_cont.as_subtree()).view_rec_vaddr_range(
                            old_cont.path(),
                            m,
                        );
                    } else {
                        assert(cont_i.children[cont_i.idx as int] is None);
                    }
                }
            }
        };

        assert forall|m: Mapping|
            ((old_self.view_mappings().contains(m) && !old_cont.view_mappings().contains(m))
                || new_cont.view_mappings().contains(m)) implies new_self.view_mappings().contains(
            m,
        ) by {
            if new_cont.view_mappings().contains(m) {
                assert(new_self.continuations[level - 1].view_mappings().contains(m));
            } else {
                let i = choose|i: int|
                    level - 1 <= i < NR_LEVELS
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

        assert(new_self.view_mappings() == (old_self.view_mappings()
            - old_cont.view_mappings()).union(new_cont.view_mappings()));
    }

    #[verifier::rlimit(120)]
    pub proof fn as_page_table_owner_preserves_view_mappings(self)
        requires
            self.inv(),
        ensures
            self.as_page_table_owner().view_rec(self.continuations[3].path())
                == self.view_mappings(),
            self.as_page_table_owner().0.inv(),
            self.as_page_table_owner().0.level() == self.continuations[3].tree_level,
            self.as_page_table_owner().pt_inv(),
    {
        broadcast use CursorOwner::group_lemmas;

        if self.level == 4 {
            self.continuations[3].as_page_table_owner_preserves_view_mappings();
            self.inv_continuation(3);
            assert(self.view_mappings() == self.continuations[3].view_mappings());
            assert(self.as_page_table_owner().view_rec(self.continuations[3].path())
                == self.view_mappings());
        } else if self.level == 3 {
            let c2 = self.continuations[2];
            let c3 = self.continuations[3];

            c2.as_page_table_owner_preserves_view_mappings();
            c2.as_subtree_inv();
            c3.view_mappings_put_child(c2.as_subtree());
            c3.as_subtree_restore(c2);

            let l4 = c3.restore(c2).0;
            c2.as_page_table_owner_pt_inv();

            c2.inv_children_unroll_all();
            c3.inv_children_unroll_all();
            l4.as_page_table_owner_preserves_view_mappings();

            assert(self.view_mappings() == self.continuations[2].view_mappings().union(
                self.continuations[3].view_mappings(),
            )) by {
                assert forall|m: Mapping| #[trigger]
                    self.view_mappings().contains(
                        m,
                    ) implies self.continuations[2].view_mappings().contains(m)
                    || self.continuations[3].view_mappings().contains(m) by {
                    let i = choose|i: int|
                        2 <= i < NR_LEVELS
                            && #[trigger] self.continuations[i].view_mappings().contains(m);
                };
            };
            assert(self.as_page_table_owner().view_rec(self.continuations[3].path())
                == self.view_mappings());
        } else if self.level == 2 {
            let c1 = self.continuations[1];
            let c2 = self.continuations[2];
            let c3 = self.continuations[3];

            c1.as_page_table_owner_preserves_view_mappings();
            c1.as_subtree_inv();
            c2.view_mappings_put_child(c1.as_subtree());
            c2.as_subtree_restore(c1);

            let l3 = c2.restore(c1).0;
            c1.as_page_table_owner_pt_inv();

            c1.inv_children_unroll_all();
            c2.inv_children_unroll_all();
            l3.as_page_table_owner_preserves_view_mappings();
            l3.as_subtree_inv();
            c3.as_subtree_restore(l3);
            c3.view_mappings_put_child(l3.as_subtree());

            let l4 = c3.restore(l3).0;
            l3.as_page_table_owner_pt_inv();

            c3.inv_children_unroll_all();
            l4.as_page_table_owner_preserves_view_mappings();

            assert(self.view_mappings() == c1.view_mappings().union(c2.view_mappings()).union(
                c3.view_mappings(),
            )) by {
                assert forall|m: Mapping| self.view_mappings().contains(m) implies (
                c1.view_mappings().contains(m) || c2.view_mappings().contains(m)
                    || c3.view_mappings().contains(m)) by {
                    let i = choose|i: int|
                        1 <= i < NR_LEVELS
                            && #[trigger] self.continuations[i].view_mappings().contains(m);
                };
            };
            assert(self.as_page_table_owner().view_rec(self.continuations[3].path())
                == self.view_mappings());
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
            let l2 = c1.restore(c0).0;
            c0.as_page_table_owner_pt_inv();

            c0.inv_children_unroll_all();
            c1.inv_children_unroll_all();
            l2.as_page_table_owner_preserves_view_mappings();
            l2.as_subtree_inv();
            c2.view_mappings_put_child(l2.as_subtree());
            c2.as_subtree_restore(l2);
            let l3 = c2.restore(l2).0;
            l2.as_page_table_owner_pt_inv();

            c2.inv_children_unroll_all();
            l3.as_page_table_owner_preserves_view_mappings();
            l3.as_subtree_inv();
            c3.view_mappings_put_child(l3.as_subtree());
            c3.as_subtree_restore(l3);
            let l4 = c3.restore(l3).0;
            l3.as_page_table_owner_pt_inv();

            c3.inv_children_unroll_all();
            l4.as_page_table_owner_preserves_view_mappings();

            assert(self.view_mappings() == c0.view_mappings().union(c1.view_mappings()).union(
                c2.view_mappings(),
            ).union(c3.view_mappings())) by {
                assert forall|m: Mapping| self.view_mappings().contains(m) implies (
                c0.view_mappings().contains(m) || c1.view_mappings().contains(m)
                    || c2.view_mappings().contains(m) || c3.view_mappings().contains(m)) by {
                    let i = choose|i: int|
                        0 <= i < NR_LEVELS
                            && #[trigger] self.continuations[i].view_mappings().contains(m);
                };
            };
            assert(self.as_page_table_owner().view_rec(self.continuations[3].path())
                == self.view_mappings());
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
            forall|m: Mapping| self.view_mappings().contains(m) ==> #[trigger] m.inv(),
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
            forall|m: Mapping| #[trigger]
                self.view_mappings().contains(m)
                    ==> set![4096usize, 2097152usize, 1073741824usize].contains(m.page_size),
    {
        self.as_page_table_owner_preserves_view_mappings();
        let pto = self.as_page_table_owner();
        let root_path = self.continuations[3].path();
        self.inv_continuation(NR_LEVELS - 1);
        // pto.0.level == continuations[3].tree_level == 0
        // pto.0.value.parent_level == continuations[3].entry_own.parent_level == 5
        // == INC_LEVELS == INC_LEVELS - 0 == INC_LEVELS - pto.0.level
        pto.view_rec_mapping_page_size(root_path);
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
            self.inv_continuation(NR_LEVELS - 1);
            // continuations[3].tree_level == INC_LEVELS - continuations[3].level() - 1
            // and continuations[3].level() == 4 (root).
        };

        assert forall|m: Mapping, n: Mapping| #[trigger]
            self@.mappings.contains(m) && #[trigger] self@.mappings.contains(n) && m
                != n implies m.va_range.end <= n.va_range.start || n.va_range.end
            <= m.va_range.start by {
            assert(self@.mappings == self.view_mappings());
            assert(pto.view_rec(root_path).contains(m));
            assert(pto.view_rec(root_path).contains(n));
            pto.view_rec_disjoint_vaddrs(root_path, m, n);
        };
    }
}

} // verus!
