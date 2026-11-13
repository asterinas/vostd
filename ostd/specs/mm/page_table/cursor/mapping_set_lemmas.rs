use vstd::prelude::*;
use vstd_extra::{
    arithmetic::{
        lemma_nat_align_down_monotone, lemma_nat_align_down_sound,
        lemma_nat_align_down_within_block, nat_align_down,
    },
    ghost_tree::*,
    ownership::*,
};

use crate::specs::{
    arch::NR_ENTRIES,
    mm::page_table::{
        cursor::{
            owners::*,
            page_size_lemmas::{lemma_page_size_divides, lemma_page_size_ge_base},
        },
        owners::*,
        *,
    },
};

use crate::mm::{PagingConstsTrait, PagingLevel, Vaddr, page_size, page_table::*};

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
        C::lemma_paging_consts_properties();
        C::lemma_page_table_config_constant_requirements();
        broadcast use {CursorContinuation::group_lemmas, PageTableOwner::group_lemmas};

        self.as_page_table_owner_pt_inv();
    }

    pub proof fn view_mappings_take_child(self)
        requires
            self.inv(),
            self.all_some(),
        ensures
            self.take_child().1.view_mappings() == self.view_mappings()
                - self.view_mappings_take_child_spec(),
    {
        C::lemma_paging_consts_properties();
        C::lemma_page_table_config_constant_requirements();
        broadcast use CursorContinuation::group_lemmas;

        let def = self.take_child().1.view_mappings();
        let diff = self.view_mappings() - self.view_mappings_take_child_spec();
        assert forall|m: Mapping| diff.contains(m) implies def.contains(m) by {
            let i = choose|i: int|
                0 <= i < self.children.len() && #[trigger] self.children[i] is Some
                    && PageTableOwner(self.children[i].unwrap()).view_rec(
                    self.path().push_tail(i),
                ).contains(m);
            assert(self.take_child().1.children[i] is Some);
        };
        assert forall|m: Mapping| #![trigger def.contains(m)] def.contains(m) implies diff.contains(
            m,
        ) by {
            let left = self.take_child().1;
            if self.view_mappings_take_child_spec().contains(m) {
                let i = choose|i: int|
                    0 <= i < left.children.len() && #[trigger] left.children[i] is Some
                        && PageTableOwner(left.children[i].unwrap()).view_rec(
                        left.path().push_tail(i),
                    ).contains(m);

                PageTableOwner(self.children[self.idx as int].unwrap()).lemma_view_rec_vaddr_range(
                    self.path().push_tail(self.idx as int),
                    m,
                );
                PageTableOwner(left.children[i as int].unwrap()).lemma_view_rec_vaddr_range(
                    left.path().push_tail(i),
                    m,
                );

                let size = page_size::<C>(
                    (C::NR_LEVELS() + 1 - self.path().len() - 1) as PagingLevel,
                );
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
            } else {
                self.put_child(child).lemma_view_mappings_intro(m, self.idx as int);
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
        C::lemma_paging_consts_properties();
        C::lemma_page_table_config_constant_requirements();
    }

    pub(super) proof fn as_page_table_owner_pt_inv(self)
        requires
            self.inv(),
            self.all_some(),
        ensures
            PageTableOwner(self.as_subtree()).pt_inv(),
    {
        C::lemma_paging_consts_properties();
        C::lemma_page_table_config_constant_requirements();
        reveal(PageTableOwner::pt_inv_at_depth);
    }
}

// ─── CursorOwner mapping lemmas ──────────────────────────────────────────────
impl<'rcu, C: PageTableConfig> CursorOwner<'rcu, C> {
    /// The current subtree's mappings equal the filter over [subtree_va, subtree_va + page_size(level))
    /// where subtree_va = vaddr::<C>(cur_subtree path).
    pub proof fn lemma_cur_subtree_eq_filtered_mappings_path(self)
        requires
            self.inv(),
            self.in_barrier_va(),
        ensures
            ({
                let subtree_va = vaddr_of::<C>(self.cur_subtree().value().path) as int;
                let size = page_size::<C>(self.level) as int;
                PageTableOwner(self.cur_subtree())@.mappings == self@.mappings.filter(
                    |m: Mapping| subtree_va <= m.va_range.start < subtree_va + size,
                )
            }),
    {
        C::lemma_paging_consts_properties();
        C::lemma_page_table_config_constant_requirements();
        broadcast use {CursorContinuation::group_lemmas, CursorOwner::group_lemmas};

        let cur_subtree = self.cur_subtree();
        let cur_path = cur_subtree.value().path;
        let subtree_va = vaddr_of::<C>(cur_path) as int;
        let size = page_size::<C>(self.level) as int;

        let subtree_mappings = PageTableOwner(cur_subtree)@.mappings;
        let filtered = self@.mappings.filter(
            |m: Mapping| subtree_va <= m.va_range.start < subtree_va + size,
        );

        let cont = self.continuations[self.level - 1];
        // cur_subtree.value.path == cont.path().push_tail(self.index())

        // Forward: subtree mappings are in the filtered set
        assert forall|m: Mapping| subtree_mappings.contains(m) implies filtered.contains(m) by {
            // m is in the current subtree's view_rec => in cont[level-1].view_mappings() => in self.view_mappings()
            // lemma_view_rec_vaddr_range gives m.va_range.start in
            // [vaddr_of(cur_path), vaddr_of(cur_path) + page_size(level)),
            // which is exactly our filter range.
            PageTableOwner(cur_subtree).lemma_view_rec_vaddr_range(cur_path, m);
        };

        // Reverse: filtered mappings are in the subtree
        assert forall|m: Mapping| filtered.contains(m) implies subtree_mappings.contains(m) by {
            // m is in self.view_mappings() and subtree_va <= m.va_range.start < subtree_va + size
            let i = choose|i: int|
                self.level - 1 <= i < C::NR_LEVELS()
                    && #[trigger] self.continuations[i].view_mappings().contains(m);

            let cont_i = self.continuations[i];
            let j = choose|j: int|
                #![auto]
                0 <= j < NR_ENTRIES && cont_i.children[j] is Some && PageTableOwner(
                    cont_i.children[j].unwrap(),
                ).view_rec(cont_i.path().push_tail(j)).contains(m);

            PageTableOwner(cont_i.children[j].unwrap()).lemma_view_rec_vaddr_range(
                cont_i.path().push_tail(j),
                m,
            );

            if i == self.level - 1 {
                // j == index: cont_i.children[j] is exactly cur_subtree; m is already
                // in subtree_mappings via view_rec at the same path.
                if j as usize != self.index() {
                    // Disjointness: sibling j's VA range doesn't overlap [subtree_va, subtree_va + page_size(level))
                    let sib_size = page_size::<C>(
                        (C::NR_LEVELS() + 1 - cont.path().len() - 1) as PagingLevel,
                    );
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
                    let sib_size = page_size::<C>(
                        (C::NR_LEVELS() + 1 - cont_i.path().len() - 1) as PagingLevel,
                    );
                    sibling_paths_disjoint::<C>(cont_i.path(), cont_i.idx as int, j, sib_size);
                    lemma_vaddr_of_eq_int::<C>(cont_i.path().push_tail(j));
                    lemma_vaddr_of_eq_int::<C>(cur_path);
                    assert(false);  // contradiction
                } else {
                    assert(false);  // cont_i.children[j] is Some contradicts
                }
            }
        };

    }

    /// Version using nat_align_down(cur_va, page_size(level)) in the filter.
    /// Uses the shared canonical subtree boundary rather than reconstructing the VA path.
    pub proof fn lemma_cur_subtree_eq_filtered_mappings(self)
        requires
            self.inv(),
            self.in_barrier_va(),
        ensures
            ({
                let start = nat_align_down(
                    self@.cur_va as nat,
                    page_size::<C>(self.level) as nat,
                ) as Vaddr;
                let size = page_size::<C>(self.level);
                PageTableOwner(self.cur_subtree())@.mappings == self@.mappings.filter(
                    |m: Mapping| start <= m.va_range.start < start + size,
                )
            }),
    {
        C::lemma_paging_consts_properties();
        C::lemma_page_table_config_constant_requirements();
        self.lemma_cur_subtree_eq_filtered_mappings_path();
        self.cur_va_in_subtree_range();
    }

    /// The cursor's VA falls within the canonical VA range of any ancestor
    /// continuation's child that the cursor descended through. Canonical
    /// form: positional `vaddr::<C>(path)` plus the architecture-parameterized upper-address base.
    pub(super) proof fn cur_va_in_cont_child_range(self, lvl: int)
        requires
            self.inv(),
            self.in_barrier_va(),
            self.level - 1 <= lvl < C::NR_LEVELS(),
        ensures
            vaddr::<C>(self.continuations[lvl].path().push_tail(self.continuations[lvl].idx as int))
                + vaddr_leading_part_spec::<C>(self.cur_va()) <= self.cur_va(),
            self.cur_va() < vaddr::<C>(
                self.continuations[lvl].path().push_tail(self.continuations[lvl].idx as int),
            ) + vaddr_leading_part_spec::<C>(self.cur_va()) + page_size::<C>(
                (lvl + 1) as PagingLevel,
            ),
            vaddr::<C>(self.continuations[lvl].path().push_tail(self.continuations[lvl].idx as int))
                + vaddr_leading_part_spec::<C>(self.cur_va()) == nat_align_down(
                self.cur_va() as nat,
                page_size::<C>((lvl + 1) as PagingLevel) as nat,
            ),
            vaddr_of::<C>(
                self.continuations[lvl].path().push_tail(self.continuations[lvl].idx as int),
            ) == nat_align_down(
                self.cur_va() as nat,
                page_size::<C>((lvl + 1) as PagingLevel) as nat,
            ),
    {
        C::lemma_paging_consts_properties();
        C::lemma_page_table_config_constant_requirements();
        lemma_vaddr_leading_part_is_align_down::<C>(self.cur_va());
        let cont = self.continuations[lvl];
        let child_path = cont.path().push_tail(cont.idx as int);
        assert(child_path.len() == C::NR_LEVELS() - lvl);
        assert forall|k: int| 0 <= k < child_path.len() implies #[trigger] child_path[k]
            == pte_index_spec::<C>(self.cur_va(), (C::NR_LEVELS() - k) as PagingLevel) by {
            lemma_pte_index_bound::<C>(self.cur_va(), (C::NR_LEVELS() - k) as PagingLevel);
        };
        lemma_vaddr_path_aligned::<C>(child_path, self.cur_va());
        lemma_vaddr_of_eq_int::<C>(child_path);
        lemma_page_size_ge_base::<C>((lvl + 1) as PagingLevel);
        lemma_nat_align_down_sound(
            self.cur_va() as nat,
            page_size::<C>((lvl + 1) as PagingLevel) as nat,
        );
    }

    /// The current subtree's VA range [subtree_va, subtree_va + page_size(level)) is contained
    /// within the VA range of any ancestor continuation's child that the cursor descended through.
    proof fn subtree_va_in_ancestor_range(self, lvl: int)
        requires
            self.inv(),
            self.in_barrier_va(),
            self.level - 1 < lvl < C::NR_LEVELS(),
        ensures
            ({
                let subtree_va = vaddr::<C>(self.cur_subtree().value().path);
                let idx_path_va = vaddr::<C>(
                    self.continuations[lvl].path().push_tail(self.continuations[lvl].idx as int),
                );
                &&& idx_path_va <= subtree_va
                &&& subtree_va + page_size::<C>(self.level) <= idx_path_va + page_size::<C>(
                    (lvl + 1) as PagingLevel,
                )
            }),
    {
        C::lemma_paging_consts_properties();
        C::lemma_page_table_config_constant_requirements();
        self.cur_va_in_cont_child_range(self.level - 1);
        self.cur_va_in_cont_child_range(lvl);

        let x = self.cur_va() as nat;
        let fine = page_size::<C>(self.level as PagingLevel) as nat;
        let coarse = page_size::<C>((lvl + 1) as PagingLevel) as nat;

        lemma_page_size_divides::<C>(self.level as PagingLevel, (lvl + 1) as PagingLevel);
        lemma_nat_align_down_monotone(x, fine, coarse);
        lemma_nat_align_down_within_block(x, fine, coarse);
    }

    /// Subtrees at different indices have disjoint VA ranges.
    pub proof fn subtree_va_ranges_disjoint(self, j: int)
        requires
            self.inv(),
            self.in_barrier_va(),
            0 <= j < NR_ENTRIES,
            j != self.index(),
            self.continuations[self.level - 1].children[j] is Some,
        ensures
            vaddr::<C>(self.continuations[self.level - 1].path().push_tail(j))
                + vaddr_leading_part_spec::<C>(self.cur_va()) + page_size::<C>(
                self.level as PagingLevel,
            ) <= self.cur_va() || self.cur_va() < vaddr::<C>(
                self.continuations[self.level - 1].path().push_tail(j),
            ) + vaddr_leading_part_spec::<C>(self.cur_va()),
    {
        C::lemma_paging_consts_properties();
        C::lemma_page_table_config_constant_requirements();
        let cont = self.continuations[self.level - 1];
        let idx = self.index();

        // Establish cont.level() == self.level via case split
        // cur_va is within the child at cont[level-1].idx
        self.cur_va_in_cont_child_range(self.level - 1);

        // Sibling paths are separated by `page_size(self.level)` (child page size).
        let size = page_size::<C>((C::NR_LEVELS() + 1 - cont.path().len() - 1) as PagingLevel);
        sibling_paths_disjoint::<C>(cont.path(), idx as int, j, size);
    }

    /// Children of higher-level continuations have VA ranges that don't include cur_va,
    /// because cur_va's indices at those levels match the path to the current position.
    pub proof fn higher_level_children_disjoint(self, i: int, j: int)
        requires
            self.inv(),
            self.in_barrier_va(),
            self.level - 1 < i < C::NR_LEVELS(),
            0 <= j < NR_ENTRIES,
            j != self.continuations[i].idx,
            self.continuations[i].children[j] is Some,
        ensures
            vaddr::<C>(self.continuations[i].path().push_tail(j)) + vaddr_leading_part_spec::<C>(
                self.cur_va(),
            ) + page_size::<C>((i + 1) as PagingLevel) <= self.cur_va() || self.cur_va() < vaddr::<
                C,
            >(self.continuations[i].path().push_tail(j)) + vaddr_leading_part_spec::<C>(
                self.cur_va(),
            ),
    {
        C::lemma_paging_consts_properties();
        C::lemma_page_table_config_constant_requirements();
        let cont = self.continuations[i];

        // Establish cont.level() == i + 1 via case split
        // cur_va is within the child at cont[i].idx
        self.cur_va_in_cont_child_range(i);

        // Siblings at this depth are separated by `page_size(i+1)` (child page size).
        let size = page_size::<C>((C::NR_LEVELS() + 1 - cont.path().len() - 1) as PagingLevel);
        sibling_paths_disjoint::<C>(cont.path(), cont.idx as int, j, size);
    }

    /// Any mapping that covers cur_va must come from the current subtree.
    /// This follows from the disjointness of VA ranges and the fact that
    /// cur_va falls within the current subtree's VA range.
    pub proof fn mapping_covering_cur_va_from_cur_subtree(self, m: Mapping)
        requires
            self.inv(),
            self.in_barrier_va(),
            self.view_mappings().contains(m),
            m.va_range.start <= self.cur_va() < m.va_range.end,
        ensures
            PageTableOwner(self.cur_subtree()).view_rec(self.cur_subtree().value().path).contains(
                m,
            ),
    {
        C::lemma_paging_consts_properties();
        C::lemma_page_table_config_constant_requirements();
        broadcast use {CursorContinuation::group_lemmas, CursorOwner::group_lemmas};

        lemma_vaddr_leading_part_is_align_down::<C>(self.cur_va());
        // m comes from some continuation level i

        let i = choose|i: int|
            self.level - 1 <= i < C::NR_LEVELS()
                && #[trigger] self.continuations[i].view_mappings().contains(m);

        let cont_i = self.continuations[i];
        let j = choose|j: int|
            #![auto]
            0 <= j < NR_ENTRIES && cont_i.children[j] is Some && PageTableOwner(
                cont_i.children[j].unwrap(),
            ).view_rec(cont_i.path().push_tail(j)).contains(m);

        let child_j = cont_i.children[j].unwrap();
        let path_j = cont_i.path().push_tail(j);
        PageTableOwner(child_j).lemma_view_rec_vaddr_range(path_j, m);
        // Bridge lemma_view_rec_vaddr_range's canonical bounds to the
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
                assert(false);
            }
        }
    }

    /// Combined replace: swap the lowest continuation, relating old and new mapping sets.
    /// Avoids the Map::remove phantom key issue by requiring both old and new to have inv().
    #[verifier::spinoff_prover]
    #[verifier::rlimit(60)]
    pub proof fn view_mappings_replace_lowest(
        old_self: Self,
        new_self: Self,
        old_cont: CursorContinuation<'rcu, C>,
        new_cont: CursorContinuation<'rcu, C>,
    )
        requires
            old_self.inv(),
            old_self.in_barrier_va(),
            new_self.inv(),
            old_self.level == new_self.level,
            old_self.continuations[old_self.level - 1] == old_cont,
            new_self.continuations[new_self.level - 1] == new_cont,
            forall|i: int|
                old_self.level <= i < C::NR_LEVELS() ==> old_self.continuations[i]
                    == new_self.continuations[i],
        ensures
            new_self.view_mappings() == (old_self.view_mappings() - old_cont.view_mappings()).union(
                new_cont.view_mappings(),
            ),
    {
        hide(CursorContinuation::inv_children_rel);
        hide(CursorContinuation::inv_children);
        hide(CursorContinuation::pt_inv_children);
        C::lemma_paging_consts_properties();
        C::lemma_page_table_config_constant_requirements();
        broadcast use {CursorContinuation::group_lemmas, CursorOwner::group_lemmas};

        let level = old_self.level;

        assert forall|m: Mapping| new_self.view_mappings().contains(m) implies ((
        old_self.view_mappings().contains(m) && !old_cont.view_mappings().contains(m))
            || new_cont.view_mappings().contains(m)) by {
            let i = choose|i: int|
                level - 1 <= i < C::NR_LEVELS()
                    && #[trigger] new_self.continuations[i].view_mappings().contains(m);
            // i == level - 1: new_self.continuations[level-1] == new_cont, so the
            // existential is witnessed by new_cont.view_mappings().contains(m).
            if i != level - 1 {
                assert(old_self.continuations[i] == new_self.continuations[i]);

                if old_cont.view_mappings().contains(m) {
                    old_self.lemma_higher_mapping_disjoint_from_lowest(i, m);
                }
            }
        };

    }

    /// Mappings carried by the active continuations up to `level`.
    closed spec fn view_mappings_through(self, level: PagingLevel) -> Set<Mapping>
        decreases level,
    {
        if level <= self.level {
            self.continuations[self.level - 1].view_mappings()
        } else {
            self.view_mappings_through((level - 1) as PagingLevel).union(
                self.continuations[level - 1].view_mappings(),
            )
        }
    }

    pub proof fn as_page_table_owner_preserves_view_mappings(self)
        requires
            self.inv(),
        ensures
            self.as_page_table_owner().view_rec(self.continuations[C::NR_LEVELS() - 1].path())
                == self.view_mappings(),
            self.as_page_table_owner().0.inv(),
            self.as_page_table_owner().0.level() == self.continuations[C::NR_LEVELS()
                - 1].tree_level,
            self.as_page_table_owner().pt_inv(),
    {
        C::lemma_paging_consts_properties();
        self.lemma_restore_to_level(C::NR_LEVELS());
        let root = self.restore_to_level(C::NR_LEVELS());
        root.as_subtree_inv();
        root.as_page_table_owner_pt_inv();
        root.as_page_table_owner_preserves_view_mappings();
        broadcast use CursorOwner::group_lemmas;

        assert forall|m: Mapping|
            self.view_mappings_through(C::NR_LEVELS()).contains(m)
                == #[trigger] self.view_mappings().contains(m) by {
            self.lemma_view_mappings_through_contains(C::NR_LEVELS(), m);
            if self.view_mappings_through(C::NR_LEVELS()).contains(m) {
                let i = choose|i: int|
                    self.level - 1 <= i < C::NR_LEVELS()
                        && #[trigger] self.continuations[i].view_mappings().contains(m);
                self.lemma_inv_continuation(i);
                self.lemma_view_mappings_intro(m, i);
            }
        };
        assert(self.view_mappings_through(C::NR_LEVELS()) =~= self.view_mappings());
    }

    /// Every mapping in the cursor view satisfies `Mapping::inv()`.
    pub proof fn lemma_view_mapping_inv(self)
        requires
            self.inv(),
        ensures
            forall|m: Mapping| self.view_mappings().contains(m) ==> #[trigger] m.inv(),
    {
        C::lemma_paging_consts_properties();
        C::lemma_page_table_config_constant_requirements();
        self.as_page_table_owner_preserves_view_mappings();
        let pto = self.as_page_table_owner();
        let root_path = self.continuations[C::NR_LEVELS() - 1].path();
        pto.lemma_view_rec_mapping_inv(root_path);
    }

    /// Non-overlapping mappings in the cursor view.
    ///
    /// Collapses the union-over-continuations `view_mappings` into a single
    /// `view_rec` rooted at the reconstructed root page table, then applies
    /// `lemma_view_rec_disjoint_vaddrs` on that single subtree.
    /// Follows from tree structure alone.
    pub proof fn as_page_table_owner_view_non_overlapping(self)
        requires
            self.inv(),
        ensures
            self@.non_overlapping(),
    {
        C::lemma_paging_consts_properties();
        C::lemma_page_table_config_constant_requirements();
        self.as_page_table_owner_preserves_view_mappings();
        let pto = self.as_page_table_owner();
        let root_path = self.continuations[C::NR_LEVELS() - 1].path();

        assert forall|m: Mapping, n: Mapping| #[trigger]
            self@.mappings.contains(m) && #[trigger] self@.mappings.contains(n) && m
                != n implies m.va_range.end <= n.va_range.start || n.va_range.end
            <= m.va_range.start by {
            pto.lemma_view_rec_disjoint_vaddrs(root_path, m, n);
        };
    }

    proof fn lemma_view_mappings_through_contains(self, level: PagingLevel, m: Mapping)
        requires
            self.inv(),
            self.level <= level <= C::NR_LEVELS(),
        ensures
            self.view_mappings_through(level).contains(m) == (exists|i: int|
                self.level - 1 <= i < level
                    && #[trigger] self.continuations[i].view_mappings().contains(m)),
        decreases level,
    {
        C::lemma_paging_consts_properties();
        if level > self.level {
            self.lemma_view_mappings_through_contains((level - 1) as PagingLevel, m);
        }
    }

    /// Reassembly preserves ownership and the union of mappings at every actual level.
    proof fn lemma_restore_to_level(self, level: PagingLevel)
        requires
            self.inv(),
            self.level <= level <= C::NR_LEVELS(),
        ensures
            self.restore_to_level(level).inv(),
            self.restore_to_level(level).all_some(),
            self.restore_to_level(level).entry_own == self.continuations[level - 1].entry_own,
            self.restore_to_level(level).tree_level == self.continuations[level - 1].tree_level,
            self.restore_to_level(level).guard == self.continuations[level - 1].guard,
            self.restore_to_level(level).path() == self.continuations[level - 1].path(),
            self.restore_to_level(level).idx == self.continuations[level - 1].idx,
            self.restore_to_level(level).view_mappings() == self.view_mappings_through(level),
        decreases level,
    {
        C::lemma_page_table_config_constant_requirements();
        C::lemma_paging_consts_properties();
        broadcast use vstd::map_lib::group_map_properties;

        self.lemma_inv_continuation(level - 1);
        let cont = self.continuations[level - 1];
        if level == self.level {
            assert(self.view_mappings_through(level) =~= cont.view_mappings());
        } else {
            self.lemma_restore_to_level((level - 1) as PagingLevel);
            let child = self.restore_to_level((level - 1) as PagingLevel);
            child.as_subtree_inv();
            child.as_page_table_owner_pt_inv();
            child.lemma_inv_children_unroll_all();
            cont.lemma_inv_children_unroll_all();
            cont.view_mappings_put_child(child.as_subtree());
            cont.as_subtree_restore(child);
            let restored = cont.restore(child).0;
            assert(restored.inv());
            restored.as_page_table_owner_preserves_view_mappings();
            child.as_page_table_owner_preserves_view_mappings();
            assert(self.view_mappings_through(level) =~= self.view_mappings_through(
                (level - 1) as PagingLevel,
            ).union(cont.view_mappings()));
        }
    }

    // Isolate address-range geometry from the caller's mapping-set algebra.
    #[verifier::spinoff_prover]
    proof fn lemma_higher_mapping_disjoint_from_lowest(self, i: int, m: Mapping)
        requires
            self.inv(),
            self.in_barrier_va(),
            self.level <= i < C::NR_LEVELS(),
            self.continuations[i].view_mappings().contains(m),
        ensures
            !self.continuations[self.level - 1].view_mappings().contains(m),
    {
        hide(CursorContinuation::inv_children_rel);
        hide(CursorContinuation::inv_children);
        hide(CursorContinuation::pt_inv_children);
        C::lemma_paging_consts_properties();
        C::lemma_page_table_config_constant_requirements();
        broadcast use {CursorContinuation::group_lemmas, CursorOwner::group_lemmas};

        let old_cont = self.continuations[self.level - 1];
        if old_cont.view_mappings().contains(m) {
            self.lemma_inv_continuation(i);
            self.lemma_inv_continuation(self.level - 1);
            let cont_i = self.continuations[i];
            let j = choose|j: int|
                #![auto]
                0 <= j < NR_ENTRIES && cont_i.children[j] is Some && PageTableOwner(
                    cont_i.children[j].unwrap(),
                ).view_rec(cont_i.path().push_tail(j)).contains(m);
            cont_i.lemma_inv_children_unroll(j);
            cont_i.lemma_pt_inv_children_unroll(j);
            cont_i.lemma_inv_children_rel_unroll(j);
            PageTableOwner(cont_i.children[j].unwrap()).lemma_view_rec_vaddr_range(
                cont_i.path().push_tail(j),
                m,
            );

            let k = choose|k: int|
                #![auto]
                0 <= k < NR_ENTRIES && old_cont.children[k] is Some && PageTableOwner(
                    old_cont.children[k].unwrap(),
                ).view_rec(old_cont.path().push_tail(k)).contains(m);
            old_cont.lemma_inv_children_unroll(k);
            old_cont.lemma_pt_inv_children_unroll(k);
            old_cont.lemma_inv_children_rel_unroll(k);
            PageTableOwner(old_cont.children[k].unwrap()).lemma_view_rec_vaddr_range(
                old_cont.path().push_tail(k),
                m,
            );

            if j as usize != cont_i.idx as int {
                self.cur_va_in_cont_child_range(self.level as int);
                self.cur_va_in_cont_child_range(i);

                let x = self.cur_va() as nat;
                let ps_node = page_size::<C>((self.level + 1) as PagingLevel) as nat;
                let ps_anc = page_size::<C>((i + 1) as PagingLevel) as nat;

                lemma_page_size_ge_base::<C>((i + 1) as PagingLevel);
                lemma_page_size_divides::<C>(
                    (self.level + 1) as PagingLevel,
                    (i + 1) as PagingLevel,
                );

                lemma_nat_align_down_monotone(x, ps_node, ps_anc);
                lemma_nat_align_down_within_block(x, ps_node, ps_anc);

                let sib_size = page_size::<C>(
                    (C::NR_LEVELS() + 1 - cont_i.path().len() - 1) as PagingLevel,
                );
                sibling_paths_disjoint::<C>(cont_i.path(), cont_i.idx as int, j, sib_size);
                // Lift positional disjointness to canonical.
                lemma_vaddr_of_eq_int::<C>(cont_i.path().push_tail(cont_i.idx as int));
                lemma_vaddr_of_eq_int::<C>(cont_i.path().push_tail(j));

                old_cont.as_subtree_inv();
                old_cont.as_page_table_owner_preserves_view_mappings();
                PageTableOwner(old_cont.as_subtree()).lemma_view_rec_vaddr_range(
                    old_cont.path(),
                    m,
                );
            } else {
                assert(cont_i.children[cont_i.idx as int] is None);
            }
        }
    }
}

} // verus!
