/// Virtual-address manipulation specs and lemmas for `CursorOwner`.
///
/// This module contains:
/// - Spec functions for zeroing VA indices below the cursor's level
///   (`zero_below_level`).
/// - Lemmas about how zeroing preserves fields other than VA.
/// - Spec functions for the cursor's current VA and VA range
///   (`cur_va`, `cur_va_range`).
/// - Lemmas relating the concrete VA to the page table view range.
/// - Specifications and proofs for repositioning the cursor inside its current node.
use vstd::prelude::*;
use vstd_extra::{arithmetic::nat_align_down, ghost_tree::*, ownership::*};

use crate::specs::{
    arch::*,
    mm::page_table::{
        cursor::{
            owners::{CursorContinuation, CursorOwner},
            page_size_lemmas::*,
        },
        owners::*,
        *,
    },
};

use crate::arch::mm::PagingConsts;
use crate::mm::{Paddr, PagingConstsTrait, PagingLevel, Vaddr, page_size, page_table::*};
use crate::specs::task::InAtomicMode;
use core::ops::Range;

verus! {

broadcast use group_ghost_tree_lemmas;

impl<'rcu, C: PageTableConfig> CursorOwner<'rcu, C> {
    pub open spec fn zero_below_level(self) -> Self
        recommends
            1 <= self.level <= C::NR_LEVELS(),
    {
        Self {
            va: nat_align_down(self.va as nat, page_size::<C>(self.level) as nat) as Vaddr,
            ..self
        }
    }

    pub open spec fn cur_va(self) -> Vaddr {
        self.va
    }

    pub open spec fn prefix_vaddr(self) -> Vaddr {
        self.prefix
    }

    pub open spec fn cur_va_range(self) -> Range<Vaddr> {
        let size = page_size::<PagingConsts>(self.level);
        let start = nat_align_down(self.cur_va() as nat, size as nat) as Vaddr;
        Range { start, end: (start + size) as Vaddr }
    }

    pub open spec fn set_va_in_node(self, new_va: Vaddr) -> Self {
        let old_cont = self.continuations[self.level - 1];
        Self {
            va: new_va,
            continuations: self.continuations.insert(
                self.level - 1,
                CursorContinuation { idx: pte_index_spec::<C>(new_va, self.level), ..old_cont },
            ),
            // Repositioning to a concrete in-range VA clears the
            // transient `popped_too_high` state.
            popped_too_high: false,
            ..self
        }
    }

    /// Incrementing the selected nonterminal entry advances by one slot without overflow.
    pub proof fn lemma_inc_index_va(self)
        requires
            self.inv(),
            self.in_barrier_va(),
            self.index() + 1 < NR_ENTRIES,
        ensures
            self.inc_index().va == self.va + page_size::<C>(self.level),
    {
        C::lemma_paging_consts_properties();
        C::axiom_current_paging_consts_hardcoded();
        self.lemma_cur_pte_index();
        lemma_inc_slot_indices::<C>(self.va, self.level);
        reveal(vaddr_replace_pte_index_spec);
        vstd::arithmetic::mul::lemma_mul_basics(page_size::<C>(self.level) as int);
    }

    /// Incrementing a nonterminal index and aligning down reaches the next slot boundary.
    pub proof fn inc_and_zero_increases_va(self)
        requires
            self.inv(),
            self.in_barrier_va(),
            self.index() + 1 < NR_ENTRIES,
        ensures
            self.inc_index().zero_below_level().va > self.va,
            self.inc_index().zero_below_level().va == self@.align_up_spec(
                page_size::<PagingConsts>(self.level),
            ),
    {
        C::lemma_paging_consts_properties();
        C::axiom_current_paging_consts_hardcoded();
        self.lemma_inc_index_va();
        lemma_page_size_ge_base::<PagingConsts>(self.level);
        let ps = page_size::<PagingConsts>(self.level) as nat;
        let va = self.va as nat;
        vstd_extra::arithmetic::lemma_nat_align_down_sound(va, ps);
        vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(va as int, ps as int);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(va as int, ps as int);
    }

    /// The current subtree starts at the cursor's aligned slot boundary and contains its VA.
    pub proof fn cur_va_in_subtree_range(self)
        requires
            self.inv(),
            self.in_barrier_va(),
        ensures
            vaddr_of::<C>(self.cur_subtree().value().path) <= self.cur_va() < vaddr_of::<C>(
                self.cur_subtree().value().path,
            ) + page_size::<PagingConsts>(self.level),
            vaddr_of::<C>(self.cur_subtree().value().path) == nat_align_down(
                self.cur_va() as nat,
                page_size::<PagingConsts>(self.level) as nat,
            ),
    {
        self.cur_va_in_cont_child_range(self.level - 1);
    }

    /// Addresses in the same guard node share indices strictly above its level.
    pub proof fn lemma_locked_range_vaddr_prefix_match(self, new_va: Vaddr)
        requires
            self.inv(),
            new_va % C::BASE_PAGE_SIZE() == 0,
            vaddr_leading_part_spec::<C>(new_va) == vaddr_leading_part_spec::<C>(
                self.prefix_vaddr(),
            ),
            self.locked_range().start <= new_va < self.locked_range().end,
        ensures
            forall|i: int|
                self.guard_level <= i < C::NR_LEVELS() ==> (#[trigger] pte_index_spec::<C>(
                    new_va,
                    (i + 1) as PagingLevel,
                )) == pte_index_spec::<C>(self.prefix, (i + 1) as PagingLevel),
    {
        C::lemma_paging_consts_properties();
        C::axiom_current_paging_consts_hardcoded();
        self.lemma_locked_range_span();
        if self.guard_level < C::NR_LEVELS() {
            lemma_same_node_pte_indices_match::<C>(
                new_va,
                self.prefix,
                self.prefix,
                self.guard_level,
            );
        }
    }

    /// The entry selected by the cursor's concrete VA is the entry owned by its current
    /// continuation. This is the architecture-parameterized replacement for exposing the
    /// decomposed address stored in `CursorOwner`.
    pub proof fn lemma_cur_pte_index(self)
        requires
            self.inv(),
            self.in_barrier_va(),
        ensures
            1 <= self.level <= C::NR_LEVELS(),
            pte_index_spec::<C>(self.cur_va(), self.level) == self.continuations[self.level
                - 1].idx,
            pte_index_spec::<C>(self.cur_va(), self.level) < NR_ENTRIES,
    {
        C::lemma_paging_consts_properties();
        C::axiom_current_paging_consts_hardcoded();
        lemma_pte_index_bound::<C>(self.cur_va(), self.level);
    }

    /// Architecture-parameterized entry point for repositioning a cursor inside its current
    /// page-table node.
    pub proof fn tracked_set_vaddr_in_node(tracked &mut self, new_va: Vaddr)
        requires
            old(self).inv(),
            new_va % C::BASE_PAGE_SIZE() == 0,
            vaddr_leading_part_spec::<C>(new_va) == vaddr_leading_part_spec::<C>(
                old(self).cur_va(),
            ),
            forall|i: int|
                old(self).level <= i < C::NR_LEVELS() ==> (#[trigger] pte_index_spec::<C>(
                    new_va,
                    (i + 1) as PagingLevel,
                )) == old(self).continuations[i].idx,
            old(self).locked_range().start <= new_va < old(self).locked_range().end,
            old(self).set_va_in_node(new_va).in_barrier_va(),
            old(self).level <= old(self).guard_level,
        ensures
            *final(self) == old(self).set_va_in_node(new_va),
            final(self).inv(),
    {
        let ghost old_self = *self;
        C::lemma_paging_consts_properties();
        C::axiom_current_paging_consts_hardcoded();
        lemma_pte_index_bound::<C>(new_va, old_self.level);
        let tracked mut cont = self.continuations.tracked_remove(self.level - 1);
        cont.idx = pte_index_spec::<C>(new_va, old_self.level);
        self.continuations.tracked_insert(self.level - 1, cont);
        self.va = new_va;
        self.popped_too_high = false;
        assert(self.continuations == old_self.continuations.insert(old_self.level - 1, cont));
        old_self.lemma_locked_range_vaddr_prefix_match(new_va);
        old_self.lemma_barrier_va_bounds(new_va);
    }
}

impl<'rcu, C: PageTableConfig, A: InAtomicMode> Cursor<'rcu, C, A> {
    /// Connects the executable cursor address to the architecture-parameterized index owned by
    /// its ghost continuation, without exposing the owner's decomposed address representation.
    pub proof fn lemma_pte_index_matches_owner(self, owner: CursorOwner<'rcu, C>)
        requires
            self.wf(owner),
            owner.inv(),
            owner.in_barrier_va(),
        ensures
            1 <= self.level <= C::NR_LEVELS(),
            pte_index_spec::<C>(self.va, self.level) == owner.continuations[owner.level - 1].idx,
            pte_index_spec::<C>(self.va, self.level) < NR_ENTRIES,
    {
        owner.lemma_cur_pte_index();
    }
}

} // verus!
