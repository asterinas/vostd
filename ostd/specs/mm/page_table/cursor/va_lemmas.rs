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
    arch::{NR_ENTRIES, NR_LEVELS, PAGE_SIZE},
    mm::page_table::{
        Mapping,
        cursor::{
            owners::{CursorContinuation, CursorOwner},
            page_size_lemmas::{
                lemma_page_size_divides, lemma_page_size_ge_page_size, lemma_page_size_spec_values,
            },
        },
        lemma_align_down_indices, lemma_inc_slot_indices,
        lemma_pte_index_bound,
        lemma_same_node_pte_indices_match,
        owners::*,
        pte_index_spec, vaddr_replace_pte_index_spec,
        vaddr_upper_bits_spec,
    },
};

use crate::arch::mm::PagingConsts;
use crate::mm::{Paddr, PagingConstsTrait, PagingLevel, Vaddr, page_size, page_size_spec, page_table::*};
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
            va: nat_align_down(
                self.va as nat,
                page_size_spec::<C>(self.level) as nat,
            ) as Vaddr,
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

    pub proof fn do_zero_below_level(tracked &mut self)
        requires
            old(self).inv(),
            old(self).level <= old(self).guard_level,
        ensures
            *final(self) == old(self).zero_below_level(),
            final(self).inv(),
    {
        let ghost old_self = *self;
        C::lemma_paging_consts_properties();
        lemma_align_down_indices::<C>(old_self.va, old_self.level);
        self.va = old_self.zero_below_level().va;

        old_self.lemma_locked_range_span();
        lemma_page_size_ge_page_size(old_self.level as PagingLevel);
        lemma_page_size_ge_page_size(old_self.guard_level as PagingLevel);
        lemma_page_size_divides(old_self.level as PagingLevel, old_self.guard_level as PagingLevel);
        let ghost old_va_val = old_self.va as nat;
        let ghost prefix_va_val = old_self.prefix as nat;
        let ghost ps = page_size::<PagingConsts>(old_self.level as PagingLevel) as nat;
        let ghost guard_ps = page_size::<PagingConsts>(old_self.guard_level as PagingLevel) as nat;
        let ghost start = old_self.locked_range().start as nat;

        vstd_extra::arithmetic::lemma_nat_align_down_monotone(prefix_va_val, ps, guard_ps);
        vstd_extra::arithmetic::lemma_mod_0_add(start as int, guard_ps as int, ps as int);

        vstd_extra::arithmetic::lemma_nat_align_down_sound(old_va_val, ps);
        if !self.popped_too_high && (self.in_locked_range() || self.level < self.guard_level) {
            if self.level == self.guard_level {
                let new_va_val = self.va as nat;
                let diff = (new_va_val - start) as nat;
                vstd::arithmetic::div_mod::lemma_mod_equivalence(
                    new_va_val as int,
                    start as int,
                    ps as int,
                );
                vstd::arithmetic::div_mod::lemma_small_mod(diff, ps);
            }
        }
    }

    pub proof fn zero_preserves_all_but_va(self)
        ensures
            self.zero_below_level().level == self.level,
            self.zero_below_level().continuations == self.continuations,
            self.zero_below_level().guard_level == self.guard_level,
            self.zero_below_level().prefix == self.prefix,
            self.zero_below_level().popped_too_high == self.popped_too_high,
    {
    }

    /// Incrementing the selected nonterminal entry advances by one slot without overflow.
    pub proof fn lemma_inc_index_va(self)
        requires
            self.inv(),
            self.in_locked_range(),
            self.index() + 1 < NR_ENTRIES,
        ensures
            self.inc_index().va == self.va + page_size_spec::<C>(self.level),
    {
        C::lemma_paging_consts_properties();
        self.lemma_cur_pte_index();
        lemma_inc_slot_indices::<C>(self.va, self.level);
        reveal(vaddr_replace_pte_index_spec);
        vstd::arithmetic::mul::lemma_mul_basics(page_size_spec::<C>(self.level) as int);
    }

    /// Incrementing a nonterminal index and aligning down reaches the next slot boundary.
    pub proof fn inc_and_zero_increases_va(self)
        requires
            self.inv(),
            self.in_locked_range(),
            self.index() + 1 < NR_ENTRIES,
        ensures
            self.inc_index().zero_below_level().va > self.va,
            self.inc_index().zero_below_level().va == self@.align_up_spec(page_size::<PagingConsts>(self.level)),
    {
        C::lemma_paging_consts_properties();
        self.lemma_inc_index_va();
        lemma_page_size_ge_page_size(self.level);
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
            self.in_locked_range(),
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

    /// Addresses in the locked block share the guard-level and higher indices.
    pub proof fn lemma_locked_range_vaddr_prefix_match(self, new_va: Vaddr)
        requires
            self.inv(),
            new_va % C::BASE_PAGE_SIZE() == 0,
            vaddr_upper_bits_spec::<C>(new_va) == vaddr_upper_bits_spec::<C>(self.prefix_vaddr()),
            self.locked_range().start <= new_va < self.locked_range().end,
        ensures
            pte_index_spec::<C>(new_va, self.guard_level) == pte_index_spec::<C>(
                self.prefix,
                self.guard_level,
            ),
            forall|i: int|
                self.guard_level - 1 <= i < C::NR_LEVELS() ==> (#[trigger] pte_index_spec::<C>(
                    new_va,
                    (i + 1) as PagingLevel,
                )) == pte_index_spec::<C>(self.prefix_vaddr(), (i + 1) as PagingLevel),
    {
        C::lemma_paging_consts_properties();
        self.lemma_locked_range_span();
        let gl = self.guard_level;
        if gl == 1 {
            lemma_page_size_spec_values();
            let ps = C::BASE_PAGE_SIZE() as int;
            let diff = new_va - self.prefix;
            vstd::arithmetic::div_mod::lemma_mod_equivalence(new_va as int, self.prefix as int, ps);
            vstd::arithmetic::div_mod::lemma_small_mod(diff as nat, ps as nat);
            assert(new_va == self.prefix);
        } else {
            lemma_same_node_pte_indices_match::<C>(
                new_va,
                self.prefix,
                self.prefix,
                (gl - 1) as PagingLevel,
            );
        }
    }

    /// The entry selected by the cursor's concrete VA is the entry owned by its current
    /// continuation. This is the architecture-parameterized replacement for exposing the
    /// decomposed address stored in `CursorOwner`.
    pub proof fn lemma_cur_pte_index(self)
        requires
            self.inv(),
            self.in_locked_range(),
        ensures
            1 <= self.level <= C::NR_LEVELS(),
            pte_index_spec::<C>(self.cur_va(), self.level) == self.continuations[self.level
                - 1].idx,
            pte_index_spec::<C>(self.cur_va(), self.level) < NR_ENTRIES,
    {
        C::lemma_paging_consts_properties();
        lemma_pte_index_bound::<C>(self.cur_va(), self.level);
    }

    /// Architecture-parameterized entry point for repositioning a cursor inside its current
    /// page-table node.
    pub proof fn tracked_set_vaddr_in_node(tracked &mut self, new_va: Vaddr)
        requires
            old(self).inv(),
            new_va % C::BASE_PAGE_SIZE() == 0,
            vaddr_upper_bits_spec::<C>(new_va) == vaddr_upper_bits_spec::<C>(old(self).cur_va()),
            forall|i: int|
                old(self).level <= i < C::NR_LEVELS() ==> (#[trigger] pte_index_spec::<C>(
                    new_va,
                    (i + 1) as PagingLevel,
                )) == pte_index_spec::<C>(old(self).cur_va(), (i + 1) as PagingLevel),
            old(self).locked_range().start <= new_va < old(self).locked_range().end,
            old(self).level <= old(self).guard_level,
        ensures
            *final(self) == old(self).set_va_in_node(new_va),
            final(self).inv(),
    {
        let ghost old_self = *self;
        C::lemma_paging_consts_properties();
        lemma_pte_index_bound::<C>(new_va, old_self.level);
        let tracked mut cont = self.continuations.tracked_remove(self.level - 1);
        cont.idx = pte_index_spec::<C>(new_va, old_self.level);
        self.continuations.tracked_insert(self.level - 1, cont);
        self.va = new_va;
        self.popped_too_high = false;
        assert(self.continuations == old_self.continuations.insert(old_self.level - 1, cont));
        old_self.lemma_locked_range_vaddr_prefix_match(new_va);
        if old_self.level < old_self.guard_level {
            old_self.lemma_prefix_in_locked_range();
        }
    }
}

impl<'rcu, C: PageTableConfig, A: InAtomicMode> Cursor<'rcu, C, A> {
    /// Connects the executable cursor address to the architecture-parameterized index owned by
    /// its ghost continuation, without exposing the owner's decomposed address representation.
    pub proof fn lemma_pte_index_matches_owner(self, owner: CursorOwner<'rcu, C>)
        requires
            self.wf(owner),
            owner.inv(),
            owner.in_locked_range(),
        ensures
            1 <= self.level <= C::NR_LEVELS(),
            pte_index_spec::<C>(self.va, self.level) == owner.continuations[owner.level - 1].idx,
            pte_index_spec::<C>(self.va, self.level) < NR_ENTRIES,
    {
        owner.lemma_cur_pte_index();
    }
}

} // verus!
