/// Virtual-address manipulation specs and lemmas for `CursorOwner`.
///
/// This module contains:
/// - Spec functions for zeroing VA indices below the cursor's level
///   (`zero_below_level_rec`, `zero_below_level`).
/// - Lemmas about how zeroing preserves fields other than VA.
/// - Spec functions for the cursor's current VA and VA range
///   (`cur_va`, `cur_va_range`).
/// - Lemmas relating the abstract VA to the page table view range.
/// - Axiom functions for updating the cursor VA (`set_va`, `set_va_in_node`).
use vstd::prelude::*;

use core::ops::Range;

use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;

use crate::mm::page_table::*;
use crate::mm::{Paddr, PagingLevel, Vaddr, page_size};
use crate::specs::arch::{NR_ENTRIES, NR_LEVELS, PAGE_SIZE};
use crate::specs::mm::page_table::AbstractVaddr;
use crate::specs::mm::page_table::Mapping;
use crate::specs::mm::page_table::cursor::owners::{CursorContinuation, CursorOwner};
use crate::specs::mm::page_table::cursor::page_size_lemmas::{
    lemma_page_size_divides, lemma_page_size_ge_page_size, lemma_page_size_spec_values,
};
use crate::specs::mm::page_table::owners::*;
use vstd_extra::arithmetic::nat_align_down;

verus! {

broadcast use group_ghost_tree_lemmas;

impl<'rcu, C: PageTableConfig> CursorOwner<'rcu, C> {
    // ─── Spec helpers ────────────────────────────────────────────────────
    pub open spec fn zero_below_level_rec(self, level: PagingLevel) -> Self
        decreases self.level - level,
    {
        if self.level <= level {
            self
        } else {
            Self {
                va: AbstractVaddr { index: self.va.index.insert(level - 1, 0), ..self.va },
                ..self.zero_below_level_rec((level + 1) as u8)
            }
        }
    }

    pub open spec fn zero_below_level(self) -> Self
        recommends
            1 <= self.level <= NR_LEVELS,
    {
        Self { va: self.va.align_down(self.level as int), ..self }
    }

    pub open spec fn cur_va(self) -> Vaddr {
        self.va.to_vaddr()
    }

    pub open spec fn cur_va_range(self) -> Range<AbstractVaddr> {
        let start = self.va.align_down(self.level as int);
        let end = self.va.align_up(self.level as int);
        Range { start, end }
    }

    pub open spec fn set_va(self, new_va: AbstractVaddr) -> Self {
        Self { va: new_va, ..self }
    }

    pub open spec fn set_va_in_node(self, new_va: AbstractVaddr) -> Self {
        let old_cont = self.continuations[self.level - 1];
        Self {
            va: new_va,
            continuations: self.continuations.insert(
                self.level - 1,
                CursorContinuation { idx: new_va.index[self.level - 1] as usize, ..old_cont },
            ),
            // Repositioning to a concrete in-range VA clears the
            // transient `popped_too_high` state.
            popped_too_high: false,
            ..self
        }
    }

    // ─── Proofs: zero preserves structure ────────────────────────────────
    pub proof fn zero_below_level_rec_preserves_above(self, level: PagingLevel)
        ensures
            forall|lv: int|
                lv >= self.level ==> self.zero_below_level_rec(level).va.index[lv]
                    == #[trigger] self.va.index[lv],
        decreases self.level - level,
    {
        if self.level > level {
            self.zero_below_level_rec_preserves_above((level + 1) as u8);
        }
    }

    /// Unfolds zero_below_level to expose the VA as align_down(level).
    pub proof fn zero_below_level_va(self)
        requires
            1 <= self.level <= NR_LEVELS,
        ensures
            self.zero_below_level().va == self.va.align_down(self.level as int),
    {
    }

    pub proof fn zero_preserves_above(self)
        requires
            self.va.inv(),
            1 <= self.level <= NR_LEVELS,
        ensures
            forall|lv: int|
                self.level <= lv < NR_LEVELS ==> self.zero_below_level().va.index[lv]
                    == #[trigger] self.va.index[lv],
    {
        self.va.align_down_shape(self.level as int);
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
        old_self.va.align_down_shape(old_self.level as int);
        old_self.va.align_down_leading_bits(old_self.level as int);
        self.va = old_self.va.align_down(old_self.level as int);

        old_self.locked_range_span();
        lemma_page_size_ge_page_size(old_self.level as PagingLevel);
        lemma_page_size_ge_page_size(old_self.guard_level as PagingLevel);
        lemma_page_size_divides(old_self.level as PagingLevel, old_self.guard_level as PagingLevel);
        old_self.va.align_down_to_vaddr_nat_align_down(old_self.level as int);

        let ghost old_va_val = old_self.va.to_vaddr() as nat;
        let ghost prefix_va_val = old_self.prefix.to_vaddr() as nat;
        let ghost ps = page_size(old_self.level as PagingLevel) as nat;
        let ghost guard_ps = page_size(old_self.guard_level as PagingLevel) as nat;
        let ghost start = old_self.locked_range().start as nat;

        vstd_extra::arithmetic::lemma_nat_align_down_monotone(prefix_va_val, ps, guard_ps);
        assert(start % ps == 0);
        vstd::arithmetic::div_mod::lemma_add_mod_noop(start as int, guard_ps as int, ps as int);

        vstd_extra::arithmetic::lemma_nat_align_down_sound(old_va_val, ps);
    }

    pub proof fn zero_rec_preserves_all_but_va(self, level: PagingLevel)
        ensures
            self.zero_below_level_rec(level).level == self.level,
            self.zero_below_level_rec(level).continuations == self.continuations,
            self.zero_below_level_rec(level).guard_level == self.guard_level,
            self.zero_below_level_rec(level).prefix == self.prefix,
            self.zero_below_level_rec(level).popped_too_high == self.popped_too_high,
        decreases self.level - level,
    {
        if self.level > level {
            self.zero_rec_preserves_all_but_va((level + 1) as u8);
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
        self.zero_rec_preserves_all_but_va(1u8);
    }

    // ─── Proofs: inc + zero ──────────────────────────────────────────────
    pub proof fn inc_and_zero_increases_va(self)
        requires
            self.inv(),
            self.in_locked_range(),
            self.index() + 1 < NR_ENTRIES,
        ensures
            self.inc_index().zero_below_level().va.to_vaddr() > self.va.to_vaddr(),
    {
        // inc_index increments va.index[level-1] by 1. zero_below_level zeroes
        // indices below level (= align_down). The result is align_up(va, ps).
        let inc = self.inc_index();
        inc.zero_preserves_all_but_va();
        inc.zero_below_level_va();

        let ps = page_size(self.level as PagingLevel) as nat;
        let self_va = self.va.to_vaddr() as nat;
        lemma_page_size_ge_page_size(self.level as PagingLevel);

        // Step 1: inc_index adds page_size to the vaddr.
        self.va.index_increment_adds_page_size(self.level as int);
        let inc_va = inc.va.to_vaddr() as nat;

        // Step 2: zero_below_level().va == inc.va.align_down(level).
        // align_down_concrete gives .reflect(nat_align_down(inc_va, ps)).
        inc.va.align_down_concrete(self.level as int);
        let new_va = vstd_extra::arithmetic::nat_align_down(inc_va, ps);
        AbstractVaddr::from_vaddr_to_vaddr_roundtrip(new_va as Vaddr);
        // Now inc.zero_below_level().va.to_vaddr() == new_va.

        // Step 3: align_down(self_va + ps, ps) = align_down(self_va, ps) + ps.
        // Because (self_va + ps) % ps == self_va % ps, adding a full ps doesn't
        // change the remainder.
        vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(self_va as int, ps as int);

        // Step 4: align_down(self_va, ps) + ps > self_va.
        // Because align_down(self_va, ps) = self_va - self_va % ps,
        // and self_va % ps < ps.
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(self_va as int, ps as int);
        vstd::arithmetic::div_mod::lemma_mod_bound(self_va as int, ps as int);
    }

    // ─── Proofs: VA range / view ─────────────────────────────────────────
    #[verifier::spinoff_prover]
    pub proof fn cur_va_range_reflects_view(self)
        requires
            self.inv(),
            self.in_locked_range(),
            !self.popped_too_high,
            self.cur_entry_owner().is_frame(),
        ensures
            self.cur_va_range().start.reflect(self@.query_range().start as Vaddr),
            self.cur_va_range().end.reflect(self@.query_range().end as Vaddr),
    {
        broadcast use CursorContinuation::group_lemmas;

        self.cur_subtree_inv();
        self.cur_va_in_subtree_range();
        self.view_preserves_inv();
        self.cur_entry_frame_present();
        let subtree = self.cur_subtree();
        let path = subtree.value().path;
        let frame = self.cur_entry_owner().frame();

        let ps = page_size(self.level as PagingLevel);
        let m = Mapping {
            va_range: Range { start: vaddr_of::<C>(path) as int, end: vaddr_of::<C>(path) + ps },
            pa_range: Range { start: frame.mapped_pa, end: (frame.mapped_pa + ps) as Paddr },
            page_size: ps,
            property: frame.prop,
        };

        assert(PageTableOwner(subtree).view_rec(path).contains(m));
        self.lemma_view_mappings_intro(m, (self.level - 1) as int);
        assert(m.inv());

        self.cur_va_in_subtree_range();
        crate::specs::mm::page_table::owners::lemma_vaddr_of_eq_int::<C>(path);

        let filtered = self@.mappings.filter(
            |m2: Mapping| m2.va_range.start <= self@.cur_va < m2.va_range.end,
        );
        vstd::set::lemma_set_choose_len(filtered);

        let cur_va = self.va.to_vaddr() as nat;
        let ps_nat = ps as nat;
        self.va.align_down_concrete(self.level as int);
        lemma_page_size_ge_page_size(self.level as PagingLevel);
        vstd_extra::arithmetic::lemma_nat_align_down_sound(cur_va, ps_nat);

        // Bridge: `cur_va == vaddr_of::<C>(path)` for paths aligned with the
        // cursor (offset is 0, the `to_vaddr_indices(0)` positional sum
        // equals `vaddr(path)`, and the `leading_bits * 2^48` is the same
        // `LEADING_BITS * 2^48` that `vaddr_of` adds).

        assert(nat_align_down(cur_va, ps_nat) == vaddr_of::<C>(path) as nat) by {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(cur_va as int, ps as int);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
                vaddr_of::<C>(path) as int,
                ps as int,
            );
            assert(vaddr_of::<C>(path) as int % ps as int == 0);
            vstd::arithmetic::div_mod::lemma_indistinguishable_quotients(
                vaddr_of::<C>(path) as int,
                cur_va as int,
                ps as int,
            );
        };

        self.locked_range_page_aligned();
        self.va.to_vaddr_bounded();
        self.in_locked_range_level_le_guard_level();
        self.va_plus_page_size_no_overflow(self.level as PagingLevel);
        self.va.align_up_advances_general(self.level as int);

        AbstractVaddr::from_vaddr_to_vaddr_roundtrip(nat_align_down(cur_va, ps_nat) as Vaddr);
        AbstractVaddr::from_vaddr_to_vaddr_roundtrip((vaddr_of::<C>(path) + ps) as Vaddr);

        self.va.align_up(self.level as int).reflect_to_vaddr();
    }

    /// The current virtual address falls within the VA range of the
    /// current subtree's path, in canonical form (positional vaddr plus
    /// the `leading_bits * 2^48` shift).
    pub proof fn cur_va_in_subtree_range(self)
        requires
            self.inv(),
            self.in_locked_range(),
        ensures
            vaddr(self.cur_subtree().value().path) + self.va.leading_bits * 0x1_0000_0000_0000int
                <= self.cur_va(),
            self.cur_va() < vaddr(self.cur_subtree().value().path) + self.va.leading_bits
                * 0x1_0000_0000_0000int + page_size(self.level as PagingLevel),
    {
        let L = self.level as int;
        let cont = self.continuations[L - 1];
        let subtree_path = cont.path().push_tail(cont.idx as int);
        let va_path = self.va.to_path(L - 1);

        self.va.to_path_len(L - 1);

        assert forall|i: int| 0 <= i < subtree_path.len() implies subtree_path[i] == va_path[i] by {
            self.va.to_path_index(L - 1, i);
        };

        self.va.to_path_inv(L - 1);
        self.cur_subtree_inv();
        AbstractVaddr::rec_vaddr_eq_if_indices_eq(subtree_path, va_path, 0);
        self.va.vaddr_range_from_path(L - 1);
    }

    pub proof fn lemma_locked_range_vaddr_prefix_match(self, new_va: AbstractVaddr)
        requires
            self.inv(),
            new_va.inv(),
            new_va.offset == 0,
            new_va.leading_bits == self.prefix.leading_bits,
            self.locked_range().start <= new_va.to_vaddr() < self.locked_range().end,
        ensures
            forall|i: int|
                #![trigger new_va.index[i]]
                self.guard_level - 1 <= i < NR_LEVELS ==> new_va.index[i] == self.prefix.index[i],
    {
        let gl = self.guard_level;
        let start = self.locked_range().start;
        let ps = page_size(gl as PagingLevel);
        let new_val = new_va.to_vaddr();
        let prefix_val = self.prefix.to_vaddr();

        self.locked_range_span();
        self.prefix_aligned_to_guard_level();
        self.prefix_plus_ps_no_overflow();
        self.prefix.aligned_align_down_is_self(gl as int);
        self.prefix.aligned_align_up_advances(gl as int);

        lemma_page_size_spec_values();
        if gl == 1 {
            new_va.reflect_to_vaddr();

            AbstractVaddr::same_page_aligned_vaddrs_equal(new_val, prefix_val, start);
            AbstractVaddr::to_vaddr_from_vaddr_roundtrip(new_va);
            AbstractVaddr::to_vaddr_from_vaddr_roundtrip(self.prefix);
        } else {
            AbstractVaddr::to_vaddr_from_vaddr_roundtrip(new_va);
            AbstractVaddr::to_vaddr_from_vaddr_roundtrip(self.prefix);
            AbstractVaddr::same_node_indices_match(
                new_val,
                prefix_val,
                start,
                (gl - 1) as PagingLevel,
            );
        }
    }

    // ─── Axioms: VA mutation ─────────────────────────────────────────────
    /// When jumping within the same page-table node, only indices at levels
    /// >= level are guaranteed to match. The entry-within-node index (level - 1)
    /// may change, so we update continuations[level-1].idx along with va.
    pub proof fn tracked_set_va_in_node(tracked &mut self, new_va: AbstractVaddr)
        requires
            old(self).inv(),
            new_va.inv(),
            new_va.offset == 0,
            new_va.leading_bits == old(self).prefix.leading_bits,
            forall|i: int|
                #![auto]
                old(self).level <= i < NR_LEVELS ==> new_va.index[i] == old(self).va.index[i],
            old(self).locked_range().start <= new_va.to_vaddr() < old(self).locked_range().end,
            // Needed for soundness of the asserted `final(self).inv()`:
            // we clear `popped_too_high`, so `CursorOwner::inv`'s
            // `!popped_too_high ==> level <= guard_level || above_locked_range`
            // clause must hold; the new VA is in-range (not above), so
            // we require `level <= guard_level`.
            old(self).level <= old(self).guard_level,
        ensures
            *final(self) == old(self).set_va_in_node(new_va),
            final(self).inv(),
    {
        let ghost old_self = *self;
        let tracked mut cont = self.continuations.tracked_remove(self.level - 1);

        assert(new_va.index.contains_key(old_self.level - 1));

        cont.idx = new_va.index[old_self.level - 1] as usize;

        self.continuations.tracked_insert(self.level - 1, cont);
        self.va = new_va;
        self.popped_too_high = false;

        assert(self.continuations == old_self.continuations.insert(old_self.level - 1, cont));

        old_self.lemma_locked_range_vaddr_prefix_match(new_va);

        if old_self.level < old_self.guard_level {
            old_self.prefix_in_locked_range();
        }
    }
}

} // verus!
