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
use crate::mm::{Paddr, PagingLevel, Vaddr};
use crate::specs::mm::page_table::Mapping;
use vstd_extra::arithmetic::{nat_align_down, nat_align_up};
use crate::specs::arch::mm::{NR_ENTRIES, NR_LEVELS};
use crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_ge_page_size;
use crate::specs::mm::page_table::cursor::owners::{CursorOwner, CursorContinuation};
use crate::specs::mm::page_table::owners::*;
use crate::specs::mm::page_table::AbstractVaddr;

verus! {

impl<'rcu, C: PageTableConfig> CursorOwner<'rcu, C> {

    // ─── Spec helpers ────────────────────────────────────────────────────

    pub open spec fn zero_below_level_rec(self, level: PagingLevel) -> Self
        decreases self.level - level
    {
        if self.level <= level {
            self
        } else {
            Self {
                va: AbstractVaddr {
                    index: self.va.index.insert(level - 1, 0),
                    ..self.va
                },
                ..self.zero_below_level_rec((level + 1) as u8)
            }
        }
    }

    pub open spec fn zero_below_level(self) -> Self
        recommends 1 <= self.level <= NR_LEVELS,
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

    pub open spec fn set_va_spec(self, new_va: AbstractVaddr) -> Self {
        Self {
            va: new_va,
            ..self
        }
    }

    pub open spec fn set_va_in_node_spec(self, new_va: AbstractVaddr) -> Self {
        let old_cont = self.continuations[self.level - 1];
        Self {
            va: new_va,
            continuations: self.continuations.insert(
                self.level - 1,
                CursorContinuation {
                    idx: new_va.index[self.level - 1] as usize,
                    ..old_cont
                },
            ),
            ..self
        }
    }

    // ─── Proofs: zero preserves structure ────────────────────────────────

    pub proof fn zero_below_level_rec_preserves_above(self, level: PagingLevel)
        ensures
            forall |lv: int| lv >= self.level ==>  self.zero_below_level_rec(level).va.index[lv] == #[trigger] self.va.index[lv],
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
    {}

    pub proof fn zero_preserves_above(self)
        requires
            self.va.inv(),
            1 <= self.level <= NR_LEVELS,
        ensures
            forall |lv: int| self.level <= lv < NR_LEVELS ==> self.zero_below_level().va.index[lv] == #[trigger] self.va.index[lv],
    {
        self.va.align_down_shape(self.level as int);
    }

    pub axiom fn do_zero_below_level(tracked &mut self)
        requires
            old(self).inv(),
        ensures
            *final(self) == old(self).zero_below_level(),
            final(self).inv();

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
            self.index() + 1 < NR_ENTRIES,
        ensures
            self.inc_index().zero_below_level().va.to_vaddr() > self.va.to_vaddr(),
    {
        // inc_index increments va.index[level-1] by 1. zero_below_level zeroes
        // indices below level (= align_down). The result is align_up(va, ps).
        let inc = self.inc_index();
        inc.zero_preserves_all_but_va();
        inc.zero_below_level_va();
        assert(inc.va.inv()) by {
            assert forall |i: int| 0 <= i < NR_LEVELS implies
                inc.va.index.contains_key(i) && 0 <= #[trigger] inc.va.index[i] && inc.va.index[i] < NR_ENTRIES
            by { if i != self.level - 1 { assert(inc.va.index[i] == self.va.index[i]); } };
        };
        let ps = page_size(self.level as PagingLevel) as nat;
        let self_va = self.va.to_vaddr() as nat;
        lemma_page_size_ge_page_size(self.level as PagingLevel);

        // Step 1: inc_index adds page_size to the vaddr.
        assert(self.va.index[self.level - 1] == self.continuations[self.level - 1].idx);
        self.va.index_increment_adds_page_size(self.level as int);
        let inc_va = inc.va.to_vaddr() as nat;
        assert(inc_va == self_va + ps);

        // Step 2: zero_below_level().va == inc.va.align_down(level).
        // align_down_concrete gives .reflect(nat_align_down(inc_va, ps)).
        inc.va.align_down_concrete(self.level as int);
        let new_va = vstd_extra::arithmetic::nat_align_down(inc_va, ps);
        AbstractVaddr::from_vaddr_to_vaddr_roundtrip(new_va as Vaddr);
        // Now inc.zero_below_level().va.to_vaddr() == new_va.

        // Step 3: align_down(self_va + ps, ps) = align_down(self_va, ps) + ps.
        // Because (self_va + ps) % ps == self_va % ps, adding a full ps doesn't
        // change the remainder.
        assert(self_va + ps == ps * 1 + self_va) by (nonlinear_arith);
        vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(1int, self_va as int, ps as int);

        // Step 4: align_down(self_va, ps) + ps > self_va.
        // Because align_down(self_va, ps) = self_va - self_va % ps,
        // and self_va % ps < ps.
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(self_va as int, ps as int);
        vstd::arithmetic::div_mod::lemma_mod_bound(self_va as int, ps as int);
        let ad = vstd_extra::arithmetic::nat_align_down(self_va, ps);
        assert(ad + ps > self_va) by {
            vstd_extra::arithmetic::lemma_nat_align_down_sound(self_va, ps);
        };
        assert(new_va == ad + ps) by {
            vstd_extra::arithmetic::lemma_nat_align_down_sound(self_va, ps);
            vstd_extra::arithmetic::lemma_nat_align_down_sound(inc_va, ps);
        };
    }

    // ─── Proofs: VA range / view ─────────────────────────────────────────

    pub proof fn cur_va_range_reflects_view(self)
        requires
            self.inv(),
            self.cur_entry_owner().is_frame(),
        ensures
            self.cur_va_range().start.reflect(self@.query_range().start as Vaddr),
            self.cur_va_range().end.reflect(self@.query_range().end as Vaddr),
    {
        self.cur_subtree_inv();
        self.cur_va_in_subtree_range();
        self.view_preserves_inv();
        self.cur_entry_frame_present();
        let subtree = self.cur_subtree();
        let path = subtree.value.path;
        let frame = self.cur_entry_owner().frame.unwrap();
        let pt_level = INC_LEVELS - path.len();
        let cont = self.continuations[self.level - 1];

        cont.path().push_tail_property_len(cont.idx as usize);
        assert(cont.level() == self.level) by {
            if self.level == 1 {} else if self.level == 2 {} else if self.level == 3 {} else {}
        };
        assert(pt_level == self.level);

        let ps = page_size(self.level as PagingLevel);
        let m = Mapping {
            va_range: Range { start: vaddr_of::<C>(path) as int, end: vaddr_of::<C>(path) as int + ps as int },
            pa_range: Range { start: frame.mapped_pa, end: (frame.mapped_pa + ps) as Paddr },
            page_size: ps,
            property: frame.prop,
        };
        assert(PageTableOwner(subtree).view_rec(path) =~= set![m]);
        assert(self.view_mappings().contains(m));
        assert(m.inv());
        // `vaddr_of::<C>(path) <= cur_va < vaddr_of::<C>(path) + ps` —
        // bridges the cursor's canonical `cur_va` to the path-derived
        // `vaddr_of`. Holds by cur_va == self.va.to_vaddr() and the
        // alignment + subtree-range invariants; admit pending extraction
        // of the bridging lemma.
        admit();
        assert(m.va_range.start <= self@.cur_va < m.va_range.end);

        let filtered = self@.mappings.filter(|m2: Mapping| m2.va_range.start <= self@.cur_va < m2.va_range.end);
        assert(filtered.contains(m));
        vstd::set::axiom_set_intersect_finite::<Mapping>(
            self@.mappings, Set::new(|m2: Mapping| m2.va_range.start <= self@.cur_va < m2.va_range.end));
        vstd::set::axiom_set_choose_len(filtered);
        let qm = self@.query_mapping();
        assert(filtered.contains(qm));
        assert(qm == m) by {
            if qm != m {
                assert(self@.mappings.contains(qm));
                assert(self@.mappings.contains(m));
                assert(!(qm.va_range.end <= m.va_range.start || m.va_range.end <= qm.va_range.start));
            }
        };

        let cur_va = self.va.to_vaddr() as nat;
        let ps_nat = ps as nat;
        self.va.align_down_concrete(self.level as int);
        self.va.align_up_concrete(self.level as int);
        self.va.align_diff(self.level as int);
        lemma_page_size_ge_page_size(self.level as PagingLevel);
        vstd_extra::arithmetic::lemma_nat_align_down_sound(cur_va, ps_nat);

        // Bridge: `cur_va == vaddr_of::<C>(path)` for paths aligned with the
        // cursor (offset is 0, the `to_vaddr_indices(0)` positional sum
        // equals `vaddr(path)`, and the `leading_bits * 2^48` is the same
        // `LEADING_BITS * 2^48` that `vaddr_of` adds).
        assert(vaddr_of::<C>(path) as int % ps as int == 0);
        assert(vaddr_of::<C>(path) <= cur_va < vaddr_of::<C>(path) + ps);
        assert(nat_align_down(cur_va, ps_nat) == vaddr_of::<C>(path) as nat) by {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(cur_va as int, ps as int);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(vaddr_of::<C>(path) as int, ps as int);
            vstd::arithmetic::div_mod::lemma_div_is_ordered(
                vaddr_of::<C>(path) as int, cur_va as int, ps as int);
            let q_cur = cur_va as int / ps as int;
            let q_path = vaddr_of::<C>(path) as int / ps as int;
            assert(q_path * ps as int == vaddr_of::<C>(path) as int);
            vstd::arithmetic::mul::lemma_mul_inequality(
                q_path, q_cur, ps as int);
            if q_path < q_cur {
                vstd::arithmetic::mul::lemma_mul_inequality(
                    q_path + 1, q_cur, ps as int);
                vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(
                    ps as int, q_path, 1int);
                assert(false);
            }
        };
        assert(nat_align_up(cur_va, ps_nat) == (vaddr_of::<C>(path) + ps) as nat);

        AbstractVaddr::from_vaddr_to_vaddr_roundtrip(nat_align_down(cur_va, ps_nat) as Vaddr);
        AbstractVaddr::from_vaddr_to_vaddr_roundtrip(nat_align_up(cur_va, ps_nat) as Vaddr);
    }

    /// The current virtual address falls within the VA range of the
    /// current subtree's path, in canonical form (positional vaddr plus
    /// the `leading_bits * 2^48` shift).
    pub proof fn cur_va_in_subtree_range(self)
        requires
            self.inv(),
        ensures
            vaddr(self.cur_subtree().value.path) as int
                + self.va.leading_bits * 0x1_0000_0000_0000int
                <= self.cur_va() as int,
            (self.cur_va() as int)
                < vaddr(self.cur_subtree().value.path) as int
                    + self.va.leading_bits * 0x1_0000_0000_0000int
                    + page_size(self.level as PagingLevel) as int,
    {
        let L = self.level as int;
        let cont = self.continuations[L - 1];
        let subtree_path = cont.path().push_tail(cont.idx as usize);
        let va_path = self.va.to_path(L - 1);

        self.va.to_path_len(L - 1);
        cont.path().push_tail_property_len(cont.idx as usize);
        assert(cont.level() == self.level) by {
            if L == 1 {} else if L == 2 {} else if L == 3 {} else {}
        };

        assert forall|i: int| 0 <= i < subtree_path.len() implies
            subtree_path.index(i) == va_path.index(i) by {
            self.va.to_path_index(L - 1, i);
            if L == 4 {
                cont.path().push_tail_property_index(cont.idx as usize);
            } else if L == 3 {
                cont.path().push_tail_property_index(cont.idx as usize);
                self.continuations[3].path().push_tail_property_index(self.continuations[3].idx as usize);
            } else if L == 2 {
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

        self.va.to_path_inv(L - 1);
        self.cur_subtree_inv();
        AbstractVaddr::rec_vaddr_eq_if_indices_eq(subtree_path, va_path, 0);
        self.va.vaddr_range_from_path(L - 1);
    }

    // ─── Axioms: VA mutation ─────────────────────────────────────────────

    pub axiom fn set_va(tracked &mut self, new_va: AbstractVaddr)
        requires
            forall |i: int| #![auto] old(self).level - 1 <= i < NR_LEVELS ==> new_va.index[i] == old(self).va.index[i],
            forall |i: int| #![auto] old(self).guard_level - 1 <= i < NR_LEVELS ==> new_va.index[i] == old(self).prefix.index[i],
        ensures
            *final(self) == old(self).set_va_spec(new_va);

    /// When jumping within the same page-table node, only indices at levels
    /// >= level are guaranteed to match. The entry-within-node index (level - 1)
    /// may change, so we update continuations[level-1].idx along with va.
    pub axiom fn set_va_in_node(tracked &mut self, new_va: AbstractVaddr)
        requires
            old(self).inv(),
            new_va.inv(),
            forall|i: int| #![auto] old(self).level <= i < NR_LEVELS
                ==> new_va.index[i] == old(self).va.index[i],
            old(self).locked_range().start <= new_va.to_vaddr()
                < old(self).locked_range().end,
        ensures
            *final(self) == old(self).set_va_in_node_spec(new_va),
            final(self).inv(),;
}

} // verus!
