// SPDX-License-Identifier: MPL-2.0
//! Bounded-arithmetic proofs for `vaddr_range`'s body.
//!
//! Factored into a leaf module because the `nonlinear_arith` tactic
//! triggers a Verus internal panic when used in `page_table/mod.rs`
//! alongside `largest_pages` (which has an `impl Iterator` return type).
//! Same workaround pattern as the older `vaddr_range_bv_lemmas`.

use vstd::arithmetic::power2::{lemma_pow2_adds, lemma_pow2_pos, pow2};
use vstd::prelude::*;

use crate::mm::page_table::{
    axiom_top_level_index_range_bounds, pte_index_bit_offset_spec, PageTableConfig,
};
use crate::mm::{PagingConstsTrait, Vaddr};

verus! {

/// Two-in-one: `start = idx.start * 2^off < 2^ADDRESS_WIDTH` and
/// `end = (idx.end * 2^off - 1) % 2^64 < 2^ADDRESS_WIDTH`.
///
/// The first follows from `idx.start < 2^(ADDRESS_WIDTH - off)`. The
/// second from `idx.end <= 2^(ADDRESS_WIDTH - off)` plus the no-wrap
/// condition: `idx.end * 2^off <= 2^ADDRESS_WIDTH ≤ 2^64`, so the `% 2^64`
/// is a no-op when the value is positive.
pub proof fn lemma_idx_times_pow2_bound<C: PageTableConfig>(start: Vaddr, end: Vaddr)
    requires
        start as int == (C::TOP_LEVEL_INDEX_RANGE_spec().start as int)
            * (pow2(pte_index_bit_offset_spec::<C::C>(C::NR_LEVELS()) as nat) as int),
        end as int == ((C::TOP_LEVEL_INDEX_RANGE_spec().end as int)
            * (pow2(pte_index_bit_offset_spec::<C::C>(C::NR_LEVELS()) as nat) as int)
            - 1) % 0x1_0000_0000_0000_0000int,
    ensures
        (start as int) < (pow2(C::ADDRESS_WIDTH() as nat) as int),
        (end as int) < (pow2(C::ADDRESS_WIDTH() as nat) as int),
        // For the end-of-range arithmetic ensures of `vaddr_range`:
        end as int == (C::TOP_LEVEL_INDEX_RANGE_spec().end as int)
            * (pow2(pte_index_bit_offset_spec::<C::C>(C::NR_LEVELS()) as nat) as int)
            - 1,
{
    axiom_top_level_index_range_bounds::<C>();
    let off = pte_index_bit_offset_spec::<C::C>(C::NR_LEVELS()) as nat;
    let aw = C::ADDRESS_WIDTH() as nat;
    let top_w = (aw as int - off as int) as nat;
    lemma_pow2_adds(top_w, off);
    lemma_pow2_pos(off);
    lemma_pow2_pos(top_w);
    lemma_pow2_pos(aw);
    // Constants for clarity.
    let i_start = C::TOP_LEVEL_INDEX_RANGE_spec().start as int;
    let i_end = C::TOP_LEVEL_INDEX_RANGE_spec().end as int;
    let p_off = pow2(off) as int;
    let p_top = pow2(top_w) as int;
    let p_aw = pow2(aw) as int;
    assert(p_top * p_off == p_aw);
    assert(start as int == i_start * p_off);
    assert(i_start < p_top);
    assert(p_off > 0);
    // start < p_top * p_off = p_aw.
    assert((start as int) < (p_top * p_off)) by (nonlinear_arith)
        requires
            start as int == i_start * p_off,
            i_start < p_top,
            p_off > 0;
    // end pre-wrap value.
    let e_pre = i_end * p_off;
    assert(i_end <= p_top);
    assert(e_pre <= p_top * p_off) by (nonlinear_arith)
        requires
            e_pre == i_end * p_off,
            i_end <= p_top,
            p_off > 0;
    // i_end > 0 — from `axiom_top_level_index_range_bounds`'s
    // `idx.start < idx.end` plus `idx.start >= 0` (usize).
    assert(i_end > 0);
    assert(e_pre > 0) by (nonlinear_arith)
        requires
            e_pre == i_end * p_off,
            i_end > 0,
            p_off > 0;
    assert(e_pre <= p_aw);
    // p_aw <= 2^64 — from `ADDRESS_WIDTH <= 64` plus monotonicity of pow2.
    if aw < 64 {
        vstd::arithmetic::power2::lemma_pow2_strictly_increases(aw, 64);
    }
    assert(pow2(64) == 0x1_0000_0000_0000_0000nat) by {
        vstd::arithmetic::power2::lemma2_to64();
    };
    assert(p_aw <= 0x1_0000_0000_0000_0000int);
    // No-wrap: 0 < e_pre <= 2^64, so (e_pre - 1) % 2^64 = e_pre - 1.
    assert(0 <= e_pre - 1);
    assert((e_pre - 1) < 0x1_0000_0000_0000_0000int);
    assert((e_pre - 1) % 0x1_0000_0000_0000_0000int == e_pre - 1) by (nonlinear_arith)
        requires 0 <= (e_pre - 1), (e_pre - 1) < 0x1_0000_0000_0000_0000int;
}

} // verus!
