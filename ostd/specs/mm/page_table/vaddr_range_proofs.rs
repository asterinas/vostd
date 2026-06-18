// SPDX-License-Identifier: MPL-2.0
//! Bounded-arithmetic proofs for `vaddr_range`'s body.
//!
//! Factored into a leaf module because the `nonlinear_arith` tactic
//! triggers a Verus internal panic when used in `page_table/mod.rs`
//! alongside `largest_pages` (which has an `impl Iterator` return type).
//! Same workaround pattern as the older `vaddr_range_bv_lemmas`.
use vstd::arithmetic::power2::{lemma_pow2_adds, lemma_pow2_pos, pow2};
use vstd::prelude::*;

use crate::mm::page_table::{PageTableConfig, pte_index_bit_offset_spec};
use crate::mm::{PagingConstsTrait, Vaddr};

verus! {

/// Facts needed to turn `idx.start << offset` into
/// `idx.start * 2^offset` for `pt_va_range_start`.
pub proof fn lemma_pt_va_range_start_shift_facts<C: PageTableConfig>(
    idx_start: usize,
    offset: usize,
)
    requires
        idx_start == C::TOP_LEVEL_INDEX_RANGE_spec().start,
        offset == pte_index_bit_offset_spec::<C>(C::NR_LEVELS()),
    ensures
        offset < usize::BITS,
        idx_start * pow2(offset as nat) <= usize::MAX,
        offset == pte_index_bit_offset_spec::<C>(C::NR_LEVELS()),
{
    C::lemma_page_table_config_constant_requirements();
    vstd::layout::unsigned_int_max_values();

    let off = pte_index_bit_offset_spec::<C>(C::NR_LEVELS()) as nat;
    let aw = C::ADDRESS_WIDTH() as nat;
    let top_w = (aw as int - off as int) as nat;
    lemma_pow2_adds(top_w, off);
    lemma_pow2_pos(off);
    lemma_pow2_pos(top_w);
    lemma_pow2_pos(aw);

    let i_start = C::TOP_LEVEL_INDEX_RANGE_spec().start as int;
    let p_off = pow2(off) as int;
    let p_top = pow2(top_w) as int;

    assert(i_start * p_off < p_top * p_off) by (nonlinear_arith)
        requires
            i_start < p_top,
            p_off > 0,
    ;

    if aw < 64 {
        vstd::arithmetic::power2::lemma_pow2_strictly_increases(aw, 64);
    }
}

/// Facts needed to turn `idx.end << offset` into
/// `idx.end * 2^offset` for `pt_va_range_end`.
pub proof fn lemma_pt_va_range_end_shift_facts<C: PageTableConfig>(idx_end: usize, offset: usize)
    requires
        idx_end == C::TOP_LEVEL_INDEX_RANGE_spec().end,
        offset == pte_index_bit_offset_spec::<C>(C::NR_LEVELS()),
    ensures
        offset < usize::BITS,
        idx_end * pow2(offset as nat) <= usize::MAX,
        0 < idx_end * pow2(offset as nat),
        offset == pte_index_bit_offset_spec::<C>(C::NR_LEVELS()),
{
    C::lemma_page_table_config_constant_requirements();
    lemma_pow2_pos(offset as nat);

    let i_end = C::TOP_LEVEL_INDEX_RANGE_spec().end as int;
    let p_off = pow2(offset as nat) as int;
    assert(i_end * p_off > 0) by (nonlinear_arith)
        requires
            i_end > 0,
            p_off > 0,
    ;
}

/// Connect `wrapping_sub(1)` to the modulo end-of-range spec after the
/// shift result is known to be non-zero.
pub proof fn lemma_pt_va_range_end_wrapping_sub<C: PageTableConfig>(
    idx_end: usize,
    offset: usize,
    shifted: usize,
    ret: usize,
)
    requires
        idx_end == C::TOP_LEVEL_INDEX_RANGE_spec().end,
        offset as int == pte_index_bit_offset_spec::<C>(C::NR_LEVELS()),
        shifted == idx_end * pow2(offset as nat),
        ret == vstd::wrapping::usize_specs::wrapping_sub(shifted, 1usize),
    ensures
        ret as int == (C::TOP_LEVEL_INDEX_RANGE_spec().end as int * pow2(
            pte_index_bit_offset_spec::<C>(C::NR_LEVELS()) as nat,
        ) as int - 1) % 0x1_0000_0000_0000_0000int,
{
    lemma_pt_va_range_end_shift_facts::<C>(idx_end, offset);
    vstd::layout::unsigned_int_max_values();
}

/// Facts needed to connect `(va >> (ADDRESS_WIDTH - 1)) & 1` with the
/// arithmetic bit-test specification.
pub proof fn lemma_sign_bit_facts<C: PageTableConfig>(
    va: Vaddr,
    address_width: usize,
    shift: usize,
    shifted: usize,
    bit: usize,
)
    requires
        address_width == C::ADDRESS_WIDTH(),
        shift == address_width - 1,
        shifted == va >> shift,
        bit == shifted & 1usize,
    ensures
        (bit != 0) == ((va as int / pow2((C::ADDRESS_WIDTH() - 1) as nat) as int) % 2 == 1),
{
    C::lemma_page_table_config_constant_requirements();

    vstd::bits::lemma_usize_shr_is_div(va, shift);
    vstd::bits::lemma_usize_low_bits_mask_is_mod(shifted, 1);
    vstd::bits::lemma_low_bits_mask_values();
    vstd::arithmetic::power2::lemma2_to64();
}

/// Two-in-one: `start = idx.start * 2^off < 2^ADDRESS_WIDTH` and
/// `end = (idx.end * 2^off - 1) % 2^64 < 2^ADDRESS_WIDTH`.
///
/// The first follows from `idx.start < 2^(ADDRESS_WIDTH - off)`. The
/// second from `idx.end <= 2^(ADDRESS_WIDTH - off)` plus the no-wrap
/// condition: `idx.end * 2^off <= 2^ADDRESS_WIDTH ≤ 2^64`, so the `% 2^64`
/// is a no-op when the value is positive.
pub proof fn lemma_idx_times_pow2_bound<C: PageTableConfig>(start: Vaddr, end: Vaddr)
    requires
        start as int == (C::TOP_LEVEL_INDEX_RANGE_spec().start as int) * (pow2(
            pte_index_bit_offset_spec::<C>(C::NR_LEVELS()) as nat,
        ) as int),
        end as int == ((C::TOP_LEVEL_INDEX_RANGE_spec().end as int) * (pow2(
            pte_index_bit_offset_spec::<C>(C::NR_LEVELS()) as nat,
        ) as int) - 1) % 0x1_0000_0000_0000_0000int,
    ensures
        (start as int) < (pow2(C::ADDRESS_WIDTH() as nat) as int),
        (end as int) < (pow2(C::ADDRESS_WIDTH() as nat) as int),
        // For the end-of-range arithmetic ensures of `vaddr_range`:
        end as int == (C::TOP_LEVEL_INDEX_RANGE_spec().end as int) * (pow2(
            pte_index_bit_offset_spec::<C>(C::NR_LEVELS()) as nat,
        ) as int) - 1,
{
    C::lemma_page_table_config_constant_requirements();
    let off = pte_index_bit_offset_spec::<C>(C::NR_LEVELS()) as nat;
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
    // start < p_top * p_off = p_aw.
    assert((start as int) < (p_top * p_off)) by (nonlinear_arith)
        requires
            start as int == i_start * p_off,
            i_start < p_top,
            p_off > 0,
    ;
    // end pre-wrap value.
    let e_pre = i_end * p_off;
    assert(e_pre <= p_top * p_off) by (nonlinear_arith)
        requires
            e_pre == i_end * p_off,
            i_end <= p_top,
            p_off > 0,
    ;
    // i_end > 0 — from `lemma_page_table_config_constant_requirements`'s
    // `idx.start < idx.end` plus `idx.start >= 0` (usize).
    assert(e_pre > 0) by (nonlinear_arith)
        requires
            e_pre == i_end * p_off,
            i_end > 0,
            p_off > 0,
    ;
}

} // verus!
