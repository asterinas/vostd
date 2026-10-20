// SPDX-License-Identifier: MPL-2.0
//! Bounded-arithmetic proofs for `vaddr_range`'s body.
//!
//! Factored into a leaf module because the `nonlinear_arith` tactic
//! triggers a Verus internal panic when used in `page_table/mod.rs`
//! alongside `largest_pages` (which has an `impl Iterator` return type).
//! Same workaround pattern as the older `vaddr_range_bv_lemmas`.
use vstd::{
    arithmetic::{
        div_mod::{lemma_mod_bound, lemma_mod_breakdown, lemma_mod_decreases},
        power2::{lemma_pow2_adds, lemma_pow2_pos, lemma_pow2_strictly_increases, pow2},
    },
    prelude::*,
};
use vstd_extra::arithmetic::nat_align_down;

use crate::specs::mm::page_table::*;

use crate::mm::{
    PagingConstsTrait, PagingLevel, Vaddr, nr_subpage_per_huge, page_size,
    page_table::PageTableConfig,
};

verus! {

/// Derives the sign-extension mask and its width from the paging constants.
pub proof fn lemma_leading_bits_properties<C: PageTableConfig>()
    ensures
        page_table_coverage_start_spec::<C>() == leading_bits_spec::<C>() * pow2(
            nr_page_table_coverage_bits_spec::<C>() as nat,
        ),
        page_table_coverage_start_spec::<C>() + pow2(nr_page_table_coverage_bits_spec::<C>() as nat)
            <= pow2(usize::BITS as nat),
        C::VA_SIGN_EXT() && (C::TOP_LEVEL_INDEX_RANGE().start * pow2(
            pte_index_bit_offset_spec::<C>(C::NR_LEVELS()) as nat,
        ) / pow2((C::ADDRESS_WIDTH() - 1) as nat) as int) % 2 == 1
            ==> page_table_coverage_start_spec::<C>() == pow2(usize::BITS as nat) - pow2(
            C::ADDRESS_WIDTH() as nat,
        ),
        leading_bits_spec::<C>() < pow2(
            (usize::BITS - nr_page_table_coverage_bits_spec::<C>()) as nat,
        ),
{
    C::lemma_paging_consts_properties();
    let bits = nr_page_table_coverage_bits_spec::<C>() as nat;
    let width = C::ADDRESS_WIDTH() as nat;
    lemma_pow2_adds((usize::BITS - bits) as nat, bits);
    lemma_pow2_adds((width - bits) as nat, bits);
    lemma_pow2_pos((width - bits) as nat);
    vstd::arithmetic::power2::lemma_pow2_strictly_increases(
        (width - bits) as nat,
        (usize::BITS - bits) as nat,
    );
    vstd::layout::unsigned_int_max_values();
    if bits < usize::BITS {
        if bits > 0 {
            vstd::arithmetic::power2::lemma_pow2_strictly_increases(
                (usize::BITS - bits) as nat,
                usize::BITS as nat,
            );
        }
    }
    assert((pow2((usize::BITS - bits) as nat) - pow2((width - bits) as nat)) * pow2(bits) == pow2(
        usize::BITS as nat,
    ) - pow2(width)) by (nonlinear_arith)
        requires
            pow2((usize::BITS - bits) as nat) * pow2(bits) == pow2(usize::BITS as nat),
            pow2((width - bits) as nat) * pow2(bits) == pow2(width),
    ;
    assert(leading_bits_spec::<C>() * pow2(bits) + pow2(bits) <= pow2(usize::BITS as nat))
        by (nonlinear_arith)
        requires
            leading_bits_spec::<C>() < pow2((usize::BITS - bits) as nat),
            pow2(bits) > 0,
            pow2((usize::BITS - bits) as nat) * pow2(bits) == pow2(usize::BITS as nat),
    ;
}

/// Managed bounds preserve their mathematical values and match the inclusive range model.
pub proof fn lemma_page_table_managed_bounds<C: PageTableConfig>()
    ensures
        page_table_managed_start_spec::<C>() == page_table_coverage_start_spec::<C>()
            + C::TOP_LEVEL_INDEX_RANGE().start * page_size::<C>(C::NR_LEVELS()),
        page_table_managed_start_spec::<C>() < page_table_managed_end_spec::<C>() <= usize::MAX + 1,
        vaddr_range_spec::<C>().end + 1 == page_table_managed_end_spec::<C>(),
{
    C::lemma_paging_consts_properties();
    C::lemma_page_table_config_constant_properties();
    lemma_leading_bits_properties::<C>();
    lemma_page_size_is_pow2_pte_index_bit_offset::<C>(C::NR_LEVELS());
    let off = pte_index_bit_offset_spec::<C>(C::NR_LEVELS()) as nat;
    let aw = C::ADDRESS_WIDTH() as nat;
    lemma_pow2_adds((aw - off) as nat, off);
    lemma_pow2_strictly_increases(aw, usize::BITS as nat);
    vstd::layout::unsigned_int_max_values();
    let base = page_table_coverage_start_spec::<C>() as int;
    let size = page_size::<C>(C::NR_LEVELS()) as int;
    let start = base + C::TOP_LEVEL_INDEX_RANGE().start * size;
    let end = page_table_managed_end_spec::<C>();
    assert(0 <= start < end <= usize::MAX + 1) by (nonlinear_arith)
        requires
            0 <= base,
            base == 0 || base == pow2(usize::BITS as nat) - pow2(aw),
            pow2(aw) < pow2(usize::BITS as nat),
            pow2(usize::BITS as nat) == usize::MAX + 1,
            0 < size,
            size == pow2(off),
            pow2((aw - off) as nat) * pow2(off) == pow2(aw),
            0 <= C::TOP_LEVEL_INDEX_RANGE().start < C::TOP_LEVEL_INDEX_RANGE().end <= pow2(
                (aw - off) as nat,
            ),
            start == base + C::TOP_LEVEL_INDEX_RANGE().start * size,
            end == base + C::TOP_LEVEL_INDEX_RANGE().end * size,
    ;
}

/// Managed address bounds are equivalent to root-index bounds when the upper address bits match.
/// The current root slot ends within the managed range whenever the address is inside it.
pub proof fn lemma_page_table_managed_index_bounds<C: PageTableConfig>(va: Vaddr)
    requires
        vaddr_leading_part_spec::<C>(va) == page_table_coverage_start_spec::<C>(),
    ensures
        (page_table_managed_start_spec::<C>() <= va) == (C::TOP_LEVEL_INDEX_RANGE().start
            <= pte_index_spec::<C>(va, C::NR_LEVELS())),
        (va < page_table_managed_end_spec::<C>()) == (pte_index_spec::<C>(va, C::NR_LEVELS())
            < C::TOP_LEVEL_INDEX_RANGE().end),
        va < page_table_managed_end_spec::<C>() ==> nat_align_down(
            va as nat,
            page_size::<C>(C::NR_LEVELS()) as nat,
        ) + page_size::<C>(C::NR_LEVELS()) <= page_table_managed_end_spec::<C>(),
{
    C::lemma_paging_consts_properties();
    lemma_page_table_managed_bounds::<C>();
    let top = C::NR_LEVELS();
    lemma_page_size_next::<C>(top);
    lemma_vaddr_leading_part_is_align_down::<C>(va);
    lemma_pte_index_spec_is_div_mod::<C>(va, top);
    let size = page_size::<C>(top) as int;
    let body = page_size::<C>((top + 1) as PagingLevel) as int;
    let fanout = nr_subpage_per_huge::<C>() as int;
    lemma_mod_decreases(va as nat, body as nat);
    lemma_mod_breakdown(va as int, size, fanout);
    let base = page_table_coverage_start_spec::<C>() as int;
    let index = pte_index_spec::<C>(va, top) as int;
    assert({
        &&& base + index * size == va - va as int % size
        &&& base + index * size <= va < base + (index + 1) * size
    }) by (nonlinear_arith)
        requires
            base == va - va as int % body,
            va as int % body == size * index + va as int % size,
            0 <= va as int % size < size,
    ;
    assert({
        &&& (page_table_managed_start_spec::<C>() <= va) == (C::TOP_LEVEL_INDEX_RANGE().start
            <= index)
        &&& (va < page_table_managed_end_spec::<C>()) == (index < C::TOP_LEVEL_INDEX_RANGE().end)
        &&& (va < page_table_managed_end_spec::<C>() ==> base + index * size + size
            <= page_table_managed_end_spec::<C>())
    }) by (nonlinear_arith)
        requires
            size > 0,
            base + index * size <= va < base + (index + 1) * size,
            page_table_managed_start_spec::<C>() == base + C::TOP_LEVEL_INDEX_RANGE().start * size,
            page_table_managed_end_spec::<C>() == base + C::TOP_LEVEL_INDEX_RANGE().end * size,
    ;
}

/// Facts needed to turn `idx.start << offset` into
/// `idx.start * 2^offset` for `pt_va_range_start`.
pub proof fn lemma_pt_va_range_start_shift_facts<C: PageTableConfig>(
    idx_start: usize,
    offset: usize,
)
    requires
        idx_start == C::TOP_LEVEL_INDEX_RANGE().start,
        offset == pte_index_bit_offset_spec::<C>(C::NR_LEVELS()),
    ensures
        offset < usize::BITS,
        idx_start * pow2(offset as nat) <= usize::MAX,
        offset == pte_index_bit_offset_spec::<C>(C::NR_LEVELS()),
{
    C::lemma_paging_consts_properties();
    C::lemma_page_table_config_constant_properties();
    vstd::layout::unsigned_int_max_values();

    let off = pte_index_bit_offset_spec::<C>(C::NR_LEVELS()) as nat;
    let aw = C::ADDRESS_WIDTH() as nat;
    let top_w = (aw - off) as nat;
    lemma_pow2_adds(top_w, off);
    lemma_pow2_pos(off);

    let i_start = C::TOP_LEVEL_INDEX_RANGE().start as int;
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
        idx_end == C::TOP_LEVEL_INDEX_RANGE().end,
        offset == pte_index_bit_offset_spec::<C>(C::NR_LEVELS()),
    ensures
        offset < usize::BITS,
        idx_end * pow2(offset as nat) <= usize::MAX,
        0 < idx_end * pow2(offset as nat),
        offset == pte_index_bit_offset_spec::<C>(C::NR_LEVELS()),
{
    C::lemma_paging_consts_properties();
    C::lemma_page_table_config_constant_properties();
    lemma_pow2_pos(offset as nat);

    let i_end = C::TOP_LEVEL_INDEX_RANGE().end as int;
    let p_off = pow2(offset as nat) as int;
    assert(i_end * p_off > 0) by (nonlinear_arith)
        requires
            i_end > 0,
            p_off > 0,
    ;
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
        start == C::TOP_LEVEL_INDEX_RANGE().start * (pow2(
            pte_index_bit_offset_spec::<C>(C::NR_LEVELS()) as nat,
        ) as int),
        end == (C::TOP_LEVEL_INDEX_RANGE().end * (pow2(
            pte_index_bit_offset_spec::<C>(C::NR_LEVELS()) as nat,
        ) as int) - 1) % 0x1_0000_0000_0000_0000int,
    ensures
        start < pow2(C::ADDRESS_WIDTH() as nat),
        end < pow2(C::ADDRESS_WIDTH() as nat),
        // For the end-of-range arithmetic ensures of `vaddr_range`:
        end == C::TOP_LEVEL_INDEX_RANGE().end * pow2(
            pte_index_bit_offset_spec::<C>(C::NR_LEVELS()) as nat,
        ) - 1,
{
    C::lemma_paging_consts_properties();
    C::lemma_page_table_config_constant_properties();
    let off = pte_index_bit_offset_spec::<C>(C::NR_LEVELS()) as nat;
    let aw = C::ADDRESS_WIDTH() as nat;
    let top_w = (aw - off) as nat;
    lemma_pow2_adds(top_w, off);
    lemma_pow2_pos(off);
    // Constants for clarity.
    let i_start = C::TOP_LEVEL_INDEX_RANGE().start as int;
    let i_end = C::TOP_LEVEL_INDEX_RANGE().end as int;
    let p_off = pow2(off) as int;
    let p_top = pow2(top_w) as int;
    let p_aw = pow2(aw) as int;
    // start < p_top * p_off = p_aw.
    assert(start < (p_top * p_off)) by (nonlinear_arith)
        requires
            start == i_start * p_off,
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
    // i_end > 0 — from `lemma_page_table_config_constant_properties`'s
    // `idx.start < idx.end` plus `idx.start >= 0` (usize).
    assert(e_pre > 0) by (nonlinear_arith)
        requires
            e_pre == i_end * p_off,
            i_end > 0,
            p_off > 0,
    ;
}

} // verus!
