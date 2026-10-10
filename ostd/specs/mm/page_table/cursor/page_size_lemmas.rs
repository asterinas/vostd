use vstd::{
    arithmetic::{
        div_mod::lemma_fundamental_div_mod,
        mul::{lemma_mul_inequality, lemma_mul_is_distributive_sub},
        power2::{lemma_pow2_adds, lemma_pow2_pos, pow2},
    },
    bits::lemma_usize_pow2_no_overflow,
    prelude::*,
};
use vstd_extra::{external::ilog2::lemma_usize_is_pow2_is_ilog2_pow2, prelude::*};

use crate::specs::arch::*;
use crate::specs::mm::page_table::{nr_pte_index_bits_spec, pte_index_bit_offset_spec};

use crate::arch::mm::PagingConsts;
use crate::mm::{
    KERNEL_VADDR_RANGE, Paddr, PagingConstsTrait, PagingLevel, Vaddr, nr_subpage_per_huge,
    page_size,
};

verus! {

/// A configured page size is the power of two at that level's index-bit offset.
pub proof fn lemma_page_size_is_pow2_pte_index_bit_offset<C: PagingConstsTrait>(level: PagingLevel)
    requires
        1 <= level <= C::NR_LEVELS() + 1,
    ensures
        pte_index_bit_offset_spec::<C>(level) < usize::BITS,
        pte_index_bit_offset_spec::<C>(level) == C::BASE_PAGE_SIZE().ilog2()
            + nr_pte_index_bits_spec::<C>() * (level - 1),
        0 < page_size::<C>(level) == pow2(pte_index_bit_offset_spec::<C>(level) as nat),
{
    C::lemma_paging_consts_properties();
    let bits = nr_pte_index_bits_spec::<C>();
    assert(usize::BITS <= usize::MAX) by (compute_only);
    lemma_usize_is_pow2_is_ilog2_pow2(C::BASE_PAGE_SIZE());
    lemma_usize_is_pow2_is_ilog2_pow2(nr_subpage_per_huge::<C>());
    assert(bits == (C::BASE_PAGE_SIZE() / C::PTE_SIZE()).ilog2());
    lemma_mul_inequality(level - 1, C::NR_LEVELS() as int, bits as int);
    assert(C::BASE_PAGE_SIZE().ilog2() + bits * (level - 1) <= C::ADDRESS_WIDTH());
    lemma_pow2_adds(C::BASE_PAGE_SIZE().ilog2() as nat, (bits * (level - 1)) as nat);
    lemma_usize_pow2_no_overflow(pte_index_bit_offset_spec::<C>(level) as nat);
}

/// Two levels that differ by `n` differ in offset by `n` index widths, which
/// multiplies the page size by the matching power of two.
pub proof fn lemma_page_size_ratio<C: PagingConstsTrait>(small: PagingLevel, large: PagingLevel)
    requires
        1 <= small <= large <= C::NR_LEVELS() + 1,
    ensures
        pte_index_bit_offset_spec::<C>(large) == pte_index_bit_offset_spec::<C>(small)
            + nr_pte_index_bits_spec::<C>() * (large - small),
        page_size::<C>(large) == page_size::<C>(small) * pow2(
            (nr_pte_index_bits_spec::<C>() * (large - small)) as nat,
        ),
{
    C::lemma_paging_consts_properties();
    lemma_page_size_is_pow2_pte_index_bit_offset::<C>(small);
    lemma_page_size_is_pow2_pte_index_bit_offset::<C>(large);
    let bits = nr_pte_index_bits_spec::<C>();
    let delta = (bits * (large - small)) as nat;
    lemma_mul_is_distributive_sub(bits as int, large as int, small as int);
    lemma_mul_is_distributive_sub(bits as int, large as int, 1);
    lemma_mul_is_distributive_sub(bits as int, small as int, 1);
    lemma_pow2_adds(pte_index_bit_offset_spec::<C>(small) as nat, delta);
    lemma_pow2_pos(delta);
}

/// A parent slot contains exactly one fanout of slots at the preceding level.
pub proof fn lemma_page_size_next<C: PagingConstsTrait>(level: PagingLevel)
    requires
        1 <= level <= C::NR_LEVELS(),
    ensures
        page_size::<C>((level + 1) as PagingLevel) == page_size::<C>(level) * nr_subpage_per_huge::<
            C,
        >(),
        0 < page_size::<C>(level) <= page_size::<C>((level + 1) as PagingLevel),
{
    C::lemma_paging_consts_properties();
    lemma_page_size_is_pow2_pte_index_bit_offset::<C>(level);
    lemma_page_size_is_pow2_pte_index_bit_offset::<C>((level + 1) as PagingLevel);
    let bits = nr_pte_index_bits_spec::<C>();
    lemma_usize_is_pow2_is_ilog2_pow2(nr_subpage_per_huge::<C>());
    lemma_mul_is_distributive_sub(bits as int, level as int, 1);
    lemma_pow2_adds(pte_index_bit_offset_spec::<C>(level) as nat, bits as nat);
    vstd::arithmetic::mul::lemma_mul_left_inequality(
        page_size::<C>(level) as int,
        1,
        nr_subpage_per_huge::<C>() as int,
    );
    vstd::arithmetic::mul::lemma_mul_basics(page_size::<C>(level) as int);
}

/// Configured page sizes divide the sizes of all higher-level slots.
pub proof fn lemma_page_size_divides<C: PagingConstsTrait>(small: PagingLevel, large: PagingLevel)
    requires
        1 <= small <= large <= C::NR_LEVELS() + 1,
    ensures
        0 < page_size::<C>(small) <= page_size::<C>(large),
        page_size::<C>(large) % page_size::<C>(small) == 0,
{
    C::lemma_paging_consts_properties();
    lemma_page_size_is_pow2_pte_index_bit_offset::<C>(small);
    lemma_page_size_is_pow2_pte_index_bit_offset::<C>(large);
    lemma_page_size_ratio::<C>(small, large);
    let delta = (nr_pte_index_bits_spec::<C>() * (large - small)) as nat;
    lemma_pow2_pos(delta);
    let a = page_size::<C>(small) as int;
    let ratio = pow2(delta) as int;
    vstd::arithmetic::div_mod::lemma_mod_multiples_basic(ratio, a);
    vstd::arithmetic::mul::lemma_mul_is_commutative(a, ratio);
    vstd::arithmetic::mul::lemma_mul_left_inequality(a, 1, ratio);
    vstd::arithmetic::mul::lemma_mul_basics(a);
}

/// The first configured level has the base-page size.
pub proof fn lemma_page_size_base<C: PagingConstsTrait>()
    ensures
        page_size::<C>(1) == C::BASE_PAGE_SIZE(),
{
    reveal(vstd::arithmetic::power::pow);
    vstd::arithmetic::power2::lemma_pow2(0);
    assert(pow2(0) == 1);
    vstd::arithmetic::mul::lemma_mul_basics(nr_pte_index_bits_spec::<C>() as int);
    vstd::arithmetic::mul::lemma_mul_basics(C::BASE_PAGE_SIZE() as int);
}

/// Every configured level has at least the base-page size.
pub proof fn lemma_page_size_ge_base<C: PagingConstsTrait>(level: PagingLevel)
    requires
        1 <= level <= C::NR_LEVELS() + 1,
    ensures
        C::BASE_PAGE_SIZE() <= page_size::<C>(level),
{
    lemma_page_size_base::<C>();
    lemma_page_size_divides::<C>(1, level);
}

/// `page_size` is monotone in the level.
pub proof fn lemma_page_size_monotone<C: PagingConstsTrait>(l1: PagingLevel, l2: PagingLevel)
    requires
        1 <= l1 <= l2 <= C::NR_LEVELS() + 1,
    ensures
        page_size::<C>(l1) <= page_size::<C>(l2),
{
    lemma_page_size_divides::<C>(l1, l2);
}

/// A level's page size divided by the base page size multiplies back exactly.
pub proof fn lemma_page_size_div_mul_eq<C: PagingConstsTrait>(level: PagingLevel)
    requires
        1 <= level <= C::NR_LEVELS() + 1,
    ensures
        (page_size::<C>(level) / C::BASE_PAGE_SIZE()) * C::BASE_PAGE_SIZE() == page_size::<C>(
            level,
        ),
{
    lemma_page_size_base::<C>();
    lemma_page_size_divides::<C>(1, level);
    lemma_fundamental_div_mod(page_size::<C>(level) as int, page_size::<C>(1) as int);
}

/// When `va` is aligned to `page_size(large_level)` and `level <= large_level`, then
/// `va` is aligned to `page_size(level)`.
pub proof fn lemma_va_align_page_size<C: PagingConstsTrait>(va: Vaddr, level: PagingLevel)
    requires
        1 <= level <= C::NR_LEVELS() + 1,
        va % C::BASE_PAGE_SIZE() == 0,
        exists|large_level: PagingLevel|
            1 <= large_level <= C::NR_LEVELS() + 1 && level <= large_level && va % page_size::<C>(
                large_level,
            ) == 0,
    ensures
        va % page_size::<C>(level) == 0,
{
    let large_level: PagingLevel = choose|l: PagingLevel|
        1 <= l <= C::NR_LEVELS() + 1 && level <= l && va % page_size::<C>(l) == 0;
    if level == 1nat {
        lemma_page_size_base::<C>();
    } else {
        let ps_l = page_size::<C>(level) as int;
        let ps_ll = page_size::<C>(large_level) as int;
        lemma_page_size_divides::<C>(level, large_level);
        let k = ps_ll / ps_l;
        vstd::arithmetic::div_mod::lemma_div_non_zero(ps_ll, ps_l);
        lemma_fundamental_div_mod(ps_ll, ps_l);
        vstd::arithmetic::div_mod::lemma_mod_mod(va as int, ps_l, k);
        assert(va as int % ps_l == 0);
    }
}

/// Special case for level 1: base-page alignment is level-1 slot alignment.
pub proof fn lemma_va_align_page_size_level_1<C: PagingConstsTrait>(va: Vaddr)
    requires
        va % C::BASE_PAGE_SIZE() == 0,
    ensures
        va % page_size::<C>(1) == 0,
{
    lemma_page_size_base::<C>();
}

/// Concrete page sizes for the x86_64 `PagingConsts`, kept for numeric automation.
pub proof fn lemma_page_size_spec_values()
    ensures
        page_size::<PagingConsts>(1) == 4096,
        page_size::<PagingConsts>(2) == 2097152,
        page_size::<PagingConsts>(3) == 1073741824,
        page_size::<PagingConsts>(4) == 549755813888,
        page_size::<PagingConsts>(5) == 281474976710656,
{
    lemma_page_size_base::<PagingConsts>();
    vstd_extra::external::ilog2::lemma_usize_ilog2_to32();
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma2_to64_rest();
    vstd::bits::lemma_usize_pow2_no_overflow(48);
}

/// Used by `Entry::split_if_mapped_huge` to instantiate the 4KB sub-page forall
/// invariant at the `i`-th sub-frame's slot.
pub proof fn lemma_split_sub_page_big_j(pa: Paddr, level: PagingLevel, i: usize) -> (big_j: usize)
    requires
        2 <= level <= NR_LEVELS,
        0 < i < NR_ENTRIES,
    ensures
        0 < big_j < page_size::<PagingConsts>(level) / PAGE_SIZE,
        pa + i * page_size::<PagingConsts>((level - 1) as PagingLevel) == pa + big_j * PAGE_SIZE,
        big_j == i * (page_size::<PagingConsts>((level - 1) as PagingLevel) / PAGE_SIZE),
{
    PagingConsts::lemma_paging_consts_properties();
    let sub_pages_per_entry: int = (page_size::<PagingConsts>((level - 1) as PagingLevel)
        / PAGE_SIZE) as int;
    let big_j_int: int = i * sub_pages_per_entry;
    lemma_page_size_spec_values();
    lemma_page_size_div_mul_eq::<PagingConsts>((level - 1) as PagingLevel);
    lemma_page_size_div_mul_eq::<PagingConsts>(level);
    lemma_page_size_next::<PagingConsts>((level - 1) as PagingLevel);
    crate::arch::mm::lemma_nr_subpage_per_huge_eq_nr_entries();
    vstd::arithmetic::mul::lemma_mul_strictly_positive(i as int, sub_pages_per_entry);
    vstd::arithmetic::mul::lemma_mul_strict_inequality(
        i as int,
        NR_ENTRIES as int,
        sub_pages_per_entry,
    );
    vstd::arithmetic::mul::lemma_mul_is_associative(
        NR_ENTRIES as int,
        sub_pages_per_entry,
        PAGE_SIZE as int,
    );
    vstd::arithmetic::div_mod::lemma_div_by_multiple(
        NR_ENTRIES as int * sub_pages_per_entry,
        PAGE_SIZE as int,
    );
    vstd::arithmetic::mul::lemma_mul_is_associative(
        i as int,
        sub_pages_per_entry,
        PAGE_SIZE as int,
    );
    big_j_int as usize
}

/// For any VA within the kernel virtual address range and any page level,
/// `va + len` does not overflow usize.
pub proof fn lemma_va_plus_page_size_no_overflow(va: Vaddr, len: usize)
    requires
        va + len <= KERNEL_VADDR_RANGE.end,
    ensures
        va + len <= usize::MAX,
{
    assert(KERNEL_VADDR_RANGE.end == 0xffff_ffff_ffff_0000usize) by (compute_only);
}

} // verus!
