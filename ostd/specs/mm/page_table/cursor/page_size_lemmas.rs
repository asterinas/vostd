use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;

use crate::mm::page_table::{page_size, page_size_spec};
use crate::mm::PagingLevel;
use crate::mm::{nr_subpage_per_huge, Paddr, Vaddr, MAX_PADDR};
use crate::specs::arch::mm::{KERNEL_VADDR_RANGE, NR_LEVELS, PAGE_SIZE};
use crate::specs::arch::paging_consts::PagingConsts;

verus! {

// ─── page_size_spec(1) ──────────────────────────────────────────────────────
/// page_size_spec(1) == PAGE_SIZE.
/// Both sides equal PAGE_SIZE * pow2(0) = PAGE_SIZE * 1 = PAGE_SIZE,
/// because the exponent ilog2 * (1 - 1) = ilog2 * 0 = 0.
pub proof fn lemma_page_size_spec_level1()
    ensures
        page_size_spec(1) == PAGE_SIZE,
{
    vstd::arithmetic::mul::lemma_mul_by_zero_is_zero(
        nr_subpage_per_huge::<PagingConsts>().ilog2() as int,
    );
    broadcast use vstd::arithmetic::power2::lemma_pow2;
    vstd::arithmetic::power::lemma_pow0(2int);
}

// ─── VA alignment ────────────────────────────────────────────────────────────
/// When `va` is aligned to `page_size(large_level)` and `level <= large_level` (so
/// page_size(level) divides page_size(large_level)), then `va` is aligned to page_size(level).
/// Note: page_size(level) for level >= 1 is always a multiple of PAGE_SIZE.
pub proof fn lemma_va_align_page_size(va: Vaddr, level: PagingLevel)
    requires
        1 <= level <= NR_LEVELS + 1,
        va % PAGE_SIZE == 0,
        exists|large_level: PagingLevel|
            1 <= large_level <= NR_LEVELS + 1 && level <= large_level && va % page_size_spec(
                large_level,
            ) == 0,
    ensures
        va % page_size_spec(level) == 0,
{
    let large_level: PagingLevel = choose|l: PagingLevel|
        1 <= l <= NR_LEVELS + 1 && level <= l && va % page_size_spec(l) == 0;
    if level == 1nat {
        lemma_page_size_spec_level1();
    } else {
        let ps_l = page_size_spec(level) as int;
        let ps_ll = page_size_spec(large_level) as int;
        lemma_page_size_ge_page_size(level);
        lemma_page_size_ge_page_size(large_level);
        lemma_page_size_divides(level, large_level);
        assert(ps_ll >= ps_l) by {
            if ps_ll < ps_l {
                vstd::arithmetic::div_mod::lemma_small_mod(ps_ll as nat, ps_l as nat);
            }
        };
        let k = ps_ll / ps_l;
        vstd::arithmetic::div_mod::lemma_div_non_zero(ps_ll, ps_l);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ps_ll, ps_l);
        vstd::arithmetic::div_mod::lemma_mod_mod(va as int, ps_l, k);
        assert(va as int % ps_l == 0);
    }
}

/// Special case for level 1: page_size_spec(1) == PAGE_SIZE, so va % PAGE_SIZE == 0 implies
/// va % page_size_spec(1) == 0.
pub proof fn lemma_va_align_page_size_level_1(va: Vaddr)
    requires
        va % PAGE_SIZE == 0,
    ensures
        va % page_size_spec(1) == 0,
{
    lemma_page_size_spec_level1();
}

/// For any level in [1, NR_LEVELS], page_size(level) is a multiple of PAGE_SIZE.
pub proof fn lemma_page_size_multiple_of_page_size(level: PagingLevel)
    requires
        1 <= level <= NR_LEVELS,
    ensures
        page_size_spec(level) % PAGE_SIZE == 0,
{
    lemma_page_size_spec_values();
}

/// For any level in [1, NR_LEVELS+1], the page size is at least PAGE_SIZE.
/// This follows from page_size(level) = PAGE_SIZE * pow2((ilog2 * (level-1)) as nat)
/// with pow2(k) >= 1 for all k >= 0.
#[verifier::spinoff_prover]
pub proof fn lemma_page_size_ge_page_size(level: PagingLevel)
    requires
        1 <= level <= NR_LEVELS + 1,
    ensures
        page_size(level) >= PAGE_SIZE,
{
    lemma_page_size_spec_values();
}

/// `page_size` is monotone in the level: a higher level has a larger or equal page size.
/// This follows from page_size(level) = PAGE_SIZE * 512^(level-1); incrementing level multiplies
/// by 512, so page_size(l+1) = 512 * page_size(l) > page_size(l).
pub proof fn lemma_page_size_monotone(l1: PagingLevel, l2: PagingLevel)
    requires
        1 <= l1 <= NR_LEVELS + 1,
        1 <= l2 <= NR_LEVELS + 1,
        l1 <= l2,
    ensures
        page_size(l1) <= page_size(l2),
{
    if l1 != l2 {
        let ps1 = page_size(l1);
        let ps2 = page_size(l2);

        lemma_page_size_ge_page_size(l1);
        lemma_page_size_ge_page_size(l2);
        lemma_page_size_divides(l1, l2);

        assert(ps1 <= ps2) by {
            if ps2 < ps1 {
                vstd::arithmetic::div_mod::lemma_small_mod(ps2 as nat, ps1 as nat);
            }
        };
    }
}

pub proof fn lemma_page_size_spec_values()
    ensures
        page_size_spec(1) == 4096,
        page_size_spec(2) == 2097152,
        page_size_spec(3) == 1073741824,
        page_size_spec(4) == 549755813888,
        page_size_spec(5) == 281474976710656,
{
    lemma_page_size_spec_level1();
    vstd_extra::external::ilog2::lemma_usize_ilog2_to32();
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma2_to64_rest();
    vstd::bits::lemma_usize_pow2_no_overflow(48);
}

/// `(page_size(level) / PAGE_SIZE) * PAGE_SIZE == page_size(level)` for level in [1, NR_LEVELS+1].
/// page_size(level) is divisible by PAGE_SIZE so the integer division is exact.
pub proof fn lemma_page_size_div_mul_eq(level: PagingLevel)
    requires
        1 <= level <= NR_LEVELS + 1,
    ensures
        (page_size_spec(level) / PAGE_SIZE) * PAGE_SIZE == page_size_spec(level),
{
    lemma_page_size_spec_values();
}

/// `NR_ENTRIES * page_size(level - 1) == page_size(level)` for level in [2, NR_LEVELS + 1].
/// A huge page at `level` consists of NR_ENTRIES sub-pages each of size `page_size(level - 1)`.
pub proof fn lemma_nr_entries_times_sub_page_size(level: PagingLevel)
    requires
        2 <= level <= NR_LEVELS + 1,
    ensures
        crate::specs::arch::mm::NR_ENTRIES as int * page_size_spec((level - 1) as PagingLevel) as int
            == page_size_spec(level) as int,
{
    lemma_page_size_spec_values();
    crate::specs::arch::paging_consts::lemma_nr_subpage_per_huge_eq_nr_entries();
}

/// Used by `Entry::split_if_mapped_huge` to instantiate the 4KB sub-page
/// forall invariant at the `i`-th sub-frame's slot.
///
/// For a huge frame at paddr `pa` with level `level > 1`, the `i`-th sub-frame
/// lives at `small_pa = pa + i * page_size(level - 1)`. In units of 4KB sub-pages
/// that's `big_j = i * (page_size(level - 1) / PAGE_SIZE)`. This lemma discharges
/// the arithmetic facts needed at the call site:
///   * `0 < big_j < page_size(level) / PAGE_SIZE` so the sub-page forall
///     (quantified over `j ∈ (0, page_size(level) / PAGE_SIZE)`) fires.
///   * `small_pa == pa + big_j * PAGE_SIZE` so the forall trigger matches.
pub proof fn lemma_split_sub_page_big_j(
    pa: Paddr,
    level: PagingLevel,
    i: usize,
) -> (big_j: usize)
    requires
        2 <= level <= NR_LEVELS,
        0 < i < crate::specs::arch::mm::NR_ENTRIES,
    ensures
        0 < big_j < page_size_spec(level) / PAGE_SIZE,
        (pa + i * page_size_spec((level - 1) as PagingLevel)) as int
            == pa as int + big_j as int * PAGE_SIZE as int,
        big_j as int == i as int * (page_size_spec((level - 1) as PagingLevel) / PAGE_SIZE) as int,
{
    let sub_pages_per_entry: int =
        (page_size_spec((level - 1) as PagingLevel) / PAGE_SIZE) as int;
    let big_j_int: int = i as int * sub_pages_per_entry;
    lemma_page_size_spec_values();
    lemma_page_size_div_mul_eq((level - 1) as PagingLevel);
    lemma_page_size_div_mul_eq(level);
    lemma_nr_entries_times_sub_page_size(level);
    vstd::arithmetic::mul::lemma_mul_strictly_positive(
        i as int, sub_pages_per_entry);
    vstd::arithmetic::mul::lemma_mul_strict_inequality(
        i as int, crate::specs::arch::mm::NR_ENTRIES as int, sub_pages_per_entry);
    vstd::arithmetic::mul::lemma_mul_is_associative(
        crate::specs::arch::mm::NR_ENTRIES as int, sub_pages_per_entry, PAGE_SIZE as int);
    vstd::arithmetic::div_mod::lemma_div_by_multiple(
        crate::specs::arch::mm::NR_ENTRIES as int * sub_pages_per_entry, PAGE_SIZE as int);
    vstd::arithmetic::mul::lemma_mul_is_associative(
        i as int, sub_pages_per_entry, PAGE_SIZE as int);
    big_j_int as usize
}

/// page_size(l2) is divisible by page_size(l1) when l1 <= l2.
/// This holds because page_size(l) = PAGE_SIZE * 512^(l-1), so
/// page_size(l2) / page_size(l1) = 512^(l2-l1), which is a positive integer.
pub proof fn lemma_page_size_divides(l1: PagingLevel, l2: PagingLevel)
    requires
        1 <= l1 <= l2 <= NR_LEVELS + 1,
    ensures
        page_size_spec(l2) % page_size_spec(l1) == 0,
{
    lemma_page_size_spec_values();
}

/// For any valid physical address `pa < MAX_PADDR` and page level, pa + page_size(level)
/// does not overflow usize. This holds because MAX_PADDR = 2^31 and page sizes are at
/// most 2^39 (NR_LEVELS = 4), so pa + size < 2^40 << usize::MAX = 2^64.
pub proof fn lemma_pa_plus_page_size_no_overflow(pa: Paddr, level: PagingLevel)
    requires
        1 <= level <= NR_LEVELS,
        pa < MAX_PADDR,
    ensures
        pa + page_size(level) < usize::MAX,
{
    lemma_page_size_spec_values();
}

/// For any VA within the kernel virtual address range and any page level,
/// va + page_size(level) does not overflow usize.
/// KERNEL_VADDR_RANGE.end = 0xffff_ffff_ffff_0000 and max page_size (level 4) = 512GB = 0x80_0000_0000.
/// The sum is at most 0x1_0000_7fff_ffff_0000 which overflows 64-bit usize.
/// However, at the levels actually used (1-3), page_size <= 1GB = 0x4000_0000, and
/// 0xffff_ffff_ffff_0000 + 0x4000_0000 = 0x1_0000_0000_3fff_0000 — still overflows.
/// So this lemma requires va + page_size(level) <= barrier_va.end <= KERNEL_VADDR_RANGE.end,
/// which is guaranteed by !map_panic_conditions / !find_next_panic_condition.
pub proof fn lemma_va_plus_page_size_no_overflow(
    va: Vaddr,
    len: usize,
)
    requires
        va + len <= KERNEL_VADDR_RANGE.end,
    ensures
        va + len <= usize::MAX,
{
    assert(KERNEL_VADDR_RANGE.end == 0xffff_ffff_ffff_0000usize) by (compute_only);
    assert(va + len <= 0xffff_ffff_ffff_0000usize);
}

/// The number of base pages in the address space fits in usize.
/// max pages = MAX_PADDR / PAGE_SIZE = 0x8000_0000 / 0x1000 = 0x8_0000 = 524288.
pub proof fn lemma_max_mappings_fit_usize()
    ensures
        MAX_PADDR / PAGE_SIZE < usize::MAX,
{
    assert(MAX_PADDR / PAGE_SIZE < usize::MAX) by (compute_only);
}

} // verus!
