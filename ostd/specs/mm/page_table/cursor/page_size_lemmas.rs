use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;

use crate::arch::mm::PagingConsts;
use crate::mm::PagingConstsTrait;
use crate::mm::PagingLevel;
use crate::mm::{KERNEL_VADDR_RANGE, MAX_PADDR, Paddr, Vaddr, nr_subpage_per_huge, page_size};
use crate::specs::arch::{NR_ENTRIES, NR_LEVELS, PAGE_SIZE};

verus! {

// ─── page_size(1) ──────────────────────────────────────────────────────
/// page_size::<C>(1) == C::BASE_PAGE_SIZE.
pub proof fn lemma_page_size_spec_level1<C: PagingConstsTrait>()
    ensures
        page_size::<C>(1) == C::BASE_PAGE_SIZE(),
{
    vstd::arithmetic::mul::lemma_mul_by_zero_is_zero(nr_subpage_per_huge::<C>().ilog2() as int);
    broadcast use vstd::arithmetic::power2::lemma_pow2;

    vstd::arithmetic::power::lemma_pow0(2int);
    // page_size_spec(1) = (PAGE_SIZE * pow2(0)) as usize = PAGE_SIZE
    // Need PAGE_SIZE == C::BASE_PAGE_SIZE() which holds for all configs
    C::lemma_paging_consts_properties();
}

// ─── VA alignment ────────────────────────────────────────────────────────────
/// When `va` is aligned to `page_size::<C>(large_level)` and `level <= large_level` (so
/// page_size::<C>(level) divides page_size::<C>(large_level)), then `va` is aligned to page_size::<C>(level).
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
        lemma_page_size_spec_level1::<C>();
    } else {
        let ps_l = page_size::<C>(level) as int;
        let ps_ll = page_size::<C>(large_level) as int;
        lemma_page_size_ge_page_size::<C>(level);
        lemma_page_size_ge_page_size::<C>(large_level);
        lemma_page_size_divides::<C>(level, large_level);
        C::lemma_paging_consts_requirements();
        assert(ps_l > 0) by {
            assert(page_size::<C>(level) >= C::BASE_PAGE_SIZE());
            assert(C::BASE_PAGE_SIZE() > 0);
        };
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

/// Special case for level 1: page_size::<C>(1) == C::BASE_PAGE_SIZE(), so va % C::BASE_PAGE_SIZE() == 0 implies
/// va % page_size::<C>(1) == 0.
pub proof fn lemma_va_align_page_size_level_1<C: PagingConstsTrait>(va: Vaddr)
    requires
        va % C::BASE_PAGE_SIZE() == 0,
    ensures
        va % page_size::<C>(1) == 0,
{
    lemma_page_size_spec_level1::<C>();
}

/// For any level in [1, C::NR_LEVELS], page_size::<C>(level) is a multiple of C::BASE_PAGE_SIZE.
pub proof fn lemma_page_size_multiple_of_page_size<C: PagingConstsTrait>(level: PagingLevel)
    requires
        1 <= level <= C::NR_LEVELS(),
    ensures
        page_size::<C>(level) % C::BASE_PAGE_SIZE() == 0,
{
    lemma_page_size_spec_level1::<C>();
    lemma_page_size_divides::<C>(1, level);
}

/// For any level in [1, C::NR_LEVELS+1], the page size is at least C::BASE_PAGE_SIZE.
pub proof fn lemma_page_size_ge_page_size<C: PagingConstsTrait>(level: PagingLevel)
    requires
        1 <= level <= C::NR_LEVELS() + 1,
    ensures
        page_size::<C>(level) >= C::BASE_PAGE_SIZE(),
{
    C::lemma_paging_consts_properties();
    crate::specs::arch::lemma_page_size_values::<C>();
}

/// `page_size` is monotone in the level: a higher level has a larger or equal page size.
/// This follows from page_size(level) = PAGE_SIZE * 512^(level-1); incrementing level multiplies
/// by 512, so page_size(l+1) = 512 * page_size(l) > page_size(l).
pub proof fn lemma_page_size_monotone<C: PagingConstsTrait>(l1: PagingLevel, l2: PagingLevel)
    requires
        1 <= l1 <= C::NR_LEVELS() + 1,
        1 <= l2 <= C::NR_LEVELS() + 1,
        l1 <= l2,
    ensures
        page_size::<C>(l1) <= page_size::<C>(l2),
{
    if l1 != l2 {
        let ps1 = page_size::<C>(l1);
        let ps2 = page_size::<C>(l2);

        lemma_page_size_ge_page_size::<C>(l1);
        lemma_page_size_ge_page_size::<C>(l2);
        lemma_page_size_divides::<C>(l1, l2);
        C::lemma_paging_consts_requirements();

        assert(ps1 > 0) by {
            assert(page_size::<C>(l1) >= C::BASE_PAGE_SIZE());
            assert(C::BASE_PAGE_SIZE() > 0);
        };
        assert(ps1 <= ps2) by {
            if ps2 < ps1 {
                vstd::arithmetic::div_mod::lemma_small_mod(ps2 as nat, ps1 as nat);
            }
        };
    }
}

/// `(page_size(level) / PAGE_SIZE) * PAGE_SIZE == page_size(level)` for level in [1, NR_LEVELS+1].
/// page_size(level) is divisible by PAGE_SIZE so the integer division is exact.
pub proof fn lemma_page_size_div_mul_eq<C: PagingConstsTrait>(level: PagingLevel)
    requires
        1 <= level <= C::NR_LEVELS() + 1,
    ensures
        (page_size::<C>(level) / C::BASE_PAGE_SIZE()) * C::BASE_PAGE_SIZE() == page_size::<C>(
            level,
        ),
{
    C::lemma_paging_consts_properties();
    C::lemma_paging_consts_requirements();
    crate::specs::arch::lemma_page_size_values::<C>();
    let ps = page_size::<C>(level) as int;
    let base = C::BASE_PAGE_SIZE() as int;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ps, base);
}

/// `NR_ENTRIES * page_size(level - 1) == page_size(level)` for level in [2, NR_LEVELS + 1].
/// A huge page at `level` consists of NR_ENTRIES sub-pages each of size `page_size(level - 1)`.
pub proof fn lemma_nr_entries_times_sub_page_size<C: PagingConstsTrait>(level: PagingLevel)
    requires
        2 <= level <= C::NR_LEVELS() + 1,
    ensures
        nr_subpage_per_huge::<C>() as int * page_size::<C>((level - 1) as PagingLevel) as int
            == page_size::<C>(level) as int,
{
    C::lemma_paging_consts_properties();
    crate::specs::arch::lemma_page_size_values::<C>();
}

pub proof fn lemma_split_sub_page_big_j<C: PagingConstsTrait>(
    pa: Paddr,
    level: PagingLevel,
    i: usize,
) -> (big_j: usize)
    requires
        2 <= level <= C::NR_LEVELS(),
        0 < i < nr_subpage_per_huge::<C>(),
    ensures
        0 < big_j < page_size::<C>(level) / C::BASE_PAGE_SIZE(),
        (pa + i * page_size::<C>((level - 1) as PagingLevel)) as int == pa as int + big_j as int
            * C::BASE_PAGE_SIZE() as int,
        big_j as int == i as int * (page_size::<C>((level - 1) as PagingLevel)
            / C::BASE_PAGE_SIZE()) as int,
{
    let sub_pages_per_entry: int = (page_size::<C>((level - 1) as PagingLevel)
        / C::BASE_PAGE_SIZE()) as int;
    let big_j_int: int = i as int * sub_pages_per_entry;
    lemma_page_size_ge_page_size::<C>((level - 1) as PagingLevel);
    C::lemma_paging_consts_requirements();
    C::lemma_paging_consts_properties();
    assert(sub_pages_per_entry > 0) by {
        vstd::arithmetic::div_mod::lemma_div_non_zero(
            page_size::<C>((level - 1) as PagingLevel) as int,
            C::BASE_PAGE_SIZE() as int,
        );
    };
    lemma_page_size_div_mul_eq::<C>((level - 1) as PagingLevel);
    lemma_page_size_div_mul_eq::<C>(level);
    lemma_nr_entries_times_sub_page_size::<C>(level);
    vstd::arithmetic::mul::lemma_mul_strictly_positive(i as int, sub_pages_per_entry);
    vstd::arithmetic::mul::lemma_mul_strict_inequality(
        i as int,
        nr_subpage_per_huge::<C>() as int,
        sub_pages_per_entry,
    );
    vstd::arithmetic::mul::lemma_mul_is_associative(
        nr_subpage_per_huge::<C>() as int,
        sub_pages_per_entry,
        C::BASE_PAGE_SIZE() as int,
    );
    vstd::arithmetic::div_mod::lemma_div_by_multiple(
        nr_subpage_per_huge::<C>() as int * sub_pages_per_entry,
        C::BASE_PAGE_SIZE() as int,
    );
    vstd::arithmetic::mul::lemma_mul_is_associative(
        i as int,
        sub_pages_per_entry,
        C::BASE_PAGE_SIZE() as int,
    );
    big_j_int as usize
}

/// page_size(l2) is divisible by page_size(l1) when l1 <= l2.
pub proof fn lemma_page_size_divides<C: PagingConstsTrait>(l1: PagingLevel, l2: PagingLevel)
    requires
        1 <= l1 <= l2 <= C::NR_LEVELS() + 1,
    ensures
        page_size::<C>(l2) % page_size::<C>(l1) == 0,
    decreases l2 - l1,
{
    C::lemma_paging_consts_requirements();
    lemma_page_size_ge_page_size::<C>(l1);
    if l1 == l2 {
    } else {
        // Induction: page_size(l2-1) % page_size(l1) == 0
        lemma_page_size_divides::<C>(l1, (l2 - 1) as PagingLevel);
        // Step relation: nr_subpage * page_size(l2-1) == page_size(l2)
        lemma_nr_entries_times_sub_page_size::<C>(l2);
        let ps1 = page_size::<C>(l1) as int;
        let ps_prev = page_size::<C>((l2 - 1) as PagingLevel) as int;
        let n = nr_subpage_per_huge::<C>() as int;
        assert(ps1 > 0) by {
            assert(page_size::<C>(l1) >= C::BASE_PAGE_SIZE());
            assert(C::BASE_PAGE_SIZE() > 0);
        };
        // ps_prev == (ps_prev / ps1) * ps1 + 0
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ps_prev, ps1);
        let k = ps_prev / ps1;
        // n * ps_prev == n * (k * ps1) == (n * k) * ps1
        vstd::arithmetic::mul::lemma_mul_is_associative(n, k, ps1);
        // (n * k) * ps1 % ps1 == 0
        vstd::arithmetic::div_mod::lemma_mod_multiples_basic(n * k, ps1);
        // page_size(l2) as int == n * ps_prev == (n * k) * ps1
        assert(page_size::<C>(l2) as int % ps1 == 0);
    }
}

pub proof fn lemma_page_size_sum_no_overflow<C: PagingConstsTrait>(level: PagingLevel)
    requires
        1 <= level <= C::NR_LEVELS(),
    ensures
        page_size::<C>(level) as int + page_size::<C>((level + 1) as PagingLevel) as int - 1
            < usize::MAX as int,
{
    C::lemma_paging_consts_properties();
    crate::specs::arch::lemma_page_size_values::<C>();
    lemma_page_size_monotone::<C>(level, (level + 1) as PagingLevel);
    lemma_page_size_monotone::<C>((level + 1) as PagingLevel, 5 as PagingLevel);
    // page_size(5) == 0x1_0000_0000_0000 == 2^48
    // sum <= 2 * 2^48 = 2^49 < 2^64 - 1
    assert(page_size::<C>(5) as int == 0x1_0000_0000_0000int);
    assert(page_size::<C>((level + 1) as PagingLevel) as int <= 0x1_0000_0000_0000int);
    assert(page_size::<C>(level) as int <= 0x1_0000_0000_0000int);
}

} // verus!
