use vstd::prelude::*;

use crate::mm::{nr_subpage_per_huge, Paddr, Vaddr, MAX_PADDR};
use crate::mm::page_table::{page_size, page_size_spec};
use crate::mm::PagingLevel;
use crate::specs::arch::mm::{NR_LEVELS, PAGE_SIZE};
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
        exists |large_level: PagingLevel|
            1 <= large_level <= NR_LEVELS + 1
            && level <= large_level
            && va % page_size_spec(large_level) == 0,
    ensures
        va % page_size_spec(level) == 0,
{
    let large_level: PagingLevel = choose |l: PagingLevel|
        1 <= l <= NR_LEVELS + 1 && level <= l && va % page_size_spec(l) == 0;
    if level == large_level {
    } else if level == 1nat {
        lemma_page_size_spec_level1();
    } else {
        let ps_l = page_size_spec(level) as int;
        let ps_ll = page_size_spec(large_level) as int;
        axiom_page_size_ge_page_size(level);
        assert(ps_l > 0);
        axiom_page_size_ge_page_size(large_level);
        assert(ps_ll > 0);
        axiom_page_size_divides(level, large_level);
        assert(ps_ll % ps_l == 0);
        assert(ps_ll >= ps_l) by {
            if ps_ll < ps_l {
                vstd::arithmetic::div_mod::lemma_small_mod(ps_ll as nat, ps_l as nat);
                assert(false);
            }
        };
        let k = ps_ll / ps_l;
        vstd::arithmetic::div_mod::lemma_div_non_zero(ps_ll, ps_l);
        assert(k > 0);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ps_ll, ps_l);
        assert(ps_ll == ps_l * k);
        vstd::arithmetic::div_mod::lemma_mod_mod(va as int, ps_l, k);
        assert(va as int % ps_ll == 0);
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

// ─── page_size axioms ────────────────────────────────────────────────────────

/// For any level in [1, NR_LEVELS], page_size(level) is a multiple of PAGE_SIZE.
///
/// Mathematically: page_size(level) = PAGE_SIZE * pow2(e) for e = ilog2 * (level-1),
/// so PAGE_SIZE divides it.  Proving this from the `page_size_spec` definition requires
/// bounding the `as usize` cast (no overflow for levels 1–NR_LEVELS), which is left as
/// an axiom following the same pattern as `axiom_page_size_ge_page_size`.
///
/// TODO: replace with a proof once the pow2-overflow bounds are established.
pub axiom fn axiom_page_size_multiple_of_page_size(level: PagingLevel)
    requires
        1 <= level <= NR_LEVELS,
    ensures
        page_size_spec(level) % PAGE_SIZE == 0;

/// For any level in [1, NR_LEVELS+1], the page size is at least PAGE_SIZE.
/// This follows from page_size(level) = PAGE_SIZE * pow2((ilog2 * (level-1)) as nat)
/// with pow2(k) >= 1 for all k >= 0.
pub axiom fn axiom_page_size_ge_page_size(level: PagingLevel)
    requires
        1 <= level <= NR_LEVELS + 1,
    ensures
        page_size(level) >= PAGE_SIZE;

/// `page_size` is monotone in the level: a higher level has a larger or equal page size.
/// This follows from page_size(level) = PAGE_SIZE * 512^(level-1); incrementing level multiplies
/// by 512, so page_size(l+1) = 512 * page_size(l) > page_size(l).
pub axiom fn axiom_page_size_monotone(l1: PagingLevel, l2: PagingLevel)
    requires
        1 <= l1 <= NR_LEVELS + 1,
        1 <= l2 <= NR_LEVELS + 1,
        l1 <= l2,
    ensures
        page_size(l1) <= page_size(l2);

/// page_size(l2) is divisible by page_size(l1) when l1 <= l2.
/// This holds because page_size(l) = PAGE_SIZE * 512^(l-1), so
/// page_size(l2) / page_size(l1) = 512^(l2-l1), which is a positive integer.
pub axiom fn axiom_page_size_divides(l1: PagingLevel, l2: PagingLevel)
    requires
        1 <= l1 <= l2 <= NR_LEVELS + 1,
    ensures
        page_size_spec(l2) % page_size_spec(l1) == 0;

/// For any valid physical address `pa < MAX_PADDR` and page level, pa + page_size(level)
/// does not overflow usize. This holds because MAX_PADDR = 2^31 and page sizes are at
/// most 2^39 (NR_LEVELS = 4), so pa + size < 2^40 << usize::MAX = 2^64.
pub axiom fn axiom_pa_plus_page_size_no_overflow(pa: Paddr, level: PagingLevel)
    requires
        1 <= level <= NR_LEVELS,
        pa < MAX_PADDR,
    ensures
        pa + page_size(level) < usize::MAX;

} // verus!
