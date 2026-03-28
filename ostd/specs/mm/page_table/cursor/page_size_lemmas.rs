use vstd::prelude::*;
use vstd::arithmetic::power2::pow2;

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
        lemma_page_size_ge_page_size(level);
        assert(ps_l > 0);
        lemma_page_size_ge_page_size(large_level);
        assert(ps_ll > 0);
        lemma_page_size_divides(level, large_level);
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

/// For any level in [1, NR_LEVELS], page_size(level) is a multiple of PAGE_SIZE.
pub proof fn lemma_page_size_multiple_of_page_size(level: PagingLevel)
    requires
        1 <= level <= NR_LEVELS,
    ensures
        page_size_spec(level) % PAGE_SIZE == 0,
{
    lemma_page_size_spec_values();
    if level == 1 {
        assert(page_size_spec(1) == 4096);
        assert(4096usize % PAGE_SIZE == 0usize) by (compute_only);
    } else if level == 2 {
        assert(page_size_spec(2) == 2097152);
        assert(2097152usize % PAGE_SIZE == 0usize) by (compute_only);
    } else if level == 3 {
        assert(page_size_spec(3) == 1073741824);
        assert(1073741824usize % PAGE_SIZE == 0usize) by (compute_only);
    } else {
        assert(level == 4) by {
            assert(NR_LEVELS == 4) by (compute_only);
            assert(level != 1u8);
            assert(level != 2u8);
            assert(level != 3u8);
        }
        assert(page_size_spec(4) == 549755813888);
        assert(549755813888usize % PAGE_SIZE == 0usize) by (compute_only);
    }
}

/// For any level in [1, NR_LEVELS+1], the page size is at least PAGE_SIZE.
/// This follows from page_size(level) = PAGE_SIZE * pow2((ilog2 * (level-1)) as nat)
/// with pow2(k) >= 1 for all k >= 0.
pub proof fn lemma_page_size_ge_page_size(level: PagingLevel)
    requires
        1 <= level <= NR_LEVELS + 1,
    ensures
        page_size(level) >= PAGE_SIZE,
{
    lemma_page_size_spec_values();
    assert(page_size(level) == page_size_spec(level));
    if level == 1 {
        assert(page_size(level) == 4096);
    } else if level == 2 {
        assert(page_size(level) == 2097152);
    } else if level == 3 {
        assert(page_size(level) == 1073741824);
    } else if level == 4 {
        assert(page_size(level) == 549755813888);
    } else {
        assert(level == 5) by {
            assert(NR_LEVELS == 4) by (compute_only);
            assert(NR_LEVELS + 1 == 5) by (compute_only);
            assert(level != 1u8);
            assert(level != 2u8);
            assert(level != 3u8);
            assert(level != 4u8);
        }
        assert(page_size(level) == 281474976710656);
    }
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
    if l1 == l2 {
    } else {
        let ps1 = page_size(l1);
        let ps2 = page_size(l2);

        assert(ps1 == page_size_spec(l1));
        assert(ps2 == page_size_spec(l2));

        lemma_page_size_ge_page_size(l1);
        lemma_page_size_ge_page_size(l2);
        assert(ps1 > 0);
        assert(ps2 > 0);

        lemma_page_size_divides(l1, l2);
        assert(ps2 % ps1 == 0);

        assert(ps1 <= ps2) by {
            if ps2 < ps1 {
                vstd::arithmetic::div_mod::lemma_small_mod(ps2 as nat, ps1 as nat);
                assert(ps2 % ps1 == ps2);
                assert(ps2 % ps1 == 0);
                assert(false);
            }
        };
    }
}

proof fn lemma_page_size_spec_values()
    ensures
        page_size_spec(1) == 4096,
        page_size_spec(2) == 2097152,
        page_size_spec(3) == 1073741824,
        page_size_spec(4) == 549755813888,
        page_size_spec(5) == 281474976710656,
{
    crate::specs::arch::paging_consts::lemma_nr_subpage_per_huge_eq_nr_entries();
    lemma_page_size_spec_level1();
    vstd_extra::external::ilog2::lemma_usize_ilog2_to32();
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma2_to64_rest();

    assert(PAGE_SIZE == 4096);
    assert(nr_subpage_per_huge::<PagingConsts>() == 512usize);
    assert(512usize.ilog2() == 9);
    assert(nr_subpage_per_huge::<PagingConsts>().ilog2() == 9);

    assert(page_size_spec(2) == (PAGE_SIZE * pow2((512usize.ilog2() * 1usize) as nat)) as usize);
    assert(page_size_spec(2) == (4096 * pow2(9)) as usize);
    assert(page_size_spec(2) == 2097152);

    assert(page_size_spec(3) == (PAGE_SIZE * pow2((512usize.ilog2() * 2usize) as nat)) as usize);
    assert(page_size_spec(3) == (4096 * pow2(18)) as usize);
    assert(page_size_spec(3) == 1073741824);

    assert(page_size_spec(4) == (PAGE_SIZE * pow2((512usize.ilog2() * 3usize) as nat)) as usize);
    assert(page_size_spec(4) == (4096 * pow2(27)) as usize);
    assert(page_size_spec(4) == 549755813888);

    assert(page_size_spec(5) == (PAGE_SIZE * pow2((512usize.ilog2() * 4usize) as nat)) as usize);
    assert(page_size_spec(5) == (4096 * pow2(36)) as usize);
    assert(page_size_spec(5) == (pow2(12) * pow2(36)) as usize) by {
        assert(pow2(12) == 4096);
    };
    assert(page_size_spec(5) == pow2(48) as usize) by {
        vstd::arithmetic::power2::lemma_pow2_adds(12nat, 36nat);
    };
    vstd::bits::lemma_usize_pow2_no_overflow(48);
    assert(page_size_spec(5) == 281474976710656);
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
    assert(NR_LEVELS == 4) by (compute_only);
    assert(1u8 <= l1);
    assert(1u8 <= l2);
    assert(l1 <= 5u8) by {
        assert(NR_LEVELS + 1 == 5) by (compute_only);
    }
    assert(l2 <= 5u8) by {
        assert(NR_LEVELS + 1 == 5) by (compute_only);
    }
    if l1 == 1 {
        if l2 == 1 {
            assert(page_size_spec(1) == 4096);
            assert(4096usize % 4096usize == 0usize) by (compute_only);
        } else if l2 == 2 {
            assert(page_size_spec(1) == 4096);
            assert(page_size_spec(2) == 2097152);
            assert(2097152usize % 4096usize == 0usize) by (compute_only);
        } else if l2 == 3 {
            assert(page_size_spec(1) == 4096);
            assert(page_size_spec(3) == 1073741824);
            assert(1073741824usize % 4096usize == 0usize) by (compute_only);
        } else if l2 == 4 {
            assert(page_size_spec(1) == 4096);
            assert(page_size_spec(4) == 549755813888);
            assert(549755813888usize % 4096usize == 0usize) by (compute_only);
        } else if l2 == 5 {
            assert(page_size_spec(1) == 4096);
            assert(page_size_spec(5) == 281474976710656);
            assert(281474976710656usize % 4096usize == 0usize) by (compute_only);
        } else {
            assert(1u8 <= l2);
            assert(l2 <= 5u8);
            assert(l2 != 1u8);
            assert(l2 != 2u8);
            assert(l2 != 3u8);
            assert(l2 != 4u8);
            assert(l2 != 5u8);
            assert(l2 == 5u8);
        }
    } else if l1 == 2 {
        assert(l1 <= l2);
        if l2 == 2 {
            assert(page_size_spec(2) == 2097152);
            assert(2097152usize % 2097152usize == 0usize) by (compute_only);
        } else if l2 == 3 {
            assert(page_size_spec(2) == 2097152);
            assert(page_size_spec(3) == 1073741824);
            assert(1073741824usize % 2097152usize == 0usize) by (compute_only);
        } else if l2 == 4 {
            assert(page_size_spec(2) == 2097152);
            assert(page_size_spec(4) == 549755813888);
            assert(549755813888usize % 2097152usize == 0usize) by (compute_only);
        } else if l2 == 5 {
            assert(page_size_spec(2) == 2097152);
            assert(page_size_spec(5) == 281474976710656);
            assert(281474976710656usize % 2097152usize == 0usize) by (compute_only);
        } else {
            assert(l2 != 2u8);
            assert(l2 != 3u8);
            assert(l2 != 4u8);
            assert(2u8 <= l2);
            assert(l2 == 5u8);
        }
    } else if l1 == 3 {
        assert(l1 <= l2);
        if l2 == 3 {
            assert(page_size_spec(3) == 1073741824);
            assert(1073741824usize % 1073741824usize == 0usize) by (compute_only);
        } else if l2 == 4 {
            assert(page_size_spec(3) == 1073741824);
            assert(page_size_spec(4) == 549755813888);
            assert(549755813888usize % 1073741824usize == 0usize) by (compute_only);
        } else if l2 == 5 {
            assert(page_size_spec(3) == 1073741824);
            assert(page_size_spec(5) == 281474976710656);
            assert(281474976710656usize % 1073741824usize == 0usize) by (compute_only);
        } else {
            assert(l2 != 3u8);
            assert(l2 != 4u8);
            assert(3u8 <= l2);
            assert(l2 == 5u8);
        }
    } else if l1 == 4 {
        assert(l1 <= l2);
        if l2 == 4 {
            assert(page_size_spec(4) == 549755813888);
            assert(549755813888usize % 549755813888usize == 0usize) by (compute_only);
        } else if l2 == 5 {
            assert(page_size_spec(4) == 549755813888);
            assert(page_size_spec(5) == 281474976710656);
            assert(281474976710656usize % 549755813888usize == 0usize) by (compute_only);
        } else {
            assert(l2 != 4u8);
            assert(4u8 <= l2);
            assert(l2 == 5u8);
        }
    } else if l1 == 5 {
        assert(l1 <= l2);
        if l2 == 5 {
            assert(page_size_spec(5) == 281474976710656);
            assert(281474976710656usize % 281474976710656usize == 0usize) by (compute_only);
        } else {
            assert(5u8 <= l2);
            assert(l2 == 5u8);
        }
    } else {
        assert(l1 != 1u8);
        assert(l1 != 2u8);
        assert(l1 != 3u8);
        assert(l1 != 4u8);
        assert(l1 == 5u8);
    }
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
    assert(MAX_PADDR == 0x8000_0000usize) by (compute_only);
    assert(pa < 0x8000_0000usize);

    if level == 1 {
        assert(page_size(level) == 4096);
        assert(pa + page_size(level) == pa + 4096usize);
        assert(pa + 4096usize < usize::MAX) by (bit_vector)
            requires
                pa < 0x8000_0000usize,
        ;
    } else if level == 2 {
        assert(page_size(level) == 2097152);
        assert(pa + page_size(level) == pa + 2097152usize);
        assert(pa + 2097152usize < usize::MAX) by (bit_vector)
            requires
                pa < 0x8000_0000usize,
        ;
    } else if level == 3 {
        assert(page_size(level) == 1073741824);
        assert(pa + page_size(level) == pa + 1073741824usize);
        assert(pa + 1073741824usize < usize::MAX) by (bit_vector)
            requires
                pa < 0x8000_0000usize,
        ;
    } else {
        assert(level == 4) by {
            assert(NR_LEVELS == 4) by (compute_only);
            assert(level != 1u8);
            assert(level != 2u8);
            assert(level != 3u8);
        }
        assert(page_size(level) == 549755813888);
        assert(pa + page_size(level) == pa + 549755813888usize);
        assert(pa + 549755813888usize < usize::MAX) by (bit_vector)
            requires
                pa < 0x8000_0000usize,
        ;
    }
}

} // verus!
