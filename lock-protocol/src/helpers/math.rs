use vstd::math::max;
use vstd::prelude::*;
use vstd::bits::*;

verus! {

pub proof fn lemma_page_shl()
    ensures
        (4096 as u64) << 0 == 0x1000,
        (4096 as u64) << 1 == 0x2000,
        (4096 as u64) << 2 == 0x4000,
        (4096 as u64) << 3 == 0x8000,
        (4096 as u64) << 4 == 0x10000,
        (4096 as u64) << 5 == 0x20000,
        (4096 as u64) << 6 == 0x40000,
        (4096 as u64) << 7 == 0x80000,
        (4096 as u64) << 8 == 0x100000,
        (4096 as u64) << 9 == 0x200000,
        (4096 as u64) << 10 == 0x400000,
        (4096 as u64) << 11 == 0x800000,
        (4096 as u64) << 12 == 0x1000000,
        (4096 as u64) << 13 == 0x2000000,
        (4096 as u64) << 14 == 0x4000000,
        (4096 as u64) << 15 == 0x8000000,
        (4096 as u64) << 16 == 0x10000000,
        (4096 as u64) << 17 == 0x20000000,
        (4096 as u64) << 18 == 0x40000000,
        (4096 as u64) << 19 == 0x80000000,
        (4096 as u64) << 20 == 0x100000000,
        (4096 as u64) << 21 == 0x200000000,
        (4096 as u64) << 22 == 0x400000000,
        (4096 as u64) << 23 == 0x800000000,
        (4096 as u64) << 24 == 0x1000000000,
        (4096 as u64) << 25 == 0x2000000000,
        (4096 as u64) << 26 == 0x4000000000,
        (4096 as u64) << 27 == 0x8000000000,
{
    broadcast use lemma_u64_shl_is_mul;

    assert((4096 as u64) << 0 == 0x1000) by (compute_only);
    assert((4096 as u64) << 1 == 0x2000) by (compute_only);
    assert((4096 as u64) << 2 == 0x4000) by (compute_only);
    assert((4096 as u64) << 3 == 0x8000) by (compute_only);
    assert((4096 as u64) << 4 == 0x10000) by (compute_only);
    assert((4096 as u64) << 5 == 0x20000) by (compute_only);
    assert((4096 as u64) << 6 == 0x40000) by (compute_only);
    assert((4096 as u64) << 7 == 0x80000) by (compute_only);
    assert((4096 as u64) << 8 == 0x100000) by (compute_only);
    assert((4096 as u64) << 9 == 0x200000) by (compute_only);
    assert((4096 as u64) << 10 == 0x400000) by (compute_only);
    assert((4096 as u64) << 11 == 0x800000) by (compute_only);
    assert((4096 as u64) << 12 == 0x1000000) by (compute_only);
    assert((4096 as u64) << 13 == 0x2000000) by (compute_only);
    assert((4096 as u64) << 14 == 0x4000000) by (compute_only);
    assert((4096 as u64) << 15 == 0x8000000) by (compute_only);
    assert((4096 as u64) << 16 == 0x10000000) by (compute_only);
    assert((4096 as u64) << 17 == 0x20000000) by (compute_only);
    assert((4096 as u64) << 18 == 0x40000000) by (compute_only);
    assert((4096 as u64) << 19 == 0x80000000) by (compute_only);
    assert((4096 as u64) << 20 == 0x100000000) by (compute_only);
    assert((4096 as u64) << 21 == 0x200000000) by (compute_only);
    assert((4096 as u64) << 22 == 0x400000000) by (compute_only);
    assert((4096 as u64) << 23 == 0x800000000) by (compute_only);
    assert((4096 as u64) << 24 == 0x1000000000) by (compute_only);
    assert((4096 as u64) << 25 == 0x2000000000) by (compute_only);
    assert((4096 as u64) << 26 == 0x4000000000) by (compute_only);
    assert((4096 as u64) << 27 == 0x8000000000) by (compute_only);
}

pub proof fn lemma_u64_and_less_than(a: u64, b: u64)
    ensures
        a & b <= a,
        a & b <= b,
        a & b <= max(a as int, b as int) as u64,
{
    assert(a & b <= a) by (bit_vector);
    assert(a & b <= b) by (bit_vector);
    let max = max(a as int, b as int) as u64;
    assert(a & b <= max);
}

pub proof fn lemma_usize_mod_0_maintain_after_add(x: usize, m: usize)
    requires
        x % m == 0,
        m > 0,
    ensures
        (x + m) % m as int == 0,
{
    use vstd::arithmetic::div_mod::*;

    lemma_mod_adds(x as int, m as int, m as int);
}

} // verus!
