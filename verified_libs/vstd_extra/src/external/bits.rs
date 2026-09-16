//! Bit-arithmetic lemmas for `u64` shifts and masks.
use vstd::prelude::*;

verus! {

/// Every bit of the all-ones word is set, so `!0 & (1 << k)` is nonzero for an
/// in-range shift amount `k`. Proved: `!0 & x == x` and the bounded symbolic
/// shift's nonzeroness are bit_vector implications.
pub broadcast proof fn lemma_u64_allones_bit(k: int)
    ensures
        #![trigger (1u64 << (k as usize))]
        0 <= k < 64 ==> ((!0u64 & (1u64 << (k as usize))) != 0),
{
    if 0 <= k < 64 {
        let ku: u32 = k as u32;
        assert((!0u64 & (1u64 << ku)) == (1u64 << ku)) by (bit_vector);
        assert((ku < 64u32) ==> ((1u64 << ku) != 0u64)) by (bit_vector);
    }
}

/// An in-range unit shift is at least `1`, so `(1u64 << k) - 1` cannot underflow.
/// Proved: the bounded symbolic shift's positivity is a bit_vector implication.
pub broadcast proof fn lemma_u64_unit_shift_pos(k: int)
    ensures
        #![trigger (1u64 << (k as usize))]
        0 <= k < 64 ==> 1u64 <= (1u64 << (k as usize)),
{
    if 0 <= k < 64 {
        let ku: u32 = k as u32;
        assert((ku < 64u32) ==> (1u64 <= (1u64 << ku))) by (bit_vector);
    }
}

/// Masking with the low-`k`-bits mask `(1u64 << k) - 1` clears bit `b >= k` of any
/// word (AND associativity folded into the statement).
pub broadcast proof fn lemma_u64_masked_bit_clear(word: u64, mask: u64, k: int, b: int)
    ensures
        #![trigger ((word & mask) & (1u64 << (b as usize))), (1u64 << (k as usize))]
        {
            &&& 0 <= k <= 64 && k <= b < 64
            &&& mask == (1u64 << (k as usize)) - 1
        } ==> ((word & mask) & (1u64 << (b as usize))) == 0,
{
    if 0 <= k <= 64 && k <= b < 64 && mask == (1u64 << (k as usize)) - 1 {
        let ku: u32 = k as u32;
        let bu: u32 = b as u32;
        assert(((word & mask) & (1u64 << bu)) == 0u64) by (bit_vector)
            requires
                ku <= bu,
                bu < 64,
                mask == (1u64 << ku) - 1u64,
        ;
    }
}

/// Masking with the low-`k`-bits mask keeps bit `b < k` of any word unchanged.
pub broadcast proof fn lemma_u64_masked_bit_keep(word: u64, mask: u64, k: int, b: int)
    ensures
        #![trigger ((word & mask) & (1u64 << (b as usize))), (1u64 << (k as usize))]
        {
            &&& 0 < k <= 64 && 0 <= b < k
            &&& mask == (1u64 << (k as usize)) - 1
        } ==> ((word & mask) & (1u64 << (b as usize))) == word & (1u64 << (b as usize)),
{
    if 0 < k <= 64 && 0 <= b < k && mask == (1u64 << (k as usize)) - 1 {
        let ku: u32 = k as u32;
        let bu: u32 = b as u32;
        assert(((word & mask) & (1u64 << bu)) == (word & (1u64 << bu))) by (bit_vector)
            requires
                bu < ku,
                ku <= 64,
                mask == (1u64 << ku) - 1u64,
        ;
    }
}

/// Setting bit `b` (OR-ing the unit bit at `b`) makes that bit nonzero. Proved:
/// the OR/AND identity and the bounded symbolic shift's nonzeroness are both
/// bit_vector implications.
pub broadcast proof fn lemma_u64_setbit_bit_set(word: u64, b: int)
    ensures
        #![trigger ((word | (1u64 << (b as usize))) & (1u64 << (b as usize)))]
        0 <= b < 64 ==> (((word | (1u64 << (b as usize))) & (1u64 << (b as usize))) != 0),
{
    if 0 <= b < 64 {
        let bu: u32 = b as u32;
        assert(((word | (1u64 << bu)) & (1u64 << bu)) == (1u64 << bu)) by (bit_vector);
        assert((bu < 64u32) ==> ((1u64 << bu) != 0u64)) by (bit_vector);
    }
}

/// Setting bit `b` leaves a different in-range bit `b2` unchanged. Proved: the
/// full implication (with the `b != b2` discriminant) is a bit_vector tautology.
pub broadcast proof fn lemma_u64_setbit_bit_keep(word: u64, b: int, b2: int)
    ensures
        #![trigger ((word | (1u64 << (b as usize))) & (1u64 << (b2 as usize))), (1u64 << (b as usize))]
        {
            &&& 0 <= b < 64
            &&& 0 <= b2 < 64
            &&& b != b2
        } ==> ((word | (1u64 << (b as usize))) & (1u64 << (b2 as usize))) == (word & (1u64 << (
        b2 as usize))),
{
    if 0 <= b < 64 && 0 <= b2 < 64 && b != b2 {
        let bu: u32 = b as u32;
        let b2u: u32 = b2 as u32;
        assert((bu != b2u) ==> (((word | (1u64 << bu)) & (1u64 << b2u)) == (word & (1u64 << b2u))))
            by (bit_vector);
    }
}

/// Clearing bit `b` (AND-ing the complement of the unit bit at `b`) clears that bit.
/// Proved: the full implication is a bit_vector tautology (`x & !t & t == 0`) over
/// the `u32`-shaped shift, which unifies with the `usize`-shaped conclusion term.
pub broadcast proof fn lemma_u64_clearbit_bit_clear(word: u64, b: int)
    ensures
        #![trigger ((word & (!(1u64 << (b as usize)))) & (1u64 << (b as usize)))]
        0 <= b < 64 ==> ((word & (!(1u64 << (b as usize)))) & (1u64 << (b as usize))) == 0,
{
    if 0 <= b < 64 {
        let bu: u32 = b as u32;
        assert((word & (!(1u64 << bu))) & (1u64 << bu) == 0u64) by (bit_vector);
    }
}

/// Clearing bit `b` leaves a different in-range bit `b2` unchanged. Proved: the
/// full implication (with the `b != b2` discriminant) is a bit_vector tautology.
pub broadcast proof fn lemma_u64_clearbit_bit_keep(word: u64, b: int, b2: int)
    ensures
        #![trigger ((word & (!(1u64 << (b as usize)))) & (1u64 << (b2 as usize))), (1u64 << (b as usize))]
        {
            &&& 0 <= b < 64
            &&& 0 <= b2 < 64
            &&& b != b2
        } ==> ((word & (!(1u64 << (b as usize)))) & (1u64 << (b2 as usize))) == (word & (1u64 << (
        b2 as usize))),
{
    if 0 <= b < 64 && 0 <= b2 < 64 && b != b2 {
        let bu: u32 = b as u32;
        let b2u: u32 = b2 as u32;
        assert((bu != b2u) ==> (((word & (!(1u64 << bu))) & (1u64 << b2u)) == (word & (1u64
            << b2u)))) by (bit_vector);
    }
}

/// AND-ing the zero word with any in-range unit bit is zero. Proved, not assumed:
/// the value-level fact is a bit_vector tautology; the `usize`-shaped shift in the
/// conclusion is reached through the `u32`-shaped form (both casts of the same
/// in-range `k` carry the same value to the shift).
pub broadcast proof fn lemma_u64_zero_and_bit(k: int)
    ensures
        #![trigger (1u64 << (k as usize))]
        0 <= k < 64 ==> (0u64 & (1u64 << (k as usize))) == 0,
{
    if 0 <= k < 64 {
        let bit: u64 = 1u64 << (k as u32);
        assert(0u64 & bit == 0u64) by (bit_vector);
    }
}

pub broadcast group group_u64_bit_algebra {
    lemma_u64_allones_bit,
    lemma_u64_unit_shift_pos,
    lemma_u64_masked_bit_clear,
    lemma_u64_masked_bit_keep,
    lemma_u64_setbit_bit_set,
    lemma_u64_setbit_bit_keep,
    lemma_u64_clearbit_bit_clear,
    lemma_u64_clearbit_bit_keep,
    lemma_u64_zero_and_bit,
}

/// The number of set bits among the lowest `n` bits of `w`.
spec fn u64_set_bits_rec(w: u64, n: u64) -> int
    decreases n,
{
    if n == 0 {
        0
    } else {
        (w & 1u64) + u64_set_bits_rec(w >> 1u64, (n - 1) as u64)
    }
}

/// The number of set bits in a `u64` word.
pub closed spec fn u64_set_bits(w: u64) -> int {
    u64_set_bits_rec(w, 64)
}

/// `u64::count_ones`: "Returns the number of ones in the binary representation
/// of `self`" (core/src/num/uint_macros.rs, `intrinsics::ctpop`).
pub assume_specification[ u64::count_ones ](v: u64) -> (r: u32)
    ensures
        (r as int) == u64_set_bits(v),
;

proof fn lemma_u64_set_bits_rec_bounds(w: u64, n: u64)
    requires
        n <= 64,
    ensures
        0 <= u64_set_bits_rec(w, n) <= n,
        w >> n == 0 ==> ((w != 0) == (1 <= u64_set_bits_rec(w, n))),
    decreases n,
{
    reveal_with_fuel(u64_set_bits_rec, 1);
    if n != 0 {
        lemma_u64_set_bits_rec_bounds(w >> 1u64, (n - 1) as u64);
        assert((w & 1u64) <= 1) by (bit_vector);
        assert((w >> 1u64) >> ((n - 1) as u64) == w >> n) by (bit_vector)
            requires
                0 < n <= 64,
        ;
        if w >> n == 0 {
            if w == 0 {
                assert(w & 1u64 == 0 && w >> 1u64 == 0) by (bit_vector)
                    requires
                        w == 0,
                ;
            } else {
                if w & 1u64 == 0 {
                    assert(w >> 1u64 != 0) by (bit_vector)
                        requires
                            w != 0,
                            w & 1u64 == 0,
                    ;
                } else {
                    assert(w & 1u64 == 1) by (bit_vector)
                        requires
                            w & 1u64 != 0,
                    ;
                }
            }
        }
    } else {
        assert(w >> n == w) by (bit_vector)
            requires
                n == 0,
        ;
    }
}

/// A nonzero word has at least one set bit (and zero has none).
pub broadcast proof fn lemma_u64_set_bits_nonzero(w: u64)
    ensures
        #![trigger u64_set_bits(w)]
        (w != 0u64) == (1 <= u64_set_bits(w)),
        0 <= u64_set_bits(w) <= 64,
{
    reveal(u64_set_bits);
    lemma_u64_set_bits_rec_bounds(w, 64);
    assert(w >> 64u64 == 0) by (bit_vector);
}

} // verus!
