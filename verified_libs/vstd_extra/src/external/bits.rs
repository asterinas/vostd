//! Trusted bit-arithmetic boundary for `u64` shifts and masks in the integer-mode
//! encoding of the active Verus version: `vir/src/prelude.rs` declares `bit_shl`
//! with no value axioms (the `Shl` case is commented "Nothing for shl"), and
//! spec-mode `-` promotes `(1u64 << k) - 1` to `int`, so mask algebra can be
//! neither derived by the solver nor expressed in standalone `bit_vector` queries
//! (whose free variables carry no context). The axioms below state Rust's defined
//! semantics for in-range shift amounts and the resulting low-`k`-bits mask shape;
//! they are the only added trusted facts (TCB) and live here rather than beside an
//! OSTD caller.
//!
//! Soundness: for `0 <= k < 64`, Rust defines `1u64 << k == 2^k` (nonzero, within
//! range), so `(1u64 << k) - 1` has exactly the bits below `k` set — AND-ing a word
//! with it clears every bit `>= k` and leaves every bit `< k` unchanged.
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
///
/// Kept as an axiom: the hypothesis embeds the subtraction `(1u64 << k) - 1`, which
/// spec-mode arithmetic promotes to `int` (E0308 feeding `&`), so neither the mask
/// value nor a subtraction-shaped hypothesis can enter a `bit_vector` formula. A
/// bit-only rewiring of the whole family (`mask == !(!0u64 << k)`) would force
/// rewriting the caller's mask terms and re-bridging the exec-computed mask value.
pub broadcast axiom fn axiom_u64_masked_bit_clear(word: u64, mask: u64, k: int, b: int)
    ensures
        #![trigger ((word & mask) & (1u64 << (b as usize))), (1u64 << (k as usize))]
        {
            &&& 0 <= k <= 64 && k <= b < 64
            &&& mask == (1u64 << (k as usize)) - 1
        } ==> ((word & mask) & (1u64 << (b as usize))) == 0,
;

/// Masking with the low-`k`-bits mask keeps bit `b < k` of any word unchanged.
pub broadcast axiom fn axiom_u64_masked_bit_keep(word: u64, mask: u64, k: int, b: int)
    ensures
        #![trigger ((word & mask) & (1u64 << (b as usize))), (1u64 << (k as usize))]
        {
            &&& 0 < k <= 64 && 0 <= b < k
            &&& mask == (1u64 << (k as usize)) - 1
        } ==> ((word & mask) & (1u64 << (b as usize))) == word & (1u64 << (b as usize)),
;

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
    axiom_u64_masked_bit_clear,
    axiom_u64_masked_bit_keep,
    lemma_u64_setbit_bit_set,
    lemma_u64_setbit_bit_keep,
    lemma_u64_clearbit_bit_clear,
    lemma_u64_clearbit_bit_keep,
    lemma_u64_zero_and_bit,
}

/// The number of set bits in a `u64` word: the uninterpreted spec carrier for
/// `count_ones` and the counting bridge.
pub uninterp spec fn u64_set_bits(w: u64) -> int;

/// `u64::count_ones`: "Returns the number of ones in the binary representation
/// of `self`" (core/src/num/uint_macros.rs, `intrinsics::ctpop`).
pub assume_specification[ u64::count_ones ](v: u64) -> (r: u32)
    ensures
        (r as int) == u64_set_bits(v),
;

/// A nonzero word has at least one set bit (and zero has none) — the "number of
/// ones" characterization of the std doc.
pub broadcast axiom fn axiom_u64_set_bits_nonzero(w: u64)
    ensures
        #![trigger u64_set_bits(w)]
        (w != 0u64) == (1 <= u64_set_bits(w)),
        0 <= u64_set_bits(w) <= 64,
;

} // verus!
