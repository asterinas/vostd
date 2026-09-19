//! Bit-arithmetic lemmas for `u64` shifts and masks.
use vstd::prelude::*;

/// Define the bit-test predicate `|$name|` for the unsigned word type `$uN`:
/// whether bit `b` of the word `w` is set, i.e. `w & (1 << b) != 0`.
macro_rules! define_bit_is_set {
    ($name:ident, $uN:ty, $one:expr) => {
        verus! {
            /// Bit `b` of the
            #[doc = stringify!($uN)]
            /// word `w` is set, i.e. `w & (1 << b) != 0`.
            pub open spec fn $name(w: $uN, b: int) -> bool {
                (w & ($one << (b as usize))) != 0
            }
        }
    };
}

define_bit_is_set!(u8_bit_is_set, u8, 1u8);
define_bit_is_set!(u16_bit_is_set, u16, 1u16);
define_bit_is_set!(u32_bit_is_set, u32, 1u32);
define_bit_is_set!(u64_bit_is_set, u64, 1u64);
define_bit_is_set!(u128_bit_is_set, u128, 1u128);
define_bit_is_set!(usize_bit_is_set, usize, 1usize);

verus! {

/// Every bit of the all-ones word is set.
pub broadcast proof fn lemma_u64_allones_bit(k: int)
    requires
        0 <= k < 64,
    ensures
        #![trigger (1u64 << (k as usize))]
        (!0u64 & (1u64 << (k as usize))) != 0,
{
    let ku: u32 = k as u32;
    assert((!0u64 & (1u64 << ku)) == (1u64 << ku)) by (bit_vector);
    assert((ku < 64u32) ==> ((1u64 << ku) != 0u64)) by (bit_vector);
}

/// An in-range unit shift is at least `1`, so `(1u64 << k) - 1` cannot underflow.
pub broadcast proof fn lemma_u64_unit_shift_pos(k: int)
    requires
        0 <= k < 64,
    ensures
        #![trigger (1u64 << (k as usize))]
        1u64 <= (1u64 << (k as usize)),
{
    let ku: u32 = k as u32;
    assert((ku < 64u32) ==> (1u64 <= (1u64 << ku))) by (bit_vector);
}

/// Masking with the low-`k`-bits mask `(1u64 << k) - 1` clears bit `b >= k` of any
/// word (AND associativity folded into the statement).
pub broadcast proof fn lemma_u64_masked_bit_clear(word: u64, mask: u64, k: int, b: int)
    requires
        0 <= k <= 64,
        k <= b < 64,
        mask == (1u64 << (k as usize)) - 1,
    ensures
        #![trigger ((word & mask) & (1u64 << (b as usize))), (1u64 << (k as usize))]
        ((word & mask) & (1u64 << (b as usize))) == 0,
{
    let ku: u32 = k as u32;
    let bu: u32 = b as u32;
    assert(((word & mask) & (1u64 << bu)) == 0u64) by (bit_vector)
        requires
            ku <= bu,
            bu < 64,
            mask == (1u64 << ku) - 1u64,
    ;
}

/// Masking with the low-`k`-bits mask keeps bit `b < k` of any word unchanged.
pub broadcast proof fn lemma_u64_masked_bit_keep(word: u64, mask: u64, k: int, b: int)
    requires
        0 < k <= 64,
        0 <= b < k,
        mask == (1u64 << (k as usize)) - 1,
    ensures
        #![trigger ((word & mask) & (1u64 << (b as usize))), (1u64 << (k as usize))]
        ((word & mask) & (1u64 << (b as usize))) == word & (1u64 << (b as usize)),
{
    let ku: u32 = k as u32;
    let bu: u32 = b as u32;
    assert(((word & mask) & (1u64 << bu)) == (word & (1u64 << bu))) by (bit_vector)
        requires
            bu < ku,
            ku <= 64,
            mask == (1u64 << ku) - 1u64,
    ;
}

/// Setting bit `b` (OR-ing the unit bit at `b`) makes that bit nonzero.
pub broadcast proof fn lemma_u64_setbit_bit_set(word: u64, b: int)
    requires
        0 <= b < 64,
    ensures
        #![trigger ((word | (1u64 << (b as usize))) & (1u64 << (b as usize)))]
        ((word | (1u64 << (b as usize))) & (1u64 << (b as usize))) != 0,
{
    let bu: u32 = b as u32;
    assert(((word | (1u64 << bu)) & (1u64 << bu)) == (1u64 << bu)) by (bit_vector);
    assert((bu < 64u32) ==> ((1u64 << bu) != 0u64)) by (bit_vector);
}

/// Setting bit `b` leaves a different in-range bit `b2` unchanged.
pub broadcast proof fn lemma_u64_setbit_bit_keep(word: u64, b: int, b2: int)
    requires
        0 <= b < 64,
        0 <= b2 < 64,
        b != b2,
    ensures
        #![trigger ((word | (1u64 << (b as usize))) & (1u64 << (b2 as usize))), (1u64 << (b as usize))]
        ((word | (1u64 << (b as usize))) & (1u64 << (b2 as usize))) == (word & (1u64 << (
        b2 as usize))),
{
    let bu: u32 = b as u32;
    let b2u: u32 = b2 as u32;
    assert((bu != b2u) ==> (((word | (1u64 << bu)) & (1u64 << b2u)) == (word & (1u64 << b2u))))
        by (bit_vector);
}

/// Clearing bit `b` (AND-ing the complement of the unit bit at `b`) clears that bit.
pub broadcast proof fn lemma_u64_clearbit_bit_clear(word: u64, b: int)
    requires
        0 <= b < 64,
    ensures
        #![trigger ((word & (!(1u64 << (b as usize)))) & (1u64 << (b as usize)))]
        ((word & (!(1u64 << (b as usize)))) & (1u64 << (b as usize))) == 0,
{
    let bu: u32 = b as u32;
    assert((word & (!(1u64 << bu))) & (1u64 << bu) == 0u64) by (bit_vector);
}

/// Clearing bit `b` leaves a different in-range bit `b2` unchanged.
pub broadcast proof fn lemma_u64_clearbit_bit_keep(word: u64, b: int, b2: int)
    requires
        0 <= b < 64,
        0 <= b2 < 64,
        b != b2,
    ensures
        #![trigger ((word & (!(1u64 << (b as usize)))) & (1u64 << (b2 as usize))), (1u64 << (b as usize))]
        ((word & (!(1u64 << (b as usize)))) & (1u64 << (b2 as usize))) == (word & (1u64 << (
        b2 as usize))),
{
    let bu: u32 = b as u32;
    let b2u: u32 = b2 as u32;
    assert((bu != b2u) ==> (((word & (!(1u64 << bu))) & (1u64 << b2u)) == (word & (1u64 << b2u))))
        by (bit_vector);
}

/// AND-ing the zero word with any word is zero.
pub proof fn lemma_u64_and_zero(x: u64)
    ensures
        0u64 & x == 0u64,
{
    assert(0u64 & x == 0u64) by (bit_vector);
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
}

} // verus!
