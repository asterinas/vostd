//! Bit-arithmetic predicates and lemmas for unsigned words.
use vstd::prelude::*;

/// Defines a bit-test predicate for an unsigned word type.
macro_rules! define_bit_is_set {
    ($name:ident, $uN:ty, $one:expr) => {
        verus! {
            /// Whether bit `b` of `w` is set.
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

/// Defines the common bit-algebra lemmas for an unsigned word type.
macro_rules! define_unsigned_bit_lemmas {
    (
        $uN:ty, $zero:expr, $one:expr, $width:expr, $width_u32:expr,
        $bit_is_set:ident,
        $allones_bit_it_set:ident,
        $unit_le_shl:ident,
        $masked_bit_clear:ident,
        $masked_bit_keep:ident,
        $setbit_bit_is_set:ident,
        $setbit_bit_unchanged:ident,
        $clearbit_not_bit_is_set:ident,
        $clearbit_bit_unchanged:ident,
        $and_zero:ident,
        $group:ident
    ) => {
        verus! {

        /// Every bit of the all-ones word is set.
        pub broadcast proof fn $allones_bit_it_set(k: int)
            requires
                0 <= k < $width,
            ensures
                #![trigger $bit_is_set(!$zero, k)]
                $bit_is_set(!$zero, k),
        {
            let ku: u32 = k as u32;
            assert((!$zero & ($one << ku)) == ($one << ku)) by (bit_vector);
            assert((ku < $width_u32) ==> (($one << ku) != $zero)) by (bit_vector);
        }

        /// An in-range unit shift is at least `1`, so `(1 << k) - 1` cannot underflow.
        pub broadcast proof fn $unit_le_shl(k: int)
            requires
                0 <= k < $width,
            ensures
                #![trigger ($one << (k as usize))]
                $one <= ($one << (k as usize)),
        {
            let ku: u32 = k as u32;
            assert((ku < $width_u32) ==> ($one <= ($one << ku))) by (bit_vector);
        }

        /// Masking with the low-`k`-bits mask clears every bit at or above `k`.
        pub broadcast proof fn $masked_bit_clear(word: $uN, mask: $uN, k: int, b: int)
            requires
                0 <= k <= $width,
                k <= b < $width,
                mask == ($one << (k as usize)) - $one,
            ensures
                #![trigger $bit_is_set(word & mask, b), ($one << (k as usize))]
                !$bit_is_set(word & mask, b),
        {
            let ku: u32 = k as u32;
            let bu: u32 = b as u32;
            assert(((word & mask) & ($one << bu)) == $zero) by (bit_vector)
                requires
                    ku <= bu,
                    bu < $width_u32,
                    mask == ($one << ku) - $one,
            ;
        }

        /// Masking with the low-`k`-bits mask keeps every bit below `k` unchanged.
        pub broadcast proof fn $masked_bit_keep(word: $uN, mask: $uN, k: int, b: int)
            requires
                0 < k <= $width,
                0 <= b < k,
                mask == ($one << (k as usize)) - $one,
            ensures
                #![trigger $bit_is_set(word & mask, b), ($one << (k as usize))]
                $bit_is_set(word & mask, b) == $bit_is_set(word, b),
        {
            let ku: u32 = k as u32;
            let bu: u32 = b as u32;
            assert(((word & mask) & ($one << bu)) == (word & ($one << bu))) by (bit_vector)
                requires
                    bu < ku,
                    ku <= $width_u32,
                    mask == ($one << ku) - $one,
            ;
        }

        /// Setting bit `b` makes that bit set.
        pub broadcast proof fn $setbit_bit_is_set(word: $uN, b: int)
            requires
                0 <= b < $width,
            ensures
                #![trigger $bit_is_set(word | ($one << (b as usize)), b)]
                $bit_is_set(word | ($one << (b as usize)), b),
        {
            let bu: u32 = b as u32;
            assert(((word | ($one << bu)) & ($one << bu)) == ($one << bu)) by (bit_vector);
            assert((bu < $width_u32) ==> (($one << bu) != $zero)) by (bit_vector);
        }

        /// Setting bit `b` leaves a different in-range bit `b2` unchanged.
        pub broadcast proof fn $setbit_bit_unchanged(word: $uN, b: int, b2: int)
            requires
                0 <= b < $width,
                0 <= b2 < $width,
                b != b2,
            ensures
                #![trigger $bit_is_set(word | ($one << (b as usize)), b2), ($one << (b as usize))]
                $bit_is_set(word | ($one << (b as usize)), b2) == $bit_is_set(word, b2),
        {
            let bu: u32 = b as u32;
            let b2u: u32 = b2 as u32;
            assert((bu != b2u) ==> (((word | ($one << bu)) & ($one << b2u))
                == (word & ($one << b2u)))) by (bit_vector);
        }

        /// Clearing bit `b` makes that bit clear.
        pub broadcast proof fn $clearbit_not_bit_is_set(word: $uN, b: int)
            requires
                0 <= b < $width,
            ensures
                #![trigger $bit_is_set(word & (!($one << (b as usize))), b)]
                !$bit_is_set(word & (!($one << (b as usize))), b),
        {
            let bu: u32 = b as u32;
            assert((word & (!($one << bu))) & ($one << bu) == $zero) by (bit_vector);
        }

        /// Clearing bit `b` leaves a different in-range bit `b2` unchanged.
        pub broadcast proof fn $clearbit_bit_unchanged(word: $uN, b: int, b2: int)
            requires
                0 <= b < $width,
                0 <= b2 < $width,
                b != b2,
            ensures
                #![trigger $bit_is_set(word & (!($one << (b as usize))), b2), ($one << (b as usize))]
                $bit_is_set(word & (!($one << (b as usize))), b2) == $bit_is_set(word, b2),
        {
            let bu: u32 = b as u32;
            let b2u: u32 = b2 as u32;
            assert((bu != b2u) ==> (((word & (!($one << bu))) & ($one << b2u))
                == (word & ($one << b2u)))) by (bit_vector);
        }

        /// AND-ing the zero word with any word is zero.
        pub proof fn $and_zero(x: $uN)
            ensures
                $zero & x == $zero,
        {
            assert($zero & x == $zero) by (bit_vector);
        }

        pub broadcast group $group {
            $allones_bit_it_set,
            $unit_le_shl,
            $masked_bit_clear,
            $masked_bit_keep,
            $setbit_bit_is_set,
            $setbit_bit_unchanged,
            $clearbit_not_bit_is_set,
            $clearbit_bit_unchanged,
        }

        } // verus!
    };
}

define_unsigned_bit_lemmas!(
    u8,
    0u8,
    1u8,
    8,
    8u32,
    u8_bit_is_set,
    lemma_u8_allones_bit_it_set,
    lemma_u8_unit_le_shl,
    lemma_u8_masked_bit_clear,
    lemma_u8_masked_bit_keep,
    lemma_u8_setbit_bit_is_set,
    lemma_u8_setbit_bit_unchanged,
    lemma_u8_clearbit_not_bit_is_set,
    lemma_u8_clearbit_bit_unchanged,
    lemma_u8_and_zero,
    group_u8_bit_algebra
);
define_unsigned_bit_lemmas!(
    u16,
    0u16,
    1u16,
    16,
    16u32,
    u16_bit_is_set,
    lemma_u16_allones_bit_it_set,
    lemma_u16_unit_le_shl,
    lemma_u16_masked_bit_clear,
    lemma_u16_masked_bit_keep,
    lemma_u16_setbit_bit_is_set,
    lemma_u16_setbit_bit_unchanged,
    lemma_u16_clearbit_not_bit_is_set,
    lemma_u16_clearbit_bit_unchanged,
    lemma_u16_and_zero,
    group_u16_bit_algebra
);
define_unsigned_bit_lemmas!(
    u32,
    0u32,
    1u32,
    32,
    32u32,
    u32_bit_is_set,
    lemma_u32_allones_bit_it_set,
    lemma_u32_unit_le_shl,
    lemma_u32_masked_bit_clear,
    lemma_u32_masked_bit_keep,
    lemma_u32_setbit_bit_is_set,
    lemma_u32_setbit_bit_unchanged,
    lemma_u32_clearbit_not_bit_is_set,
    lemma_u32_clearbit_bit_unchanged,
    lemma_u32_and_zero,
    group_u32_bit_algebra
);
define_unsigned_bit_lemmas!(
    u64,
    0u64,
    1u64,
    64,
    64u32,
    u64_bit_is_set,
    lemma_u64_allones_bit_it_set,
    lemma_u64_unit_le_shl,
    lemma_u64_masked_bit_clear,
    lemma_u64_masked_bit_keep,
    lemma_u64_setbit_bit_is_set,
    lemma_u64_setbit_bit_unchanged,
    lemma_u64_clearbit_not_bit_is_set,
    lemma_u64_clearbit_bit_unchanged,
    lemma_u64_and_zero,
    group_u64_bit_algebra
);
define_unsigned_bit_lemmas!(
    u128,
    0u128,
    1u128,
    128,
    128u32,
    u128_bit_is_set,
    lemma_u128_allones_bit_it_set,
    lemma_u128_unit_le_shl,
    lemma_u128_masked_bit_clear,
    lemma_u128_masked_bit_keep,
    lemma_u128_setbit_bit_is_set,
    lemma_u128_setbit_bit_unchanged,
    lemma_u128_clearbit_not_bit_is_set,
    lemma_u128_clearbit_bit_unchanged,
    lemma_u128_and_zero,
    group_u128_bit_algebra
);
define_unsigned_bit_lemmas!(
    usize,
    0usize,
    1usize,
    usize::BITS as int,
    usize::BITS,
    usize_bit_is_set,
    lemma_usize_allones_bit_it_set,
    lemma_usize_unit_le_shl,
    lemma_usize_masked_bit_clear,
    lemma_usize_masked_bit_keep,
    lemma_usize_setbit_bit_is_set,
    lemma_usize_setbit_bit_unchanged,
    lemma_usize_clearbit_not_bit_is_set,
    lemma_usize_clearbit_bit_unchanged,
    lemma_usize_and_zero,
    group_usize_bit_algebra
);
