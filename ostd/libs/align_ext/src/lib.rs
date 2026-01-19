// SPDX-License-Identifier: MPL-2.0
#![allow(unused_macros)]
#![cfg_attr(not(test), no_std)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::pow2;
use vstd::arithmetic::power2::{lemma2_to64, lemma_pow2_strictly_increases};
use vstd::bits::*;
use vstd::pervasive::trigger;
use vstd::prelude::*;
use vstd_extra::prelude::*;

/// An extension trait for Rust integer types, including `u8`, `u16`, `u32`,
/// `u64`, and `usize`, to provide methods to make integers aligned to a
/// power of two.
pub trait AlignExt {
    /// Returns to the smallest number that is greater than or equal to
    /// `self` and is a multiple of the given power of two.
    ///
    /// The method panics if `power_of_two` is not a
    /// power of two or is smaller than 2 or the calculation overflows
    /// because `self` is too large.
    ///
    /// # Examples
    ///
    /// ```
    /// use crate::align_ext::AlignExt;
    /// assert_eq!(12usize.align_up(2), 12);
    /// assert_eq!(12usize.align_up(4), 12);
    /// assert_eq!(12usize.align_up(8), 16);
    /// assert_eq!(12usize.align_up(16), 16);
    /// ```
    fn align_up(self, power_of_two: Self) -> Self;

    /// Returns to the greatest number that is smaller than or equal to
    /// `self` and is a multiple of the given power of two.
    ///
    /// The method panics if `power_of_two` is not a
    /// power of two or is smaller than 2 or the calculation overflows
    /// because `self` is too large. In release mode,
    ///
    /// # Examples
    ///
    /// ```
    /// use crate::align_ext::AlignExt;
    /// assert_eq!(12usize.align_down(2), 12);
    /// assert_eq!(12usize.align_down(4), 12);
    /// assert_eq!(12usize.align_down(8), 8);
    /// assert_eq!(12usize.align_down(16), 0);
    /// ```
    fn align_down(self, power_of_two: Self) -> Self;
}

verus! {

proof fn lemma_usize_low_bits_mask_is_mod(x: usize, n: nat)
    requires
        n < usize::BITS,
    ensures
        (x & (low_bits_mask(n) as usize)) == x % (pow2(n) as usize),
{
    if usize::BITS == 64 {
        lemma_u64_low_bits_mask_is_mod(x as u64, n);
    } else {
        lemma_u32_low_bits_mask_is_mod(x as u32, n);
    }
}

} // verus!
macro_rules! call_lemma_low_bits_mask_is_mod {
    (u8, $x:expr, $n:expr) => {
        lemma_u8_low_bits_mask_is_mod($x, $n)
    };
    (u16, $x:expr, $n:expr) => {
        lemma_u16_low_bits_mask_is_mod($x, $n)
    };
    (u32, $x:expr, $n:expr) => {
        lemma_u32_low_bits_mask_is_mod($x, $n)
    };
    (u64, $x:expr, $n:expr) => {
        lemma_u64_low_bits_mask_is_mod($x, $n)
    };
    (usize, $x:expr, $n:expr) => {
        lemma_usize_low_bits_mask_is_mod($x, $n)
    };
}

macro_rules! impl_align_ext {
    ($( $uint_type:ty ),+,) => {
        $(
            #[verus_verify]
            impl AlignExt for $uint_type {
                #[inline]
                #[verus_spec(ret =>
                    requires
                        exists |e:nat| pow2(e) == align,
                        align >= 2,
                        self + (align - 1) <= $uint_type::MAX,
                    ensures
                        ret >= self,
                        ret % align == 0,
                        ret == nat_align_up(self as nat, align as nat),
                        forall |n: nat| !(n>=self && #[trigger] (n % align as nat) == 0) || (ret <= n),
                )]
                fn align_up(self, align: Self) -> Self {
                    //assert!(align.is_power_of_two() && align >= 2);
                    proof!{
                        let x_int = self as int + align as int - 1;
                        let x = x_int as Self;
                        if self as int % align as int == 0 {
                            assert((align as int - 1) % align as int == align as int - 1) by {
                                lemma_small_mod((align as int - 1) as nat, align as nat);
                            }
                            assert(x_int % align as int == align as int - 1) by {
                                lemma_mod_adds(self as int, align as int - 1, align as int);
                            }
                        } else {
                            let q = self as int / align as int;
                            let r = self as int % align as int;
                            lemma_fundamental_div_mod(self as int, align as int);

                            assert((q + 1) * align as int == q * align as int + align as int) by {
                                lemma_mul_is_distributive_add(align as int, q, 1);
                            }
                            assert(((q + 1) * align as int) % align as int == 0) by {
                                lemma_mod_multiples_basic(q + 1, align as int);
                            }
                            assert((r - 1) % align as int == r - 1) by {
                                lemma_small_mod((r - 1) as nat, align as nat);
                            }
                            assert(x_int % align as int == (r - 1)) by {
                                lemma_mod_adds((q + 1) * align as int, r - 1, align as int);
                            }
                        }

                        lemma_low_bits_mask_values();
                        let mask = (align - 1) as Self;
                        let e = choose |e: nat| pow2(e) == align;
                        assert(e < $uint_type::BITS) by {
                            if e >= $uint_type::BITS {
                                lemma_pow2_strictly_increases($uint_type::BITS as nat, e);
                                lemma2_to64();
                            }
                        }
                        call_lemma_low_bits_mask_is_mod!($uint_type, x, e);
                        assert(x == (x & mask) + (x & !mask)) by (bit_vector);
                        lemma_nat_align_up_sound(self as nat, align as nat);
                    }
                    self.checked_add(align - 1).unwrap() & !(align - 1)
                }

                #[inline]
                #[verus_spec(ret =>
                    requires
                        exists |e:nat| pow2(e) == align,
                        align >= 2,
                    ensures
                        ret <= self,
                        ret % align == 0,
                        ret == nat_align_down(self as nat, align as nat),
                        forall |n: nat|  !(n<=self && #[trigger] (n % align as nat) == 0) || (ret >= n),
                )]
                fn align_down(self, align: Self) -> Self {
                    //assert!(align.is_power_of_two() && align >= 2);
                    proof!{
                        lemma_low_bits_mask_values();
                        let mask = (align - 1) as Self;
                        let e = choose |e: nat| pow2(e) == align;
                        assert(e < $uint_type::BITS) by {
                            if e >= $uint_type::BITS {
                                lemma_pow2_strictly_increases($uint_type::BITS as nat, e);
                                lemma2_to64();
                            }
                        }
                        call_lemma_low_bits_mask_is_mod!($uint_type, self, e);
                        assert(self == (self & mask) + (self & !mask)) by (bit_vector);
                        assert((self & !mask) as nat == nat_align_down(self as nat, align as nat));
                        lemma_nat_align_down_sound(self as nat, align as nat);
                    }
                    self & !(align - 1)
                }
            }
        )*
    }
}

impl_align_ext! {
    u8,
    u16,
    u32,
    u64,
    usize,
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_align_up() {
        let input_ns = [0usize, 1, 2, 9, 15, 21, 32, 47, 50];
        let input_as = [2usize, 2, 2, 2, 4, 4, 8, 8, 8];
        let output_ns = [0usize, 2, 2, 10, 16, 24, 32, 48, 56];

        for i in 0..input_ns.len() {
            let n = input_ns[i];
            let a = input_as[i];
            let n2 = output_ns[i];
            assert!(n.align_up(a) == n2);
        }
    }

    #[test]
    fn test_align_down() {
        let input_ns = [0usize, 1, 2, 9, 15, 21, 32, 47, 50];
        let input_as = [2usize, 2, 2, 2, 4, 4, 8, 8, 8];
        let output_ns = [0usize, 0, 2, 8, 12, 20, 32, 40, 48];

        for i in 0..input_ns.len() {
            let n = input_ns[i];
            let a = input_as[i];
            let n2 = output_ns[i];
            assert!(n.align_down(a) == n2);
        }
    }
}
