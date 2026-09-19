//! Specifications for bit-related standard-library functions.
use crate::bits::u64_bit_is_set;
use vstd::prelude::*;

verus! {

/// The number of set bits among the lowest `n` bits of `w`.
spec fn u64_set_bits_rec(w: u64, n: u64) -> int
    decreases n,
{
    if n == 0 {
        0
    } else {
        u64_bit_is_set(w, (n - 1) as int) as int + u64_set_bits_rec(w, (n - 1) as u64)
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
        let prev = (n - 1) as u64;
        lemma_u64_set_bits_rec_bounds(w, prev);
        if w >> n == 0 {
            if w == 0 {
                assert(u64_bit_is_set(w, prev as int) == false) by {
                    assert((w & (1u64 << (prev as usize))) == 0u64) by (bit_vector)
                        requires
                            w == 0,
                    ;
                }
                assert(w >> prev == 0) by (bit_vector)
                    requires
                        w == 0,
                ;
            } else {
                if u64_bit_is_set(w, prev as int) {
                    assert(1 <= u64_bit_is_set(w, prev as int) as int);
                } else {
                    assert((w & (1u64 << (prev as usize))) == 0u64);
                    assert(w >> prev == 0) by (bit_vector)
                        requires
                            0 < n <= 64,
                            prev == n - 1,
                            w >> n == 0,
                            (w & (1u64 << (prev as usize))) == 0u64,
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
