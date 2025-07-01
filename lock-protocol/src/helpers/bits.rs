use vstd::prelude::*;
use vstd::bits::{
    low_bits_mask, lemma_u32_shl_is_mul, lemma_u64_shl_is_mul, lemma_u32_pow2_no_overflow,
    lemma_u64_pow2_no_overflow,
};

verus! {

pub fn low_bits_mask_usize(k: usize) -> usize
    requires
        0 <= k < 64,
    returns
        low_bits_mask(k as nat) as usize,
{
    proof {
        if (usize::BITS == 32) {
            lemma_u32_pow2_no_overflow(k as nat);
            lemma_u32_shl_is_mul(1, k as u32);
        } else {
            lemma_u64_pow2_no_overflow(k as nat);
            lemma_u64_shl_is_mul(1, k as u64);
        }
    }
    (1 << k) - 1
}

} // verus!
