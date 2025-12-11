use vstd::arithmetic::power::lemma_pow_strictly_increases_converse;
use vstd::arithmetic::power::pow;
use vstd::layout::is_power_2;
use vstd::prelude::*;
use vstd::bits::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::power2::*;
use vstd_extra::extra_num::lemma_is_power2_exists_pow2;
use vstd::arithmetic::power::lemma_pow_strictly_increases;
use vstd::arithmetic::mul::lemma_mul_is_commutative;

verus! {

// Power-of-2 bitwise alignment produces modular alignment
proof fn lemma_power2_and_alignment(x: u64, align_: u64)
    requires
        align_ > 0,
        is_power_2(align_ as int),
        align_ < u64::MAX as usize,
    ensures
        (x & !((align_ - 1) as u64)) % align_ == 0,
        (x & !((align_ - 1) as u64)) == x - (x % align_),
{
    lemma_is_power2_exists_pow2(align_ as nat);
    let n = choose|n: nat| pow2(n) == align_ as nat;
    assert(n < u64::BITS) by {
        assert(pow2(64) > u64::MAX) by {
            lemma2_to64();
        };
        // monotonicity
        lemma_pow2(n);
        lemma_pow2(64);
        lemma_pow_strictly_increases_converse(2, n, 64);
    };

    lemma_u64_low_bits_mask_is_mod(x, n);

    // Establish the relationships

    // x & !(mask) = x - (x & mask) for any mask
    assert((x & !((align_ - 1) as u64)) == x - (x & ((align_ - 1) as u64))) by (bit_vector);

    // x & mask = x % pow2(n)

    // x & !mask = x - (x % align_)

    // x = (x / align_) * align_ + (x % align_)
    // x - (x % align_) = (x / align_) * align_
    lemma_fundamental_div_mod(x as int, align_ as int);
    assert((x as int - (x as int % align_ as int)) == (x as int / align_ as int) * align_ as int);
    assert(((x as int / align_ as int) * align_ as int) % align_ as int == 0) by {
        lemma_mod_multiples_vanish(x as int / align_ as int, 0int, align_ as int);
    };
}

proof fn lemma_mask_bound_preservation(x: u64, mask: u64)
    ensures
        x & !mask >= x - mask,
{
    assert(x & !mask >= x - mask) by (bit_vector);
}

proof fn lemma_aligned_identity(x: u64, align_: u64)
    requires
        align_ > 0,
        is_power_2(align_ as int),
        align_ < u64::MAX as usize,
        x % align_ == 0,
    ensures
        x & !((align_ - 1) as u64) == x,
{
    // Reuse the logic from the original lemma but specialized for the aligned case
    lemma_is_power2_exists_pow2(align_ as nat);
    let n = choose|n: nat| pow2(n) == align_ as nat;

    // Prove n < u64::BITS
    assert(n < u64::BITS) by {
        assert(pow2(64) > u64::MAX) by {
            lemma2_to64();
        };
        lemma_pow2(n);
        lemma_pow2(64);
        lemma_pow_strictly_increases_converse(2, n, 64);
    };

    // Now use the low bits mask property
    lemma_u64_low_bits_mask_is_mod(x, n);

    // x & mask = x % pow2(n) = x % align_

    // Since x % align_ == 0, we have x & (align_ - 1) == 0

    // Use the bit identity: x & !mask = x - (x & mask)
    assert((x & !((align_ - 1) as u64)) == x - (x & ((align_ - 1) as u64))) by (bit_vector);
}

#[verifier::allow_in_spec]
pub fn align_down(x: usize, align: usize) -> (res: usize)
    requires
        is_power_2(align as int),
        align < u64::MAX as usize,
    ensures
        res > x - align,
        res <= x,
        res % align == 0,
        x % align == 0 ==> res == x,
    returns
        (x - (x % align)) as usize,
{
    let x_ = x as u64;
    let align_ = align as u64;
    let align_minus_1 = align_ - 1 as u64;
    let res_ = x_ & !align_minus_1;

    assert(res_ <= x_) by {
        assert(x_ & !align_minus_1 <= x_) by (bit_vector);
    };

    assert(res_ % align_ == 0) by {
        lemma_power2_and_alignment(x_, align_);
    };

    assert(res_ as usize == (x - (x % align)) as usize) by {
        lemma_power2_and_alignment(x_, align_);

        // res_ = x_ & !align_minus_1
        // align_minus_1 = align_ - 1

        // From the lemma, x_ & !((align_ - 1) as u64) == x_ - (x_ % align_)

        // Now we need to show the casting preserves equality
        // x_ % align_ == (x % align) as u64
    };

    res_ as usize
}

pub proof fn lemma_align_down_properties(x: usize, align: usize)
    by (nonlinear_arith)
    requires
        is_power_2(align as int),
        align < usize::MAX as usize,
    ensures
        align_down(x, align) as int == x as int - (x as int % align as int) == (x / align) * align,
        align_down(x, align) as nat == x as nat - (x as nat % align as nat) == (x / align) * align,
{
}

// FIXME: We can improve the proof of this function.
pub proof fn lemma_align_down_monotone(x: usize, y: usize, align: usize)
    requires
        is_power_2(align as int),
        align < u64::MAX as usize,
        x <= y,
    ensures
        align_down(x, align) <= align_down(y, align),
{
    lemma_align_down_properties(x, align);
    lemma_align_down_properties(y, align);
    assert(x as int / align as int <= y as int / align as int) by (nonlinear_arith)
        requires
            x as int <= y as int,
            align > 0,
    ;
    assert(x / align * align <= y / align * align) by (nonlinear_arith)
        requires
            x as int / align as int <= y as int / align as int,
            align > 0,
    ;
}

pub proof fn lemma_align_down_squeeze(x: usize, y: usize, z: usize, align: usize)
    requires
        is_power_2(align as int),
        align < u64::MAX as usize,
        x <= y <= z,
        align_down(x, align) == align_down(z, align),
    ensures
        align_down(x, align) == align_down(y, align),
{
    lemma_align_down_monotone(x, y, align);
    lemma_align_down_monotone(y, z, align);
}

} // verus!
