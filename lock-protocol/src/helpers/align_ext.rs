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
        assert(pow2(n) < u64::MAX as nat);
        assert(pow2(64) > u64::MAX) by {
            lemma2_to64();
        };
        assert(pow2(n) < pow2(64));
        // monotonicity
        lemma_pow2(n);
        lemma_pow2(64);
        assert(pow(2, n) < pow(2, 64)) by {
            assert(pow2(n) == pow(2, n) as nat);
            assert(pow2(64) == pow(2, 64) as nat);
        };
        lemma_pow_strictly_increases_converse(2, n, 64);
        assert(n < 64);
        assert(u64::BITS == 64);
    };

    lemma_u64_low_bits_mask_is_mod(x, n);

    // Establish the relationships
    assert(align_ == pow2(n) as u64);
    assert(align_ - 1 == low_bits_mask(n) as u64) by {
        lemma_low_bits_mask_values();
        // low bits mask
        assert(pow2(n) - 1 == low_bits_mask(n));
    };

    // x & !(mask) = x - (x & mask) for any mask
    assert((x & !((align_ - 1) as u64)) == x - (x & ((align_ - 1) as u64))) by (bit_vector);

    // x & mask = x % pow2(n)
    assert((x & ((align_ - 1) as u64)) == x % (pow2(n) as u64));
    assert((x & ((align_ - 1) as u64)) == x % align_);

    // x & !mask = x - (x % align_)
    assert((x & !((align_ - 1) as u64)) == x - (x % align_));

    // x = (x / align_) * align_ + (x % align_)
    // x - (x % align_) = (x / align_) * align_
    lemma_fundamental_div_mod(x as int, align_ as int);
    assert(x as int == (x as int / align_ as int) * align_ as int + (x as int % align_ as int));
    assert((x as int - (x as int % align_ as int)) == (x as int / align_ as int) * align_ as int);
    assert(((x as int / align_ as int) * align_ as int) % align_ as int == 0) by {
        lemma_mod_multiples_vanish(x as int / align_ as int, 0int, align_ as int);
        assert((align_ as int * (x as int / align_ as int) + 0int) % align_ as int == 0int
            % align_ as int);
        assert((align_ as int * (x as int / align_ as int)) % align_ as int == 0);
        assert((x as int / align_ as int) * align_ as int == align_ as int * (x as int
            / align_ as int)) by {
            lemma_mul_is_commutative(x as int / align_ as int, align_ as int);
        };
    };
    assert((x as int - (x as int % align_ as int)) % align_ as int == 0);
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
        assert(pow2(n) < u64::MAX as nat);
        assert(pow2(64) > u64::MAX) by {
            lemma2_to64();
        };
        assert(pow2(n) < pow2(64));
        lemma_pow2(n);
        lemma_pow2(64);
        assert(pow(2, n) < pow(2, 64)) by {
            assert(pow2(n) == pow(2, n) as nat);
            assert(pow2(64) == pow(2, 64) as nat);
        };
        lemma_pow_strictly_increases_converse(2, n, 64);
        assert(n < 64);
        assert(u64::BITS == 64);
    };

    // Now use the low bits mask property
    lemma_u64_low_bits_mask_is_mod(x, n);

    assert(align_ == pow2(n) as u64);
    assert(align_ - 1 == low_bits_mask(n) as u64) by {
        lemma_low_bits_mask_values();
        assert(pow2(n) - 1 == low_bits_mask(n));
    };

    // x & mask = x % pow2(n) = x % align_
    assert((x & ((align_ - 1) as u64)) == x % (pow2(n) as u64));
    assert((x & ((align_ - 1) as u64)) == x % align_);

    // Since x % align_ == 0, we have x & (align_ - 1) == 0
    assert(x & ((align_ - 1) as u64) == 0);

    // Use the bit identity: x & !mask = x - (x & mask)
    assert((x & !((align_ - 1) as u64)) == x - (x & ((align_ - 1) as u64))) by (bit_vector);
    assert(x - (x & ((align_ - 1) as u64)) == x - 0);
    assert(x - 0 == x);
    assert(x & !((align_ - 1) as u64) == x);
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

    assert(res_ > x_ - align_) by {
        lemma_mask_bound_preservation(x_, align_minus_1);
    };

    assert(x % align == 0 ==> res_ as usize == x) by {
        if x % align == 0 {
            // If x is already aligned, then x_ % align_ == 0
            assert(x_ % align_ == 0);

            // Use the specialized lemma for aligned inputs
            lemma_aligned_identity(x_, align_);

            // From the lemma: x_ & !((align_ - 1) as u64) == x_
            // Since res_ = x_ & !align_minus_1 and align_minus_1 == (align_ - 1) as u64
            assert(align_minus_1 == (align_ - 1) as u64);
            assert(res_ == x_ & !align_minus_1);
            assert(x_ & !align_minus_1 == x_ & !((align_ - 1) as u64));
            assert(x_ & !((align_ - 1) as u64) == x_);
            assert(res_ == x_);
        }
    };

    assert(res_ as usize == (x - (x % align)) as usize) by {
        lemma_power2_and_alignment(x_, align_);

        // res_ = x_ & !align_minus_1
        // align_minus_1 = align_ - 1
        assert(align_minus_1 == (align_ - 1) as u64);
        assert(res_ == x_ & !align_minus_1);
        assert(x_ & !align_minus_1 == x_ & !((align_ - 1) as u64));

        // From the lemma, x_ & !((align_ - 1) as u64) == x_ - (x_ % align_)
        assert(res_ == x_ - (x_ % align_));

        // Now we need to show the casting preserves equality
        // x_ % align_ == (x % align) as u64
        assert(x_ % align_ == (x % align) as u64);
        assert(x_ - (x_ % align_) == (x as u64) - ((x % align) as u64));
        assert((x as u64) - ((x % align) as u64) == (x - (x % align)) as u64);
        assert(res_ == (x - (x % align)) as u64);
        assert(res_ as usize == (x - (x % align)) as usize);
    };

    res_ as usize
}

} // verus!
