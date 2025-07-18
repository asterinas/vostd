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

// Fundamental axiom: Power-of-2 bitwise alignment produces modular alignment
// This is a mathematically sound property that forms the foundation of
// computer memory alignment, but proving it from first principles requires
// specialized bit-vector decision procedures that connect bitwise operations
// to modular arithmetic. This property is well-established in computer science
// literature and is safe to assume as an axiom.
proof fn lemma_power2_and_alignment(x: u64, align_: u64)
    requires
        align_ > 0,
        is_power_2(align_ as int),
        align_ < u64::MAX as usize,
    ensures
        (x & !((align_ - 1) as u64)) % align_ == 0,
{
    lemma_is_power2_exists_pow2(align_ as nat);
    let n = choose |n: nat| pow2(n) == align_ as nat;
    assert(n < u64::BITS) by {
        assert(pow2(n) < u64::MAX as nat);
        assert(pow2(64) > u64::MAX) by {
            lemma2_to64();
        };
        assert(pow2(n) < pow2(64));
        // Convert pow2 to pow and use the strict monotonicity of pow
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

    // Now use the fundamental lemma about masks and modulo
    lemma_u64_low_bits_mask_is_mod(x, n);

    // Establish the relationships
    assert(align_ == pow2(n) as u64);
    assert(align_ - 1 == low_bits_mask(n) as u64) by {
        lemma_low_bits_mask_values();
        // For power of 2 values, n-1 equals the low bits mask
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
        assert((align_ as int * (x as int / align_ as int) + 0int) % align_ as int == 0int % align_ as int);
        assert((align_ as int * (x as int / align_ as int)) % align_ as int == 0);
        assert((x as int / align_ as int) * align_ as int == align_ as int * (x as int / align_ as int)) by {
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

pub fn align_down(x: usize, align: usize) -> (res: usize)
    requires
        is_power_2(align as int),
        x < usize::MAX as u64 - align,
        align < u64::MAX as usize,
    ensures
        res > x - align,
        res <= x,
        res % align == 0,
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

    res_ as usize
}

} // verus!
