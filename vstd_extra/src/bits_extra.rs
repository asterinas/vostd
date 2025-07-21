use vstd::prelude::*;
use vstd::arithmetic::power2::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::bits::*;

verus! {

pub proof fn lemma_usize_pow2_no_overflow(n: nat)
    requires
        n < usize::BITS,
    ensures
        0 < pow2(n) <= usize::MAX,
{
    lemma_pow2_pos(n);
    if usize::BITS == 32 {
        lemma_u32_pow2_no_overflow(n);
    } else if usize::BITS == 64 {
        lemma_u64_pow2_no_overflow(n);
    } else {
        assert(false);  // Unsupported usize size
    }
}

proof fn test(x: u64, shift: u64)
    requires
        0 <= shift < <u64>::BITS,
    ensures
        x * pow2(shift as nat) <= <u64>::MAX <==> x <= (<u64>::MAX >> shift),
{
    assert(<u64>::MAX >> shift == <u64>::MAX as nat / pow2(shift as nat)) by {
        lemma_u64_shr_is_div(<u64>::MAX, shift as u64);
    };

    lemma_pow2_pos(shift as nat);
    assert(pow2(shift as nat) > 0);

    if x * pow2(shift as nat) <= <u64>::MAX {
        assert(x <= (<u64>::MAX as nat) / pow2(shift as nat)) by {
            let p = pow2(shift as nat) as int;
            lemma_div_is_ordered(x as int * p, <u64>::MAX as int, p);
            lemma_div_by_multiple(x as int, p);
        };
        assert(x <= (<u64>::MAX >> shift));
    }
    if x <= (<u64>::MAX >> shift) {
        assert(x <= (<u64>::MAX as nat) / pow2(shift as nat));
        assert(x * pow2(shift as nat) <= <u64>::MAX as nat) by {
            let p = pow2(shift as nat) as int;
            let d = <u64>::MAX as int;
            let q = d / p;
            assert(x as int <= q);
            lemma_mul_inequality(x as int, q, p);
            lemma_remainder_lower(d, p);
            lemma_mul_is_commutative(q, p);
        };
        assert(x * pow2(shift as nat) <= <u64>::MAX);
    }
}

} // verus!
