use vstd::arithmetic::logarithm::lemma_log_pow;
use vstd::arithmetic::logarithm::lemma_log_s;
use vstd::arithmetic::logarithm::log;
use vstd::arithmetic::power::pow;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;
use vstd::bits::*;
use vstd::math::*;

verus! {

fn test() {
    reveal(pow2);
    reveal(pow);
    assert(pow2(31) == 0x80000000) by (compute_only);
    assert(pow2(39) == 0x8000000000) by (compute_only);

    broadcast use lemma_log_s;

    assert(log(2, 512) == 9) by {
        assert(512 == pow(2, 9)) by (compute_only);
        assert(log(2, 512) == 9) by { lemma_log_pow(2, 9) }
    };
}

fn test2() {
    broadcast use lemma_u64_shl_is_mul;

    assert(4096 << 1 != 0) by (compute_only);
}

} // verus!
