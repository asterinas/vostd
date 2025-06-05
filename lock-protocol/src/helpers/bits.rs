use vstd::prelude::*;
use vstd::bits::low_bits_mask;

verus! {

#[verifier::external_body]
pub fn low_bits_mask_u64(k: u64) -> (res: u64)
    requires
        0 <= k < 64,
    ensures
        res == low_bits_mask(k as nat),
{
    (1 << k) - 1
}

} // verus!
