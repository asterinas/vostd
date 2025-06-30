use vstd::prelude::*;
use vstd::bits::low_bits_mask;

verus! {

#[verifier::external_body]
pub fn low_bits_mask_usize(k: usize) -> (res: usize)
    requires
        0 <= k < 64,
    ensures
        res == low_bits_mask(k as nat),
{
    (1 << k) - 1
}

} // verus!
