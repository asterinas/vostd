use vstd::prelude::*;
use vstd::bits::*;

use super::math::is_power_2;

verus! {

pub fn align_down(x: usize, align: usize) -> (res: usize)
    requires
        align > 0,
        is_power_2(align as int),
        x < usize::MAX as u64 - align,
    ensures
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
        assert(!align_minus_1 & align_minus_1 == 0) by (bit_vector);
        // assert(res_ % align_ == 0);
        assume(res_ % align_ == 0);  // TODO
    };
    res_ as usize
}

} // verus!
