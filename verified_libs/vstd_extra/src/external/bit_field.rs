// SPDX-License-Identifier: MPL-2.0
//! External specification for [`::bit_field::BitField`](https://docs.rs/bit_field) on `u32`.
use vstd::{
    prelude::*,
    std_specs::range::{slice_range_end, slice_range_start},
};

use core::ops::RangeBounds;

verus! {

pub assume_specification<R: RangeBounds<usize>>[ <u32 as ::bit_field::BitField>::get_bits ](
    word: &u32,
    range: R,
) -> u32
    requires
        0 <= slice_range_start(&range) < slice_range_end(&range, 32) <= 32,
    returns
        ({
            let start = slice_range_start(&range);
            let width = slice_range_end(&range, 32) - start;
            (*word >> (start as u32)) & (u32::MAX >> ((32 - width) as u32))
        }),
;

} // verus!
