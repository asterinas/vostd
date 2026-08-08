// SPDX-License-Identifier: MPL-2.0
//! Spec model for [`RangeAllocator`](crate::util::range_alloc::RangeAllocator).
use vstd::prelude::*;

verus! {

/// Spec model capturing the managed full range of a `RangeAllocator`.
///
/// The exec `RangeAllocator` exposes this model via its `View` implementation
/// (defined inline in `ostd/src/util/range_alloc.rs`, since reading the private
/// `fullrange` field is only permitted in that module). Public function contracts
/// then refer to the allocator's range through `self@` instead of touching the
/// private field directly.
pub ghost struct RangeAllocatorModel {
    pub ghost start: int,
    pub ghost end: int,
}

impl RangeAllocatorModel {
    pub open spec fn new(start: int, end: int) -> Self {
        RangeAllocatorModel { start, end }
    }
}

} // verus!
