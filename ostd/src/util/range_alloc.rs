// SPDX-License-Identifier: MPL-2.0
use alloc::collections::btree_map::BTreeMap;
use core::ops::Range;

use vstd::prelude::*;

use crate::specs::util::range_alloc_specs::RangeAllocatorModel;
use crate::sync::{PreemptDisabled, SpinLock, SpinLockGuard};

#[verus_verify]
pub struct RangeAllocator {
    fullrange: Range<usize>,
    freelist: SpinLock<Option<BTreeMap<usize, FreeRange>>, PreemptDisabled>,
}

/// An error returned when allocating from a [`RangeAllocator`].
#[verus_verify]
#[derive(Debug)]
pub struct RangeAllocError;

verus! {

impl View for RangeAllocator {
    type V = RangeAllocatorModel;

    /// Specification view of the allocator's managed full range. This is the
    /// only place that reads the private `fullrange` field (which is permitted
    /// in this module); public contracts refer to the range through `self@`,
    /// and the model itself lives in `ostd/specs/util/range_alloc_specs.rs`.
    closed spec fn view(&self) -> RangeAllocatorModel {
        RangeAllocatorModel { start: self.fullrange.start as int, end: self.fullrange.end as int }
    }
}

} // verus!
#[verus_verify]
impl RangeAllocator {
    #[verus_spec(ret =>
        ensures
            ret@.start == fullrange.start,
            ret@.end == fullrange.end,
    )]
    pub const fn new(fullrange: Range<usize>) -> Self {
        Self {
            fullrange,
            freelist: SpinLock::new(None),
        }
    }

    #[verus_spec(ret =>
        ensures
            ret.start == self@.start,
            ret.end == self@.end,
    )]
    pub const fn fullrange(&self) -> &Range<usize> {
        &self.fullrange
    }

    /// Allocates a specific kernel virtual area.
    #[verifier::external_body]
    #[verus_spec(res =>
        requires allocate_range.start < allocate_range.end,
        ensures
            res is Ok ==> (self@.start <= allocate_range.start
                && allocate_range.end <= self@.end),
    )]
    pub fn alloc_specific(&self, allocate_range: &Range<usize>) -> Result<(), RangeAllocError> {
        debug_assert!(allocate_range.start < allocate_range.end);

        let mut lock_guard = self.get_freelist_guard();
        let freelist = lock_guard.as_mut().unwrap();
        let mut target_node = None;
        let mut left_length = 0;
        let mut right_length = 0;

        for (key, value) in freelist.iter() {
            if value.block.end >= allocate_range.end && value.block.start <= allocate_range.start {
                target_node = Some(*key);
                left_length = allocate_range.start - value.block.start;
                right_length = value.block.end - allocate_range.end;
                break;
            }
        }

        if let Some(key) = target_node {
            if left_length == 0 {
                freelist.remove(&key);
            } else if let Some(freenode) = freelist.get_mut(&key) {
                freenode.block.end = allocate_range.start;
            }

            if right_length != 0 {
                freelist.insert(
                    allocate_range.end,
                    FreeRange::new(allocate_range.end..(allocate_range.end + right_length)),
                );
            }
        }

        if target_node.is_some() {
            Ok(())
        } else {
            Err(RangeAllocError)
        }
    }

    /// Allocates a range specific by the `size`.
    ///
    /// This is currently implemented with a simple FIRST-FIT algorithm.
    #[verifier::external_body]
    #[verus_spec(res =>
        ensures
            res is Ok ==> (res->Ok_0.end - res->Ok_0.start == size),
            res is Ok ==> (self@.start <= res->Ok_0.start
                && res->Ok_0.end <= self@.end),
    )]
    pub fn alloc(&self, size: usize) -> Result<Range<usize>, RangeAllocError> {
        let mut lock_guard = self.get_freelist_guard();
        let freelist = lock_guard.as_mut().unwrap();
        let mut allocate_range = None;
        let mut to_remove = None;

        for (key, value) in freelist.iter() {
            if value.block.end - value.block.start >= size {
                allocate_range = Some((value.block.end - size)..value.block.end);
                to_remove = Some(*key);
                break;
            }
        }

        if let Some(key) = to_remove {
            if let Some(freenode) = freelist.get_mut(&key) {
                if freenode.block.end - size == freenode.block.start {
                    freelist.remove(&key);
                } else {
                    freenode.block.end -= size;
                }
            }
        }

        if let Some(range) = allocate_range {
            Ok(range)
        } else {
            Err(RangeAllocError)
        }
    }

    /// Frees a `range`.
    #[verifier::external_body]
    pub fn free(&self, range: Range<usize>) {
        let mut lock_guard = self.freelist.lock();
        let freelist = lock_guard.as_mut().unwrap_or_else(|| {
            panic!("Free a 'KVirtArea' when 'VirtAddrAllocator' has not been initialized.")
        });
        // 1. get the previous free block, check if we can merge this block with the free one
        //     - if contiguous, merge this area with the free block.
        //     - if not contiguous, create a new free block, insert it into the list.
        let mut free_range = range.clone();

        if let Some((prev_va, prev_node)) = freelist
            .upper_bound_mut(core::ops::Bound::Excluded(&free_range.start))
            .peek_prev()
        {
            if prev_node.block.end == free_range.start {
                let prev_va = *prev_va;
                free_range.start = prev_node.block.start;
                freelist.remove(&prev_va);
            }
        }
        freelist.insert(free_range.start, FreeRange::new(free_range.clone()));

        // 2. check if we can merge the current block with the next block, if we can, do so.
        if let Some((next_va, next_node)) = freelist
            .lower_bound_mut(core::ops::Bound::Excluded(&free_range.start))
            .peek_next()
        {
            if free_range.end == next_node.block.start {
                let next_va = *next_va;
                free_range.end = next_node.block.end;
                freelist.remove(&next_va);
                freelist.get_mut(&free_range.start).unwrap().block.end = free_range.end;
            }
        }
    }

    #[verifier::external_body]
    fn get_freelist_guard(
        &self,
    ) -> SpinLockGuard<Option<BTreeMap<usize, FreeRange>>, PreemptDisabled> {
        let mut lock_guard = self.freelist.lock();
        if lock_guard.is_none() {
            let mut freelist: BTreeMap<usize, FreeRange> = BTreeMap::new();
            freelist.insert(self.fullrange.start, FreeRange::new(self.fullrange.clone()));
            *lock_guard = Some(freelist);
        }
        lock_guard
    }
}

#[verus_verify]
struct FreeRange {
    block: Range<usize>,
}

#[verus_verify]
impl FreeRange {
    #[verus_spec(ret =>
        ensures
            ret.block.start == range.start,
            ret.block.end == range.end,
    )]
    const fn new(range: Range<usize>) -> Self {
        Self { block: range }
    }
}
