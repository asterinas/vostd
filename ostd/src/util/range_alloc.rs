// SPDX-License-Identifier: MPL-2.0
use vstd::{prelude::*, resource::Loc};
use vstd_extra::{
    debug_assert,
    external::btree::*,
    panic::UnwrapOrPanic,
    resource::flags::{OneShotPending, OneShotSet},
    resource_invariant::ResourceInvariant,
    sum::Sum,
};

use alloc::collections::btree_map::BTreeMap;
use core::ops::Range;

use crate::sync::{PreemptDisabled, SpinLock, SpinLockGuard};

verus! {

ghost struct FreelistConstant {
    fullrange: Range<int>,
    initialized_id: Loc,
}

ghost struct FreelistInvariant;

closed spec fn freelist_wf(fullrange: Range<int>, freelist: Map<usize, FreeRange>) -> bool {
    forall|key: usize| #[trigger]
        freelist.contains_key(key) ==> {
            let block = freelist[key].block;
            &&& fullrange.start <= block.start <= block.end <= fullrange.end
        }
}

impl ResourceInvariant<Option<BTreeMap<usize, FreeRange>>> for FreelistInvariant {
    type Constant = FreelistConstant;

    type Resource = Sum<OneShotPending, OneShotSet>;

    closed spec fn inv(
        constant: FreelistConstant,
        freelist: Option<BTreeMap<usize, FreeRange>>,
        resource: Self::Resource,
    ) -> bool {
        &&& match resource {
            Sum::Left(pending) => {
                &&& pending.id() == constant.initialized_id
                &&& freelist is None
            },
            Sum::Right(set) => {
                &&& set.id() == constant.initialized_id
                &&& freelist is Some
                &&& freelist_wf(constant.fullrange, freelist->0@)
            },
        }
    }
}

} // verus!
#[verus_verify]
pub struct RangeAllocator {
    fullrange: Range<usize>,
    // TODO: PreemptDisabled added, SpinLock should be improved.
    freelist: SpinLock<Option<BTreeMap<usize, FreeRange>>, PreemptDisabled, FreelistInvariant>,
}

/// An error returned when allocating from a [`RangeAllocator`].
#[verus_verify]
#[derive(Debug)]
pub struct RangeAllocError;

verus! {

broadcast use {group_btree_extra_axioms, vstd::std_specs::btree::group_btree_axioms};

impl View for RangeAllocator {
    type V = Range<int>;

    /// Specification view of the allocator's managed full range.
    closed spec fn view(&self) -> Range<int> {
        Range { start: self.fullrange.start as int, end: self.fullrange.end as int }
    }
}

impl RangeAllocator {
    pub closed spec fn initialized_id(self) -> Loc {
        self.freelist.constant().initialized_id
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.freelist.constant().fullrange == self@
    }
}

impl RangeAllocator {
    pub const fn new(fullrange: Range<usize>) -> (ret: Self)
        ensures
            ret@.start == fullrange.start,
            ret@.end == fullrange.end,
    {
        let ghost fullrange_view = Range {
            start: fullrange.start as int,
            end: fullrange.end as int,
        };
        let tracked initialized = OneShotPending::new();
        let ghost constant = FreelistConstant {
            fullrange: fullrange_view,
            initialized_id: initialized.id(),
        };
        let tracked resource = Sum::Left(initialized);
        Self { fullrange, freelist: SpinLock::new(None, Ghost(constant), Tracked(resource)) }
    }
}

} // verus!
#[verus_verify]
impl RangeAllocator {
    #[verus_spec(ret =>
        ensures
            ret.start == self@.start,
            ret.end == self@.end,
    )]
    pub const fn fullrange(&self) -> &Range<usize> {
        &self.fullrange
    }

    /// Allocates a specific kernel virtual area.
    #[verus_spec(res =>
        with
            -> initialized: Tracked<OneShotSet>,
        requires
            self@.start <= allocate_range.start < allocate_range.end <= self@.end,
        ensures
            res is Ok ==> (self@.start <= allocate_range.start
                && allocate_range.end <= self@.end),
            initialized@.id() == self.initialized_id(),
    )]
    pub fn alloc_specific(&self, allocate_range: &Range<usize>) -> Result<(), RangeAllocError> {
        debug_assert!(allocate_range.start < allocate_range.end);

        proof_decl! {
            let tracked initialized: OneShotSet;
        }
        let mut lock_guard = #[verus_spec(with => Tracked(initialized))]
        self.get_freelist_guard();
        let freelist = lock_guard.as_mut().unwrap();
        let mut target_node = None;
        let mut left_length = 0;
        let mut right_length = 0;

        #[verus_spec(invariant
                self@.start <= allocate_range.start < allocate_range.end <= self@.end,
                right_length <= usize::MAX - allocate_range.end,
                freelist_wf(self@, freelist@),
                target_node matches Some(target_key) ==> {
                    &&& freelist@.contains_key(target_key)
                    &&& freelist@[target_key].block.start <= allocate_range.start
                        < allocate_range.end <= freelist@[target_key].block.end
                    &&& left_length == allocate_range.start - freelist@[target_key].block.start
                    &&& right_length == freelist@[target_key].block.end - allocate_range.end
                },
        )]
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

        let res = if target_node.is_some() {
            Ok(())
        } else {
            Err(RangeAllocError)
        };
        lock_guard.drop();
        #[verus_spec(with |= Tracked(initialized))]
        res
    }

    /// Allocates a range specific by the `size`.
    ///
    /// This is currently implemented with a simple FIRST-FIT algorithm.
    #[verus_spec(res =>
        with
            -> initialized: Tracked<OneShotSet>,
        requires self@.start <= self@.end,
        ensures
            res is Ok ==> (res->Ok_0.end - res->Ok_0.start == size),
            res is Ok ==> (self@.start <= res->Ok_0.start
                && res->Ok_0.end <= self@.end),
            initialized@.id() == self.initialized_id(),
    )]
    pub fn alloc(&self, size: usize) -> Result<Range<usize>, RangeAllocError> {
        proof_decl! {
            let tracked initialized: OneShotSet;
        }
        let mut lock_guard = #[verus_spec(with => Tracked(initialized))]
        self.get_freelist_guard();
        let freelist = lock_guard.as_mut().unwrap();
        let mut allocate_range: Option<Range<usize>> = None;
        let mut to_remove: Option<usize> = None;
        #[verus_spec(invariant
                allocate_range matches Some(range) ==> {
                    &&& range.end - range.start == size
                    &&& self@.start <= range.start
                    &&& range.end <= self@.end
                },
                to_remove matches Some(key) ==> {
                    &&& allocate_range is Some
                    &&& freelist@.contains_key(key)
                    &&& freelist@[key].block.start <= allocate_range->0.start
                    &&& freelist@[key].block.end == allocate_range->0.end
                },
                freelist_wf(self@, freelist@),
        )]
        for (key, value) in freelist.iter() {
            proof! {
                assert(freelist@.contains_key(*key));
            }
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

        let res = if let Some(range) = allocate_range {
            Ok(range)
        } else {
            Err(RangeAllocError)
        };
        lock_guard.drop();
        #[verus_spec(with |= Tracked(initialized))]
        res
    }

    /// Frees a `range`.
    #[verus_spec(
        with
            Tracked(initialized): Tracked<OneShotSet>,
        requires
            self@.start <= range.start <= range.end <= self@.end,
            initialized.id() == self.initialized_id(),
    )]
    pub fn free(&self, range: Range<usize>) {
        proof! {
            use_type_invariant(self);
        }
        let mut lock_guard = self.freelist.lock();
        proof_decl! {
            let tracked resource: &mut Sum<OneShotPending, OneShotSet>;
        }
        #[verus_spec(with => Tracked(resource))]
        lock_guard.tracked_borrow_mut_resource();
        proof! {
            if *resource is Left {
                resource.tracked_borrow_left().incompatible(&initialized);
            }
        }
        /* let freelist = lock_guard.as_mut().unwrap_or_else(|| {
            panic!("Free a 'KVirtArea' when 'VirtAddrAllocator' has not been initialized.")
        }); */
        let freelist = lock_guard.as_mut().unwrap_or_panic();
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
                proof! {
                    assert(!before_lower_bound(
                        next_va,
                        core::ops::Bound::Excluded(&free_range.start),
                    ));
                }
                freelist.remove(&next_va);
                freelist.get_mut(&free_range.start).unwrap().block.end = free_range.end;
            }
        }
        lock_guard.drop();
    }

    #[verus_spec(ret =>
        with
            -> initialized: Tracked<OneShotSet>,
        requires self@.start <= self@.end,
        ensures
            ret@ is Some,
            freelist_wf(self@, ret@->0@),
            ret.constant().fullrange == self@,
            ret.resource() is Right,
            ret.resource()->Right_0.id() == ret.constant().initialized_id,
            initialized@.id() == self.initialized_id(),
    )]
    fn get_freelist_guard(
        &self,
    ) -> SpinLockGuard<'_, Option<BTreeMap<usize, FreeRange>>, PreemptDisabled, FreelistInvariant>
    {
        proof! {
            use_type_invariant(self);
        }
        let mut lock_guard = self.freelist.lock();
        if lock_guard.is_none() {
            let mut freelist: BTreeMap<usize, FreeRange> = BTreeMap::new();
            freelist.insert(self.fullrange.start, FreeRange::new(self.fullrange.clone()));
            *lock_guard = Some(freelist);
        }
        proof_decl! {
            let tracked resource: &mut Sum<OneShotPending, OneShotSet>;
            let tracked initialized: OneShotSet;
        }
        #[verus_spec(with => Tracked(resource))]
        lock_guard.tracked_borrow_mut_resource();
        proof! {
            initialized = resource.tracked_ensure_set();
        }
        #[verus_spec(with |= Tracked(initialized))]
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
