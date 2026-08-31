// SPDX-License-Identifier: MPL-2.0
use vstd::prelude::*;
use vstd::resource::{Loc, set::*};
use vstd_extra::{
    debug_assert,
    external::btree::*,
    panic::{UnwrapOrPanic, may_panic},
    resource_invariant::ResourceInvariant,
};

use alloc::collections::btree_map::BTreeMap;
use core::ops::Range;

use crate::sync::{PreemptDisabled, SpinLock, SpinLockGuard};

verus! {

tracked struct FreelistResource {
    initialized_auth: GhostSetAuth<()>,
    initialized_empty: GhostSubset<()>,
    initialized_witness: Option<GhostPersistentSingleton<()>>,
}

struct FreelistConstant {
    fullrange: Range<int>,
    initialized_id: Loc,
}

struct FreelistInvariant;

closed spec fn initialized_resource(
    constant: FreelistConstant,
    resource: FreelistResource,
) -> bool {
    &&& resource.initialized_auth.id() == constant.initialized_id
    &&& resource.initialized_empty.id() == constant.initialized_id
    &&& resource.initialized_empty@.is_empty()
    &&& resource.initialized_auth@.contains(())
    &&& resource.initialized_witness is Some
    &&& resource.initialized_witness->0.id() == constant.initialized_id
    &&& resource.initialized_witness->0@ == ()
}

closed spec fn freelist_wf(fullrange: Range<int>, freelist: Map<usize, FreeRange>) -> bool {
    forall|key: usize| #[trigger]
        freelist.contains_key(key) ==> {
            let block = freelist[key].block;
            &&& fullrange.start <= block.start <= block.end <= fullrange.end
        }
}

proof fn lemma_freelist_wf_remove(
    fullrange: Range<int>,
    freelist: Map<usize, FreeRange>,
    key: usize,
)
    requires
        freelist_wf(fullrange, freelist),
    ensures
        freelist_wf(fullrange, freelist.remove(key)),
{
}

proof fn lemma_freelist_wf_insert(
    fullrange: Range<int>,
    freelist: Map<usize, FreeRange>,
    key: usize,
    value: FreeRange,
)
    requires
        freelist_wf(fullrange, freelist),
        fullrange.start <= value.block.start <= value.block.end <= fullrange.end,
    ensures
        freelist_wf(fullrange, freelist.insert(key, value)),
{
}

impl ResourceInvariant<Option<BTreeMap<usize, FreeRange>>> for FreelistInvariant {
    type Constant = FreelistConstant;

    type Resource = FreelistResource;

    closed spec fn inv(
        constant: FreelistConstant,
        freelist: Option<BTreeMap<usize, FreeRange>>,
        resource: Self::Resource,
    ) -> bool {
        &&& resource.initialized_auth.id() == constant.initialized_id
        &&& resource.initialized_empty.id() == constant.initialized_id
        &&& resource.initialized_empty@.is_empty()
        &&& resource.initialized_auth@.contains(()) == (freelist is Some)
        &&& match resource.initialized_witness {
            Some(witness) => {
                &&& witness.id() == constant.initialized_id
                &&& witness@ == ()
                &&& freelist is Some
            },
            None => freelist is None,
        }
        &&& freelist is Some ==> freelist_wf(constant.fullrange, freelist->0@)
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
        &&& self.freelist.constant().fullrange.start == self.fullrange.start
        &&& self.freelist.constant().fullrange.end == self.fullrange.end
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
        let tracked (initialized_auth, initialized_empty) = GhostSetAuth::new(Set::empty());
        let ghost constant = FreelistConstant {
            fullrange: fullrange_view,
            initialized_id: initialized_auth.id(),
        };
        let tracked resource = FreelistResource {
            initialized_auth,
            initialized_empty,
            initialized_witness: None,
        };
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
            -> initialized: Tracked<GhostPersistentSingleton<()>>,
        requires
            self@.start <= allocate_range.start < allocate_range.end <= self@.end,
        ensures
            res is Ok ==> (self@.start <= allocate_range.start
                && allocate_range.end <= self@.end),
            initialized@.id() == self.initialized_id(),
            initialized@@ == (),
    )]
    pub fn alloc_specific(&self, allocate_range: &Range<usize>) -> Result<(), RangeAllocError> {
        debug_assert!(allocate_range.start < allocate_range.end);

        proof_decl! {
            let tracked initialized: GhostPersistentSingleton<()>;
        }
        let mut lock_guard = #[verus_spec(with => Tracked(initialized))]
        self.get_freelist_guard();
        let freelist = lock_guard.as_mut().unwrap();
        let mut target_node = None;
        let mut left_length = 0;
        let mut right_length = 0;

        #[verus_spec(invariant
                self@.start <= allocate_range.start,
                allocate_range.end <= self@.end,
                right_length <= usize::MAX - allocate_range.end,
                freelist_wf(self@, freelist@),
                target_node is Some ==> freelist@.contains_key(target_node->0),
                target_node is Some ==>
                    freelist@[target_node->0].block.start <= allocate_range.start,
                target_node is Some ==>
                    allocate_range.end <= freelist@[target_node->0].block.end,
                target_node is Some ==>
                    left_length == allocate_range.start
                        - freelist@[target_node->0].block.start,
                target_node is Some ==>
                    right_length == freelist@[target_node->0].block.end - allocate_range.end,
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
            proof_decl! { let ghost old_freelist = freelist@; }
            if left_length == 0 {
                freelist.remove(&key);
                proof! {
                    lemma_freelist_wf_remove(self@, old_freelist, key);
                    assert(freelist_wf(self@, freelist@));
                }
            } else if let Some(freenode) = freelist.get_mut(&key) {
                freenode.block.end = allocate_range.start;
                proof! {
                    lemma_freelist_wf_remove(self@, old_freelist, key);
                    lemma_freelist_wf_insert(
                        self@,
                        old_freelist.remove(key),
                        key,
                        freelist@[key],
                    );
                    assert(freelist_wf(self@, freelist@));
                }
            }

            if right_length != 0 {
                proof_decl! { let ghost old_freelist = freelist@; }
                freelist.insert(
                    allocate_range.end,
                    FreeRange::new(allocate_range.end..(allocate_range.end + right_length)),
                );
                proof! {
                    lemma_freelist_wf_insert(
                        self@,
                        old_freelist,
                        allocate_range.end,
                        freelist@[allocate_range.end],
                    );
                    assert(freelist_wf(self@, freelist@));
                }
            }
        }

        let res = if target_node.is_some() {
            Ok(())
        } else {
            Err(RangeAllocError)
        };
        proof! {
            assert(freelist_wf(self@, freelist@));
            assert(initialized_resource(lock_guard.constant(), lock_guard.resource()));
        }
        lock_guard.drop();
        #[verus_spec(with |= Tracked(initialized))]
        res
    }

    /// Allocates a range specific by the `size`.
    ///
    /// This is currently implemented with a simple FIRST-FIT algorithm.
    #[verus_spec(res =>
        with
            -> initialized: Tracked<GhostPersistentSingleton<()>>,
        requires self@.start <= self@.end,
        ensures
            res is Ok ==> (res->Ok_0.end - res->Ok_0.start == size),
            res is Ok ==> (self@.start <= res->Ok_0.start
                && res->Ok_0.end <= self@.end),
            initialized@.id() == self.initialized_id(),
            initialized@@ == (),
    )]
    pub fn alloc(&self, size: usize) -> Result<Range<usize>, RangeAllocError> {
        proof_decl! {
            let tracked initialized: GhostPersistentSingleton<()>;
        }
        let mut lock_guard = #[verus_spec(with => Tracked(initialized))]
        self.get_freelist_guard();
        let freelist = lock_guard.as_mut().unwrap();
        proof! {
            use_type_invariant(self);
            assert(freelist_wf(self@, freelist@));
        }
        let mut allocate_range: Option<Range<usize>> = None;
        let mut to_remove: Option<usize> = None;
        #[verus_spec(invariant
                allocate_range is Some ==> allocate_range->0.end - allocate_range->0.start == size,
                allocate_range is Some ==> self@.start <= allocate_range->0.start,
                allocate_range is Some ==> allocate_range->0.end <= self@.end,
                to_remove is Some ==> allocate_range is Some,
                to_remove is Some ==> freelist@.contains_key(to_remove->0),
                to_remove is Some ==>
                    freelist@[to_remove->0].block.start <= allocate_range->0.start,
                to_remove is Some ==> freelist@[to_remove->0].block.end == allocate_range->0.end,
                freelist_wf(self@, freelist@),
        )]
        for (key, value) in freelist.iter() {
            proof! {
                assert(freelist@.contains_key(*key));
                assert(self@.start <= value.block.start <= value.block.end <= self@.end);
            }
            if value.block.end - value.block.start >= size {
                allocate_range = Some((value.block.end - size)..value.block.end);
                to_remove = Some(*key);
                break;
            }
        }

        if let Some(key) = to_remove {
            proof_decl! { let ghost old_freelist = freelist@; }
            if let Some(freenode) = freelist.get_mut(&key) {
                if freenode.block.end - size == freenode.block.start {
                    freelist.remove(&key);
                    proof! {
                        lemma_freelist_wf_remove(self@, old_freelist, key);
                        assert(freelist_wf(self@, freelist@));
                    }
                } else {
                    freenode.block.end -= size;
                    proof! {
                        let block = freelist@[key].block;
                        assert(self@.start <= block.start <= block.end <= self@.end);
                        lemma_freelist_wf_remove(self@, old_freelist, key);
                        lemma_freelist_wf_insert(
                            self@,
                            old_freelist.remove(key),
                            key,
                            freelist@[key],
                        );
                        assert(freelist_wf(self@, freelist@));
                    }
                }
            }
        }

        let res = if let Some(range) = allocate_range {
            Ok(range)
        } else {
            Err(RangeAllocError)
        };
        proof! {
            assert(freelist_wf(self@, freelist@));
            assert(initialized_resource(lock_guard.constant(), lock_guard.resource()));
        }
        lock_guard.drop();
        #[verus_spec(with |= Tracked(initialized))]
        res
    }

    /// Frees a `range`.
    #[verus_spec(
        with
            Tracked(initialized): Tracked<Option<GhostPersistentSingleton<()>>>,
        requires
            self@.start <= range.start <= range.end <= self@.end,
            initialized is Some ==> initialized->0.id() == self.initialized_id(),
            initialized is Some ==> initialized->0@ == (),
            initialized is None ==> may_panic(),
    )]
    pub fn free(&self, range: Range<usize>) {
        proof! {
            use_type_invariant(self);
        }
        let mut lock_guard = self.freelist.lock();
        proof! {
            assert(lock_guard.constant().fullrange == self@);
        }
        proof_decl! {
            let ghost lock_value = lock_guard@;
        }
        proof_decl! {
            let tracked resource: &mut FreelistResource;
        }
        #[verus_spec(with => Tracked(resource))]
        lock_guard.tracked_borrow_mut_resource();
        proof! {
            if initialized is Some {
                let tracked initialized = initialized.tracked_unwrap();
                initialized.agree(&resource.initialized_auth);
                assert(lock_value is Some);
            }
            assert(lock_guard@ is None ==> initialized is None);
            assert(lock_guard@ is None ==> may_panic());
        }
        /* let freelist = lock_guard.as_mut().unwrap_or_else(|| {
            panic!("Free a 'KVirtArea' when 'VirtAddrAllocator' has not been initialized.")
        }); */
        let freelist = lock_guard.as_mut().unwrap_or_panic();
        proof! {
            assert(freelist_wf(self@, freelist@));
        }
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
                proof_decl! { let ghost old_freelist = freelist@; }
                freelist.remove(&prev_va);
                proof! {
                    lemma_freelist_wf_remove(self@, old_freelist, prev_va);
                    assert(freelist_wf(self@, freelist@));
                }
            }
        }
        proof_decl! { let ghost old_freelist = freelist@; }
        freelist.insert(free_range.start, FreeRange::new(free_range.clone()));
        proof! {
            lemma_freelist_wf_insert(
                self@,
                old_freelist,
                free_range.start,
                freelist@[free_range.start],
            );
            assert(freelist_wf(self@, freelist@));
        }

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
                proof_decl! { let ghost old_freelist = freelist@; }
                freelist.remove(&next_va);
                proof! {
                    lemma_freelist_wf_remove(self@, old_freelist, next_va);
                    assert(freelist_wf(self@, freelist@));
                }
                proof_decl! { let ghost old_freelist = freelist@; }
                freelist.get_mut(&free_range.start).unwrap().block.end = free_range.end;
                proof! {
                    lemma_freelist_wf_remove(self@, old_freelist, free_range.start);
                    lemma_freelist_wf_insert(
                        self@,
                        old_freelist.remove(free_range.start),
                        free_range.start,
                        freelist@[free_range.start],
                    );
                    assert(freelist_wf(self@, freelist@));
                }
            }
        }
        proof! {
            assert(freelist_wf(self@, freelist@));
            assert(initialized_resource(lock_guard.constant(), lock_guard.resource()));
        }
        lock_guard.drop();
    }

    #[verus_spec(ret =>
        with
            -> initialized: Tracked<GhostPersistentSingleton<()>>,
        requires self@.start <= self@.end,
        ensures
            ret@ is Some,
            freelist_wf(self@, ret@->0@),
            ret.constant().fullrange == self@,
            initialized_resource(ret.constant(), ret.resource()),
            initialized@.id() == self.initialized_id(),
            initialized@@ == (),
    )]
    fn get_freelist_guard(
        &self,
    ) -> SpinLockGuard<'_, Option<BTreeMap<usize, FreeRange>>, PreemptDisabled, FreelistInvariant>
    {
        proof! {
            use_type_invariant(self);
        }
        let mut lock_guard = self.freelist.lock();
        proof! {
            assert(lock_guard.constant().fullrange == self@);
        }
        if lock_guard.is_none() {
            let mut freelist: BTreeMap<usize, FreeRange> = BTreeMap::new();
            freelist.insert(self.fullrange.start, FreeRange::new(self.fullrange.clone()));
            *lock_guard = Some(freelist);
        }
        proof_decl! {
            let tracked resource: &mut FreelistResource;
            let tracked initialized: GhostPersistentSingleton<()>;
        }
        #[verus_spec(with => Tracked(resource))]
        lock_guard.tracked_borrow_mut_resource();
        proof! {
            if resource.initialized_witness is Some {
                let tracked witness = resource.initialized_witness.tracked_borrow();
                initialized = witness.duplicate();
            } else {
                let tracked singleton = resource.initialized_auth.insert(());
                let tracked witness = singleton.persist();
                initialized = witness.duplicate();
                resource.initialized_witness = Some(witness);
            }
            assert(FreelistInvariant::inv(
                lock_guard.constant(),
                lock_guard.value(),
                lock_guard.resource(),
            ));
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
