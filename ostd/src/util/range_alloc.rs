// SPDX-License-Identifier: MPL-2.0
//! A verified first-fit range allocator.
//!
//! # Verified Properties
//!
//! The free list is hidden behind a spin lock and modeled as an abstract set of
//! addresses. Construction returns a splittable [`GhostSubset`] permission.
//! Allocating a specific range consumes the corresponding permission and
//! returns a [`GhostSubRange`] allocation token; freeing performs the inverse
//! transition.
#[cfg(feature = "irc11")]
use vstd::thread_view::Objective;
use vstd::{
    prelude::*,
    resource::{
        Loc,
        set::{GhostSetAuth, GhostSubset},
    },
    seq_lib::lemma_seq_contains_after_push,
    std_specs::btree::{
        CursorMutModel, before_lower_bound, before_upper_bound, positioned_at_lower_bound,
        positioned_at_upper_bound,
    },
    std_specs::cmp::OrdSpec,
};
use vstd_extra::{
    debug_assert,
    panic::UnwrapOrPanic,
    range::RangeExtraFns,
    resource::flags::{OneShotPending, OneShotSet},
    resource::range::GhostSubRange,
    resource_invariant::ResourceInvariant,
    sum::Sum,
};

use crate::sync::{PreemptDisabled, SpinLock, SpinLockGuard};
use alloc::collections::btree_map::BTreeMap;
use core::ops::Range;

#[verus_verify]
pub struct RangeAllocator {
    fullrange: Range<usize>,
    freelist: SpinLock<Option<BTreeMap<usize, FreeRange>>, PreemptDisabled, FreelistInvariant>,
}

/// An error returned when allocating from a [`RangeAllocator`].
#[verus_verify]
#[derive(Debug)]
pub struct RangeAllocError;

verus! {

impl View for RangeAllocator {
    type V = Range<usize>;

    closed spec fn view(&self) -> Range<usize> {
        self.fullrange
    }
}

impl RangeAllocator {
    /// The identifier shared by this allocator's allocated-set authority and allocation tokens.
    pub closed spec fn id(self) -> Loc {
        self.freelist.constant().allocated_id
    }

    /// The identifier shared by this allocator's free-set authority and allocation permissions.
    pub closed spec fn free_id(self) -> Loc {
        self.freelist.constant().free_id
    }

    /// The free permission and borrowed allocation tokens account for this allocator's full range.
    pub open spec fn owns_free_pool(
        self,
        permit: GhostSubset<usize>,
        allocations: Seq<GhostSubRange<usize>>,
    ) -> bool {
        &&& permit.id() == self.free_id()
        &&& forall|i: int|
            0 <= i < allocations.len() ==> #[trigger] allocations[i].id() == self.id()
        &&& forall|address: usize| #[trigger]
            self@.view_set().contains(address) ==> {
                permit@.contains(address) || exists|i: int|
                    0 <= i < allocations.len() && #[trigger] allocations[i]@.contains(address)
            }
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.freelist.constant().fullrange == self@ && self@.start <= self@.end
    }
}

ghost struct FreelistConstant {
    fullrange: Range<usize>,
    initialized_id: Loc,
    free_id: Loc,
    allocated_id: Loc,
}

ghost struct FreelistInvariant;

/// The set-of-ranges view of a free-list map, dropping its keys and `FreeRange` wrapper.
closed spec fn freelist_model(freelist: Map<usize, FreeRange>) -> Set<Range<usize>> {
    freelist.dom().map(|key: usize| freelist[key].block)
}

/// The addresses covered by the free-list ranges.
closed spec fn free_set(freelist: Set<Range<usize>>) -> Set<usize> {
    freelist.map(|block: Range<usize>| block.view_set()).flatten()
}

/// Concrete-map well-formedness used while verifying `BTreeMap` operations.
closed spec fn concrete_freelist_wf(
    fullrange: Range<usize>,
    freelist: Map<usize, FreeRange>,
) -> bool {
    &&& fullrange.start <= fullrange.end
    &&& forall|key: usize| #[trigger]
        freelist.contains_key(key) ==> {
            let block = freelist[key].block;
            &&& fullrange.start <= block.start <= block.end <= fullrange.end
            &&& (block.start < block.end || fullrange.start == fullrange.end)
            &&& key == block.start
        }
    &&& forall|left: usize, right: usize|
        #![trigger freelist.contains_key(left), freelist.contains_key(right)]
        freelist.contains_key(left) && freelist.contains_key(right) && left != right
            ==> freelist[left].block.view_set().disjoint(freelist[right].block.view_set())
}

/// Distinct free-list blocks are not adjacent; maximal free runs are merged.
closed spec fn freelist_blocks_not_adjacent(freelist: Map<usize, FreeRange>) -> bool {
    forall|left: usize, right: usize|
        #![trigger freelist.contains_key(left), freelist.contains_key(right)]
        freelist.contains_key(left) && freelist.contains_key(right) && left != right
            ==> freelist[left].block.end < freelist[right].block.start || freelist[right].block.end
            < freelist[left].block.start
}

/// Whether `block` wholly covers `range`.
closed spec fn block_contains(block: Range<usize>, range: Range<usize>) -> bool {
    block.start <= range.start && range.end <= block.end
}

/// Splittable free-range permissions for a sequence of allocators.
pub type RangeAllocatorPermits = Seq<GhostSubset<usize>>;

/// Lock-guarded proof resource: initialization state, the authoritative set,
/// and the authoritative free and allocated address sets.
tracked struct FreelistResource {
    initialized: Sum<OneShotPending, OneShotSet>,
    free: GhostSetAuth<usize>,
    allocated: GhostSetAuth<usize>,
}

#[cfg(feature = "irc11")]
unsafe impl Objective for FreelistResource {

}

impl ResourceInvariant<Option<BTreeMap<usize, FreeRange>>> for FreelistInvariant {
    type Constant = FreelistConstant;

    type Resource = FreelistResource;

    closed spec fn inv(
        constant: FreelistConstant,
        freelist: Option<BTreeMap<usize, FreeRange>>,
        resource: Self::Resource,
    ) -> bool {
        &&& resource.free.id() == constant.free_id
        &&& resource.allocated.id() == constant.allocated_id
        &&& match resource.initialized {
            Sum::Left(pending) => {
                &&& pending.id() == constant.initialized_id
                &&& freelist is None
                &&& resource.free@ == constant.fullrange.view_set()
                &&& resource.allocated@ == Set::empty()
            },
            Sum::Right(set) => {
                &&& set.id() == constant.initialized_id
                &&& freelist is Some
                &&& concrete_freelist_wf(constant.fullrange, freelist->0@)
                &&& freelist_blocks_not_adjacent(freelist->0@)
                &&& resource.free@ == free_set(freelist_model(freelist->0@))
                &&& resource.allocated@ == constant.fullrange.view_set() - resource.free@
            },
        }
    }
}

} // verus!
#[verus_verify]
impl RangeAllocator {
    #[verus_spec(ret =>
        with -> permit: Tracked<GhostSubset<usize>>,
        requires
            fullrange.start <= fullrange.end,
        ensures
            ret@.start == fullrange.start,
            ret@.end == fullrange.end,
            permit@.id() == ret.free_id(),
            permit@@ == fullrange.view_set(),
    )]
    /* `#[verus_spec]` on a `const fn` does not keep `proof_decl!` locals visible to
     * `verus_exec_expr!` in the active Verus toolchain, so this constructor cannot remain const.
     * Origin Rust: pub const fn new(fullrange: Range<usize>) -> Self {
     */
    pub fn new(fullrange: Range<usize>) -> Self {
        proof_decl! {
            let tracked initialized = OneShotPending::alloc();
            let tracked (free, permit) = GhostSetAuth::new(fullrange.view_set());
            let tracked (allocated, empty_allocated) = GhostSetAuth::new(Set::empty());
            let ghost constant = FreelistConstant {
                fullrange,
                initialized_id: initialized.id(),
                free_id: free.id(),
                allocated_id: allocated.id(),
            };
            let tracked resource = FreelistResource {
                initialized: Sum::Left(initialized),
                free,
                allocated,
            };
        }

        #[verus_spec(with |= Tracked(permit))]
        verus_exec_expr! {
            Self {
                fullrange,
                freelist: SpinLock::new(None, Ghost(constant), Tracked(resource)),
            }
        }
    }

    #[verus_spec(returns self@)]
    pub const fn fullrange(&self) -> &Range<usize> {
        &self.fullrange
    }

    /// Allocates a specific kernel virtual area.
    ///
    /// # Verified Properties
    ///
    /// ## Safety
    /// - No unsafe code; no panic under the verified contract.
    ///
    /// ## Functional Correctness
    /// - Returns `Ok` for `allocate_range` under the free-range permission
    ///   precondition.
    ///
    /// ## Preconditions
    /// - The target range is non-empty and lies within this allocator's range.
    /// - Supply a free-range permission for exactly `allocate_range`.
    ///
    /// ## Postconditions
    /// - Consumes the free-range permission and returns a [`GhostSubRange`]
    ///   proving ownership of the allocated range, consumed by
    ///   [`RangeAllocator::free`].
    #[verus_spec(res =>
        with
            Tracked(permit): Tracked<GhostSubRange<usize>>,
            -> allocated: Tracked<Option<GhostSubRange<usize>>>,
        requires
            self@.start <= allocate_range.start < allocate_range.end <= self@.end,
            permit.id() == self.free_id(),
            permit.range() == allocate_range,
        ensures
            res is Ok,
            allocated@ matches Some(token) && {
                &&& token.id() == self.id()
                &&& token.range() == allocate_range
            },
    )]
    pub fn alloc_specific(&self, allocate_range: &Range<usize>) -> Result<(), RangeAllocError> {
        debug_assert!(allocate_range.start < allocate_range.end);

        let mut lock_guard = self.get_freelist_guard();
        proof_decl! {
            let tracked allocated: Option<GhostSubRange<usize>>;
            let ghost initial_map = lock_guard@->0@;
            let ghost initial_freelist = freelist_model(initial_map);
            let ghost mut checked = Set::<(usize, FreeRange)>::empty();
        }
        proof! {
            let tracked resource = lock_guard.tracked_borrow_mut_resource();
            permit.tracked_borrow().agree(&resource.free);
            lemma_contiguous_subset_has_covering_block(
                self@,
                initial_map,
                *allocate_range,
            );
        }
        let freelist = lock_guard.as_mut().unwrap();
        let mut target_node = None;
        let mut left_length = 0;
        let mut right_length = 0;
        #[verus_spec(it =>
            invariant
                self@.start <= allocate_range.start < allocate_range.end <= self@.end,
                right_length <= usize::MAX - allocate_range.end,
                concrete_freelist_wf(self@, freelist@),
                freelist_blocks_not_adjacent(freelist@),
                freelist@ == initial_map,
                freelist_model(freelist@) == initial_freelist,
                it.seq().unref().to_set() == freelist@.kv_pairs(),
                target_node matches Some(target_key) ==> {
                    &&& freelist@.contains_key(target_key)
                    &&& freelist@[target_key].block.start <= allocate_range.start
                        < allocate_range.end <= freelist@[target_key].block.end
                    &&& left_length == allocate_range.start - freelist@[target_key].block.start
                    &&& right_length == freelist@[target_key].block.end - allocate_range.end
                },
            invariant_except_break
                target_node is None,
                checked == it.seq()[..it.index()].unref().to_set(),
                it.index() == it.seq().len() ==> checked == it.seq().unref().to_set(),
                forall|entry: (usize, FreeRange)|
                    #![trigger checked.contains(entry)]
                    checked.contains(entry) ==> !block_contains(
                        entry.1.block,
                        *allocate_range,
                    ),
            ensures
                target_node is None ==> forall|entry: (usize, FreeRange)|
                    #![trigger freelist@.kv_pairs().contains(entry)]
                    freelist@.kv_pairs().contains(entry) ==> !block_contains(
                        entry.1.block,
                        *allocate_range,
                    ),
        )]
        for (key, value) in freelist.iter() {
            if value.block.end >= allocate_range.end && value.block.start <= allocate_range.start {
                target_node = Some(*key);
                left_length = allocate_range.start - value.block.start;
                right_length = value.block.end - allocate_range.end;
                break;
            }
            proof! {
                let ghost entry = (*key, *value);
                checked = checked.insert(entry);
                assert(it.seq()[..it.index() + 1].unref() ==
                    it.seq()[..it.index()].unref().push(entry));
                assert(checked == it.seq()[..it.index() + 1].unref().to_set()) by {
                    assert forall|candidate: (usize, FreeRange)|
                        checked.contains(candidate) <==>
                            it.seq()[..it.index() + 1].unref().to_set().contains(candidate) by {
                        lemma_seq_contains_after_push(
                            it.seq()[..it.index()].unref(),
                            entry,
                            candidate,
                        );
                    }
                }
                if it.index() + 1 == it.seq().len() {
                    assert(it.seq()[..it.index() + 1] == it.seq());
                }
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
        proof! {
            if res is Err {
                let key = choose|key: usize|
                    #![trigger initial_map.contains_key(key)]
                    initial_map.contains_key(key)
                        && block_contains(initial_map[key].block, *allocate_range);
                assert(freelist@.kv_pairs().contains((key, freelist@[key])));
                assert(false);
            }
            let tracked resource = lock_guard.tracked_borrow_mut_resource();
            if res is Ok {
                let ghost key = target_node->0;
                lemma_alloc_specific_model(
                    self@,
                    initial_map,
                    freelist@,
                    key,
                    *allocate_range,
                );
                resource.free.delete(permit.tracked_into_subset());
                let tracked subset = resource.allocated.insert_set(allocate_range.view_set());
                allocated = Some(GhostSubRange::tracked_new(subset, *allocate_range));
                assert(resource.allocated@ == lock_guard.constant().fullrange.view_set()
                    - resource.free@);
            } else {
                allocated = None;
            }
        }
        lock_guard.drop();
        #[verus_spec(with |= Tracked(allocated))]
        res
    }

    /// Allocates a range specific by the `size`.
    ///
    /// This is currently implemented with a simple FIRST-FIT algorithm.
    ///
    /// # Verified Properties
    ///
    /// ## Safety
    /// - No unsafe code; no panic under the verified contract.
    ///
    /// ## Functional Correctness
    /// - On `Ok`, the returned range lies within `self@` and has exactly
    ///   `size` addresses.
    ///
    /// ## Preconditions
    /// - Supply the remaining free-address permission and borrow the allocation
    ///   tokens that together account for this allocator's full range.
    /// - Split permissions can be used independently with `alloc_specific`;
    ///   `alloc` requires ownership of the entire current free pool.
    ///
    /// ## Postconditions
    /// - On `Ok`, removes the returned range from the supplied permission and
    ///   returns a [`GhostSubRange`] proving ownership, consumed by
    ///   [`RangeAllocator::free`]. On `Err`, no allocation token is returned.
    /// - Append the returned token to the borrowed collection before calling
    ///   `alloc` again. On failure, the existing permissions remain usable.
    #[verus_spec(res =>
        with
            Tracked(permit): Tracked<&mut GhostSubset<usize>>,
            Tracked(allocations): Tracked<&Seq<GhostSubRange<usize>>>,
            -> allocated: Tracked<Option<GhostSubRange<usize>>>,
        requires
            self.owns_free_pool(*old(permit), *allocations),
        ensures
            res matches Ok(res) ==> {
                &&& res.end - res.start == size
                &&& self@.start <= res.start <= res.end <= self@.end
                &&& allocated@ matches Some(token) && {
                    &&& token.id() == self.id()
                    &&& token.range() == res
                    &&& self.owns_free_pool(*final(permit), allocations.push(token))
                }
            },
            res is Ok <==> allocated@ is Some,
            final(permit).id() == old(permit).id(),
            res matches Ok(range) ==> final(permit)@ == old(permit)@ - range.view_set(),
            res matches Ok(range) ==> range.view_set() <= old(permit)@,
            res is Err ==> final(permit)@ == old(permit)@,
    )]
    pub fn alloc(&self, size: usize) -> Result<Range<usize>, RangeAllocError> {
        let mut lock_guard = self.get_freelist_guard();
        proof! {
            proof fn lemma_allocations_agree(
                tracked allocations: &Seq<GhostSubRange<usize>>,
                tracked authority: &GhostSetAuth<usize>,
                count: int,
            )
                requires
                    0 <= count <= allocations.len(),
                    forall|i: int| 0 <= i < allocations.len() ==> #[trigger]
                        allocations[i].id() == authority.id(),
                ensures
                    forall|i: int| 0 <= i < count ==> #[trigger] allocations[i]@
                        <= authority@,
                decreases count,
            {
                if count > 0 {
                    lemma_allocations_agree(allocations, authority, count - 1);
                    let tracked token = allocations.tracked_borrow(count - 1);
                    token.tracked_borrow().agree(authority);
                }
            }

            let tracked resource = lock_guard.tracked_borrow_mut_resource();
            permit.agree(&resource.free);
            lemma_allocations_agree(allocations, &resource.allocated, allocations.len() as int);
            assert(resource.free@ <= permit@) by {
                assert forall|address: usize| #[trigger] resource.free@.contains(address) implies
                    permit@.contains(address) by {
                    lemma_concrete_free_set_contains(lock_guard@->0@, address);
                    let key = choose|key: usize| #[trigger]
                        lock_guard@->0@.contains_key(key)
                            && lock_guard@->0@[key].block.view_set().contains(address);
                    assert(self@.view_set().contains(address));
                    if !permit@.contains(address) {
                        let j = choose|j: int| 0 <= j < allocations.len()
                            && #[trigger] allocations[j]@.contains(address);
                        assert(allocations[j]@ <= resource.allocated@);
                    }
                }
            }
            assert(permit@ == resource.free@);
        }
        let freelist = lock_guard.as_mut().unwrap();
        proof_decl! {
            let tracked allocated: Option<GhostSubRange<usize>>;
            let ghost initial_map = freelist@;
            let ghost initial_freelist = freelist_model(freelist@);
        }
        let mut allocate_range: Option<Range<usize>> = None;
        let mut to_remove: Option<usize> = None;
        #[verus_spec(invariant
                allocate_range is Some <==> to_remove is Some,
                to_remove matches Some(key) ==> allocate_range matches Some(range) && {
                    &&& range.end - range.start == size
                    &&& self@.start <= range.start
                    &&& range.end <= self@.end
                    &&& freelist@.contains_key(key)
                    &&& freelist@[key].block.start <= range.start
                    &&& freelist@[key].block.end == range.end
                },
                concrete_freelist_wf(self@, freelist@),
                freelist_blocks_not_adjacent(freelist@),
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

        proof! {
            if let Some(key) = to_remove {
                lemma_free_set_contains_range(initial_freelist, freelist@[key].block);
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

        proof! {
            let tracked resource = lock_guard.tracked_borrow_mut_resource();
            if allocate_range is Some {
                let ghost range = allocate_range -> 0;
                lemma_alloc_suffix_model(self@, initial_map, freelist@, to_remove->0, range);
                let ghost permit_before = *permit;
                let tracked free_subset = permit.split(range.view_set());
                resource.free.delete(free_subset);
                let tracked allocated_subset = resource.allocated.insert_set(range.view_set());
                let tracked token = GhostSubRange::tracked_new(allocated_subset, range);
                let ghost next_allocations = allocations.push(token);
                assert(self.owns_free_pool(*permit, next_allocations)) by {
                    assert forall|address: usize| #[trigger] self@.view_set().contains(address)
                        implies permit@.contains(address) || exists|i: int|
                            0 <= i < next_allocations.len()
                                && #[trigger] next_allocations[i]@.contains(address) by {
                        if !permit@.contains(address) {
                            if range.view_set().contains(address) {
                                assert(next_allocations[allocations.len() as int]@
                                    .contains(address));
                            } else {
                                assert(!permit_before@.contains(address));
                                let i = choose|i: int| 0 <= i < allocations.len()
                                    && #[trigger] allocations[i]@.contains(address);
                                assert(next_allocations[i]@.contains(address));
                            }
                        }
                    }
                }
                allocated = Some(token);
                assert(resource.allocated@ == lock_guard.constant().fullrange.view_set()
                    - resource.free@);
            } else {
                allocated = None;
            }
        }
        lock_guard.drop();
        #[verus_spec(with |= Tracked(allocated))]
        if let Some(range) = allocate_range {
            Ok(range)
        } else {
            Err(RangeAllocError)
        }
    }

    /// Frees a `range`.
    ///
    /// # Verified Properties
    ///
    /// ## Safety
    /// - No unsafe code.
    ///
    /// ## Preconditions
    /// - The range to free lies within this allocator's range.
    /// - Supply the allocation token returned when this exact range was
    ///   allocated. The token is consumed by this operation.
    ///
    /// ## Postconditions
    /// - Returns a free-range permission for the released range. Its underlying
    ///   subset can be combined with the allocator's remaining free permission.
    #[verus_verify(spinoff_prover)]
    #[verus_spec(
        with
            Tracked(allocated): Tracked<GhostSubRange<usize>>,
            -> free_permit: Tracked<GhostSubRange<usize>>,
        requires
            self@.start <= range.start < range.end <= self@.end,
            allocated.id() == self.id(),
            allocated.range() == range,
        ensures
            free_permit@.id() == self.free_id(),
            free_permit@.range() == range,
    )]
    pub fn free(&self, range: Range<usize>) {
        proof! {
            use_type_invariant(self);
        }
        let mut lock_guard = self.freelist.lock();
        proof_decl! {
            let tracked free_permit: GhostSubRange<usize>;
            let tracked resource = lock_guard.tracked_borrow_mut_resource();
            let tracked allocated_subset = allocated.tracked_borrow();
            allocated_subset.agree(&resource.allocated);
            if resource.initialized is Left {
                assert(resource.allocated@.is_empty());
                assert(allocated_subset@.contains(range.start));
                assert(false);
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
        proof_decl! {
            let ghost before_left_map = freelist@;
            let ghost before_left_range = free_range;
            let ghost mut merged_left = false;
        }

        /* Retaining the cursor in a local keeps its verified position model available to the
         * proof; it does not change the lookup, mutation, or control flow.
         * Origin Rust: if let Some((prev_va, prev_node)) = freelist
         *     .upper_bound_mut(core::ops::Bound::Excluded(&free_range.start))
         *     .peek_prev()
         * {
         */
        let mut prev_cursor =
            freelist.upper_bound_mut(core::ops::Bound::Excluded(&free_range.start));
        proof_decl! {
            let ghost prev_cursor_model = prev_cursor@;
        }
        if let Some((prev_va, prev_node)) = prev_cursor.peek_prev() {
            proof! {
                assert(before_upper_bound(
                    *prev_va,
                    core::ops::Bound::Excluded(&free_range.start),
                ));
            }
            if prev_node.block.end == free_range.start {
                let prev_va = *prev_va;
                free_range.start = prev_node.block.start;
                freelist.remove(&prev_va);
                proof! {
                    assert(freelist@ == before_left_map.remove(prev_va));
                    lemma_remove_left_neighbor(
                        self@,
                        before_left_map,
                        freelist@,
                        prev_va,
                        before_left_range,
                        free_range,
                    );
                    merged_left = true;
                }
            }
            proof! {
                assert forall|key: usize| #[trigger] freelist@.contains_key(key)
                    implies freelist@[key].block.end != free_range.start by {
                    if freelist@[key].block.end == free_range.start {
                        lemma_upper_bound_prev_is_maximal(
                            prev_cursor_model,
                            before_left_range.start,
                            *prev_va,
                            key,
                        );
                        if key != *prev_va {
                            assert(before_left_map.contains_key(key));
                            assert(before_left_map.contains_key(*prev_va));
                            assert(false);
                        } else {
                            assert(false);
                        }
                    }
                }
            }
        }
        proof! {
            if prev_cursor_model.position == 0 {
                assert forall|key: usize| #[trigger] freelist@.contains_key(key)
                    implies freelist@[key].block.end != free_range.start by {
                    if freelist@[key].block.end == free_range.start {
                        lemma_upper_bound_has_previous(
                            prev_cursor_model,
                            before_left_range.start,
                            key,
                        );
                        assert(false);
                    }
                }
            }
        }
        proof_decl! {
            if !merged_left {
                assert(freelist@ == before_left_map);
            }
            let ghost before_insert_map = freelist@;
        }
        freelist.insert(free_range.start, FreeRange::new(free_range.clone()));
        proof_decl! {
            lemma_insert_free_range(self@, before_insert_map, freelist@, free_range);
            let ghost before_right_map = freelist@;
            let ghost before_right_range = free_range;
            let ghost mut merged_right = false;
        }
        // 2. check if we can merge the current block with the next block, if we can, do so.
        /* Retaining the cursor in a local keeps its verified position model available to the
         * proof; it does not change the lookup, mutation, or control flow.
         * Origin Rust: if let Some((next_va, next_node)) = freelist
         *     .lower_bound_mut(core::ops::Bound::Excluded(&free_range.start))
         *     .peek_next()
         * {
         */
        let mut next_cursor =
            freelist.lower_bound_mut(core::ops::Bound::Excluded(&free_range.start));
        proof_decl! {
            let ghost next_cursor_model = next_cursor@;
        }
        if let Some((next_va, next_node)) = next_cursor.peek_next() {
            proof! {
                assert(!before_lower_bound(
                    *next_va,
                    core::ops::Bound::Excluded(&free_range.start),
                ));
            }
            if free_range.end == next_node.block.start {
                let next_va = *next_va;
                free_range.end = next_node.block.end;
                freelist.remove(&next_va);
                freelist.get_mut(&free_range.start).unwrap().block.end = free_range.end;
                proof! {
                    assert(freelist@ == before_right_map.remove(next_va).insert(
                        before_right_range.start,
                        FreeRange { block: free_range },
                    ));
                    lemma_merge_right_neighbor(
                        self@,
                        before_right_map,
                        freelist@,
                        next_va,
                        before_right_range,
                        free_range,
                    );
                    merged_right = true;
                }
            }
            proof! {
                assert forall|key: usize| #[trigger] freelist@.contains_key(key)
                    implies key == free_range.start
                        || freelist@[key].block.start != free_range.end by {
                    if key != free_range.start
                        && freelist@[key].block.start == free_range.end {
                        lemma_lower_bound_next_is_minimal(
                            next_cursor_model,
                            before_right_range.start,
                            *next_va,
                            key,
                        );
                        if merged_right {
                            assert(before_right_map.contains_key(key));
                            assert(before_right_map.contains_key(*next_va));
                            assert(before_insert_map.contains_key(*next_va));
                            assert(before_left_map.contains_key(key));
                            assert(before_left_map.contains_key(*next_va));
                            assert(before_left_map[key] == before_right_map[key]);
                            assert(before_right_map[*next_va].block.end == free_range.end);
                            assert(false);
                        } else {
                            assert(freelist@ == before_right_map);
                            if key == *next_va {
                                assert(false);
                            } else {
                                assert(*next_va < key);
                                assert(before_right_map.contains_key(*next_va));
                                assert(before_right_map.contains_key(before_right_range.start));
                                assert(concrete_freelist_wf(self@, before_right_map));
                                assert(before_right_map[*next_va].block.view_set().contains(
                                    *next_va,
                                ));
                                assert(false);
                            }
                        }
                    }
                }
            }
        }
        proof! {
            if next_cursor_model.position == next_cursor_model.keys.len() {
                assert forall|key: usize| #[trigger] freelist@.contains_key(key)
                    implies key == free_range.start
                        || freelist@[key].block.start != free_range.end by {
                    if key != free_range.start
                        && freelist@[key].block.start == free_range.end {
                        assert(freelist@[key].block.start == key);
                        lemma_lower_bound_has_next(
                            next_cursor_model,
                            before_right_range.start,
                            key,
                        );
                        assert(false);
                    }
                }
            }
        }
        proof! {
            lemma_restored_freelist_is_separated(
                self@,
                before_left_map,
                freelist@,
                free_range.start,
                free_range,
            );
        }
        proof! {
            let tracked resource = lock_guard.tracked_borrow_mut_resource();
            resource.allocated.delete(allocated.tracked_into_subset());
            let tracked free_subset = resource.free.insert_set(range.view_set());
            free_permit = GhostSubRange::tracked_new(free_subset, range);
            assert(resource.allocated@ == lock_guard.constant().fullrange.view_set()
                - resource.free@);
            assert(resource.free@ == free_set(freelist_model(freelist@))) by {
                if !merged_right {
                    assert(freelist@ == before_right_map);
                }
            }
        }
        #[verus_spec(with |= Tracked(free_permit))]
        lock_guard.drop()
    }

    #[verus_spec(ret =>
        ensures
            ret@ is Some,
            ret@ matches Some(freelist) ==> {
                &&& concrete_freelist_wf(self@, freelist@)
                &&& freelist_blocks_not_adjacent(freelist@)
                &&& ret.resource().free@ == free_set(freelist_model(freelist@))
                &&& ret.resource().allocated@ == self@.view_set() - ret.resource().free@
            },
            ret.constant().fullrange == self@,
            ret.constant().free_id == self.free_id(),
            ret.constant().allocated_id == self.id(),
            ret.resource().free.id() == self.free_id(),
            ret.resource().allocated.id() == self.id(),
            ret.resource().initialized is Right,
            ret.resource().initialized->Right_0.id() == ret.constant().initialized_id,
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
            proof_decl! {
                let tracked resource = lock_guard.tracked_borrow_mut_resource();
                let tracked pending = resource.initialized.tracked_swap_left(OneShotPending::alloc());
                resource.initialized = Sum::Right(pending.set());
                assert(freelist_model(lock_guard@->0@) == Set::empty().insert(self@)) by {
                    assert forall|block: Range<usize>|
                        freelist_model(lock_guard@->0@).contains(block) <==>
                            #[trigger] Set::empty().insert(self@).contains(block) by {
                        if Set::empty().insert(self@).contains(block) {
                            assert(lock_guard@->0@.dom().contains(self.fullrange.start));
                        }
                    }
                }
                let ghost freelist = Set::empty().insert(self@);
                freelist.lemma_map_contains(|range: Range<usize>| range.view_set(), self@.view_set());
                assert(exists|range: Range<usize>|
                    freelist.contains(range) && self@.view_set() == #[trigger] range.view_set()) by {
                }
            }
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
    #[verus_spec(ret => returns (Self { block: range }))]
    const fn new(range: Range<usize>) -> Self {
        Self { block: range }
    }
}

// Auxiliary set-model lemmas backing the allocator proofs above.

verus! {

proof fn lemma_free_set_contains_range(freelist: Set<Range<usize>>, block: Range<usize>)
    requires
        freelist.contains(block),
    ensures
        block.view_set() <= free_set(freelist),
{
    freelist.lemma_map_contains(|range: Range<usize>| range.view_set(), block.view_set());
}

proof fn lemma_concrete_free_set_contains(freelist: Map<usize, FreeRange>, address: usize)
    ensures
        free_set(freelist_model(freelist)).contains(address) <==> (exists|key: usize| #[trigger]
            freelist.contains_key(key) && freelist[key].block.view_set().contains(address)),
{
    let ranges = freelist_model(freelist);

    if exists|key: usize| #[trigger]
        freelist.contains_key(key) && freelist[key].block.view_set().contains(address) {
        let key = choose|key: usize| #[trigger]
            freelist.contains_key(key) && freelist[key].block.view_set().contains(address);
        let range = freelist[key].block;
        freelist.dom().lemma_map_contains(|key: usize| freelist[key].block, range);
        ranges.lemma_map_contains(|range: Range<usize>| range.view_set(), range.view_set());
    }
}

proof fn lemma_upper_bound_has_previous(
    model: CursorMutModel<usize, FreeRange>,
    bound: usize,
    key: usize,
)
    requires
        model.wf(),
        positioned_at_upper_bound(model, core::ops::Bound::Excluded(&bound)),
        model.map.contains_key(key),
        before_upper_bound(key, core::ops::Bound::Excluded(&bound)),
    ensures
        model.position > 0,
{
    let key_idx = choose|i: int| 0 <= i < model.keys.len() && #[trigger] model.keys[i] == key;
    if model.position == 0 {
        assert(false);
    }
}

proof fn lemma_upper_bound_prev_is_maximal(
    model: CursorMutModel<usize, FreeRange>,
    bound: usize,
    previous: usize,
    key: usize,
)
    requires
        model.wf(),
        positioned_at_upper_bound(model, core::ops::Bound::Excluded(&bound)),
        model.map.contains_key(key),
        before_upper_bound(key, core::ops::Bound::Excluded(&bound)),
        model.position > 0,
        previous == model.keys[model.position - 1],
    ensures
        key <= previous,
{
    let key_idx = choose|i: int| 0 <= i < model.keys.len() && #[trigger] model.keys[i] == key;
    if key_idx < model.position - 1 {
        assert(model.keys[key_idx].cmp_spec(&model.keys[model.position - 1]) is Less);
    }
}

proof fn lemma_lower_bound_has_next(
    model: CursorMutModel<usize, FreeRange>,
    bound: usize,
    key: usize,
)
    requires
        model.wf(),
        positioned_at_lower_bound(model, core::ops::Bound::Excluded(&bound)),
        model.map.contains_key(key),
        !before_lower_bound(key, core::ops::Bound::Excluded(&bound)),
    ensures
        model.position < model.keys.len(),
{
    let key_idx = choose|i: int| 0 <= i < model.keys.len() && #[trigger] model.keys[i] == key;
    if model.position == model.keys.len() {
        assert(false);
    }
}

proof fn lemma_lower_bound_next_is_minimal(
    model: CursorMutModel<usize, FreeRange>,
    bound: usize,
    next: usize,
    key: usize,
)
    requires
        model.wf(),
        positioned_at_lower_bound(model, core::ops::Bound::Excluded(&bound)),
        model.map.contains_key(key),
        !before_lower_bound(key, core::ops::Bound::Excluded(&bound)),
        model.position < model.keys.len(),
        next == model.keys[model.position],
    ensures
        next <= key,
{
    let key_idx = choose|i: int| 0 <= i < model.keys.len() && #[trigger] model.keys[i] == key;
    if model.position < key_idx {
        assert(model.keys[model.position].cmp_spec(&model.keys[key_idx]) is Less);
    }
}

/// A nonempty contiguous subset of a well-formed free set is covered by one block.
proof fn lemma_contiguous_subset_has_covering_block(
    fullrange: Range<usize>,
    freelist: Map<usize, FreeRange>,
    range: Range<usize>,
)
    requires
        concrete_freelist_wf(fullrange, freelist),
        freelist_blocks_not_adjacent(freelist),
        range.start < range.end,
        range.view_set() <= free_set(freelist_model(freelist)),
    ensures
        exists|key: usize| #[trigger]
            freelist.contains_key(key) && block_contains(freelist[key].block, range),
{
    lemma_concrete_free_set_contains(freelist, range.start);
    let key = choose|key: usize| #[trigger]
        freelist.contains_key(key) && freelist[key].block.view_set().contains(range.start);
    let block = freelist[key].block;
    if block.end < range.end {
        let address = block.end;
        lemma_concrete_free_set_contains(freelist, address);
        let other = choose|other: usize| #[trigger]
            freelist.contains_key(other) && freelist[other].block.view_set().contains(address);
        if block.end < freelist[other].block.start {
            assert(false);
        } else {
            assert(false);
        }
    }
}

/// Restores the canonical separation property after inserting one merged free block.
proof fn lemma_restored_freelist_is_separated(
    fullrange: Range<usize>,
    old_freelist: Map<usize, FreeRange>,
    new_freelist: Map<usize, FreeRange>,
    new_key: usize,
    new_range: Range<usize>,
)
    requires
        freelist_blocks_not_adjacent(old_freelist),
        concrete_freelist_wf(fullrange, new_freelist),
        new_freelist.contains_key(new_key),
        new_key == new_range.start,
        new_freelist[new_key].block == new_range,
        forall|key: usize| #[trigger]
            new_freelist.contains_key(key) && key != new_key ==> old_freelist.contains_key(key)
                && new_freelist[key] == old_freelist[key],
        forall|key: usize| #[trigger]
            new_freelist.contains_key(key) ==> new_freelist[key].block.end != new_range.start,
        forall|key: usize| #[trigger]
            new_freelist.contains_key(key) ==> key == new_key || new_freelist[key].block.start
                != new_range.end,
    ensures
        freelist_blocks_not_adjacent(new_freelist),
{
    assert forall|left: usize, right: usize|
        #![trigger new_freelist.contains_key(left), new_freelist.contains_key(right)]
        new_freelist.contains_key(left) && new_freelist.contains_key(right) && left
            != right implies new_freelist[left].block.end < new_freelist[right].block.start
        || new_freelist[right].block.end < new_freelist[left].block.start by {
        if left == new_key || right == new_key {
            let other = if left == new_key {
                right
            } else {
                left
            };
            if new_key < other {
                if other < new_range.end {
                    assert(new_freelist[other].block.view_set().contains(other));
                    assert(false);
                }
            } else {
                if new_range.start < new_freelist[other].block.end {
                    assert(new_freelist[other].block.view_set().contains(new_range.start));
                    assert(false);
                }
            }
        }
    }
}

proof fn lemma_alloc_suffix_model(
    fullrange: Range<usize>,
    old_freelist: Map<usize, FreeRange>,
    new_freelist: Map<usize, FreeRange>,
    key: usize,
    allocation: Range<usize>,
)
    requires
        concrete_freelist_wf(fullrange, old_freelist),
        freelist_blocks_not_adjacent(old_freelist),
        old_freelist.contains_key(key),
        old_freelist[key].block.start <= allocation.start <= allocation.end,
        old_freelist[key].block.end == allocation.end,
        new_freelist == if old_freelist[key].block.start == allocation.start {
            old_freelist.remove(key)
        } else {
            old_freelist.insert(
                key,
                FreeRange { block: old_freelist[key].block.start..allocation.start },
            )
        },
    ensures
        concrete_freelist_wf(fullrange, new_freelist),
        freelist_blocks_not_adjacent(new_freelist),
        free_set(freelist_model(new_freelist)) == free_set(freelist_model(old_freelist))
            - allocation.view_set(),
{
    let allocation_model = allocation;
    assert forall|address: usize| #[trigger]
        free_set(freelist_model(new_freelist)).contains(address) <==> (free_set(
            freelist_model(old_freelist),
        ) - allocation_model.view_set()).contains(address) by {
        lemma_concrete_free_set_contains(old_freelist, address);
        lemma_concrete_free_set_contains(new_freelist, address);
        if free_set(freelist_model(new_freelist)).contains(address) {
            let new_key = choose|new_key: usize| #[trigger]
                new_freelist.contains_key(new_key)
                    && new_freelist[new_key].block.view_set().contains(address);
            if new_key == key {
            } else if allocation_model.view_set().contains(address) {
                assert(false);
            }
        }
        if (free_set(freelist_model(old_freelist)) - allocation_model.view_set()).contains(
            address,
        ) {
            let old_key = choose|old_key: usize| #[trigger]
                old_freelist.contains_key(old_key)
                    && old_freelist[old_key].block.view_set().contains(address);
            if old_key == key {
                assert(new_freelist.contains_key(key));
            } else {
                assert(new_freelist.contains_key(old_key));
            }
        }
    }
}

proof fn lemma_alloc_specific_model(
    fullrange: Range<usize>,
    old_freelist: Map<usize, FreeRange>,
    new_freelist: Map<usize, FreeRange>,
    key: usize,
    allocation: Range<usize>,
)
    requires
        concrete_freelist_wf(fullrange, old_freelist),
        freelist_blocks_not_adjacent(old_freelist),
        old_freelist.contains_key(key),
        old_freelist[key].block.start <= allocation.start < allocation.end
            <= old_freelist[key].block.end,
        new_freelist == (if allocation.end < old_freelist[key].block.end {
            (if old_freelist[key].block.start == allocation.start {
                old_freelist.remove(key)
            } else {
                old_freelist.insert(
                    key,
                    FreeRange { block: old_freelist[key].block.start..allocation.start },
                )
            }).insert(
                allocation.end,
                FreeRange { block: allocation.end..old_freelist[key].block.end },
            )
        } else if old_freelist[key].block.start == allocation.start {
            old_freelist.remove(key)
        } else {
            old_freelist.insert(
                key,
                FreeRange { block: old_freelist[key].block.start..allocation.start },
            )
        }),
    ensures
        concrete_freelist_wf(fullrange, new_freelist),
        freelist_blocks_not_adjacent(new_freelist),
        free_set(freelist_model(new_freelist)) == free_set(freelist_model(old_freelist))
            - allocation.view_set(),
{
    let allocation_model = allocation;
    assert forall|address: usize| #[trigger]
        free_set(freelist_model(new_freelist)).contains(address) <==> (free_set(
            freelist_model(old_freelist),
        ) - allocation_model.view_set()).contains(address) by {
        lemma_concrete_free_set_contains(old_freelist, address);
        lemma_concrete_free_set_contains(new_freelist, address);
        if free_set(freelist_model(new_freelist)).contains(address) {
            let new_key = choose|new_key: usize| #[trigger]
                new_freelist.contains_key(new_key)
                    && new_freelist[new_key].block.view_set().contains(address);
            if new_key == key {
            } else if new_key == allocation.end && allocation.end < old_freelist[key].block.end {
            } else if allocation_model.view_set().contains(address) {
                assert(false);
            }
        }
        if (free_set(freelist_model(old_freelist)) - allocation_model.view_set()).contains(
            address,
        ) {
            let old_key = choose|old_key: usize| #[trigger]
                old_freelist.contains_key(old_key)
                    && old_freelist[old_key].block.view_set().contains(address);
            if old_key == key {
                if address < allocation.start {
                    assert(new_freelist.contains_key(key));
                } else {
                    assert(new_freelist.contains_key(allocation.end));
                }
            } else {
                if old_key == allocation.end && allocation.end < old_freelist[key].block.end {
                    let other_block = old_freelist[old_key].block;
                    assert(false);
                } else {
                    assert(new_freelist.contains_key(old_key));
                }
            }
        }
    }
}

proof fn lemma_remove_left_neighbor(
    fullrange: Range<usize>,
    old_freelist: Map<usize, FreeRange>,
    new_freelist: Map<usize, FreeRange>,
    key: usize,
    free_range: Range<usize>,
    merged_range: Range<usize>,
)
    requires
        concrete_freelist_wf(fullrange, old_freelist),
        old_freelist.contains_key(key),
        old_freelist[key].block.end == free_range.start,
        merged_range.start == old_freelist[key].block.start,
        merged_range.end == free_range.end,
        free_range.start < free_range.end,
        free_range.view_set().disjoint(free_set(freelist_model(old_freelist))),
        new_freelist == old_freelist.remove(key),
    ensures
        concrete_freelist_wf(fullrange, new_freelist),
        free_set(freelist_model(new_freelist)).union(merged_range.view_set()) == free_set(
            freelist_model(old_freelist),
        ).union(free_range.view_set()),
        merged_range.view_set().disjoint(free_set(freelist_model(new_freelist))),
{
    let free_model = free_range;
    let merged_model = merged_range;
    assert forall|address: usize| #[trigger]
        free_set(freelist_model(new_freelist)).union(merged_model.view_set()).contains(address)
            <==> free_set(freelist_model(old_freelist)).union(free_model.view_set()).contains(
            address,
        ) by {
        lemma_concrete_free_set_contains(old_freelist, address);
        lemma_concrete_free_set_contains(new_freelist, address);
    }
    assert forall|address: usize|
        merged_model.view_set().contains(address) implies !#[trigger] free_set(
        freelist_model(new_freelist),
    ).contains(address) by {
        if free_set(freelist_model(new_freelist)).contains(address) {
            lemma_concrete_free_set_contains(old_freelist, address);
            assert(false);
        }
    }
}

proof fn lemma_insert_free_range(
    fullrange: Range<usize>,
    old_freelist: Map<usize, FreeRange>,
    new_freelist: Map<usize, FreeRange>,
    free_range: Range<usize>,
)
    requires
        concrete_freelist_wf(fullrange, old_freelist),
        free_range.start < free_range.end,
        fullrange.start <= free_range.start < free_range.end <= fullrange.end,
        free_range.view_set().disjoint(free_set(freelist_model(old_freelist))),
        new_freelist == old_freelist.insert(free_range.start, FreeRange { block: free_range }),
    ensures
        concrete_freelist_wf(fullrange, new_freelist),
        free_set(freelist_model(new_freelist)) == free_set(freelist_model(old_freelist)).union(
            free_range.view_set(),
        ),
{
    let free_model = free_range;
    assert forall|address: usize| #[trigger]
        free_set(freelist_model(new_freelist)).contains(address) <==> free_set(
            freelist_model(old_freelist),
        ).union(free_model.view_set()).contains(address) by {
        lemma_concrete_free_set_contains(old_freelist, address);
        lemma_concrete_free_set_contains(new_freelist, address);
        if free_set(freelist_model(old_freelist)).contains(address) {
            let old_key = choose|old_key: usize| #[trigger]
                old_freelist.contains_key(old_key)
                    && old_freelist[old_key].block.view_set().contains(address);
            if old_key == free_range.start {
                assert(free_set(freelist_model(old_freelist)).contains(free_range.start));
                assert(false);
            } else {
                assert(new_freelist.contains_key(old_key));
            }
        }
        if free_model.view_set().contains(address) {
            assert(new_freelist.contains_key(free_range.start));
        }
    }
    assert forall|left: usize, right: usize|
        #![trigger new_freelist.contains_key(left), new_freelist.contains_key(right)]
        new_freelist.contains_key(left) && new_freelist.contains_key(right) && left
            != right implies new_freelist[left].block.view_set().disjoint(
        new_freelist[right].block.view_set(),
    ) by {
        if left == free_range.start || right == free_range.start {
            let other_key = if left == free_range.start {
                right
            } else {
                left
            };
            let other_model = old_freelist[other_key].block;
            assert forall|address: usize|
                free_model.view_set().contains(
                    address,
                ) implies !#[trigger] other_model.view_set().contains(address) by {
                if other_model.view_set().contains(address) {
                    lemma_concrete_free_set_contains(old_freelist, address);
                    assert(false);
                }
            }
        }
    }
}

proof fn lemma_merge_right_neighbor(
    fullrange: Range<usize>,
    old_freelist: Map<usize, FreeRange>,
    new_freelist: Map<usize, FreeRange>,
    next_key: usize,
    free_range: Range<usize>,
    merged_range: Range<usize>,
)
    requires
        concrete_freelist_wf(fullrange, old_freelist),
        old_freelist.contains_key(free_range.start),
        old_freelist[free_range.start].block == free_range,
        old_freelist.contains_key(next_key),
        next_key != free_range.start,
        old_freelist[next_key].block.start == free_range.end,
        merged_range.start == free_range.start,
        merged_range.end == old_freelist[next_key].block.end,
        new_freelist == old_freelist.remove(next_key).insert(
            free_range.start,
            FreeRange { block: merged_range },
        ),
    ensures
        concrete_freelist_wf(fullrange, new_freelist),
        free_set(freelist_model(new_freelist)) == free_set(freelist_model(old_freelist)),
{
    assert forall|address: usize| #[trigger]
        free_set(freelist_model(new_freelist)).contains(address) <==> free_set(
            freelist_model(old_freelist),
        ).contains(address) by {
        lemma_concrete_free_set_contains(old_freelist, address);
        if free_set(freelist_model(old_freelist)).contains(address) {
            let old_key = choose|old_key: usize| #[trigger]
                old_freelist.contains_key(old_key)
                    && old_freelist[old_key].block.view_set().contains(address);
            assert(exists|new_key: usize| #[trigger]
                new_freelist.contains_key(new_key)
                    && new_freelist[new_key].block.view_set().contains(address)) by {
                if old_key == free_range.start || old_key == next_key {
                    assert(new_freelist.contains_key(free_range.start));
                } else {
                    assert(new_freelist.contains_key(old_key));
                }
            }
            lemma_concrete_free_set_contains(new_freelist, address);
        }
    }
}

} // verus!
