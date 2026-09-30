// SPDX-License-Identifier: MPL-2.0
//! A verified first-fit range allocator.
//!
//! # Verified Properties
//!
//! The free list is hidden behind a spin lock and mirrored by a [`GhostSubset`]
//! retained alongside its [`GhostSetAuth`]. Successful allocations return a
//! [`GhostSubRange`] token to the caller, and freeing a range consumes that
//! token.
//! Callers may additionally thread a [`RangeAllocatorState`] through the
//! allocation interface to keep a predictive mirror of every allocator's free
//! blocks, characterized by [`RangeAllocator::can_allocate`]; the threaded
//! state keeps its identity and this allocator's entry across each operation.
#[cfg(feature = "irc11")]
use vstd::thread_view::Objective;
use vstd::{
    prelude::*,
    resource::{
        Loc,
        map::{GhostMapAuth, GhostPointsTo},
        set::{GhostSetAuth, GhostSubset},
    },
    seq_lib::lemma_seq_contains_after_push,
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
    /// The identifier shared by this allocator's free-set authority and allocation tokens.
    pub closed spec fn id(self) -> Loc {
        self.freelist.constant().free_id
    }

    /// The identifier of the shared [`RangeAllocatorState`] threaded by the caller.
    pub closed spec fn state_id(self) -> Loc {
        self.freelist.constant().state_id
    }

    /// The key of this allocator's entry in the caller's [`RangeAllocatorState`].
    pub closed spec fn state_key(self) -> usize {
        self.freelist.constant().state_key
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.freelist.constant().fullrange == self@ && self@.start <= self@.end
    }
}

impl RangeAllocator {
    /// Whether the caller's shared state predicts that
    /// [`RangeAllocator::alloc_specific`] will grant `range`: some entirely free
    /// block wholly covering it.
    pub closed spec fn can_allocate(self, state: RangeAllocatorState, range: Range<usize>) -> bool {
        state@.contains_key(self.state_key()) && exists|key: usize|
            #![trigger state@[self.state_key()][key]]
            {
                let freelist = state@[self.state_key()];
                let block = freelist[key];
                &&& freelist.contains_key(key)
                &&& block_contains(block, range)
            }
    }
}

/// Two allocator values sharing the same state entry agree on predictions.
pub proof fn lemma_can_allocate_same_identity(
    left: RangeAllocator,
    right: RangeAllocator,
    state: RangeAllocatorState,
    range: Range<usize>,
)
    requires
        left.state_key() == right.state_key(),
    ensures
        left.can_allocate(state, range) == right.can_allocate(state, range),
{
    reveal(RangeAllocator::can_allocate);
}

ghost struct FreelistConstant {
    fullrange: Range<usize>,
    initialized_id: Loc,
    state_id: Loc,
    state_key: usize,
    free_id: Loc,
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
            &&& key == block.start
        }
    &&& forall|left: usize, right: usize|
        #![trigger freelist.contains_key(left), freelist.contains_key(right)]
        freelist.contains_key(left) && freelist.contains_key(right) && left != right
            ==> freelist[left].block.view_set().disjoint(freelist[right].block.view_set())
}

/// Whether `block` wholly covers `range`.
closed spec fn block_contains(block: Range<usize>, range: Range<usize>) -> bool {
    block.start <= range.start && range.end <= block.end
}

/// The block map mirrored in the shared state: the key of each free block is its
/// start address.
closed spec fn state_model(freelist: Map<usize, FreeRange>) -> Map<usize, Range<usize>> {
    Map::new(freelist.dom(), |key: usize| freelist[key].block)
}

/// A caller-threaded mirror of every allocator's free blocks, keyed by each
/// allocator's [`RangeAllocator::state_key`].
pub type RangeAllocatorState = GhostMapAuth<usize, Map<usize, Range<usize>>>;

/// Lock-guarded proof resource: initialization state, the authoritative set,
/// ownership of all currently free addresses, and the block map mirrored
/// into the caller-threaded `RangeAllocatorState`.
tracked struct FreelistResource {
    initialized: Sum<OneShotPending, OneShotSet>,
    state: GhostSetAuth<usize>,
    remaining: GhostSubset<usize>,
    model: GhostPointsTo<usize, Map<usize, Range<usize>>>,
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
        &&& resource.state.id() == constant.free_id
        &&& resource.remaining.id() == constant.free_id
        &&& resource.model.id() == constant.state_id
        &&& resource.model.key() == constant.state_key
        &&& resource.state@ == constant.fullrange.view_set()
        &&& match resource.initialized {
            Sum::Left(pending) => {
                &&& pending.id() == constant.initialized_id
                &&& freelist is None
                &&& resource.remaining@ == constant.fullrange.view_set()
                &&& resource.model.value() == Map::empty().insert(
                    constant.fullrange.start,
                    constant.fullrange,
                )
            },
            Sum::Right(set) => {
                &&& set.id() == constant.initialized_id
                &&& freelist is Some
                &&& concrete_freelist_wf(constant.fullrange, freelist->0@)
                &&& resource.remaining@ == free_set(freelist_model(freelist->0@))
                &&& resource.model.value() == state_model(freelist->0@)
            },
        }
    }
}

} // verus!
#[verus_verify]
impl RangeAllocator {
    #[verus_spec(ret =>
        with Ghost(state_key): Ghost<usize>, state_arg: Tracked<&mut RangeAllocatorState>,
        requires
            fullrange.start <= fullrange.end,
            !old(state_arg@)@.contains_key(state_key),
        ensures
            ret@.start == fullrange.start,
            ret@.end == fullrange.end,
            ret.state_id() == final(state_arg@).id(),
            final(state_arg@).id() == old(state_arg@).id(),
            final(state_arg@)@.contains_key(ret.state_key()),
            final(state_arg@)@ == old(state_arg@)@.insert(
                state_key,
                Map::empty().insert(fullrange.start, fullrange),
            ),
    )]
    /* `#[verus_spec]` on a `const fn` does not keep `proof_decl!` locals visible to
     * `verus_exec_expr!` in the active Verus toolchain, so this constructor cannot remain const.
     * Origin Rust: pub const fn new(fullrange: Range<usize>) -> Self {
     */
    pub fn new(fullrange: Range<usize>) -> Self {
        proof_decl! {
            let tracked state = state_arg.get();
            let tracked initialized = OneShotPending::alloc();
            let tracked (state_auth, remaining) = GhostSetAuth::new(fullrange.view_set());
            let tracked model = state.insert(state_key, Map::empty().insert(fullrange.start, fullrange));
            let ghost constant = FreelistConstant {
                fullrange,
                initialized_id: initialized.id(),
                state_id: state.id(),
                state_key,
                free_id: state_auth.id(),
            };
            let tracked resource = FreelistResource {
                initialized: Sum::Left(initialized),
                state: state_auth,
                remaining,
                model,
            };
        }

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

    /// Allocates a caller-specified range.
    ///
    /// # Verified Properties
    ///
    /// ## Safety
    /// - No unsafe code; no panic under the verified contract.
    ///
    /// ## Functional Correctness
    /// - Returns `Ok` if and only if the shared state's free list covers
    ///   `allocate_range`.
    ///
    /// ## Preconditions
    /// - The target range is non-empty and lies within this allocator's range.
    /// - Thread the shared [`RangeAllocatorState`] mirroring this allocator's
    ///   free blocks so that later predictions stay exact.
    ///
    /// ## Postconditions
    /// - On success, returns a [`GhostSubRange`] proving ownership of the
    ///   allocated range; a token is dispatched if and only if the result is
    ///   `Ok`, and it is consumed by [`RangeAllocator::free`].
    /// - The threaded [`RangeAllocatorState`] keeps its identity, this
    ///   allocator's entry, and every other window's entry across calls.
    #[verus_spec(res =>
        with
            Tracked(state): Tracked<&mut RangeAllocatorState>,
            -> allocated: Tracked<Option<GhostSubRange<usize>>>,
        requires
            self@.start <= allocate_range.start < allocate_range.end <= self@.end,
            old(state).id() == self.state_id(),
            old(state)@.contains_key(self.state_key()),
        ensures
            res is Ok <==> allocated@ is Some,
            res is Ok <==> self.can_allocate(*old(state), *allocate_range),
            final(state).id() == old(state).id(),
            final(state)@.contains_key(self.state_key()),
            forall|key: usize| key != self.state_key() ==>
                (final(state)@.contains_key(key) <==>
                    old(state)@.contains_key(key)),
            allocated@ matches Some(token) ==> {
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
            resource.model.agree(state);
            assert(state@.dom().contains(self.state_key()));
            assert(state@[self.state_key()] == state_model(initial_map));
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

        proof! {
            if let Some(key) = target_node {
                let block = freelist@[key].block;
                lemma_free_set_contains_range(initial_freelist, block);
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
            reveal(RangeAllocator::can_allocate);
            reveal(state_model);
            // The mirror agrees with the freelist, so a predicted block is a freelist block.
            if self.can_allocate(*state, *allocate_range) && res is Err {
                let key = choose|key: usize|
                    #![trigger state@[self.state_key()][key]]
                    {
                        let freelist = state@[self.state_key()];
                        let block = freelist[key];
                        &&& freelist.contains_key(key)
                        &&& block.start <= allocate_range.start
                        &&& allocate_range.end <= block.end
                    };
                assert(freelist@ == initial_map);
                assert(freelist@.dom() == state_model(initial_map).dom());
                assert(freelist@.contains_key(key));
                assert(block_contains(freelist@[key].block, *allocate_range));
                assert(freelist@.kv_pairs().contains((key, freelist@[key])));
                assert(false);
            }
            assert(self.can_allocate(*state, *allocate_range) ==> res is Ok);
            // Success carves a free block that the mirror already knew about.
            if res is Ok {
                let ghost covered_key = target_node->0;
                let ghost covered_block = initial_map[covered_key].block;
                assert(initial_map.dom().contains(covered_key));
                assert(state_model(initial_map)[covered_key] == covered_block);
                assert(state@[self.state_key()][covered_key] == covered_block);
                assert(self.can_allocate(*state, *allocate_range));
            }
            assert(res is Ok ==> self.can_allocate(*state, *allocate_range));
            assert(res is Ok <==> self.can_allocate(*state, *allocate_range));
            let ghost constant = lock_guard.constant();
            let ghost value = lock_guard@;
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
                let tracked subset = resource.remaining.split(allocate_range.view_set());
                allocated = Some(GhostSubRange::tracked_new(subset, *allocate_range));
            } else {
                allocated = None;
            }
            resource.model.update(state, state_model(freelist@));
            assert(value is Some);
            assert(freelist@ == value->0@);
            assert(resource.model.id() == self.state_id());
            assert(resource.model.key() == self.state_key());
            assert(resource.model.value() == state_model(freelist@));
            assert(FreelistInvariant::inv(constant, value, *resource));
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
    /// - Thread the shared [`RangeAllocatorState`] mirroring this allocator's
    ///   free blocks so that later predictions stay exact.
    ///
    /// ## Postconditions
    /// - On success, returns a [`GhostSubRange`] proving ownership of the
    ///   returned range; a token is dispatched if and only if the result is
    ///   `Ok`, and it is consumed by [`RangeAllocator::free`].
    /// - The threaded [`RangeAllocatorState`] keeps its identity and this
    ///   allocator's entry across calls.
    #[verus_spec(res =>
        with
            Tracked(state): Tracked<&mut RangeAllocatorState>,
            -> allocated: Tracked<Option<GhostSubRange<usize>>>,
        requires
            old(state).id() == self.state_id(),
            old(state)@.contains_key(self.state_key()),
        ensures
            res matches Ok(res) ==> {
                &&& res.end - res.start == size
                &&& self@.start <= res.start <= res.end <= self@.end
                &&& allocated@ matches Some(token) && {
                    &&& token.id() == self.id()
                    &&& token.range() == res
                }
            },
            res is Ok <==> allocated@ is Some,
            final(state).id() == old(state).id(),
            final(state)@.contains_key(self.state_key()),
    )]
    pub fn alloc(&self, size: usize) -> Result<Range<usize>, RangeAllocError> {
        proof! {
            use_type_invariant(self);
        }
        let mut lock_guard = self.get_freelist_guard();
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
            let ghost constant = lock_guard.constant();
            let ghost value = lock_guard@;
            let tracked resource = lock_guard.tracked_borrow_mut_resource();
            if allocate_range is Some {
                let ghost range = allocate_range -> 0;
                lemma_alloc_suffix_model(self@, initial_map, freelist@, to_remove->0, range);
                let tracked subset = resource.remaining.split(range.view_set());
                allocated = Some(GhostSubRange::tracked_new(subset, range));
            } else {
                allocated = None;
            }
            resource.model.update(state, state_model(freelist@));
            assert(value is Some);
            assert(freelist@ == value->0@);
            assert(resource.model.id() == self.state_id());
            assert(resource.model.key() == self.state_key());
            assert(resource.model.value() == state_model(freelist@));
            assert(FreelistInvariant::inv(constant, value, *resource));
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
    /// - Thread the shared [`RangeAllocatorState`] mirroring this allocator's
    ///   free blocks so that later predictions stay exact.
    ///
    /// ## Postconditions
    /// - The threaded [`RangeAllocatorState`] keeps its identity, this
    ///   allocator's entry, and every other window's entry across calls.
    #[verus_spec(
        with
            Tracked(allocated): Tracked<GhostSubRange<usize>>,
            Tracked(state): Tracked<&mut RangeAllocatorState>,
        requires
            self@.start <= range.start < range.end <= self@.end,
            allocated.id() == self.id(),
            allocated.range() == range,
            old(state).id() == self.state_id(),
            old(state)@.contains_key(self.state_key()),
        ensures
            final(state).id() == old(state).id(),
            final(state)@.contains_key(self.state_key()),
            forall|key: usize| key != self.state_key() ==>
                (final(state)@.contains_key(key) <==>
                    old(state)@.contains_key(key)),
    )]
    pub fn free(&self, range: Range<usize>) {
        proof! {
            use_type_invariant(self);
        }
        let mut lock_guard = self.freelist.lock();
        proof_decl! {
            let tracked resource = lock_guard.tracked_borrow_mut_resource();
            let tracked allocated_subset = allocated.tracked_borrow();
            allocated_subset.agree(&resource.state);
            resource.remaining.disjoint(allocated_subset);
            resource.model.agree(state);
            if resource.initialized is Left {
                assert(resource.remaining@.contains(range.start));
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

        if let Some((prev_va, prev_node)) = freelist
            .upper_bound_mut(core::ops::Bound::Excluded(&free_range.start))
            .peek_prev()
        {
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
        if let Some((next_va, next_node)) = freelist
            .lower_bound_mut(core::ops::Bound::Excluded(&free_range.start))
            .peek_next()
        {
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
        }
        proof! {
            let tracked resource = lock_guard.tracked_borrow_mut_resource();
            resource.remaining.combine(allocated.tracked_into_subset());
            assert(resource.remaining@ == free_set(freelist_model(freelist@))) by {
                if !merged_right {
                    assert(freelist@ == before_right_map);
                }
            }
            resource.model.update(state, state_model(freelist@));
        }
        lock_guard.drop();
    }

    #[verus_spec(ret =>
        ensures
            ret@ is Some,
            ret@ matches Some(freelist) ==> {
                &&& concrete_freelist_wf(self@, freelist@)
                &&& ret.resource().remaining@ == free_set(freelist_model(freelist@))
            },
            ret.constant().fullrange == self@,
            ret.constant().free_id == self.id(),
            ret.constant().state_id == self.state_id(),
            ret.constant().state_key == self.state_key(),
            ret.resource().state.id() == self.id(),
            ret.resource().remaining.id() == self.id(),
            ret.resource().model.id() == self.state_id(),
            ret.resource().model.key() == self.state_key(),
            ret.resource().model.value() == state_model(ret@->0@),
            ret.resource().state@ == self@.view_set(),
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
                reveal(state_model);
                assert(resource.model.value() == state_model(lock_guard@->0@));
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

proof fn lemma_alloc_suffix_model(
    fullrange: Range<usize>,
    old_freelist: Map<usize, FreeRange>,
    new_freelist: Map<usize, FreeRange>,
    key: usize,
    allocation: Range<usize>,
)
    requires
        concrete_freelist_wf(fullrange, old_freelist),
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
                    assert(other_block.view_set().contains(allocation.end));
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
