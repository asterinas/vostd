// SPDX-License-Identifier: MPL-2.0
//! A verified first-fit range allocator.
//!
//! # Verified Properties
//!
//! The free list is hidden behind a spin lock and mirrored in ghost state by a
//! caller-held [`RangeAllocatorState`] keyed by the allocator's `state_key`/
//! `state_id`. Each mutating method threads that token and preserves its id,
//! its key, and `freelist_wf` of the updated entry.
#[cfg(feature = "irc11")]
use vstd::thread_view::Objective;
use vstd::{
    prelude::*,
    resource::{
        Loc,
        map::{GhostMapAuth, GhostPointsTo},
    },
    seq_lib::{group_seq_properties, lemma_seq_contains_after_push},
    std_specs::btree::before_lower_bound,
};
use vstd_extra::{
    debug_assert,
    panic::UnwrapOrPanic,
    range::RangeExtraFns,
    resource::flags::{OneShotPending, OneShotSet},
    resource_invariant::ResourceInvariant,
    sum::Sum,
};

use crate::sync::{PreemptDisabled, SpinLock, SpinLockGuard};
use alloc::collections::btree_map::BTreeMap;
use core::ops::Range;

verus! {

pub(super) ghost struct FreelistConstant {
    pub(super) fullrange: Range<int>,
    pub(super) initialized_id: Loc,
    pub(super) state_id: Loc,
    pub(super) state_key: usize,
}

ghost struct FreelistInvariant;

/// Caller-side authority over the allocator's shared free-list state.
pub type RangeAllocatorState = GhostMapAuth<usize, FreeListModel>;

/// The free list viewed as a map from block start to its address range.
pub type FreeListModel = Map<usize, Range<int>>;

/// The `int`-range view of a free-list map, dropping the `FreeRange` wrapper.
closed spec fn freelist_model(freelist: Map<usize, FreeRange>) -> FreeListModel {
    Map::new(
        freelist.dom(),
        |key: usize|
            Range { start: freelist[key].block.start as int, end: freelist[key].block.end as int },
    )
}

/// The addresses covered by some free block.
pub(super) closed spec fn free_set(freelist: FreeListModel) -> Set<int> {
    freelist.dom().map(|key: usize| freelist[key].view_set()).flatten()
}

/// The addresses within `fullrange` not covered by any free block.
pub(super) closed spec fn allocated_set(fullrange: Range<int>, freelist: FreeListModel) -> Set<
    int,
> {
    fullrange.view_set() - free_set(freelist)
}

/// `fullrange` is well-ordered (`start <= end`) and every free block lies within it.
pub closed spec fn freelist_wf(fullrange: Range<int>, freelist: FreeListModel) -> bool {
    &&& fullrange.start <= fullrange.end
    &&& forall|key: usize| #[trigger]
        freelist.contains_key(key) ==> {
            let block = freelist[key];
            &&& fullrange.start <= block.start <= block.end <= fullrange.end
        }
}

/// Whether `block` wholly covers `range`.
pub(super) open spec fn block_contains(block: Range<int>, range: Range<usize>) -> bool {
    block.start <= range.start && range.end <= block.end
}

/// Lock-guarded proof resource: the one-shot initializability token plus the
/// points-to the shared freelist-model entry.
pub(super) tracked struct FreelistResource {
    pub(super) initialized: Sum<OneShotPending, OneShotSet>,
    pub(super) state: GhostPointsTo<usize, FreeListModel>,
}

#[cfg(feature = "irc11")]
unsafe impl Objective for FreelistResource {

}

/// Relates the lock's content and constant to its resource: the resource's state
/// point tracks the freelist model entry keyed by `constant.state_key`.
closed spec fn freelist_inv(
    constant: FreelistConstant,
    freelist: Option<BTreeMap<usize, FreeRange>>,
    resource: FreelistResource,
) -> bool {
    &&& resource.state.key() == constant.state_key
    &&& resource.state.id() == constant.state_id
    &&& match resource.initialized {
        Sum::Left(pending) => {
            &&& pending.id() == constant.initialized_id
            &&& freelist is None
            &&& resource.state.value() == Map::empty().insert(
                constant.fullrange.start as usize,
                constant.fullrange,
            )
        },
        Sum::Right(set) => {
            let map = freelist_model(freelist->0@);
            &&& set.id() == constant.initialized_id
            &&& freelist is Some
            &&& freelist_wf(constant.fullrange, map)
            &&& resource.state.value() == map
        },
    }
}

impl ResourceInvariant<Option<BTreeMap<usize, FreeRange>>> for FreelistInvariant {
    type Constant = FreelistConstant;

    type Resource = FreelistResource;

    closed spec fn inv(
        constant: FreelistConstant,
        freelist: Option<BTreeMap<usize, FreeRange>>,
        resource: Self::Resource,
    ) -> bool {
        freelist_inv(constant, freelist, resource)
    }
}

} // verus!
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

broadcast use vstd::std_specs::btree::group_btree_axioms;

impl View for RangeAllocator {
    type V = Range<int>;

    closed spec fn view(&self) -> Range<int> {
        Range { start: self.fullrange.start as int, end: self.fullrange.end as int }
    }
}

impl RangeAllocator {
    pub closed spec fn initialized_id(self) -> Loc {
        self.freelist.constant().initialized_id
    }

    /// The key this allocator occupies in the shared [`RangeAllocatorState`] map.
    pub closed spec fn state_key(self) -> usize {
        self.freelist.constant().state_key
    }

    /// The identifier of the points-to authority tracking this allocator's
    /// `state_key` entry, which a threaded state token must match.
    pub closed spec fn state_id(self) -> Loc {
        self.freelist.constant().state_id
    }

    /// Whether the shared state's free list has a block wholly covering `range`.
    pub closed spec fn can_allocate(self, state: RangeAllocatorState, range: Range<usize>) -> bool {
        state@.contains_key(self.state_key()) && exists|key: usize|
            #![trigger state@[self.state_key()][key]]
            {
                let freelist = state@[self.state_key()];
                &&& freelist.contains_key(key)
                &&& block_contains(freelist[key], range)
            }
    }

    /// Whether `range` is currently allocated in the shared state, i.e. none of
    /// its addresses is free.
    pub closed spec fn can_free(self, state: RangeAllocatorState, range: Range<usize>) -> bool {
        state@.contains_key(self.state_key()) && (Range {
            start: range.start as int,
            end: range.end as int,
        }).view_set() <= allocated_set(self@, state@[self.state_key()])
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.freelist.constant().fullrange == self@ && self@.start <= self@.end
    }
}

/// `can_allocate` depends only on the state's key: two allocators sharing the
/// same `state_key` agree on `can_allocate`.
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
            final(state_arg@)@.contains_key(ret.state_key()),
            final(state_arg@).id() == old(state_arg@).id(),
            final(state_arg@)@ == old(state_arg@)@.insert(
                state_key,
                Map::empty().insert(fullrange.start, Range {
                    start: fullrange.start as int,
                    end: fullrange.end as int,
                }),
            ),
    )]
    /* `#[verus_spec]` on a `const fn` does not keep `proof_decl!` locals visible to
     * `verus_exec_expr!` in the active Verus toolchain, so this constructor cannot remain const.
     * Origin Rust: pub const fn new(fullrange: Range<usize>) -> Self {
     */
    pub fn new(fullrange: Range<usize>) -> Self {
        proof_decl! {
            let tracked state = state_arg.get();
            let ghost fullrange_view = Range {
                start: fullrange.start as int,
                end: fullrange.end as int,
            };
            let tracked initialized = OneShotPending::alloc();
            let tracked state_point = state.insert(
                state_key,
                Map::empty().insert(fullrange.start, fullrange_view),
            );
            let ghost constant = FreelistConstant {
                fullrange: fullrange_view,
                initialized_id: initialized.id(),
                state_id: state.id(),
                state_key,
            };
            let tracked resource = FreelistResource {
                initialized: Sum::Left(initialized),
                state: state_point,
            };
        }

        verus_exec_expr! {
            Self {
                fullrange,
                freelist: SpinLock::new(None, Ghost(constant), Tracked(resource)),
            }
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
    /// - Thread this allocator's slice of the shared [`RangeAllocatorState`]
    ///   with matching `state_id`/`state_key`.
    ///
    /// ## Postconditions
    /// - The returned one-shot initialization token matches `initialized_id`.
    /// - The state token's id and `state_key` entry survive the call.
    /// - The updated free list stays `freelist_wf`.
    #[verus_spec(res =>
        with
            Tracked(state): Tracked<&mut RangeAllocatorState>,
            -> initialized: Tracked<OneShotSet>,
        requires
            self@.start <= allocate_range.start < allocate_range.end <= self@.end,
            old(state).id() == self.state_id(),
            old(state)@.contains_key(self.state_key()),
        ensures
            res is Ok <==> self.can_allocate(*old(state), *allocate_range),
            initialized@.id() == self.initialized_id(),
            final(state).id() == old(state).id(),
            final(state)@.contains_key(self.state_key()),
            freelist_wf(self@, final(state)@[self.state_key()]),
    )]
    pub fn alloc_specific(&self, allocate_range: &Range<usize>) -> Result<(), RangeAllocError> {
        proof! {}
        debug_assert!(allocate_range.start < allocate_range.end);

        proof_decl! {
            let tracked initialized: OneShotSet;
        }
        let mut lock_guard = #[verus_spec(with => Tracked(initialized))]
        self.get_freelist_guard();
        proof_decl! {
            let ghost initial_freelist = freelist_model(lock_guard@->0@);
            let tracked resource = lock_guard.tracked_borrow_mut_resource();
            resource.state.agree(state);
        }
        let freelist = lock_guard.as_mut().unwrap();
        let mut target_node = None;
        let mut left_length = 0;
        let mut right_length = 0;
        proof_decl! {
            let ghost mut checked = Set::<(usize, FreeRange)>::empty();
        }
        proof! {
            broadcast use group_seq_properties;
            broadcast use Seq::to_set_ensures;
        }
        #[verus_spec(it =>
            invariant
                self@.start <= allocate_range.start < allocate_range.end <= self@.end,
                right_length <= usize::MAX - allocate_range.end,
                freelist_wf(self@, freelist_model(freelist@)),
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
                    #![auto]
                    checked.contains(entry) ==> !block_contains(
                            Range {
                                start: entry.1.block.start as int,
                                end: entry.1.block.end as int,
                            },
                            *allocate_range,
                        ),
            ensures
                target_node is None ==> checked == it.seq().unref().to_set(),
                target_node is None ==> checked == freelist@.kv_pairs(),
                target_node is None ==> forall|entry: (usize, FreeRange)|
                    #![auto]
                    freelist@.kv_pairs().contains(entry) ==> !block_contains(
                        Range {
                            start: entry.1.block.start as int,
                            end: entry.1.block.end as int,
                        },
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
                assert(it.seq()[..it.index() + 1].unref() =~=
                    it.seq()[..it.index()].unref().push(entry));
                assert(checked =~= it.seq()[..it.index() + 1].unref().to_set()) by {
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
                    assert(it.seq()[..it.index() + 1] =~= it.seq());
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
            if self.can_allocate(*state, *allocate_range) && res is Err {
                let key = choose|key: usize| #![trigger (*state)@[self.state_key()][key]] {
                    let model = (*state)@[self.state_key()];
                    &&& model.contains_key(key)
                    &&& block_contains(model[key], *allocate_range)
                };
                assert(freelist@.kv_pairs().contains((key, freelist@[key])));
                assert(false);
            }
            let tracked resource = lock_guard.tracked_borrow_mut_resource();
            resource.state.update(state, freelist_model(freelist@));
        }
        lock_guard.drop();
        #[verus_spec(with |= Tracked(initialized))]
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
    /// - Thread this allocator's slice of the shared [`RangeAllocatorState`]
    ///   with matching `state_id`/`state_key`.
    ///
    /// ## Postconditions
    /// - The returned one-shot initialization token matches `initialized_id`.
    /// - The state token's id and `state_key` entry survive the call.
    /// - The updated free list stays `freelist_wf`.
    #[verus_spec(res =>
        with
            Tracked(state): Tracked<&mut RangeAllocatorState>,
            -> initialized: Tracked<OneShotSet>,
        requires
            old(state).id() == self.state_id(),
            old(state)@.contains_key(self.state_key()),
        ensures
            res matches Ok(res) ==> {
                &&& res.end - res.start == size
                &&& self@.start <= res.start <= res.end <= self@.end
            },
            initialized@.id() == self.initialized_id(),
            final(state).id() == old(state).id(),
            final(state)@.contains_key(self.state_key()),
            freelist_wf(self@, final(state)@[self.state_key()]),
    )]
    pub fn alloc(&self, size: usize) -> Result<Range<usize>, RangeAllocError> {
        proof! {}
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
                freelist_wf(self@, freelist_model(freelist@)),
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
        proof! {
            let tracked resource = lock_guard.tracked_borrow_mut_resource();
            resource.state.update(state, freelist_model(freelist@));
        }
        lock_guard.drop();
        #[verus_spec(with |= Tracked(initialized))]
        res
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
    /// - Thread this allocator's slice of the shared [`RangeAllocatorState`]
    ///   with matching `state_id`/`state_key`.
    /// - Hold this allocator's initialization token
    ///   (matching `initialized_id`).
    /// - Prove `self.can_free`: `range` is currently allocated.
    ///
    /// ## Postconditions
    /// - The state token's id and `state_key` entry survive the call.
    /// - The updated free list stays `freelist_wf`.
    #[verus_spec(
        with
            Tracked(initialized): Tracked<&OneShotSet>,
            Tracked(state): Tracked<&mut RangeAllocatorState>,
        requires
            self@.start <= range.start <= range.end <= self@.end,
            initialized.id() == self.initialized_id(),
            old(state).id() == self.state_id(),
            old(state)@.contains_key(self.state_key()),
            self.can_free(*old(state), range),
        ensures
            final(state).id() == old(state).id(),
            final(state)@.contains_key(self.state_key()),
            freelist_wf(self@, final(state)@[self.state_key()]),
    )]
    pub fn free(&self, range: Range<usize>) {
        proof! {
            use_type_invariant(self);
        }
        let mut lock_guard = self.freelist.lock();
        proof_decl! {
            let tracked resource = lock_guard.tracked_borrow_mut_resource();
            if resource.initialized is Left {
                resource.initialized.tracked_borrow_left().incompatible(initialized);
            }
            resource.state.agree(state);
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
        proof! {
            let tracked resource = lock_guard.tracked_borrow_mut_resource();
            resource.state.update(state, freelist_model(freelist@));
        }
        lock_guard.drop();
    }

    #[verus_spec(ret =>
        with
            -> initialized: Tracked<OneShotSet>,
        ensures
            ret@ is Some,
            ret@ matches Some(freelist) ==> {
                &&& freelist_wf(self@, freelist_model(freelist@))
                &&& ret.resource().state.value() == freelist_model(freelist@)
            },
            ret.constant().fullrange == self@,
            ret.constant().state_id == self.state_id(),
            ret.constant().state_key == self.state_key(),
            ret.resource().state.id() == self.state_id(),
            ret.resource().state.key() == self.state_key(),
            ret.resource().initialized is Right,
            ret.resource().initialized->Right_0.id() == ret.constant().initialized_id,
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
            proof_decl! {
                let tracked resource = lock_guard.tracked_borrow_mut_resource();
                let tracked pending = resource.initialized.tracked_swap_left(OneShotPending::alloc());
                resource.initialized = Sum::Right(pending.set());
            }
            proof! {
                reveal(freelist_model);
            }
        }
        proof_decl! {
            let tracked initialized = lock_guard.tracked_borrow_mut_resource().initialized.tracked_borrow_right().duplicate();
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
