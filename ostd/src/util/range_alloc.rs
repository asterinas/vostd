// SPDX-License-Identifier: MPL-2.0
use vstd::{
    prelude::*,
    resource::{
        Loc,
        map::{GhostMapAuth, GhostPointsTo},
    },
    std_specs::btree::before_lower_bound,
};
use vstd_extra::{
    debug_assert,
    panic::UnwrapOrPanic,
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

pub type RangeAllocatorState = GhostMapAuth<usize, FreeListModel>;

pub(super) type FreeListModel = Map<usize, Range<int>>;

closed spec fn freelist_model(freelist: Map<usize, FreeRange>) -> FreeListModel {
    Map::new(
        freelist.dom(),
        |key: usize|
            Range { start: freelist[key].block.start as int, end: freelist[key].block.end as int },
    )
}

pub closed spec fn range_set(range: Range<int>) -> Set<int> {
    vstd::set_lib::set_int_range(range.start, range.end)
}

pub(super) closed spec fn free_set(freelist: FreeListModel) -> Set<int> {
    freelist.dom().map(|key: usize| range_set(freelist[key])).flatten()
}

pub closed spec fn allocated_set(fullrange: Range<int>, freelist: FreeListModel) -> Set<int> {
    range_set(fullrange) - free_set(freelist)
}

pub(super) closed spec fn freelist_wf(fullrange: Range<int>, freelist: FreeListModel) -> bool {
    &&& fullrange.start <= fullrange.end
    &&& forall|key: usize| #[trigger]
        freelist.contains_key(key) ==> {
            let block = freelist[key];
            &&& fullrange.start <= block.start <= block.end <= fullrange.end
        }
}

pub(super) open spec fn block_contains(block: Range<int>, range: Range<usize>) -> bool {
    block.start <= range.start && range.end <= block.end
}

pub(super) tracked struct FreelistResource {
    pub(super) initialized: Sum<OneShotPending, OneShotSet>,
    pub(super) state: GhostPointsTo<usize, FreeListModel>,
}

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
            &&& set.id() == constant.initialized_id
            &&& freelist is Some
            &&& freelist_wf(constant.fullrange, freelist_model(freelist->0@))
            &&& resource.state.value() == freelist_model(freelist->0@)
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

    pub closed spec fn state_key(self) -> usize {
        self.freelist.constant().state_key
    }

    pub closed spec fn state_id(self) -> Loc {
        self.freelist.constant().state_id
    }

    pub closed spec fn can_allocate(self, state: RangeAllocatorState, range: Range<usize>) -> bool {
        state@.contains_key(self.state_key()) && exists|key: usize|
            #![trigger state@[self.state_key()][key]]
            {
                let freelist = state@[self.state_key()];
                let block = freelist[key];
                &&& freelist.contains_key(key)
                &&& block.start <= range.start
                &&& range.end <= block.end
            }
    }

    pub closed spec fn can_free(self, state: RangeAllocatorState, range: Range<usize>) -> bool {
        state@.contains_key(self.state_key()) && range_set(
            Range { start: range.start as int, end: range.end as int },
        ) <= allocated_set(self@, state@[self.state_key()])
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.freelist.constant().fullrange == self@ && self@.start <= self@.end
    }
}

pub proof fn lemma_can_allocate_same_identity(
    left: RangeAllocator,
    right: RangeAllocator,
    state: RangeAllocatorState,
    range: Range<usize>,
)
    requires
        left.state_id() == right.state_id(),
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
}
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
            Tracked(state): Tracked<&mut RangeAllocatorState>,
            -> initialized: Tracked<OneShotSet>,
        requires
            self@.start <= allocate_range.start < allocate_range.end <= self@.end,
            old(state).id() == self.state_id(),
            old(state)@.contains_key(self.state_key()),
        ensures
            res is Ok <==> self.can_allocate(*old(state), *allocate_range),
            initialized@.id() == self.initialized_id(),
    )]
    pub fn alloc_specific(&self, allocate_range: &Range<usize>) -> Result<(), RangeAllocError> {
        proof! {
            use_type_invariant(self);
        }
        debug_assert!(allocate_range.start < allocate_range.end);

        proof_decl! {
            let tracked initialized: OneShotSet;
        }
        let mut lock_guard = #[verus_spec(with => Tracked(initialized))]
        self.get_freelist_guard();
        proof_decl! {
            let ghost initial_freelist = freelist_model(lock_guard@->0@);
            let tracked resource = lock_guard.tracked_borrow_mut_resource();
            assert(resource.state.key() == self.state_key());
            resource.state.agree(state);
            assert(state@[self.state_key()] == initial_freelist);
        }
        let freelist = lock_guard.as_mut().unwrap();
        let mut target_node = None;
        let mut left_length = 0;
        let mut right_length = 0;
        proof_decl! {
            let ghost mut checked = Set::<(usize, FreeRange)>::empty();
        }
        proof! {
            reveal(block_contains);
            broadcast use vstd::seq_lib::group_seq_properties;
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
                let ghost prev_checked = checked;
                assert forall|candidate: (usize, FreeRange)|
                    #![auto]
                    checked.insert(entry).contains(candidate) implies !block_contains(
                            Range {
                                start: candidate.1.block.start as int,
                                end: candidate.1.block.end as int,
                            },
                            *allocate_range,
                        ) by {
                    assert(target_node is None);
                    if candidate != entry {
                        assert(checked.contains(candidate));
                    } else {
                        assert(value.block.end < allocate_range.end
                            || value.block.start > allocate_range.start);
                    }
                }
                checked = checked.insert(entry);
                assert(it.seq()[it.index()] == (key, value));
                assert(it.seq()[..it.index() + 1] =~= it.seq()[..it.index()].push(it.seq()[it.index()]));
                assert(it.seq()[..it.index() + 1].unref() =~=
                    it.seq()[..it.index()].unref().push(entry));
                assert(checked =~= it.seq()[..it.index() + 1].unref().to_set()) by {
                    assert forall|candidate: (usize, FreeRange)|
                        checked.contains(candidate) <==>
                            it.seq()[..it.index() + 1].unref().to_set().contains(candidate) by {
                        assert(prev_checked.contains(candidate) <==>
                            it.seq()[..it.index()].unref().to_set().contains(candidate));
                        assert(it.seq()[..it.index()].unref().to_set().contains(candidate) <==>
                            it.seq()[..it.index()].unref().contains(candidate));
                        assert(it.seq()[..it.index() + 1].unref().to_set().contains(candidate) <==>
                            it.seq()[..it.index() + 1].unref().contains(candidate));
                        vstd::seq_lib::lemma_seq_contains_after_push(
                            it.seq()[..it.index()].unref(),
                            entry,
                            candidate,
                        );
                        assert(it.seq()[..it.index()].unref().push(entry).contains(candidate) <==>
                            it.seq()[..it.index()].unref().contains(candidate)
                                || candidate == entry);
                    }
                }
                if it.index() + 1 == it.seq().len() {
                    assert(it.seq()[..it.index() + 1] =~= it.seq());
                    assert(checked == it.seq().unref().to_set());
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
            reveal(RangeAllocator::can_allocate);
            reveal(block_contains);
            assert(res is Ok ==> self.can_allocate(*state, *allocate_range));
            if self.can_allocate(*state, *allocate_range) && res is Err {
                let key = choose|key: usize| #![trigger (*state)@[self.state_key()][key]] {
                    let model = (*state)@[self.state_key()];
                    let block = model[key];
                    &&& model.contains_key(key)
                    &&& block.start <= allocate_range.start
                    &&& allocate_range.end <= block.end
                };
                reveal(freelist_model);
                assert(freelist@.contains_key(key));
                assert(freelist@.kv_pairs().contains((key, freelist@[key])));
                assert(block_contains(
                    Range {
                        start: freelist@[key].block.start as int,
                        end: freelist@[key].block.end as int,
                    },
                    *allocate_range,
                ));
                assert(false);
            }
            assert(self.can_allocate(*state, *allocate_range) ==> res is Ok);
            assert(res is Ok <==> self.can_allocate(*state, *allocate_range));
            let ghost constant = lock_guard.constant();
            let ghost value = lock_guard@;
            let tracked resource = lock_guard.tracked_borrow_mut_resource();
            assert(resource.state.id() == self.state_id());
            assert(resource.state.key() == constant.state_key);
            resource.state.update(state, freelist_model(freelist@));
            assert(freelist_wf(self@, freelist_model(freelist@)));
            assert(resource.state.value() == freelist_model(freelist@));
            assert(constant.fullrange == self@);
            assert(value is Some);
            assert(resource.state.key() == constant.state_key);
            assert(resource.state.id() == constant.state_id);
            assert(resource.initialized is Right);
            assert(resource.initialized->Right_0.id() == constant.initialized_id);
            assert(freelist_inv(constant, value, *resource));
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
            Tracked(state): Tracked<&mut RangeAllocatorState>,
            -> initialized: Tracked<OneShotSet>,
        requires
            self@.start <= self@.end,
            old(state).id() == self.state_id(),
            old(state)@.contains_key(self.state_key()),
        ensures
            res matches Ok(res) ==> {
                &&& res.end - res.start == size
                &&& self@.start <= res.start <= res.end <= self@.end
            },
            initialized@.id() == self.initialized_id(),
    )]
    pub fn alloc(&self, size: usize) -> Result<Range<usize>, RangeAllocError> {
        proof! {
            use_type_invariant(self);
        }
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
            let ghost constant = lock_guard.constant();
            let ghost value = lock_guard@;
            let tracked resource = lock_guard.tracked_borrow_mut_resource();
            assert(resource.state.id() == self.state_id());
            assert(resource.state.key() == constant.state_key);
            resource.state.update(state, freelist_model(freelist@));
            assert(freelist_wf(self@, freelist_model(freelist@)));
            assert(resource.state.value() == freelist_model(freelist@));
            assert(constant.fullrange == self@);
            assert(value is Some);
            assert(resource.state.key() == constant.state_key);
            assert(resource.state.id() == constant.state_id);
            assert(resource.initialized is Right);
            assert(resource.initialized->Right_0.id() == constant.initialized_id);
            assert(freelist_inv(constant, value, *resource));
        }
        lock_guard.drop();
        #[verus_spec(with |= Tracked(initialized))]
        res
    }

    /// Frees a `range`.
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
            assert(resource.state.id() == self.state_id());
            resource.state.update(state, freelist_model(freelist@));
            assert(freelist_wf(self@, freelist_model(freelist@)));
        }
        lock_guard.drop();
    }

    #[verus_spec(ret =>
        with
            -> initialized: Tracked<OneShotSet>,
        requires self@.start <= self@.end,
        ensures
            ret@ is Some,
            freelist_wf(self@, freelist_model(ret@->0@)),
            ret.constant().fullrange == self@,
            ret.constant().state_id == self.state_id(),
            ret.constant().state_key == self.state_key(),
            ret.resource().state.id() == self.state_id(),
            ret.resource().state.key() == self.state_key(),
            ret.resource().state.value() == freelist_model(ret@->0@),
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
                reveal(free_set);
                reveal(range_set);
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
