// SPDX-License-Identifier: MPL-2.0
//! I/O port allocator.
use vstd::prelude::*;
use vstd::resource::set::{GhostSetAuth, GhostSubset};
use vstd::tokens::InstanceId;
use vstd_extra::ownership::Inv;

use core::ops::Range;

use id_alloc::IdAlloc;
use log::debug;
use spin::Once;

use super::{IoPort, lemma_port_id_set_contains, lemma_port_id_set_insert, port_id_set};
use crate::{
    io::RawIoPortRange,
    sync::{LocalIrqDisabled, SpinLock},
};

verus! {

/// Opaque specification for the third-party one-time initialization primitive.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(R)]
pub struct ExOnce<T, R>(spin::once::Once<T, R>);

/// Identity assigned to the single global PIO allocator during trusted boot initialization.
pub uninterp spec fn io_port_allocator_instance_id() -> InstanceId;

/// Allocated ids of a bitmap prefix `[0, end)`: `i` is in iff `s[i]`.
pub(crate) closed spec fn id_alloc_bits(s: Seq<bool>, end: int) -> Set<usize>
    decreases end,
{
    if end <= 0 {
        Set::empty()
    } else {
        let rest = id_alloc_bits(s, end - 1);
        if s[end - 1] {
            rest.insert((end - 1) as usize)
        } else {
            rest
        }
    }
}

/// Set of ids currently allocated by `allocator`.
pub(crate) open spec fn id_alloc_view(allocator: &IdAlloc) -> Set<usize> {
    id_alloc_bits(allocator@, allocator@.len() as int)
}

/// Number of ids `allocator` can hold.
pub(crate) open spec fn id_alloc_capacity(allocator: &IdAlloc) -> usize {
    allocator@.len() as usize
}

/// Characterizes `id_alloc_bits`: `id_alloc_bits(s, end).contains(j)` holds exactly when
/// `0 <= j < end` and `s[j]` is `true`.
pub(crate) proof fn lemma_id_alloc_bits_char(s: Seq<bool>, end: int, j: usize)
    requires
        0 <= end,
        end <= usize::MAX as int,
        s.len() >= end,
        0 <= (j as int),
    ensures
        id_alloc_bits(s, end).contains(j) == ((j as int) < end && s[j as int]),
    decreases end,
{
    reveal(id_alloc_bits);
    if end <= 0 {
        assert(id_alloc_bits(s, end) =~= Set::empty());
    } else {
        lemma_id_alloc_bits_char(s, end - 1, j);
        if (j as int) == end - 1 {
            assert(id_alloc_bits(s, end - 1).contains(j) == (((j as int) < end - 1)
                && s[j as int]));
            assert(id_alloc_bits(s, end).contains(j) == s[end - 1]);
            assert(s[j as int] == s[end - 1]);
        } else {
            // j != end-1: the bit folded in at (end-1) is distinct from j.
            assert(id_alloc_bits(s, end - 1).contains(j) == (((j as int) < end - 1)
                && s[j as int]));
            assert(((end - 1) as usize) as int == end - 1);
            assert(j != (end - 1) as usize);
            if s[end - 1] {
                assert(id_alloc_bits(s, end - 1).insert((end - 1) as usize).contains(j)
                    == id_alloc_bits(s, end - 1).contains(j));
            }
            assert(id_alloc_bits(s, end).contains(j) == id_alloc_bits(s, end - 1).contains(j));
            assert(((j as int) < end - 1 && s[j as int]) == ((j as int) < end && s[j as int]));
        }
    }
}

/// For an in-bounds id, `id_alloc_view` membership coincides with the allocated bitmap bit.
pub(crate) proof fn lemma_id_alloc_view_contains(allocator: &IdAlloc, id: usize)
    requires
        allocator.inv(),
        (id as int) < allocator@.len(),
        allocator@.len() <= usize::MAX as int,
    ensures
        id_alloc_view(allocator).contains(id) == allocator@[id as int],
{
    lemma_id_alloc_bits_char(allocator@, allocator@.len() as int, id);
}

/// Derives the set-level postcondition of `alloc_specific` from its bitmap postcondition.
pub(crate) proof fn lemma_alloc_specific_view(
    old_a: &IdAlloc,
    final_a: &IdAlloc,
    id: usize,
    res: Option<usize>,
)
    requires
        old_a.inv(),
        final_a.inv(),
        (id as int) < old_a@.len(),
        old_a@.len() <= usize::MAX as int,
        final_a@.len() == old_a@.len(),
        res is None ==> old_a@[id as int] && final_a@ == old_a@,
        res is Some ==> final_a@ == old_a@.update(id as int, true) && !old_a@[id as int],
        res is Some ==> res == Some(id),
    ensures
        id_alloc_view(final_a) == id_alloc_view(old_a).insert(id),
        id_alloc_view(old_a).subset_of(id_alloc_view(final_a)),
        id_alloc_view(old_a).contains(id) ==> res is None,
        !id_alloc_view(old_a).contains(id) ==> res == Some(id),
{
    let old_len: int = old_a@.len() as int;
    assert forall|j: usize|
        id_alloc_view(final_a).contains(j) == (id_alloc_view(old_a).insert(id)).contains(j) by {
        lemma_id_alloc_bits_char(old_a@, old_len, j);
        lemma_id_alloc_bits_char(final_a@, final_a@.len() as int, j);
        if res is Some {
            assert forall|jj: int|
                #![trigger final_a@[jj]]
                final_a@[jj] == (if jj == id as int {
                    true
                } else {
                    old_a@[jj]
                }) by {
                assert(final_a@ == old_a@.update(id as int, true));
            }
        } else {
            assert(final_a@ == old_a@);
            assert(old_a@[id as int]);
        }
    }
    assert forall|j: usize|
        #![trigger id_alloc_view(old_a).contains(j)]
        id_alloc_view(old_a).contains(j) implies id_alloc_view(final_a).contains(j) by {
        lemma_id_alloc_bits_char(old_a@, old_len, j);
        lemma_id_alloc_bits_char(final_a@, final_a@.len() as int, j);
        if res is Some {
            assert forall|jj: int|
                #![trigger final_a@[jj]]
                final_a@[jj] == (if jj == id as int {
                    true
                } else {
                    old_a@[jj]
                }) by {
                assert(final_a@ == old_a@.update(id as int, true));
            }
        } else {
            assert(final_a@ == old_a@);
        }
    }
    lemma_id_alloc_bits_char(old_a@, old_len, id);
    assert(id_alloc_view(old_a).contains(id) == old_a@[id as int]);
    if res is Some {
        assert(!old_a@[id as int]);
        assert(res == Some(id));
    } else {
        assert(old_a@[id as int]);
    }
}

/// Representation invariant of `IoPortAllocatorInner`.
pub(crate) open spec fn io_port_inner_inv_values(
    allocated_instance_id: InstanceId,
    allocated: Set<usize>,
    allocator: &IdAlloc,
) -> bool {
    &&& allocated_instance_id == io_port_allocator_instance_id()
    &&& allocator.inv()
    &&& allocator@.len() == crate::arch::io::MAX_IO_PORT as int
    &&& allocated.subset_of(id_alloc_view(allocator))
    &&& id_alloc_capacity(allocator) == crate::arch::io::MAX_IO_PORT as usize
}

} // verus!
/// Transparent facade used only to pass ghost frame facts to the third-party mutation.
#[repr(transparent)]
#[verus_verify]
struct ModeledIdAlloc {
    inner: IdAlloc,
}

#[verus_verify]
impl ModeledIdAlloc {
    #[verus_spec(result =>
        with
            Ghost(allocated_instance_id): Ghost<InstanceId>,
            Ghost(preserved): Ghost<Set<usize>>,
        requires
            id < id_alloc_capacity(&old(self).inner),
            io_port_inner_inv_values(allocated_instance_id, preserved, &old(self).inner),
        ensures
            final(self).inner.inv(),
            final(self).inner@.len() == crate::arch::io::MAX_IO_PORT as int,
            id_alloc_capacity(&final(self).inner) == id_alloc_capacity(&old(self).inner),
            id_alloc_view(&final(self).inner) == id_alloc_view(&old(self).inner).insert(id),
            id_alloc_view(&old(self).inner).subset_of(id_alloc_view(&final(self).inner)),
            preserved.subset_of(id_alloc_view(&final(self).inner)),
            io_port_inner_inv_values(
                allocated_instance_id,
                preserved,
                &final(self).inner,
            ),
            id_alloc_view(&old(self).inner).contains(id) ==> result is None,
            !id_alloc_view(&old(self).inner).contains(id) ==> result == Some(id),
    )]
    fn alloc_specific(&mut self, id: usize) -> Option<usize> {
        proof! {
            assert(id < id_alloc_capacity(&old(self).inner));
            assert(id_alloc_capacity(&old(self).inner)
                == crate::arch::io::MAX_IO_PORT as usize);
            assert(old(self).inner@.len() == crate::arch::io::MAX_IO_PORT as int);
            assert((id as int) < old(self).inner@.len());
        }
        let res = self.inner.alloc_specific(id);
        proof! {
            assert(self.inner@.len() == old(self).inner@.len());
            assert(self.inner@.len() == crate::arch::io::MAX_IO_PORT as int);
            assert(self.inner.inv());
            assert(old(self).inner@.len() <= usize::MAX as int);
            lemma_alloc_specific_view(&old(self).inner, &self.inner, id, res);
            assert(id_alloc_capacity(&self.inner) == id_alloc_capacity(&old(self).inner));
            assert(preserved.subset_of(id_alloc_view(&self.inner)));
            assert(io_port_inner_inv_values(allocated_instance_id, preserved, &self.inner));
        }
        res
    }
}

verus! {

/// Authority over the set of PIO ids currently allocated by the global allocator.
///
/// The `Loc` of `auth` identifies the protocol instance and `auth@` is the set of allocated
/// ids. [`IoPortClaim`] fragments minted by [`IoPortAllocation::allocate`] transfer the
/// ownership of an acquired PIO range to the caller.
pub(super) tracked struct IoPortAllocation {
    auth: GhostSetAuth<usize>,
}

/// Fragment claiming ownership of a PIO id range handed out by [`IoPortAllocator::acquire`].
///
/// A claim asserts that its ids are allocated by the [`IoPortAllocation`] with the same
/// instance identity, and is consumed when the ids are released by
/// [`IoPortAllocator::recycle`].
pub(super) tracked struct IoPortClaim {
    subset: GhostSubset<usize>,
}

impl IoPortAllocation {
    /// Instance identity of the protocol.
    pub closed spec fn instance_id(self) -> InstanceId {
        self.auth.id()
    }

    /// Ids currently allocated.
    pub closed spec fn value(self) -> Set<usize> {
        self.auth@
    }

    /// Creates a fresh protocol instance with an empty allocated set.
    pub proof fn initialize() -> (tracked result: Self) {
        let tracked (auth, _empty_claims) = GhostSetAuth::new(Set::empty());
        Self { auth }
    }

    /// Allocates `ids`, requiring them to be currently free, and mints the matching claim
    /// fragment.
    pub proof fn allocate(tracked &mut self, ids: Set<usize>) -> (tracked claim: IoPortClaim)
        requires
            old(self).value().disjoint(ids),
        ensures
            final(self).instance_id() == old(self).instance_id(),
            final(self).value() == old(self).value().union(ids),
            claim.instance_id() == final(self).instance_id(),
            claim.set() == ids,
    {
        let tracked subset = self.auth.insert_set(ids);
        IoPortClaim { subset }
    }

    /// Consumes `claim`, removing its ids from the allocated set.
    pub proof fn release(tracked &mut self, tracked claim: IoPortClaim)
        requires
            claim.instance_id() == old(self).instance_id(),
        ensures
            final(self).instance_id() == old(self).instance_id(),
            final(self).value() == old(self).value().difference(claim.set()),
    {
        self.auth.delete(claim.subset);
    }

    /// Certifies `claim.set() <= self.value()` (the claim's ids are currently allocated).
    pub proof fn claim_includes(tracked &self, tracked claim: &IoPortClaim)
        requires
            claim.instance_id() == self.instance_id(),
        ensures
            claim.set() <= self.value(),
    {
        claim.subset.agree(&self.auth);
    }
}

impl IoPortClaim {
    /// Instance identity of the protocol that issued this claim.
    pub closed spec fn instance_id(self) -> InstanceId {
        self.subset.id()
    }

    /// Ids claimed by this fragment.
    pub closed spec fn set(self) -> Set<usize> {
        self.subset@
    }
}

} // verus!
/// Lock-protected executable bitmap and the state-machine token that models it.
#[verus_verify]
struct IoPortAllocatorInner {
    allocator: ModeledIdAlloc,
    #[cfg(verus_keep_ghost_body)]
    tracked_allocated: Tracked<IoPortAllocation>,
}

verus! {

impl IoPortAllocatorInner {
    pub closed spec fn type_inv(self) -> bool {
        io_port_inner_inv_values(
            self.tracked_allocated@.instance_id(),
            self.tracked_allocated@.value(),
            &self.allocator.inner,
        )
    }
}

} // verus!
/// I/O port allocator that allocates port I/O access to device drivers.
#[verus_verify]
pub struct IoPortAllocator {
    /// Each ID indicates whether a Port I/O (1B) is allocated.
    ///
    /// Instead of using `RangeAllocator` like `IoMemAllocator` does, it is more reasonable to use `IdAlloc`,
    /// as PIO space includes only a small region; for example, x86 module in OSTD allows just 65536 I/O ports.
    allocator: SpinLock</* Original Rust: IdAlloc */ IoPortAllocatorInner, LocalIrqDisabled>,
}

#[verus_verify]
impl IoPortAllocator {
    /// Acquires the `IoPort`. Return None if any region in `port` cannot be allocated.
    #[verus_spec(result =>
        with
            -> claim: Tracked<Option<IoPortClaim>>,
        requires
            vstd::layout::size_of::<T>() <= u16::MAX,
            size_of::<T>() <= u16::MAX,
            port as usize + size_of::<T>() <= u16::MAX,
            io_port_allocator_initialized(),
        ensures
            result is Some ==> result->Some_0@ == port,
            result is Some ==> result->Some_0.well_formed(),
            result is Some <==> claim@ is Some,
            result is Some ==> claim@->Some_0.instance_id() ==
                io_port_allocator_instance_id(),
            result is Some ==> result->Some_0.claim_matches_set(claim@->Some_0.set()),
    )]
    pub fn acquire<T, A>(&self, port: u16) -> Option<IoPort<T, A>> {
        let mut allocator = self.allocator.lock();
        let allocator_inner = &mut *allocator;
        proof! {
            lemma_io_port_alloc_init(&*allocator_inner);
        }
        let mut range = port..(port + size_of::<T>() as u16);
        // `Iterator::any` with a capturing closure is not supported by Verus.
        // Original Rust:
        // if range.any(|i| allocator.is_allocated(i as usize)) { return None; }
        let mut already_allocated = false;
        #[verus_spec(scan_iter =>
            invariant
                allocator_inner.allocator.inner.inv(),
                allocator_inner.allocator.inner@.len()
                    == crate::arch::io::MAX_IO_PORT as int,
                !already_allocated ==> forall|id: usize|
                    range.start as usize <= id <
                        (range.start as int + scan_iter.index()) as usize ==>
                        !id_alloc_view(&allocator_inner.allocator.inner).contains(id),
        )]
        for i in range.clone() {
            proof! {
                assert((i as usize) < allocator_inner.allocator.inner@.len()) by {
                    assert((i as usize) < range.end as usize);
                    assert((range.end as usize) <= u16::MAX as usize);
                    assert((u16::MAX as usize) <= crate::arch::io::MAX_IO_PORT as usize);
                    assert(allocator_inner.allocator.inner@.len()
                        == crate::arch::io::MAX_IO_PORT as int);
                }
            }
            if allocator_inner.allocator.inner.is_allocated(i as usize) {
                already_allocated = true;
            }
            proof! {
                lemma_id_alloc_view_contains(&allocator_inner.allocator.inner, i as usize);
            }
        }
        proof_decl! {
            let tracked range_claim: IoPortClaim;
        }
        if already_allocated {
            allocator.drop();
            return {
                proof_with!(|= Tracked(None));
                None
            };
        }

        proof_decl! {
            let ghost ids = port_id_set(range.start as usize, range.end as usize);
            let ghost allocation_start_view = id_alloc_view(&allocator_inner.allocator.inner);
        }
        proof! {
            assert(ids.disjoint(id_alloc_view(&allocator_inner.allocator.inner))) by {
                assert forall|id: usize| #[trigger] ids.contains(id) implies
                    !id_alloc_view(&allocator_inner.allocator.inner).contains(id) by {
                    lemma_port_id_set_contains(
                        range.start as usize,
                        range.end as usize,
                        id,
                    );
                }
            }
            assert forall|id: usize| ids.contains(id) implies
                id < id_alloc_capacity(&allocator_inner.allocator.inner) by {
                lemma_port_id_set_contains(
                    range.start as usize,
                    range.end as usize,
                    id,
                );
            }
            assert forall|id: usize|
                range.start as usize <= id < range.end as usize implies
                !id_alloc_view(&allocator_inner.allocator.inner).contains(id) by {
                lemma_port_id_set_contains(
                    range.start as usize,
                    range.end as usize,
                    id,
                );
            }
        }
        #[verus_spec(allocation_iter =>
            invariant
                allocator_inner.allocator.inner.inv(),
                allocator_inner.allocator.inner@.len()
                    == crate::arch::io::MAX_IO_PORT as int,
                range.end as usize <= id_alloc_capacity(&allocator_inner.allocator.inner),
                allocator_inner.tracked_allocated@.instance_id() ==
                    io_port_allocator_instance_id(),
                allocator_inner.tracked_allocated@.value().subset_of(allocation_start_view),
                allocator_inner.tracked_allocated@.value().subset_of(
                    id_alloc_view(&allocator_inner.allocator.inner),
                ),
                id_alloc_capacity(&allocator_inner.allocator.inner) ==
                    crate::arch::io::MAX_IO_PORT as usize,
                id_alloc_view(&allocator_inner.allocator.inner) ==
                    allocation_start_view.union(
                        port_id_set(
                            range.start as usize,
                            (range.start as int + allocation_iter.index()) as usize,
                        ),
                    ),
                forall|id: usize|
                    (range.start as int + allocation_iter.index()) as usize <= id <
                        range.end as usize ==>
                    !id_alloc_view(&allocator_inner.allocator.inner).contains(id),
        )]
        for i in range.clone() {
            proof_decl! {
                let ghost old_view = id_alloc_view(&allocator_inner.allocator.inner);
            }
            proof! {
                assert((i as usize) ==
                    (range.start as int + allocation_iter.index()) as usize);
                assert((i as usize) < id_alloc_capacity(&allocator_inner.allocator.inner));
                assert(!id_alloc_view(&allocator_inner.allocator.inner).contains(i as usize));
                assert(allocator_inner.tracked_allocated@.value().subset_of(
                    old_view.insert(i as usize),
                )) by {
                    assert forall|id: usize|
                        allocator_inner.tracked_allocated@.value().contains(id) implies
                        old_view.insert(i as usize).contains(id) by {
                    }
                }
                assert(io_port_inner_inv_values(
                    allocator_inner.tracked_allocated@.instance_id(),
                    allocator_inner.tracked_allocated@.value(),
                    &allocator_inner.allocator.inner,
                ));
            }
            #[verus_spec(with
                Ghost(allocator_inner.tracked_allocated@.instance_id()),
                Ghost(allocator_inner.tracked_allocated@.value()),
            )]
            /* Original Rust: allocator.alloc_specific(i as usize); */
            let _ = allocator_inner.allocator.alloc_specific(i as usize);
            proof! {
                lemma_port_id_set_insert(range.start as usize, i as usize);
                assert(id_alloc_view(&allocator_inner.allocator.inner) ==
                    old_view.insert(i as usize));
            }
        }
        proof! {
            assert(ids.disjoint(allocator_inner.tracked_allocated@.value())) by {
                assert forall|id: usize| #[trigger] ids.contains(id) implies
                    !allocator_inner.tracked_allocated@.value().contains(id) by {
                }
            }
            range_claim = allocator_inner.tracked_allocated.borrow_mut().allocate(ids);
        }

        // SAFETY: The created IoPort is guaranteed not to access system device I/O
        /* Original Rust: unsafe { Some(IoPort::new(port)) } */
        let result = unsafe { Some(IoPort::new(port)) };
        allocator.drop();
        proof_with!(|= Tracked(Some(range_claim)));
        result
    }

    /// Recycles an PIO range.
    ///
    /// # Safety
    ///
    /// The caller must have ownership of the PIO region through the `IoPortAllocator::acquire` interface.
    #[verus_spec(
        with
            Tracked(claim): Tracked<IoPortClaim>,
        requires
            claim.instance_id() == io_port_allocator_instance_id(),
            claim.set() =~= port_id_set(range.start as usize, range.end as usize),
            range.start <= range.end,
            io_port_allocator_initialized(),
    )]
    pub(in crate::io) unsafe fn recycle(&self, range: Range<u16>) {
        /* debug!("Recycling MMIO range: {:#x?}", range); */
        /* Original Rust:
        self.allocator
            .lock()
            .free_consecutive(range.start as usize..range.end as usize);
        */

        let mut allocator = self.allocator.lock();
        let allocator_inner = &mut *allocator;
        proof! {
            lemma_io_port_alloc_init(&*allocator_inner);
            assert(range.start as usize <= range.end as usize);
            assert(claim.instance_id() == allocator_inner.tracked_allocated@.instance_id());
            allocator_inner.tracked_allocated.borrow().claim_includes(&claim);
            assert(port_id_set(range.start as usize, range.end as usize)
                <= allocator_inner.tracked_allocated@.value());
            assert(port_id_set(range.start as usize, range.end as usize)
                <= id_alloc_view(&allocator_inner.allocator.inner));
            assert((range.end as usize) <= allocator_inner.allocator.inner@.len()) by {
                assert((range.end as usize) <= u16::MAX as usize);
                assert((u16::MAX as usize) <= crate::arch::io::MAX_IO_PORT as usize);
                assert(allocator_inner.allocator.inner@.len()
                    == crate::arch::io::MAX_IO_PORT as int);
            }
            allocator_inner.tracked_allocated.borrow_mut().release(claim);
            assert forall|id: usize|
                #[trigger] allocator_inner.tracked_allocated@.value().contains(id) implies {
                &&& id_alloc_view(&allocator_inner.allocator.inner).contains(id)
                &&& !(range.start as usize <= id < range.end as usize)
            } by {
                lemma_port_id_set_contains(
                    range.start as usize,
                    range.end as usize,
                    id,
                );
            }
            assert forall|i: int|
                range.start as usize <= i
                    && i < allocator_inner.allocator.inner@.len()
                    && i < range.end as usize implies
                allocator_inner.allocator.inner@[i]
            by {
                assert(0 <= i);
                assert(i < allocator_inner.allocator.inner@.len());
                assert(allocator_inner.allocator.inner@.len() <= usize::MAX as int);
                assert(i <= usize::MAX as int);
                assert((i as usize) as int == i);
                lemma_port_id_set_contains(
                    range.start as usize,
                    range.end as usize,
                    i as usize,
                );
                assert(port_id_set(range.start as usize, range.end as usize).contains(i as usize));
                assert(id_alloc_view(&allocator_inner.allocator.inner).contains(i as usize));
                lemma_id_alloc_view_contains(&allocator_inner.allocator.inner, i as usize);
                assert(allocator_inner.allocator.inner@[i]);
            }
        }
        allocator_inner
            .allocator
            .inner
            .free_consecutive(range.start as usize..range.end as usize);
        allocator.drop();
    }
}

verus! {

/// Trusted boot-state fact required before accessing the global PIO allocator.
///
/// Verus cannot currently mention an `exec static` in a specification, so this predicate is the
/// explicit specification boundary for the architecture's guarantee that [`init`] ran first.
pub uninterp spec fn io_port_allocator_initialized() -> bool;

/// Trusted: once `init` has run, the global allocator's inner satisfies its invariant.
#[verifier::external_body]
proof fn lemma_io_port_alloc_init(inner: &IoPortAllocatorInner)
    requires
        io_port_allocator_initialized(),
    ensures
        io_port_inner_inv_values(
            inner.tracked_allocated@.instance_id(),
            inner.tracked_allocated@.value(),
            &inner.allocator.inner,
        ),
{
}

} // verus!
pub(super) static IO_PORT_ALLOCATOR: Once<IoPortAllocator> = Once::new();

/// Initializes the static `IO_PORT_ALLOCATOR` and removes the system device I/O port regions.
///
/// # Safety
///
/// User must ensure that:
///
/// 1. All the port I/O regions belonging to the system device are defined using the macros
///    `sensitive_io_port` and `reserve_io_port_range`.
///
/// 2. `MAX_IO_PORT` defined in `crate::arch::io` is guaranteed not to exceed the maximum
///    value specified by architecture.
#[verifier::external_body]
pub(crate) unsafe fn init() {
    // SAFETY: `MAX_IO_PORT` is guaranteed not to exceed the maximum value specified by architecture.
    let mut allocator = IdAlloc::with_capacity(crate::arch::io::MAX_IO_PORT as usize);

    extern "C" {
        fn __sensitive_io_ports_start();
        fn __sensitive_io_ports_end();
    }
    let start = __sensitive_io_ports_start as usize;
    let end = __sensitive_io_ports_end as usize;
    assert!((end - start) % size_of::<RawIoPortRange>() == 0);

    // Iterate through the sensitive I/O port ranges and remove them from the allocator.
    let io_port_range_count = (end - start) / size_of::<RawIoPortRange>();
    for i in 0..io_port_range_count {
        let range_base_addr = __sensitive_io_ports_start as usize + i * size_of::<RawIoPortRange>();
        // SAFETY: The range is guaranteed to be valid as it is defined in the `.sensitive_io_ports` section.
        let port_range = unsafe { *(range_base_addr as *const RawIoPortRange) };

        assert!(port_range.begin < port_range.end);
        debug!("Removing sensitive I/O port range: {:#x?}", port_range);

        for i in port_range.begin..port_range.end {
            allocator.alloc_specific(i as usize);
        }
    }

    /* Original Rust:
    IO_PORT_ALLOCATOR.call_once(|| IoPortAllocator {
        allocator: SpinLock::new(allocator),
    }); */
    IO_PORT_ALLOCATOR.call_once(|| {
        proof_decl! {
            let tracked allocated = IoPortAllocation::initialize();
        }
        let inner = IoPortAllocatorInner {
            allocator: ModeledIdAlloc { inner: allocator },
            #[cfg(verus_keep_ghost_body)]
            tracked_allocated: Tracked::new(allocated),
        };
        IoPortAllocator {
            allocator: SpinLock::new(inner, Ghost::new(()), Tracked::new(())),
        }
    });
}
