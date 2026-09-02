// SPDX-License-Identifier: MPL-2.0
//! I/O port allocator.
use vstd::prelude::*;
use vstd::resource::set::{GhostSetAuth, GhostSubset};
use vstd::tokens::InstanceId;
use vstd_extra::external::{id_alloc_capacity, id_alloc_view};

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

closed spec fn io_port_inner_inv_values(
    allocated_instance_id: InstanceId,
    allocated: Set<usize>,
    allocator: &IdAlloc,
) -> bool {
    &&& allocated_instance_id == io_port_allocator_instance_id()
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
        no_unwind
    )]
    fn alloc_specific(&mut self, id: usize) -> Option<usize> {
        self.inner.alloc_specific(id)
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
    #[verifier::type_invariant]
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
    allocator: SpinLock<IoPortAllocatorInner, LocalIrqDisabled>,
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
            use_type_invariant(&*allocator_inner);
        }
        let mut range = port..(port + size_of::<T>() as u16);
        // `Iterator::any` with a capturing closure is not supported by Verus. Original Rust:
        // if range.any(|i| allocator.is_allocated(i as usize)) { return None; }
        let mut already_allocated = false;
        #[verus_spec(scan_iter =>
            invariant
                allocator_inner.type_inv(),
                !already_allocated ==> forall|id: usize|
                    range.start as usize <= id <
                        (range.start as int + scan_iter.index()) as usize ==>
                        !id_alloc_view(&allocator_inner.allocator.inner).contains(id),
        )]
        for i in range.clone() {
            if allocator_inner.allocator.inner.is_allocated(i as usize) {
                already_allocated = true;
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
    )]
    pub(in crate::io) unsafe fn recycle(&self, range: Range<u16>) {
        /* debug!("Recycling MMIO range: {:#x?}", range); */

        let mut allocator = self.allocator.lock();
        let allocator_inner = &mut *allocator;
        proof! {
            use_type_invariant(&*allocator_inner);
            assert(range.start as usize <= range.end as usize);
            assert(claim.instance_id() == allocator_inner.tracked_allocated@.instance_id());
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

    IO_PORT_ALLOCATOR.call_once(|| {
        proof_decl! {
            let tracked allocated = IoPortAllocation::initialize();
        }
        let inner = IoPortAllocatorInner {
            allocator: ModeledIdAlloc { inner: allocator },
            #[cfg(verus_keep_ghost_body)]
            tracked_allocated: Tracked::new(allocated),
        };
        // Original Rust: `IoPortAllocator { allocator: SpinLock::new(allocator) }`.
        IoPortAllocator {
            allocator: SpinLock::new(inner, Ghost::new(()), Tracked::new(())),
        }
    });
}
