// SPDX-License-Identifier: MPL-2.0
//! I/O port allocator.
use vstd::{
    prelude::*,
    resource::set::{GhostSetAuth, GhostSubset},
    tokens::InstanceId,
};
use vstd_extra::{ownership::Inv, resource_invariant::ResourceInvariant};

use crate::arch::device::io_port::valid_io_port_access;

use core::ops::Range;

use id_alloc::IdAlloc;
use log::debug;
use spin::Once;

use super::IoPort;
use crate::{
    io::RawIoPortRange,
    sync::{LocalIrqDisabled, SpinLock},
};

verus! {

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

pub(crate) open spec fn io_port_inner_inv_values(
    allocated_instance_id: InstanceId,
    allocated: Set<usize>,
    allocator: &IdAlloc,
) -> bool {
    &&& allocated_instance_id == io_port_allocator_instance_id()
    &&& allocator.inv()
    &&& allocator@.len() == crate::arch::io::MAX_IO_PORT
    &&& allocated.subset_of(id_alloc_view(allocator))
    &&& id_alloc_capacity(allocator) == crate::arch::io::MAX_IO_PORT as usize
}

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

ghost struct IoPortAllocInvariant;

impl ResourceInvariant<IdAlloc> for IoPortAllocInvariant {
    type Constant = ();

    type Resource = IoPortAllocation;

    closed spec fn inv(_constant: (), alloc: IdAlloc, r: IoPortAllocation) -> bool {
        io_port_inner_inv_values(r.instance_id(), r.value(), &alloc)
    }
}

} // verus!
/// I/O port allocator that allocates port I/O access to device drivers.
#[verus_verify]
pub(super) struct IoPortAllocator {
    /// Each ID indicates whether a Port I/O (1B) is allocated.
    ///
    /// Instead of using `RangeAllocator` like `IoMemAllocator` does, it is more reasonable to use `IdAlloc`,
    /// as PIO space includes only a small region; for example, x86 module in OSTD allows just 65536 I/O ports.
    allocator: SpinLock<IdAlloc, LocalIrqDisabled, IoPortAllocInvariant>,
}

#[verus_verify]
impl IoPortAllocator {
    /// Acquires an `IoPort`. Returns `None` if the PIO range is unavailable.
    ///
    /// `is_overlapping` indicates whether another `IoPort` can have a PIO range that overlaps with
    /// this one. If it is true, only the first port in the PIO range will be marked as occupied;
    /// otherwise, all ports in the PIO range will be marked as occupied.
    #[verus_spec(result =>
        with
            Tracked(claim_out): Tracked<&mut Tracked<Option<IoPortClaim>>>,
        requires
            size_of::<T>() <= u16::MAX,
            is_overlapping ==> port as usize + size_of::<T>() <= u16::MAX,
            valid_io_port_access::<T>(port),
            io_port_allocator_initialized(),
            (*old(claim_out))@ is None,
        ensures
            result is Some <==> (*final(claim_out))@ is Some,
            result matches Some(io_port) ==> {
                &&& io_port@ == port
                &&& io_port.is_overlapping() == is_overlapping
                &&& io_port.claim_matches_set((*final(claim_out))@->Some_0.set())
                &&& (*final(claim_out))@->Some_0.instance_id() == io_port_allocator_instance_id()
            },
    )]
    pub(super) fn acquire<T, A>(&self, port: u16, is_overlapping: bool) -> Option<IoPort<T, A>> {
        let range = if !is_overlapping {
            port..port.checked_add(size_of::<T>().try_into().ok()?)?
        } else {
            port..port.checked_add(1)?
        };
        /* debug!("Try to acquire PIO range: {:#x?}", range); */
        let mut allocator = self.allocator.lock();
        proof_decl! {
            let ghost instance_id = allocator.resource().instance_id();
            let ghost preserved = allocator.resource().value();
        }
        proof! {
            assert(io_port_inner_inv_values(instance_id, preserved, &allocator.value()));
        }
        let allocator_inner = &mut *allocator;
        // `Iterator::any` with a capturing closure is not supported by Verus.
        // Original Rust:
        // if range.any(|i| allocator.is_allocated(i as usize)) { return None; }
        let mut already_allocated = false;
        #[verus_spec(scan_iter =>
            invariant
                allocator_inner.inv(),
                allocator_inner@.len()
                    == crate::arch::io::MAX_IO_PORT,
                !already_allocated ==> forall|id: usize|
                    range.start as usize <= id <
                        (range.start as int + scan_iter.index()) as usize ==>
                        !id_alloc_view(&allocator_inner).contains(id),
        )]
        for i in range.clone() {
            proof! {
                assert((i as usize) < allocator_inner@.len()) by {
                    assert((i as usize) < range.end as usize);
                    assert((range.end as usize) <= u16::MAX as usize);
                    assert((u16::MAX as usize) <= crate::arch::io::MAX_IO_PORT as usize);
                    assert(allocator_inner@.len()
                        == crate::arch::io::MAX_IO_PORT);
                }
            }
            if allocator_inner.is_allocated(i as usize) {
                already_allocated = true;
            }
            proof! {
                lemma_id_alloc_view_contains(&allocator_inner, i as usize);
            }
        }
        proof_decl! {
            let tracked range_claim: IoPortClaim;
        }
        if already_allocated {
            allocator.drop();
            proof! {
                *claim_out = Tracked(None);
            }
            return None;
        }

        proof_decl! {
            let ghost ids = Set::<usize>::range(range.start as usize, range.end as usize);
            let ghost allocation_start_view = id_alloc_view(&allocator_inner);
        }
        proof! {
            assert(ids.disjoint(id_alloc_view(&allocator_inner))) by {
                assert forall|id: usize| #[trigger] ids.contains(id) implies
                    !id_alloc_view(&allocator_inner).contains(id) by {
                }
            }
            assert forall|id: usize| ids.contains(id) implies
                id < id_alloc_capacity(&allocator_inner) by {
            }
            assert forall|id: usize|
                range.start as usize <= id < range.end as usize implies
                !id_alloc_view(&allocator_inner).contains(id) by {
            }
        }
        #[verus_spec(allocation_iter =>
            invariant
                allocator_inner.inv(),
                allocator_inner@.len()
                    == crate::arch::io::MAX_IO_PORT,
                range.end as usize <= id_alloc_capacity(&allocator_inner),
                instance_id == io_port_allocator_instance_id(),
                preserved.subset_of(allocation_start_view),
                preserved.subset_of(id_alloc_view(&allocator_inner)),
                id_alloc_capacity(&allocator_inner) ==
                    crate::arch::io::MAX_IO_PORT as usize,
                id_alloc_view(&allocator_inner) ==
                    allocation_start_view.union(
                        Set::<usize>::range(
                            range.start as usize,
                            (range.start as int + allocation_iter.index()) as usize,
                        ),
                    ),
                forall|id: usize|
                    (range.start as int + allocation_iter.index()) as usize <= id <
                        range.end as usize ==>
                    !id_alloc_view(&allocator_inner).contains(id),
        )]
        for i in range.clone() {
            proof_decl! {
                let ghost old_view = id_alloc_view(&allocator_inner);
                let ghost old_seq = allocator_inner@;
                let ghost old_len = (allocator_inner@.len()) as int;
            }
            proof! {
                assert((i as usize) ==
                    (range.start as int + allocation_iter.index()) as usize);
                assert((i as usize) < id_alloc_capacity(&allocator_inner));
                assert(allocator_inner.inv());
                assert(!id_alloc_view(&allocator_inner).contains(i as usize));
                assert(preserved.subset_of(old_view.insert(i as usize))) by {
                    assert forall|id: usize|
                        preserved.contains(id) implies
                        old_view.insert(i as usize).contains(id) by {
                    }
                }
            }
            /* Original Rust: allocator.alloc_specific(i as usize); */
            let _res = allocator_inner.alloc_specific(i as usize);
            proof! {
                assert(allocator_inner@.len() == old_len);
                assert(id_alloc_view(&allocator_inner) == old_view.insert(i as usize)) by {
                    // Extending the interval by one byte. vstd exposes no range-extension
                    // lemma, so the step goes through set extensionality here; membership
                    // comes from the default `range_set_properties` broadcast.
                    assert(Set::<usize>::range(range.start as usize, i as usize).insert(i as usize)
                        =~= Set::<usize>::range(
                            range.start as usize,
                            (i as usize + 1) as usize,
                        )) by {
                        assert forall|j: usize|
                            #![trigger Set::<usize>::range(
                                range.start as usize,
                                (i as usize + 1) as usize,
                            ).contains(j)]
                            Set::<usize>::range(
                                range.start as usize,
                                (i as usize + 1) as usize,
                            ).contains(j)
                                == Set::<usize>::range(
                                    range.start as usize,
                                    i as usize,
                                ).insert(i as usize).contains(j) by {
                        }
                    }
                    assert forall|j: usize|
                        #![trigger id_alloc_view(&allocator_inner).contains(j)]
                        id_alloc_view(&allocator_inner).contains(j)
                        == old_view.insert(i as usize).contains(j) by {
                        lemma_id_alloc_bits_char(old_seq, old_len, j);
                        lemma_id_alloc_bits_char(allocator_inner@, old_len, j);
                        if _res is Some {
                            assert(allocator_inner@ == old_seq.update(i as int, true));
                            assert(allocator_inner@[j as int] == (if j == i {
                                true
                            } else {
                                old_seq[j as int]
                            }));
                        } else {
                            assert(old_seq[i as int]);
                            assert(allocator_inner@ == old_seq);
                        }
                    }
                }
                assert(preserved.subset_of(id_alloc_view(&allocator_inner)));
                assert(io_port_inner_inv_values(instance_id, preserved, &allocator_inner));
            }
        }
        proof! {
            assert(ids.disjoint(preserved)) by {
                assert forall|id: usize| #[trigger] ids.contains(id) implies
                    !preserved.contains(id) by {
                }
            }
            assert(preserved.disjoint(ids));
            range_claim = allocator.tracked_borrow_mut_resource().allocate(ids);
        }

        // SAFETY: The created `IoPort` is guaranteed not to access system device I/O.
        /* Original Rust: unsafe { Some(IoPort::new_overlapping(port, is_overlapping)) } */
        let result = unsafe { Some(IoPort::new_overlapping(port, is_overlapping)) };
        proof! {
            assert(id_alloc_view(&allocator.value()) == allocation_start_view.union(ids));
            assert(preserved.subset_of(allocation_start_view));
            assert(allocator.resource().value() == preserved.union(ids));
            assert(io_port_inner_inv_values(
                allocator.resource().instance_id(),
                allocator.resource().value(),
                &allocator.value(),
            ));
        }
        allocator.drop();
        proof! {
            *claim_out = Tracked(Some(range_claim));
        }
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
            claim.set() =~= Set::<usize>::range(range.start as usize, range.end as usize),
            range.start <= range.end,
            io_port_allocator_initialized(),
    )]
    pub(super) unsafe fn recycle(&self, range: Range<u16>) {
        /* debug!("Recycling PIO range: {:#x?}", range); */
        /* Original Rust:
        self.allocator
            .lock()
            .free_consecutive(range.start as usize..range.end as usize);
        */

        let mut allocator = self.allocator.lock();
        proof_decl! {
            let ghost instance_id: InstanceId;
            let ghost preserved: Set<usize>;
            let ghost bitmap_view: Set<usize>;
            let ghost token_released: Set<usize>;
            let ghost pre_seq: Seq<bool>;
            let ghost pre_len: int;
        }
        proof! {
            assert(range.start as usize <= range.end as usize);
            instance_id = allocator.resource().instance_id();
            preserved = allocator.resource().value();
            pre_seq = allocator.value()@;
            pre_len = allocator.value()@.len() as int;
            bitmap_view = id_alloc_view(&allocator.value());
            assert(io_port_inner_inv_values(instance_id, preserved, &allocator.value()));
            assert(preserved.subset_of(bitmap_view));
            assert(bitmap_view == id_alloc_bits(pre_seq, pre_len));
            assert(pre_len == crate::arch::io::MAX_IO_PORT);
            assert(crate::arch::io::MAX_IO_PORT <= usize::MAX);
            assert(pre_len <= usize::MAX);
            assert(claim.instance_id() == instance_id);
            assert((range.end as usize) <= allocator.value()@.len()) by {
                assert((range.end as usize) <= u16::MAX as usize);
                assert((u16::MAX as usize) <= crate::arch::io::MAX_IO_PORT as usize);
                assert(allocator.value()@.len()
                    == crate::arch::io::MAX_IO_PORT);
            }
        }
        proof! {
            let tracked r = allocator.tracked_borrow_mut_resource();
            r.claim_includes(&claim);
            assert(Set::<usize>::range(range.start as usize, range.end as usize) <= r.value());
            assert(r.value() == preserved);
            assert(Set::<usize>::range(range.start as usize, range.end as usize) <= preserved);
            r.release(claim);
            token_released = r.value();
            assert(token_released
                == preserved.difference(Set::<usize>::range(
                    range.start as usize,
                    range.end as usize,
                )));
            assert forall|id: usize|
                #![trigger token_released.contains(id)]
                token_released.contains(id) implies {
                &&& bitmap_view.contains(id)
                &&& !(range.start as usize <= id < range.end as usize)
            } by {
            }
        }
        let allocator_inner = &mut *allocator;
        /* Original Rust:
        self.allocator
            .lock()
            .free_consecutive(range.start as usize..range.end as usize);
        */
        proof! {
            assert(allocator_inner@.len() == crate::arch::io::MAX_IO_PORT);
            assert(id_alloc_capacity(&allocator_inner)
                == crate::arch::io::MAX_IO_PORT as usize);
            assert(allocator_inner@ == pre_seq);
            assert((range.end as usize) <= id_alloc_capacity(&allocator_inner));
            assert(io_port_inner_inv_values(instance_id, preserved, &allocator_inner));
            assert(id_alloc_view(&allocator_inner) == bitmap_view);
            assert forall|i: int|
                range.start as usize <= i
                    && i < allocator_inner@.len()
                    && i < range.end as usize implies
                allocator_inner@[i]
            by {
                assert(Set::<usize>::range(range.start as usize, range.end as usize)
                    <= preserved);
                assert(preserved.subset_of(bitmap_view));
                assert(bitmap_view == id_alloc_view(&allocator_inner));
                assert(Set::<usize>::range(range.start as usize, range.end as usize)
                    .contains(i as usize));
                lemma_id_alloc_view_contains(&allocator_inner, i as usize);
            }
        }
        allocator_inner.free_consecutive(range.start as usize..range.end as usize);
        proof! {
            assert(allocator.value() == *allocator_inner);
            let final_llen: int = allocator_inner@.len() as int;
            assert(final_llen == pre_len);
            assert(final_llen <= usize::MAX);
            assert forall|id: usize|
                #![trigger allocator.resource().value().contains(id)]
                allocator.resource().value().contains(id) implies
                id_alloc_view(&allocator_inner).contains(id) by {
                lemma_id_alloc_bits_char(pre_seq, pre_len, id);
                lemma_id_alloc_bits_char(allocator_inner@, final_llen, id);
                assert(allocator.resource().value().contains(id)
                    == (preserved.contains(id)
                        && !Set::<usize>::range(
                            range.start as usize,
                            range.end as usize,
                        ).contains(id)));
                assert(Set::<usize>::range(range.start as usize, range.end as usize)
                    <= preserved);
                assert(preserved.subset_of(bitmap_view));
                assert(bitmap_view == id_alloc_bits(pre_seq, pre_len));
                assert(id_alloc_view(&allocator_inner)
                    == id_alloc_bits(allocator_inner@, final_llen));
            }
            assert(allocator_inner.inv());
            assert(allocator_inner@.len() == crate::arch::io::MAX_IO_PORT);
            assert(id_alloc_capacity(&allocator_inner)
                == crate::arch::io::MAX_IO_PORT as usize);
            assert(allocator.resource().instance_id() == instance_id);
            assert(io_port_inner_inv_values(
                allocator.resource().instance_id(),
                allocator.resource().value(),
                &allocator_inner,
            ));
        }
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
pub(in crate::io) unsafe fn init() {
    // SAFETY: `MAX_IO_PORT` is guaranteed not to exceed the maximum value specified by architecture.
    let mut allocator = IdAlloc::with_capacity(crate::arch::io::MAX_IO_PORT as usize);

    unsafe extern "C" {
        fn __sensitive_io_ports_start();
        fn __sensitive_io_ports_end();
    }
    let start = __sensitive_io_ports_start as *const () as usize;
    let end = __sensitive_io_ports_end as *const () as usize;
    assert!((end - start).is_multiple_of(size_of::<RawIoPortRange>()));

    // Iterate through the sensitive I/O port ranges and remove them from the allocator.
    let io_port_range_count = (end - start) / size_of::<RawIoPortRange>();
    for i in 0..io_port_range_count {
        let range_base_addr =
            __sensitive_io_ports_start as *const () as usize + i * size_of::<RawIoPortRange>();
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
    IO_PORT_ALLOCATOR.call_once(|| IoPortAllocator {
        allocator: SpinLock::new(
            allocator,
            Ghost::new(()),
            Tracked::new(IoPortAllocation::initialize()),
        ),
    });
}

// Auxiliary proof lemmas for the id-alloc bitmap model.
verus! {

/// Characterizes `id_alloc_bits`: `id_alloc_bits(s, end).contains(j)` holds exactly when
/// `0 <= j < end` and `s[j]` is `true`.
pub(crate) proof fn lemma_id_alloc_bits_char(s: Seq<bool>, end: int, j: usize)
    requires
        0 <= end,
        end <= usize::MAX,
        s.len() >= end,
        0 <= j,
    ensures
        id_alloc_bits(s, end).contains(j) == (j < end && s[j as int]),
    decreases end,
{
    reveal(id_alloc_bits);
    if end <= 0 {
        assert(id_alloc_bits(s, end) =~= Set::empty());
    } else {
        lemma_id_alloc_bits_char(s, end - 1, j);
        if j == end - 1 {
            assert(id_alloc_bits(s, end - 1).contains(j) == (j < end - 1 && s[j as int]));
            assert(id_alloc_bits(s, end).contains(j) == s[end - 1]);
            assert(s[j as int] == s[end - 1]);
        } else {
            // j != end-1: the bit folded in at (end-1) is distinct from j.
            assert(id_alloc_bits(s, end - 1).contains(j) == (j < end - 1 && s[j as int]));
            assert(((end - 1) as usize) == end - 1);
            assert(j != (end - 1) as usize);
            if s[end - 1] {
                assert(id_alloc_bits(s, end - 1).insert((end - 1) as usize).contains(j)
                    == id_alloc_bits(s, end - 1).contains(j));
            }
            assert(id_alloc_bits(s, end).contains(j) == id_alloc_bits(s, end - 1).contains(j));
            assert((j < end - 1 && s[j as int]) == (j < end && s[j as int]));
        }
    }
}

/// For an in-bounds id, `id_alloc_view` membership coincides with the allocated bitmap bit.
pub(crate) proof fn lemma_id_alloc_view_contains(allocator: &IdAlloc, id: usize)
    requires
        allocator.inv(),
        id < allocator@.len(),
        allocator@.len() <= usize::MAX,
    ensures
        id_alloc_view(allocator).contains(id) == allocator@[id as int],
{
    lemma_id_alloc_bits_char(allocator@, allocator@.len() as int, id);
}

} // verus!
