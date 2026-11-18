// SPDX-License-Identifier: MPL-2.0
//! I/O port allocator.
#[cfg(feature = "irc11")]
use vstd::thread_view::Objective;
use vstd::{
    prelude::*,
    resource::set::{GhostSetAuth, GhostSubset},
    std_specs::iter::IteratorSpec,
    tokens::InstanceId,
};
use vstd_extra::{
    external::{group_io_port_models, obeys_io_port_access_spec, valid_io_port_access},
    ownership::Inv,
    resource_invariant::SimpleResourceInvariant,
};

use crate::arch::io::MAX_IO_PORT;

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
spec fn id_alloc_bits(s: Seq<bool>, end: int) -> Set<usize> {
    Set::<usize>::range(0, end as usize).filter(|id: usize| s[id as int])
}

/// Set of ids currently allocated by `allocator`.
spec fn id_alloc_view(allocator: &IdAlloc) -> Set<usize> {
    id_alloc_bits(allocator@, allocator@.len() as int)
}

/// Authority over the set of PIO ids currently allocated by the global allocator.
///
/// The `Loc` of `auth` identifies the protocol instance and `auth@` is the set of allocated
/// ids. [`GhostSubset`] fragments minted by [`IoPortAllocation::tracked_allocate`] transfer the
/// ownership of an acquired PIO range to the caller.
pub(super) tracked struct IoPortAllocation {
    auth: GhostSetAuth<usize>,
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
    pub proof fn tracked_empty() -> (tracked result: Self)
        ensures
            result.value() == Set::<usize>::empty(),
    {
        let tracked (auth, _empty_claims) = GhostSetAuth::new(Set::empty());
        Self { auth }
    }

    /// Allocates `ids`, requiring them to be currently free, and mints the matching claim
    /// fragment.
    pub proof fn tracked_allocate(tracked &mut self, ids: Set<usize>) -> (tracked claim:
        GhostSubset<usize>)
        requires
            old(self).value().disjoint(ids),
        ensures
            final(self).instance_id() == old(self).instance_id(),
            final(self).value() == old(self).value().union(ids),
            claim.id() == final(self).instance_id(),
            claim@ == ids,
    {
        self.auth.insert_set(ids)
    }

    /// Consumes `claim`, removing its ids from the allocated set.
    pub proof fn tracked_release(tracked &mut self, tracked claim: GhostSubset<usize>)
        requires
            claim.id() == old(self).instance_id(),
        ensures
            final(self).instance_id() == old(self).instance_id(),
            final(self).value() == old(self).value().difference(claim@),
    {
        self.auth.delete(claim);
    }

    /// Certifies `claim@ <= self.value()` (the claim's ids are currently allocated).
    pub proof fn lemma_claim_includes(tracked &self, tracked claim: &GhostSubset<usize>)
        requires
            claim.id() == self.instance_id(),
        ensures
            claim@ <= self.value(),
    {
        claim.agree(&self.auth);
    }
}

ghost struct IoPortAllocInvariant;

#[cfg(feature = "irc11")]
unsafe impl Objective for IoPortAllocation {

}

impl SimpleResourceInvariant<IdAlloc> for IoPortAllocInvariant {
    type Resource = IoPortAllocation;

    closed spec fn inv(alloc: IdAlloc, r: IoPortAllocation) -> bool {
        &&& r.instance_id() == io_port_allocator_instance_id()
        &&& alloc.inv()
        &&& alloc@.len() == MAX_IO_PORT + 1
        &&& r.value().subset_of(id_alloc_view(&alloc))
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
        requires
            size_of::<T>() == 1 || size_of::<T>() == 2 || size_of::<T>() == 4,
            port + size_of::<T>() <= MAX_IO_PORT + 1 ==> obeys_io_port_access_spec::<T>(),
            io_port_allocator_initialized(),
        ensures
            result matches Some(io_port) ==> {
                &&& io_port@ == port
                &&& io_port.is_overlapping() == is_overlapping
                &&& io_port.is_allocated()
                &&& port + size_of::<T>() <= MAX_IO_PORT + 1
            },
    )]
    pub(super) fn acquire<T, A>(&self, port: u16, is_overlapping: bool) -> Option<IoPort<T, A>> {
        proof! {
            broadcast use group_io_port_models;
        }
        /* Verus does not support the generic inline const block used upstream. */
        let max_io_port_for_t = /* const */ {
            assert!(1 <= size_of::<T>() && size_of::<T>() <= 4);
            MAX_IO_PORT as usize + 1 - size_of::<T>()
        };
        let port = port as usize;
        if port > max_io_port_for_t {
            return None;
        }
        let range = if !is_overlapping {
            port..port + size_of::<T>()
        } else {
            port..port + 1
        };
        /* debug!("Try to acquire PIO range: {:#x?}", range); */
        let mut allocator = self.allocator.lock();
        proof_decl! {
            let ghost instance_id = allocator.resource().instance_id();
            let ghost preserved = allocator.resource().value();
        }
        proof! {
            assert(
                instance_id == io_port_allocator_instance_id()
                    && allocator.value().inv()
                    && allocator.value()@.len() == MAX_IO_PORT + 1
                    && preserved.subset_of(id_alloc_view(&allocator.value()))
            );
        }
        let allocator_inner = &mut *allocator;
        proof_decl! {
            let tracked range_claim: GhostSubset<usize>;
        }
        if range.clone().any(
            #[verus_spec(ret: bool =>
                requires
                    range.start <= i < range.end,
                ensures
                    ret == id_alloc_view(&allocator_inner).contains(i),
            )]
            |i| {
                proof! {
                    lemma_id_alloc_view_contains(&allocator_inner, i);
                }
                allocator_inner.is_allocated(i)
            },
        ) {
            allocator.drop();
            return None;
        }

        proof_decl! {
            let ghost ids = Set::<usize>::range(range.start, range.end);
            let ghost allocation_start_view = id_alloc_view(&allocator_inner);
        }
        proof! {
            assert(ids.disjoint(id_alloc_view(&allocator_inner))) by {
                assert forall|id: usize| #[trigger] ids.contains(id) implies
                    !id_alloc_view(&allocator_inner).contains(id) by {
                    assert(IteratorSpec::remaining(&range)[
                        id as int - range.start as int
                    ] == id);
                }
            }
            assert forall|id: usize| ids.contains(id) implies
                id < allocator_inner@.len() by {
            }
            assert forall|id: usize|
                range.start <= id < range.end implies
                !id_alloc_view(&allocator_inner).contains(id) by {
            }
        }
        #[verus_spec(allocation_iter =>
            invariant
                allocator_inner.inv(),
                allocator_inner@.len()
                    == MAX_IO_PORT + 1,
                range.end <= allocator_inner@.len(),
                instance_id == io_port_allocator_instance_id(),
                preserved.subset_of(allocation_start_view),
                preserved.subset_of(id_alloc_view(&allocator_inner)),
                id_alloc_view(&allocator_inner) ==
                    allocation_start_view.union(
                        Set::<usize>::range(
                            range.start,
                            (range.start + allocation_iter.index()) as usize,
                        ),
                    ),
                forall|id: usize|
                    (range.start + allocation_iter.index()) as usize <= id <
                        range.end ==>
                    !id_alloc_view(&allocator_inner).contains(id),
        )]
        for i in range.clone() {
            proof_decl! {
                let ghost old_view = id_alloc_view(&allocator_inner);
                let ghost old_seq = allocator_inner@;
                let ghost old_len = (allocator_inner@.len()) as int;
            }
            proof! {
                assert(i ==
                    (range.start + allocation_iter.index()) as usize);
                assert(i < allocator_inner@.len());
                assert(allocator_inner.inv());
                assert(!id_alloc_view(&allocator_inner).contains(i));
                assert(preserved.subset_of(old_view.insert(i))) by {
                    assert forall|id: usize|
                        preserved.contains(id) implies
                        old_view.insert(i).contains(id) by {
                    }
                }
            }
            allocator_inner.alloc_specific(i);
            proof! {
                assert(allocator_inner@.len() == old_len);
                assert(id_alloc_view(&allocator_inner) == old_view.insert(i)) by {
                    // Extending the interval by one byte. vstd exposes no range-extension
                    // lemma, so the step goes through set extensionality here; membership
                    // comes from the default `range_set_properties` broadcast.
                    assert(Set::<usize>::range(range.start, i).insert(i)
                        =~= Set::<usize>::range(
                            range.start,
                            (i + 1) as usize,
                        )) by {
                        assert forall|j: usize|
                            #![trigger Set::<usize>::range(
                                range.start,
                                (i + 1) as usize,
                            ).contains(j)]
                            Set::<usize>::range(
                                range.start,
                                (i + 1) as usize,
                            ).contains(j)
                                == Set::<usize>::range(
                                    range.start,
                                    i,
                                ).insert(i).contains(j) by {
                        }
                    }
                    assert forall|j: usize|
                        #![trigger id_alloc_view(&allocator_inner).contains(j)]
                        id_alloc_view(&allocator_inner).contains(j)
                        == old_view.insert(i).contains(j) by {
                        lemma_id_alloc_bits_char(old_seq, old_len, j);
                        lemma_id_alloc_bits_char(allocator_inner@, old_len, j);
                        assert(allocator_inner@ == old_seq.update(i as int, true));
                        assert(allocator_inner@[j as int] == (if j == i {
                            true
                        } else {
                            old_seq[j as int]
                        }));
                    }
                }
                assert(preserved.subset_of(id_alloc_view(&allocator_inner)));
                assert(
                instance_id == io_port_allocator_instance_id()
                    && allocator_inner.inv()
                    && allocator_inner@.len() == MAX_IO_PORT + 1
                    && preserved.subset_of(id_alloc_view(&allocator_inner))
            );
            }
        }
        proof! {
            assert(ids.disjoint(preserved)) by {
                assert forall|id: usize| #[trigger] ids.contains(id) implies
                    !preserved.contains(id) by {
                }
            }
            assert(preserved.disjoint(ids));
            range_claim = allocator.tracked_borrow_mut_resource().tracked_allocate(ids);
        }

        // SAFETY: The created `IoPort` is guaranteed not to access system device I/O.
        /* Origin Rust:
         * unsafe { Some(IoPort::new_overlapping(port as u16, is_overlapping)) }
         */
        let result = unsafe {
            Some(IoPort::new_overlapping(
                port as u16,
                is_overlapping,
                verus_exec_expr! { Tracked(Some(range_claim)) },
            ))
        };
        proof! {
            assert(id_alloc_view(&allocator.value()) == allocation_start_view.union(ids));
            assert(preserved.subset_of(allocation_start_view));
            assert(allocator.resource().value() == preserved.union(ids));
            assert(
                allocator.resource().instance_id() == io_port_allocator_instance_id()
                    && allocator.value().inv()
                    && allocator.value()@.len() == MAX_IO_PORT + 1
                    && allocator.resource().value().subset_of(id_alloc_view(&allocator.value()))
            );
        }
        allocator.drop();
        result
    }

    /// Recycles an PIO range.
    ///
    /// # Safety
    ///
    /// The caller must have ownership of the PIO region through the `IoPortAllocator::acquire` interface.
    #[verus_spec(
        with
            Tracked(claim): Tracked<GhostSubset<usize>>,
        requires
            claim.id() == io_port_allocator_instance_id(),
            claim@ =~= Set::<usize>::range(range.start, range.end),
            range.start <= range.end <= MAX_IO_PORT + 1,
            io_port_allocator_initialized(),
    )]
    pub(super) unsafe fn recycle(&self, range: Range<usize>) {
        /* debug!("Recycling PIO range: {:#x?}", range); */
        /* Original Rust:
        self.allocator
            .lock()
            .free_consecutive(range);
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
            assert(range.start <= range.end);
            instance_id = allocator.resource().instance_id();
            preserved = allocator.resource().value();
            pre_seq = allocator.value()@;
            pre_len = allocator.value()@.len() as int;
            bitmap_view = id_alloc_view(&allocator.value());
            assert(
                instance_id == io_port_allocator_instance_id()
                    && allocator.value().inv()
                    && allocator.value()@.len() == MAX_IO_PORT + 1
                    && preserved.subset_of(id_alloc_view(&allocator.value()))
            );
            assert(preserved.subset_of(bitmap_view));
            assert(bitmap_view == id_alloc_bits(pre_seq, pre_len));
            assert(pre_len == MAX_IO_PORT + 1);
            assert(pre_len <= usize::MAX);
            assert(claim.id() == instance_id);
            assert(range.end <= allocator.value()@.len());
        }
        proof! {
            let tracked r = allocator.tracked_borrow_mut_resource();
            r.lemma_claim_includes(&claim);
            assert(Set::<usize>::range(range.start, range.end) <= r.value());
            assert(r.value() == preserved);
            assert(Set::<usize>::range(range.start, range.end) <= preserved);
            r.tracked_release(claim);
            token_released = r.value();
            assert(token_released
                == preserved.difference(Set::<usize>::range(
                    range.start,
                    range.end,
                )));
            assert forall|id: usize|
                #![trigger token_released.contains(id)]
                token_released.contains(id) implies {
                &&& bitmap_view.contains(id)
                &&& !(range.start <= id < range.end)
            } by {
            }
        }
        let allocator_inner = &mut *allocator;
        /* Original Rust:
        self.allocator
            .lock()
            .free_consecutive(range);
        */
        proof! {
            assert(allocator_inner@.len() == MAX_IO_PORT + 1);
            assert(allocator_inner@ == pre_seq);
            assert(range.end <= allocator_inner@.len());
            assert(
                instance_id == io_port_allocator_instance_id()
                    && allocator_inner.inv()
                    && allocator_inner@.len() == MAX_IO_PORT + 1
                    && preserved.subset_of(id_alloc_view(&allocator_inner))
            );
            assert(id_alloc_view(&allocator_inner) == bitmap_view);
            assert forall|i: int|
                range.start <= i < range.end
                    && i < allocator_inner@.len() implies
                allocator_inner@[i]
            by {
                assert(Set::<usize>::range(range.start, range.end)
                    <= preserved);
                assert(preserved.subset_of(bitmap_view));
                assert(bitmap_view == id_alloc_view(&allocator_inner));
                assert(Set::<usize>::range(range.start, range.end)
                    .contains(i as usize));
                lemma_id_alloc_view_contains(&allocator_inner, i as usize);
            }
        }
        proof_decl! {
            let ghost released_start = range.start;
            let ghost released_end = range.end;
        }
        allocator_inner.free_consecutive(range);
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
                            released_start,
                            released_end,
                        ).contains(id)));
                assert(Set::<usize>::range(released_start, released_end)
                    <= preserved);
                assert(preserved.subset_of(bitmap_view));
                assert(bitmap_view == id_alloc_bits(pre_seq, pre_len));
                assert(id_alloc_view(&allocator_inner)
                    == id_alloc_bits(allocator_inner@, final_llen));
            }
            assert(allocator_inner.inv());
            assert(allocator_inner@.len() == MAX_IO_PORT + 1);
            assert(allocator.resource().instance_id() == instance_id);
            assert(
                allocator.resource().instance_id() == io_port_allocator_instance_id()
                    && allocator_inner.inv()
                    && allocator_inner@.len() == MAX_IO_PORT + 1
                    && allocator.resource().value().subset_of(id_alloc_view(&allocator_inner))
            );
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
#[verus_spec(ensures io_port_allocator_initialized())]
pub(in crate::io) unsafe fn init() {
    // SAFETY: `MAX_IO_PORT` is guaranteed not to exceed the maximum value specified by architecture.
    let max_nr_io_ports = MAX_IO_PORT as usize + 1;
    let mut allocator = IdAlloc::with_capacity(max_nr_io_ports);

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
            Tracked::new(IoPortAllocation::tracked_empty()),
        ),
    });
}

// Auxiliary proof lemmas for the id-alloc bitmap model.
verus! {

/// Characterizes `id_alloc_bits`: `id_alloc_bits(s, end).contains(j)` holds exactly when
/// `0 <= j < end` and `s[j]` is `true`.
proof fn lemma_id_alloc_bits_char(s: Seq<bool>, end: int, j: usize)
    requires
        0 <= end <= usize::MAX,
        s.len() >= end,
    ensures
        id_alloc_bits(s, end).contains(j) == (j < end && s[j as int]),
{
    reveal(id_alloc_bits);
}

/// For an in-bounds id, `id_alloc_view` membership coincides with the allocated bitmap bit.
proof fn lemma_id_alloc_view_contains(allocator: &IdAlloc, id: usize)
    requires
        allocator.inv(),
        id < allocator@.len() <= usize::MAX,
    ensures
        id_alloc_view(allocator).contains(id) == allocator@[id as int],
{
    lemma_id_alloc_bits_char(allocator@, allocator@.len() as int, id);
}

} // verus!
// #[cfg(ktest)]
mod test {
    use vstd::prelude::*;
    use vstd_extra::{assert, external::group_io_port_models, panic::may_panic};

    use super::io_port_allocator_initialized;
    use crate::arch::device::io_port::ReadWriteAccess;
    // use crate::prelude::ktest;

    type IoPort = crate::io::IoPort<u32, ReadWriteAccess>;
    type ByteIoPort = crate::io::IoPort<u8, ReadWriteAccess>;
    // #[ktest]
    #[verus_spec(requires io_port_allocator_initialized())]
    fn illegal_region() {
        let io_port_a = IoPort::acquire(0xffff);
        assert!(io_port_a.is_err());

        let io_port_overlapping = IoPort::acquire_overlapping(0xfffe);
        assert!(io_port_overlapping.is_err());
    }

    // #[ktest]
    #[verus_spec(requires io_port_allocator_initialized(), may_panic())]
    fn conflict_region() {
        proof! { broadcast use group_io_port_models; }
        let io_port_a = IoPort::acquire(0x60);
        assert!(io_port_a.is_ok());

        // This allocation will fail because its range conflicts with `io_port_a`.
        let io_port_b = IoPort::acquire(0x62);
        assert!(io_port_b.is_err());

        /* The migrated IoPort uses an explicit ownership-consuming drop method.
         * Origin Rust: drop(io_port_a);
         */
        io_port_a.unwrap().drop();

        // After dropping `io_port_a`, conflicts no longer exist so the allocation will succeed.
        let io_port_b = IoPort::acquire(0x62);
        assert!(io_port_b.is_ok());
    }

    // #[ktest]
    #[verus_spec(requires io_port_allocator_initialized(), may_panic())]
    fn overlapping_region() {
        proof! { broadcast use group_io_port_models; }
        // Reference: <https://wiki.osdev.org/PCI#Configuration_Space_Access_Mechanism_#1>
        let pci_data = IoPort::acquire_overlapping(0xcf8);
        // Reference: <https://www.intel.com/Assets/PDF/datasheet/290562.pdf>
        let rst_ctrl = ByteIoPort::acquire(0xcf9);
        assert!(pci_data.is_ok());
        assert!(rst_ctrl.is_ok());

        let pci_data2 = IoPort::acquire_overlapping(0xcf8);
        let rst_ctrl2 = ByteIoPort::acquire(0xcf9);
        assert!(pci_data2.is_err());
        assert!(rst_ctrl2.is_err());

        /* The migrated IoPort uses an explicit ownership-consuming drop method.
         * Origin Rust: drop(pci_data);
         */
        pci_data.unwrap().drop();
        /* The migrated IoPort uses an explicit ownership-consuming drop method.
         * Origin Rust: drop(rst_ctrl);
         */
        rst_ctrl.unwrap().drop();

        let rst_ctrl3 = ByteIoPort::acquire(0xcf9);
        assert!(rst_ctrl3.is_ok());

        let pci_data3 = IoPort::acquire_overlapping(0xcf8);
        assert!(pci_data3.is_ok());
    }

    // #[ktest]
    #[verus_spec(requires io_port_allocator_initialized(), may_panic())]
    fn last_region() {
        proof! { broadcast use group_io_port_models; }
        /* Verus requires proof that the result is Ok before unwrap.
         * Origin Rust: let io_port = IoPort::acquire(0xfffc).unwrap();
         */
        let io_port = IoPort::acquire(0xfffc);
        assert!(io_port.is_ok());
        let io_port = io_port.unwrap();
        assert!(ByteIoPort::acquire(0xffff).is_err());
        io_port.drop();

        /* Verus requires proof that the result is Ok before unwrap.
         * Origin Rust: let io_port = ByteIoPort::acquire_overlapping(0xffff).unwrap();
         */
        let io_port = ByteIoPort::acquire_overlapping(0xffff);
        assert!(io_port.is_ok());
        let io_port = io_port.unwrap();
        assert!(ByteIoPort::acquire(0xffff).is_err());
        io_port.drop();

        assert!(ByteIoPort::acquire(0xffff).is_ok());
    }
}
