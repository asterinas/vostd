// SPDX-License-Identifier: MPL-2.0
//! I/O port allocator.
use vstd::prelude::*;

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

/// Verus model for the external bitmap-backed ID allocator.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExIdAlloc(IdAlloc);

/// Opaque specification for the third-party one-time initialization primitive.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(R)]
pub struct ExOnce<T, R>(spin::once::Once<T, R>);

/// IDs currently allocated by an external `IdAlloc`.
pub uninterp spec fn id_alloc_view(allocator: &IdAlloc) -> Set<usize>;

/// Capacity configured for an external `IdAlloc`.
pub uninterp spec fn id_alloc_capacity(allocator: &IdAlloc) -> usize;

pub assume_specification[ IdAlloc::with_capacity ](capacity: usize) -> (allocator: IdAlloc)
    ensures
        id_alloc_capacity(&allocator) == capacity,
        id_alloc_view(&allocator) == Set::<usize>::empty(),
;

pub assume_specification[ IdAlloc::is_allocated ](allocator: &IdAlloc, id: usize) -> (allocated:
    bool)
    ensures
        id < id_alloc_capacity(allocator) ==> allocated == id_alloc_view(allocator).contains(id),
;

pub assume_specification[ IdAlloc::alloc_specific ](allocator: &mut IdAlloc, id: usize) -> (result:
    Option<usize>)
    ensures
        id_alloc_capacity(final(allocator)) == id_alloc_capacity(old(allocator)),
        id < id_alloc_capacity(old(allocator)) && id_alloc_view(old(allocator)).contains(id) ==> {
            &&& result is None
            &&& id_alloc_view(final(allocator)) == id_alloc_view(old(allocator))
        },
        id < id_alloc_capacity(old(allocator)) && !id_alloc_view(old(allocator)).contains(id) ==> {
            &&& result == Some(id)
            &&& id_alloc_view(final(allocator)) == id_alloc_view(old(allocator)).insert(id)
        },
;

pub assume_specification[ IdAlloc::free_consecutive ](allocator: &mut IdAlloc, range: Range<usize>)
    ensures
        id_alloc_capacity(final(allocator)) == id_alloc_capacity(old(allocator)),
        range.end <= id_alloc_capacity(old(allocator)) ==> forall|id: usize| #[trigger]
            id_alloc_view(final(allocator)).contains(id) <==> id_alloc_view(
                old(allocator),
            ).contains(id) && !(range.start <= id < range.end),
;

} // verus!
/// I/O port allocator that allocates port I/O access to device drivers.
#[verus_verify]
pub struct IoPortAllocator {
    /// Each ID indicates whether a Port I/O (1B) is allocated.
    ///
    /// Instead of using `RangeAllocator` like `IoMemAllocator` does, it is more reasonable to use `IdAlloc`,
    /// as PIO space includes only a small region; for example, x86 module in OSTD allows just 65536 I/O ports.
    allocator: SpinLock<IdAlloc, LocalIrqDisabled>,
}

#[verus_verify]
impl IoPortAllocator {
    /// Acquires the `IoPort`. Return None if any region in `port` cannot be allocated.
    #[verus_spec(result =>
        requires
            size_of::<T>() <= u16::MAX,
            port as usize + size_of::<T>() <= u16::MAX,
        ensures
            result is Some ==> result->Some_0@ == port,
    )]
    pub fn acquire<T, A>(&self, port: u16) -> Option<IoPort<T, A>> {
        let mut allocator = self.allocator.lock();
        let mut range = port..(port + size_of::<T>() as u16);
        // `Iterator::any` with a capturing closure is not supported by Verus. Original Rust:
        // if range.any(|i| allocator.is_allocated(i as usize)) { return None; }
        let mut already_allocated = false;
        for i in range.clone() {
            if allocator.is_allocated(i as usize) {
                already_allocated = true;
            }
        }
        if already_allocated {
            return None;
        }

        for i in range.clone() {
            allocator.alloc_specific(i as usize);
        }

        // SAFETY: The created IoPort is guaranteed not to access system device I/O
        unsafe { Some(IoPort::new(port)) }
    }

    /// Recycles an PIO range.
    ///
    /// # Safety
    ///
    /// The caller must have ownership of the PIO region through the `IoPortAllocator::acquire` interface.
    pub(in crate::io) unsafe fn recycle(&self, range: Range<u16>) {
        /* debug!("Recycling MMIO range: {:#x?}", range); */

        self.allocator
            .lock()
            .free_consecutive(range.start as usize..range.end as usize);
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

    IO_PORT_ALLOCATOR.call_once(|| IoPortAllocator {
        allocator: SpinLock::new(allocator),
    });
}
