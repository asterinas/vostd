// SPDX-License-Identifier: MPL-2.0
//! I/O Memory allocator.
use crate::specs::arch::PAGE_SIZE;
use crate::sync::{OnceImpl, TrivialPred};
use vstd::prelude::*;
use vstd_extra::resource::flags::OneShotSet;

use alloc::vec::Vec;
use core::ops::Range;

use log::{debug, info};
/*use spin::Once;*/

use crate::{
    io::io_mem::IoMem,
    mm::{CachePolicy, PageFlags},
    util::range_alloc::RangeAllocator,
};

/// I/O memory allocator that allocates memory I/O access to device drivers.
#[verus_verify]
pub struct IoMemAllocator {
    allocators: Vec<RangeAllocator>,
}

#[verus_verify]
impl IoMemAllocator {
    /// Acquires the I/O memory access for `range`.
    ///
    /// If the range is not available, then the return value will be `None`.
    #[verus_spec(result =>
        requires
            vstd::arithmetic::power2::is_pow2(PAGE_SIZE as int),
            range.start < range.end,
            range.end <= usize::MAX - (PAGE_SIZE - 1),
            io_mem_range_registered(range),
        ensures
            result is Some ==> result->Some_0.paddr_spec() == range.start,
            result is Some ==> result->Some_0.length_spec()
                == vstd_extra::external::range::range_usize_len_spec(&range),
    )]
    pub fn acquire(&self, range: Range<usize>) -> Option<IoMem> {
        let allocator = find_allocator(&self.allocators, &range)?;
        proof! {
            // Trusted boot fact (`io_mem_range_registered`): `range` was registered inside a
            // single builder window, and `find_allocator` returns its first overlapping window,
            // which is the containing window because the registered windows are disjoint.
            assume(allocator@.start <= range.start && range.end <= allocator@.end);
        }
        proof_decl! {
            let tracked initialized: OneShotSet;
        }
        let result = #[verus_spec(with => Tracked(initialized))]
        allocator.alloc_specific(&range);
        result.ok()?;

        /* debug!("Acquiring MMIO range:{:x?}..{:x?}", range.start, range.end); */

        // SAFETY: The created `IoMem` is guaranteed not to access physical memory or system device I/O.
        // Original Rust used the upstream bitflags-style associated constant `PageFlags::RW`.
        unsafe { Some(IoMem::new(range, PageFlags::RW(), CachePolicy::Uncacheable)) }
    }

    /// Recycles an MMIO range.
    ///
    /// # Safety
    ///
    /// The caller must have ownership of the MMIO region through the `IoMemAllocator::get` interface.
    #[expect(dead_code)]
    #[verifier::external_body]
    pub(in crate::io) unsafe fn recycle(&self, range: Range<usize>) {
        let allocator = find_allocator(&self.allocators, &range).unwrap();

        /* debug!("Recycling MMIO range:{:x}..{:x}", range.start, range.end); */

        allocator.free(range);
    }

    /// Initializes usable memory I/O region.
    ///
    /// # Safety
    ///
    /// User must ensure the range doesn't belong to physical memory or system device I/O.
    #[verus_verify]
    unsafe fn new(allocators: Vec<RangeAllocator>) -> Self {
        Self { allocators }
    }
}

/// Builder for `IoMemAllocator`.
///
/// The builder must contains the memory I/O regions that don't belong to the physical memory. Also, OSTD
/// must exclude the memory I/O regions of the system device before building the `IoMemAllocator`.
#[verus_verify]
pub(crate) struct IoMemAllocatorBuilder {
    allocators: Vec<RangeAllocator>,
}

#[verus_verify]
impl IoMemAllocatorBuilder {
    /// Initializes memory I/O region for devices.
    ///
    /// # Safety
    ///
    /// User must ensure the range doesn't belong to physical memory.
    #[verus_verify]
    pub(crate) unsafe fn new(ranges: Vec<Range<usize>>) -> Self {
        /* info!(
            "Creating new I/O memory allocator builder, ranges: {:#x?}",
            ranges
        ); */
        let mut allocators = Vec::with_capacity(ranges.len());
        for range in ranges {
            allocators.push(RangeAllocator::new(range));
        }
        Self { allocators }
    }

    /// Removes access to a specific memory I/O range.
    ///
    /// All drivers in OSTD must use this method to prevent peripheral drivers from accessing illegal memory I/O range.
    #[verus_spec(
        requires
            range.start < range.end,
            vstd_extra::panic::may_panic(),
            io_mem_range_registered(range),
    )]
    pub(crate) fn remove(&self, range: Range<usize>) {
        // Formatting machinery used by the original panic is not modeled by Verus.
        // Original Rust used two formatted `panic!` branches here.
        let allocator = find_allocator(&self.allocators, &range);
        vstd_extra::assert!(allocator.is_some());
        let allocator = allocator.unwrap();
        proof! {
            // Trusted boot fact, same reasoning as in `acquire`.
            assume(allocator@.start <= range.start && range.end <= allocator@.end);
        }
        proof_decl! {
            let tracked initialized: OneShotSet;
        }
        let result = #[verus_spec(with => Tracked(initialized))]
        allocator.alloc_specific(&range);
        vstd_extra::assert!(result.is_ok());
    }
}

/// The I/O Memory allocator of the system.
verus! {

/// Trusted boot-state fact required before allocating or removing a `range`.
///
/// Verus cannot mention an exec static in a specification, so this predicate is the explicit
/// specification boundary for the boot-time guarantee that `range` was registered inside a
/// single MMIO window of the builder (and the windows are pairwise disjoint), which is what
/// `RangeAllocator::alloc_specific` requires.
pub uninterp spec fn io_mem_range_registered(range: Range<usize>) -> bool;

pub exec static IO_MEM_ALLOCATOR: OnceImpl<IoMemAllocator, TrivialPred>
    ensures
        IO_MEM_ALLOCATOR.wf(),
{
    OnceImpl::new(Ghost(TrivialPred))
}

} // verus!
/// Initializes the static `IO_MEM_ALLOCATOR` based on builder.
///
/// # Safety
///
/// User must ensure all the memory I/O regions that belong to the system device have been removed by calling the
/// `remove` function.
#[verus_verify]
pub(crate) unsafe fn init(io_mem_builder: IoMemAllocatorBuilder) {
    // SAFETY: The safety is upheld by the caller.
    IO_MEM_ALLOCATOR.init(unsafe { IoMemAllocator::new(io_mem_builder.allocators) });
}

#[verus_verify]
fn find_allocator<'a>(
    allocators: &'a [RangeAllocator],
    range: &Range<usize>,
) -> Option<&'a RangeAllocator> {
    for allocator in allocators.iter() {
        let allocator_range = allocator.fullrange();
        // Verus does not yet support `continue` in `for` loops. Original Rust:
        /*
        if allocator_range.start >= range.end || allocator_range.end <= range.start {
            continue;
        }

        return Some(allocator);
        */
        if allocator_range.start < range.end && allocator_range.end > range.start {
            return Some(allocator);
        }
    }
    None
}

#[cfg(ktest)]
mod test {
    use alloc::vec;

    use super::{IoMemAllocator, IoMemAllocatorBuilder};
    use crate::{mm::PAGE_SIZE, prelude::ktest};

    #[expect(clippy::reversed_empty_ranges)]
    #[expect(clippy::single_range_in_vec_init)]
    #[ktest]
    fn illegal_region() {
        let range = vec![0x4000_0000..0x4200_0000];
        let allocator =
            unsafe { IoMemAllocator::new(IoMemAllocatorBuilder::new(range).allocators) };
        assert!(allocator.acquire(0..0).is_none());
        assert!(allocator.acquire(0x4000_0000..0x4000_0000).is_none());
        assert!(allocator.acquire(0x4000_1000..0x4000_0000).is_none());
        assert!(allocator.acquire(usize::MAX..0).is_none());
    }

    #[ktest]
    fn conflict_region() {
        let max_paddr = 0x100_000_000_000; // 16 TB

        let io_mem_region_a = max_paddr..max_paddr + 0x200_0000;
        let io_mem_region_b =
            (io_mem_region_a.end + PAGE_SIZE)..(io_mem_region_a.end + 10 * PAGE_SIZE);
        let range = vec![io_mem_region_a.clone(), io_mem_region_b.clone()];

        let allocator =
            unsafe { IoMemAllocator::new(IoMemAllocatorBuilder::new(range).allocators) };

        assert!(
            allocator
                .acquire((io_mem_region_a.start - 1)..io_mem_region_a.start)
                .is_none()
        );
        assert!(
            allocator
                .acquire(io_mem_region_a.start..(io_mem_region_a.start + 1))
                .is_some()
        );

        assert!(
            allocator
                .acquire((io_mem_region_a.end + 1)..(io_mem_region_b.start - 1))
                .is_none()
        );
        assert!(
            allocator
                .acquire((io_mem_region_a.end - 1)..(io_mem_region_b.start + 1))
                .is_none()
        );

        assert!(
            allocator
                .acquire((io_mem_region_a.end - 1)..io_mem_region_a.end)
                .is_some()
        );
        assert!(
            allocator
                .acquire(io_mem_region_a.end..(io_mem_region_a.end + 1))
                .is_none()
        );
    }
}
