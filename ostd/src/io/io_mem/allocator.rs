// SPDX-License-Identifier: MPL-2.0
//! I/O Memory allocator.
//! # Verification Design
//! We do not expose ghost tokens representing the permission to allocate a fresh range of I/O memory.
//! So one cannot verify whether `acquire` will succeed or not.
//!
//! However, one can verify that if `acquire` succeeds, then acquiring a second overlapping range will fail.
use vstd::{arithmetic::power2::is_pow2, modes::tracked_swap, prelude::*, resource::Loc};
use vstd_extra::{
    once::OnceImpl, range::ranges_disjoint, resource_invariant::TrivialResourceInvariant,
};

use crate::specs::arch::PAGE_SIZE;
use crate::util::range_alloc::FreePermit;

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
            self.overlaps_range(range) ==> range.start < range.end,
            self.covers_range(range) && range.start < range.end
                ==> range.end <= usize::MAX - (PAGE_SIZE - 1),
        ensures
            result matches Some(io_mem) ==> {
                &&& io_mem.paddr() == range.start
                &&& io_mem.length() == range.end - range.start
                &&& range.start < range.end
                &&& self.covers_range(range)
                &&& io_mem.allocation_perm() matches Some(permit)
                &&& permit.range() == range
                &&& self.has_allocation(permit.id(), range)
            },
    )]
    pub fn acquire(&self, range: Range<usize>) -> Option<IoMem> {
        proof! {
            broadcast use lemma_any_index;
        }
        proof_decl! {
            let tracked mut allocated: Option<FreePermit>;
        }
        (#[verus_spec(with => Tracked(allocated))]
        find_allocator(&self.allocators, &range)?.alloc_specific(&range))
        .ok()?;

        /* debug!("Acquiring MMIO range:{:x?}..{:x?}", range.start, range.end); */

        proof! {
            reveal_with_fuel(is_pow2, 13);
        }
        // SAFETY: The created `IoMem` is guaranteed not to access physical memory or system device I/O.
        // unsafe { Some(IoMem::new(range, PageFlags::RW, CachePolicy::Uncacheable)) }
        let mut io_mem = unsafe { IoMem::new(range, PageFlags::RW, CachePolicy::Uncacheable) };
        proof! {
            tracked_swap(io_mem.tracked_perm.borrow_mut(), &mut allocated);
        }
        Some(io_mem)
    }

    /// Recycles an MMIO range.
    ///
    /// # Safety
    ///
    /// The caller must have ownership of the MMIO region through the `IoMemAllocator::get` interface.
    #[expect(dead_code)]
    #[verus_spec(
        with
            Tracked(allocated): Tracked<FreePermit>,
        requires
            allocated.range() == range,
            self.has_allocation(allocated.id(), range),
    )]
    pub(in crate::io) unsafe fn recycle(&self, range: Range<usize>) {
        proof! {
            broadcast use lemma_any_index;
            use_type_invariant(self);
        }
        let allocator = find_allocator(&self.allocators, &range).unwrap();

        /* debug!("Recycling MMIO range:{:x}..{:x}", range.start, range.end); */

        #[verus_spec(with Tracked(allocated))]
        allocator.free(range);
    }

    /// Initializes usable memory I/O region.
    ///
    /// # Safety
    ///
    /// User must ensure the range doesn't belong to physical memory or system device I/O.
    #[verus_spec(ret =>
        requires
            windows_disjoint(allocators@),
        ensures
            ret.allocators@ == allocators@,
    )]
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
    #[verus_spec(ret =>
        requires
            ranges_disjoint(ranges@),
            ranges@.all(|range: Range<usize>| range.start <= range.end),
        ensures
            ret@ == ranges@,
            ret.has_registered_windows() == usize_ranges_match_registered(ranges@),
    )]
    pub(crate) unsafe fn new(ranges: Vec<Range<usize>>) -> Self {
        /* info!(
            "Creating new I/O memory allocator builder, ranges: {:#x?}",
            ranges
        ); */
        let mut allocators: Vec<RangeAllocator> = Vec::with_capacity(ranges.len());
        #[verus_spec(it =>
            invariant
                allocators@.len() == it.index(),
                forall|j: int| #![trigger it.seq()[j]] 0 <= j < it.index() ==> {
                    &&& allocators@[j]@.start == it.seq()[j].start
                    &&& allocators@[j]@.end == it.seq()[j].end
                },
                ranges_disjoint(it.seq()),
                it.seq().all(|range: Range<usize>| range.start <= range.end),
                windows_disjoint(allocators@),
        )]
        for range in ranges {
            allocators.push(RangeAllocator::new(range));
            proof! {
                assert forall|i: int| #![trigger allocators@[i]]
                    0 <= i < allocators@.len() - 1
                    implies allocators@[i]@.end <= range.start
                        || range.end <= allocators@[i]@.start by {
                    assert(it.seq()[i].end <= it.seq()[it.index()].start
                        || it.seq()[it.index()].end <= it.seq()[i].start);
                }
            }
        }
        proof! {
            if usize_ranges_match_registered(ranges@) {
                assert(ranges@ =~= registered_io_mem_windows());
            }
        }
        Self { allocators }
    }

    /* /// Removes access to a specific memory I/O range.
    ///
    /// All drivers in OSTD must use this method to prevent peripheral drivers from accessing illegal memory I/O range.
    pub(crate) fn remove(&self, range: Range<usize>) {
        let Some(allocator) = find_allocator(&self.allocators, &range) else {
            panic!(
                "Allocator for the system device's MMIO was not found. Range: {:x?}",
                range
            );
        };

        if let Err(err) = allocator.alloc_specific(&range) {
            panic!(
                "An error occurred while trying to remove access to the system device's MMIO. Range: {:x?}. Error: {:?}",
                range, err
            );
        }
    }*/
}

verus! {

broadcast use vstd::std_specs::vec::group_vec_axioms;

/// The MMIO windows are pairwise disjoint, so the first overlapping window found by
/// `find_allocator` is the window containing a registered range, regardless of window order.
closed spec fn windows_disjoint(allocators: Seq<RangeAllocator>) -> bool {
    forall|i: int, j: int|
        #![trigger allocators[i], allocators[j]]
        0 <= i < j < allocators.len() ==> allocators[i]@.end <= allocators[j]@.start
            || allocators[j]@.end <= allocators[i]@.start
}

/// The abstract MMIO windows registered by platform boot code.
pub uninterp spec fn registered_io_mem_windows() -> Seq<Range<usize>>;

/// The concrete range allocators represent the abstract boot-time windows exactly.
closed spec fn windows_match_registered(allocators: Seq<RangeAllocator>) -> bool {
    allocators.map_values(|allocator: RangeAllocator| allocator@) == registered_io_mem_windows()
}

/// The ranges passed across the unsafe builder boundary represent the abstract windows.
pub open spec fn usize_ranges_match_registered(ranges: Seq<Range<usize>>) -> bool {
    &&& ranges.len() == registered_io_mem_windows().len()
    &&& forall|i: int|
        #![trigger ranges[i]]
        0 <= i < ranges.len() ==> {
            &&& ranges[i].start <= ranges[i].end
            &&& ranges[i] == registered_io_mem_windows()[i]
        }
}

impl View for IoMemAllocatorBuilder {
    type V = Seq<Range<usize>>;

    closed spec fn view(&self) -> Seq<Range<usize>> {
        self.allocators@.map_values(|allocator: RangeAllocator| allocator@)
    }
}

impl IoMemAllocatorBuilder {
    /// Whether these local windows match the boot-time MMIO registry.
    pub closed spec fn has_registered_windows(self) -> bool {
        windows_match_registered(self.allocators@)
    }

    /// The builder always holds the disjoint windows handed to [`IoMemAllocatorBuilder::new`].
    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        windows_disjoint(self.allocators@)
    }
}

impl IoMemAllocator {
    /// Whether `id` is the allocation-token identity of a window containing `range`.
    pub closed spec fn has_allocation(self, id: Loc, range: Range<usize>) -> bool {
        self.allocators@.any(
            |allocator: RangeAllocator|
                allocator.free_id() == id && allocator@.start <= range.start < range.end
                    <= allocator@.end,
        )
    }

    /// Whether lookup finds a window overlapping the requested endpoints.
    pub closed spec fn overlaps_range(self, range: Range<usize>) -> bool {
        self.allocators@.any(
            |allocator: RangeAllocator|
                allocator@.start < range.end && range.start < allocator@.end,
        )
    }

    /// Whether some window wholly covers `range`.
    pub closed spec fn covers_range(self, range: Range<usize>) -> bool {
        self.allocators@.any(
            |allocator: RangeAllocator|
                allocator@.start <= range.start && range.end <= allocator@.end,
        )
    }

    /// The allocator inherits the disjoint windows of the builder it was built from.
    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        windows_disjoint(self.allocators@)
    }
}

/// A range is registered when one abstract boot-time MMIO window contains it.
pub open spec fn io_mem_range_registered(range: Range<usize>) -> bool {
    registered_io_mem_windows().any(
        |window: Range<usize>| window.start <= range.start && range.end <= window.end,
    )
}

/// Whether the global I/O memory allocator has been initialized.
pub uninterp spec fn io_mem_allocator_initialized() -> bool;

/// The I/O Memory allocator of the system.
// Original Rust: pub static IO_MEM_ALLOCATOR: Once<IoMemAllocator> = Once::new();
pub exec static IO_MEM_ALLOCATOR: OnceImpl<IoMemAllocator, TrivialResourceInvariant>
    ensures
        IO_MEM_ALLOCATOR.wf(),
{
    OnceImpl::new(Ghost(TrivialResourceInvariant))
}

} // verus!
/// Initializes the static `IO_MEM_ALLOCATOR` based on builder.
///
/// # Safety
///
/// User must ensure all the memory I/O regions that belong to the system device have been removed by calling the
/// `remove` function.
#[verifier::external_body]
#[verus_spec(
    requires
        io_mem_builder.has_registered_windows(),
    ensures
        io_mem_allocator_initialized(),
)]
pub(crate) unsafe fn init(io_mem_builder: IoMemAllocatorBuilder) {
    proof! {
        use_type_invariant(&io_mem_builder);
    }
    // SAFETY: The safety is upheld by the caller.
    // Original Rust: IO_MEM_ALLOCATOR.call_once(|| unsafe { IoMemAllocator::new(io_mem_builder.allocators) });
    IO_MEM_ALLOCATOR.init(unsafe { IoMemAllocator::new(io_mem_builder.allocators) });
}

#[verus_verify]
#[verus_spec(ret =>
    ensures
        ret matches Some(res) ==> {
            &&& res@.start < range.end
            &&& res@.end > range.start
            &&& allocators@.contains(*res)
        },
        ret is None ==> allocators@.all(|allocator: RangeAllocator|
            allocator@.start >= range.end || allocator@.end <= range.start),
)]
fn find_allocator<'a>(
    allocators: &'a [RangeAllocator],
    range: &Range<usize>,
) -> Option<&'a RangeAllocator> {
    #[verus_spec(it => invariant
        forall|i: int| #![trigger allocators@[i]] 0 <= i < it.index()
            ==> allocators@[i]@.start >= range.end || allocators@[i]@.end <= range.start,
    )]
    for allocator in allocators.iter() {
        let allocator_range = allocator.fullrange();
        if allocator_range.start >= range.end || allocator_range.end <= range.start {
            continue;
        }

        return Some(allocator);
    }
    None
}

// #[cfg(ktest)]
mod test {
    use vstd::prelude::*;

    use alloc::vec;

    use super::{IoMemAllocator, IoMemAllocatorBuilder};
    use crate::mm::PAGE_SIZE;
    // use crate::prelude::ktest;

    #[expect(clippy::reversed_empty_ranges)]
    #[expect(clippy::single_range_in_vec_init)]
    // #[ktest]
    #[verus_spec]
    fn illegal_region() {
        let range = vec![0x4000_0000..0x4200_0000];
        let allocator =
            unsafe { IoMemAllocator::new(IoMemAllocatorBuilder::new(range).allocators) };
        assert!(allocator.acquire(0..0).is_none());
        assert!(allocator.acquire(0x4000_0000..0x4000_0000).is_none());
        assert!(allocator.acquire(0x4000_1000..0x4000_0000).is_none());
        assert!(allocator.acquire(usize::MAX..0).is_none());
    }

    // #[ktest]
    #[verus_spec]
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

        // assert!(allocator
        //    .acquire(io_mem_region_a.start..(io_mem_region_a.start + 1))
        //    .is_some());

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

        // assert!(allocator
        //    .acquire((io_mem_region_a.end - 1)..io_mem_region_a.end)
        //    .is_some());

        assert!(
            allocator
                .acquire(io_mem_region_a.end..(io_mem_region_a.end + 1))
                .is_none()
        );
    }
}

verus! {

// Bridge `Seq::any`'s predicate trigger to the indexed windows used by the allocator proofs.
broadcast proof fn lemma_any_index<A>(seq: Seq<A>, predicate: spec_fn(A) -> bool)
    ensures
        #[trigger] seq.any(predicate) == (exists|i: int|
            0 <= i < seq.len() && predicate(#[trigger] seq[i])),
{
    if exists|i: int| 0 <= i < seq.len() && predicate(#[trigger] seq[i]) {
        let i = choose|i: int| 0 <= i < seq.len() && predicate(#[trigger] seq[i]);
    }
}

} // verus!
