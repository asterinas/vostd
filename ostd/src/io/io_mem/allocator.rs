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
            use_type_invariant(self);
            lemma_found_window_contains(&self.allocators, &range, allocator);
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
    #[verus_spec(ret =>
        requires
            windows_ordered(allocators@),
            windows_match_registered(allocators@),
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
            usize_ranges_ordered(ranges@),
            usize_ranges_match_registered(ranges@),
        ensures
            ret.type_inv(),
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
                forall|j: int| 0 <= j < it.index() ==> {
                    &&& allocators@[j]@.start == it.seq()[j].start
                    &&& allocators@[j]@.end == it.seq()[j].end
                },
                usize_ranges_ordered(it.seq()),
                usize_ranges_match_registered(it.seq()),
                forall|j: int| 0 <= j < it.index() ==>
                    allocators@[j]@ == registered_io_mem_windows()[j],
                windows_ordered(allocators@),
        )]
        for range in ranges {
            proof! {
                assert(range == it.seq()[it.index()]);
            }
            allocators.push(RangeAllocator::new(range));
            proof! {
                assert(allocators@[allocators@.len() - 1]@.start == range.start);
                assert(range.start == registered_io_mem_windows()[it.index()].start);
                assert(range.end == registered_io_mem_windows()[it.index()].end);
                assert forall|i: int|
                    0 <= i < allocators@.len() - 1
                    implies allocators@[i]@.end <= range.start by {
                    assert(allocators@[i]@.end == it.seq()[i].end);
                    assert(it.seq()[i].end <= it.seq()[i as int + 1].start);
                }
                assert(windows_ordered(allocators@));
            }
        }
        proof! {
            assert(allocators@.len() == registered_io_mem_windows().len());
            assert(windows_match_registered(allocators@));
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
            use_type_invariant(self);
            lemma_found_window_contains(&self.allocators, &range, allocator);
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

broadcast use vstd::std_specs::vec::group_vec_axioms;

/// The registered MMIO windows are pairwise ordered: every window ends at or before the start
/// of the next one, so no window can partially cover a range that is contained in another one.
pub open spec fn windows_ordered(allocators: Seq<RangeAllocator>) -> bool {
    forall|i: int, j: int|
        0 <= i < j < allocators.len() ==> allocators[i]@.end <= allocators[j]@.start
}

/// The format of the windows handed to [`IoMemAllocatorBuilder::new`].
pub open spec fn usize_ranges_ordered(ranges: Seq<Range<usize>>) -> bool {
    forall|i: int, j: int| 0 <= i < j < ranges.len() ==> ranges[i].end <= ranges[j].start
}

/// The abstract MMIO windows registered by platform boot code.
pub uninterp spec fn registered_io_mem_windows() -> Seq<Range<int>>;

/// The concrete range allocators represent the abstract boot-time windows exactly.
pub open spec fn windows_match_registered(allocators: Seq<RangeAllocator>) -> bool {
    &&& allocators.len() == registered_io_mem_windows().len()
    &&& forall|i: int|
        0 <= i < allocators.len() ==> allocators[i]@ == registered_io_mem_windows()[i]
}

/// The ranges passed across the unsafe builder boundary represent the abstract windows.
pub open spec fn usize_ranges_match_registered(ranges: Seq<Range<usize>>) -> bool {
    &&& ranges.len() == registered_io_mem_windows().len()
    &&& forall|i: int|
        0 <= i < ranges.len() ==> {
            &&& ranges[i].start == registered_io_mem_windows()[i].start
            &&& ranges[i].end == registered_io_mem_windows()[i].end
        }
}

impl IoMemAllocatorBuilder {
    /// The builder always holds the ordered windows handed to [`IoMemAllocatorBuilder::new`].
    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        windows_ordered(self.allocators@) && windows_match_registered(self.allocators@)
    }
}

impl IoMemAllocator {
    /// The allocator inherits the ordered windows of the builder it was built from.
    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        windows_ordered(self.allocators@) && windows_match_registered(self.allocators@)
    }
}

/// The trusted boot fact [`io_mem_range_registered`], made concrete: the index of the
/// registered window containing `range`.
pub proof fn lemma_registered_window(windows: &Vec<RangeAllocator>, range: Range<usize>) -> (idx:
    int)
    requires
        windows_ordered(windows@),
        windows_match_registered(windows@),
        io_mem_range_registered(range),
    ensures
        0 <= idx < windows@.len(),
        windows@[idx]@.start <= range.start && range.end <= windows@[idx]@.end,
{
    let idx = choose|m: int|
        0 <= m < registered_io_mem_windows().len() && registered_io_mem_windows()[m].start
            <= range.start && range.end <= registered_io_mem_windows()[m].end;
    assert(windows@[idx]@ == registered_io_mem_windows()[idx]);
    idx
}

/// The window overlapping `range` found by [`find_allocator`] is exactly the registered
/// window containing it: ordered windows cannot partially cover a range contained in
/// another window.
pub proof fn lemma_found_window_contains(
    windows: &Vec<RangeAllocator>,
    range: &Range<usize>,
    found: &RangeAllocator,
)
    requires
        windows_ordered(windows@),
        windows_match_registered(windows@),
        io_mem_range_registered(*range),
        found@.start < range.end && found@.end > range.start,
        exists|k: int| 0 <= k < windows@.len() && windows@[k]@ == found@,
    ensures
        found@.start <= range.start && range.end <= found@.end,
{
    let container_idx = lemma_registered_window(windows, *range);
    let found_idx = choose|k: int| 0 <= k < windows@.len() && windows@[k]@ == found@;
    if found_idx < container_idx {
        assert(windows@[found_idx]@.end <= windows@[container_idx]@.start);
        assert(windows@[container_idx]@.start <= range.start);
        assert(false);
    } else if found_idx == container_idx {
        assert(windows@[found_idx]@.start <= range.start && range.end <= windows@[found_idx]@.end);
    } else {
        assert(range.end <= windows@[container_idx]@.end);
        assert(windows@[container_idx]@.end <= windows@[found_idx]@.start);
        assert(false);
    }
}

/// A range is registered when one abstract boot-time MMIO window contains it.
pub open spec fn io_mem_range_registered(range: Range<usize>) -> bool {
    exists|m: int|
        0 <= m < registered_io_mem_windows().len() && registered_io_mem_windows()[m].start
            <= range.start && range.end <= registered_io_mem_windows()[m].end
}

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
    proof! {
        use_type_invariant(&io_mem_builder);
    }
    // SAFETY: The safety is upheld by the caller.
    IO_MEM_ALLOCATOR.init(unsafe { IoMemAllocator::new(io_mem_builder.allocators) });
}

#[verus_verify]
#[verus_spec(ret =>
    ensures
        ret matches Some(res) ==> {
            &&& res@.start < range.end
            &&& res@.end > range.start
            &&& exists|k: int| 0 <= k < allocators@.len() && allocators@[k]@ == res@
        }
)]
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
