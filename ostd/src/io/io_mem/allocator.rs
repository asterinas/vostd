// SPDX-License-Identifier: MPL-2.0
//! I/O Memory allocator.
use vstd::{arithmetic::power2::is_pow2, prelude::*, resource::Loc};
use vstd_extra::{
    once::OnceImpl,
    panic::may_panic,
    range::{RangeExtraFns, lemma_ranges_disjoint, ranges_disjoint, ranges_separated},
    resource_invariant::TrivialResourceInvariant,
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
        with
            -> allocated: Tracked<Option<FreePermit>>,
        requires
            self.overlaps_range(range) ==> range.start < range.end,
            self.covers_range(range) && range.start < range.end
                ==> range.end <= usize::MAX - (PAGE_SIZE - 1),
        ensures
            result matches Some(io_mem) ==> {
                &&& io_mem.paddr() == range.start
                &&& io_mem.length() == range.end - range.start
            },
            result is Some ==> range.start < range.end && self.covers_range(range),
            result is Some <==> allocated@ is Some,
            allocated@ matches Some(token) ==> {
                &&& token.range() == range
                &&& self.has_allocation(token.id(), range)
            },
    )]
    pub fn acquire(&self, range: Range<usize>) -> Option<IoMem> {
        proof! {
            broadcast use lemma_any_index;
            use_type_invariant(self);
            lemma_windows_disjoint(self.allocators@);
        }
        proof_decl! {
            let tracked allocated: Option<FreePermit>;
        }
        /* Explicit early returns attach the tracked output on both failure paths.
         * Origin Rust:
         * find_allocator(&self.allocators, &range)?.alloc_specific(&range).ok()?;
         */
        let Some(allocator) = find_allocator(&self.allocators, &range) else {
            return #[verus_spec(with |= Tracked(None))]
            None;
        };
        if (#[verus_spec(with => Tracked(allocated))]
        allocator.alloc_specific(&range))
        .is_err()
        {
            return #[verus_spec(with |= Tracked(allocated))]
            None;
        }

        /* debug!("Acquiring MMIO range:{:x?}..{:x?}", range.start, range.end); */

        proof! {
            // PAGE_SIZE = 4096 = 2^12: 13 unfoldings of the opaque `is_pow2`.
            reveal_with_fuel(is_pow2, 13);
        }

        // SAFETY: The created `IoMem` is guaranteed not to access physical memory or system device I/O.
        #[verus_spec(with |= Tracked(allocated))]
        unsafe {
            Some(IoMem::new(range, PageFlags::RW, CachePolicy::Uncacheable))
        }
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
            range.start < range.end,
            self.covers_range(range),
            allocated.range() == range,
            self.has_allocation(allocated.id(), range),
    )]
    pub(in crate::io) unsafe fn recycle(&self, range: Range<usize>) {
        proof! {
            broadcast use lemma_any_index;
            use_type_invariant(self);
            lemma_windows_disjoint(self.allocators@);
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
        proof! {
            lemma_ranges_disjoint(ranges@);
        }
        #[verus_spec(it =>
            invariant
                allocators@.len() == it.index(),
                forall|j: int| #![trigger it.seq()[j]] 0 <= j < it.index() ==> {
                    &&& allocators@[j]@.start == it.seq()[j].start
                    &&& allocators@[j]@.end == it.seq()[j].end
                },
                ranges_disjoint(it.seq()),
                ranges_separated(it.seq()),
                it.seq().all(|range: Range<usize>| range.start <= range.end),
                windows_disjoint(allocators@),
        )]
        for range in ranges {
            proof! { lemma_windows_disjoint(allocators@); }
            allocators.push(RangeAllocator::new(range));
            proof! {
                assert forall|i: int| #![trigger allocators@[i]]
                    0 <= i < allocators@.len() - 1
                    implies allocators@[i]@.end <= range.start
                        || range.end <= allocators@[i]@.start by {
                    assert(it.seq()[i].end <= it.seq()[it.index()].start
                        || it.seq()[it.index()].end <= it.seq()[i].start);
                }
                let windows = allocators@.map_values(|allocator: RangeAllocator| allocator@);
                assert forall|i: int, j: int| #![trigger windows[i], windows[j]]
                    0 <= i < j < windows.len()
                    implies windows[i].end <= windows[j].start
                        || windows[j].end <= windows[i].start by {
                    assert(allocators@[i]@.end <= allocators@[j]@.start
                        || allocators@[j]@.end <= allocators@[i]@.start);
                }
                assert(ranges_separated(windows));
                lemma_ranges_disjoint(windows);
            }
        }
        proof! {
            assert(allocators@.map_values(|allocator: RangeAllocator| allocator@)
                =~= ranges@);
            if usize_ranges_match_registered(ranges@) {
                assert(ranges@ =~= registered_io_mem_windows());
            }
        }
        Self { allocators }
    }

    /// Removes access to a specific memory I/O range.
    ///
    /// All drivers in OSTD must use this method to prevent peripheral drivers from accessing illegal memory I/O range.
    #[verus_spec(
        requires
            range.start < range.end,
            may_panic(),
    )]
    pub(crate) fn remove(&self, range: Range<usize>) {
        let Some(allocator) = find_allocator(&self.allocators, &range) else {
            vstd_extra::panic!(
                "Allocator for the system device's MMIO was not found. Range: {:x?}",
                range
            );
        };

        proof! {
            use_type_invariant(self);
            lemma_windows_disjoint(self.allocators@);
        }
        proof_decl! {
            let tracked allocated: Option<FreePermit>;
        }

        if let Err(err) = #[verus_spec(with => Tracked(allocated))]
        allocator.alloc_specific(&range)
        {
            vstd_extra::panic!(
                "An error occurred while trying to remove access to the system device's MMIO. Range: {:x?}. Error: {:?}",
                range,
                err
            );
        }
    }
}

verus! {

broadcast use vstd::std_specs::vec::group_vec_axioms;

/// The MMIO windows are pairwise disjoint, so the first overlapping window found by
/// `find_allocator` is the window containing a registered range, regardless of window order.
closed spec fn windows_disjoint(allocators: Seq<RangeAllocator>) -> bool {
    ranges_disjoint(allocators.map_values(|allocator: RangeAllocator| allocator@))
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
    /// Whether these local windows match the boot-time MMIO registry.
    pub closed spec fn has_registered_windows(self) -> bool {
        windows_match_registered(self.allocators@)
    }

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
            unsafe { IoMemAllocator::new((IoMemAllocatorBuilder::new(range)).allocators) };
        proof_decl! {
            let tracked empty_allocation: Option<super::FreePermit>;
        }
        assert!(
            (#[verus_spec(with => Tracked(empty_allocation))]
            allocator.acquire(0..0))
            .is_none()
        );
        proof_decl! {
            assert(empty_allocation is None);
            let tracked empty_window_allocation: Option<super::FreePermit>;
        }
        assert!(
            (#[verus_spec(with => Tracked(empty_window_allocation))]
            allocator.acquire(0x4000_0000..0x4000_0000))
            .is_none()
        );
        proof_decl! {
            assert(empty_window_allocation is None);
            let tracked reversed_allocation: Option<super::FreePermit>;
        }
        assert!(
            (#[verus_spec(with => Tracked(reversed_allocation))]
            allocator.acquire(0x4000_1000..0x4000_0000))
            .is_none()
        );
        proof_decl! {
            assert(reversed_allocation is None);
            let tracked max_reversed_allocation: Option<super::FreePermit>;
        }
        assert!(
            (#[verus_spec(with => Tracked(max_reversed_allocation))]
            allocator.acquire(usize::MAX..0))
            .is_none()
        );
        proof! {
            assert(max_reversed_allocation is None);
        }
    }

    // #[ktest]
    fn conflict_region() {
        let max_paddr = 0x100_000_000_000; // 16 TB

        let io_mem_region_a = max_paddr..max_paddr + 0x200_0000;
        let io_mem_region_b =
            (io_mem_region_a.end + PAGE_SIZE)..(io_mem_region_a.end + 10 * PAGE_SIZE);
        let range = vec![io_mem_region_a.clone(), io_mem_region_b.clone()];

        proof! {
            super::lemma_ranges_disjoint(range@);
        }
        let allocator =
            unsafe { IoMemAllocator::new((IoMemAllocatorBuilder::new(range)).allocators) };
        proof_decl! {
            let ghost first_range = io_mem_region_a.start..((io_mem_region_a.start + 1) as usize);
            let ghost last_range = ((io_mem_region_a.end - 1) as usize)..io_mem_region_a.end;
        }

        proof_decl! {
            let tracked before_window_allocation: Option<super::FreePermit>;
        }
        assert!(
            (#[verus_spec(with => Tracked(before_window_allocation))]
            allocator.acquire((io_mem_region_a.start - 1)..io_mem_region_a.start))
            .is_none()
        );
        proof_decl! {
            assert(before_window_allocation is None);
            let tracked first_allocation: Option<super::FreePermit>;
        }
        vstd_extra::assert!(
            (#[verus_spec(with => Tracked(first_allocation))]
            allocator.acquire(io_mem_region_a.start..(io_mem_region_a.start + 1)))
            .is_some()
        );
        proof! {
            assert(first_allocation is Some);
            assert(first_allocation->0.range() == first_range);
            assert(allocator.has_allocation(first_allocation->0.id(), first_range));
        }

        proof_decl! {
            let tracked gap_allocation: Option<super::FreePermit>;
        }
        assert!(
            (#[verus_spec(with => Tracked(gap_allocation))]
            allocator.acquire((io_mem_region_a.end + 1)..(io_mem_region_b.start - 1)))
            .is_none()
        );
        proof_decl! {
            assert(gap_allocation is None);
            let tracked cross_window_allocation: Option<super::FreePermit>;
        }
        assert!(
            (#[verus_spec(with => Tracked(cross_window_allocation))]
            allocator.acquire((io_mem_region_a.end - 1)..(io_mem_region_b.start + 1)))
            .is_none()
        );
        proof! {
            assert(cross_window_allocation is None);
        }

        proof_decl! {
            let tracked last_allocation: Option<super::FreePermit>;
        }
        vstd_extra::assert!(
            (#[verus_spec(with => Tracked(last_allocation))]
            allocator.acquire((io_mem_region_a.end - 1)..io_mem_region_a.end))
            .is_some()
        );
        proof_decl! {
            assert(last_allocation is Some);
            assert(last_allocation->0.range() == last_range);
            assert(allocator.has_allocation(last_allocation->0.id(), last_range));
            let tracked after_window_allocation: Option<super::FreePermit>;
        }
        assert!(
            (#[verus_spec(with => Tracked(after_window_allocation))]
            allocator.acquire(io_mem_region_a.end..(io_mem_region_a.end + 1)))
            .is_none()
        );
        proof! {
            assert(after_window_allocation is None);
        }

        /* Check occupied-range rejection and reuse after returning its token.
         * Origin Rust: <none; new executable code>
         */
        proof_decl! {
            let tracked duplicate_allocation: Option<super::FreePermit>;
        }
        vstd_extra::assert!(
            (#[verus_spec(with => Tracked(duplicate_allocation))]
            allocator.acquire(io_mem_region_a.start..(io_mem_region_a.start + 1)))
            .is_none()
        );
        proof_decl! {
            assert(duplicate_allocation is None);
            let tracked first_token = first_allocation.tracked_unwrap();
        }
        unsafe {
            #[verus_spec(with Tracked(first_token))]
            allocator.recycle(io_mem_region_a.start..(io_mem_region_a.start + 1));
        }
        proof_decl! {
            let tracked recycled_allocation: Option<super::FreePermit>;
        }
        vstd_extra::assert!(
            (#[verus_spec(with => Tracked(recycled_allocation))]
            allocator.acquire(io_mem_region_a.start..(io_mem_region_a.start + 1)))
            .is_some()
        );
        proof! {
            assert(recycled_allocation matches Some(token) && {
                &&& token.range() == first_range
                &&& allocator.has_allocation(token.id(), first_range)
            });
        }
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
        assert(predicate(seq[i]));
    }
}

/// Exposes endpoint separation directly on allocator views for lookup proofs.
proof fn lemma_windows_disjoint(allocators: Seq<RangeAllocator>)
    requires
        windows_disjoint(allocators),
    ensures
        forall|i: int, j: int|
            #![trigger allocators[i], allocators[j]]
            0 <= i < j < allocators.len() ==> allocators[i]@.end <= allocators[j]@.start
                || allocators[j]@.end <= allocators[i]@.start,
{
    let ranges = allocators.map_values(|allocator: RangeAllocator| allocator@);
    lemma_ranges_disjoint(ranges);
    assert forall|i: int, j: int|
        #![trigger allocators[i], allocators[j]]
        0 <= i < j < allocators.len() implies allocators[i]@.end <= allocators[j]@.start
        || allocators[j]@.end <= allocators[i]@.start by {
        assert(ranges[i].end <= ranges[j].start || ranges[j].end <= ranges[i].start);
    }
}

} // verus!
