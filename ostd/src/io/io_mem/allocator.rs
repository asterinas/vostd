// SPDX-License-Identifier: MPL-2.0
//! I/O Memory allocator.
//!
//! # Verified Properties
//!
//! The allocatable windows are the boot-time registered MMIO windows, handed
//! to [`IoMemAllocatorBuilder::new`] in their registered order; every
//! allocator built from a builder inherits them. Construction returns one
//! splittable free-address permission per window. A builder removal consumes
//! the requested portion of the corresponding permission, proving that the
//! underlying range allocation cannot panic. The registered-window registry
//! is trusted boot-time data.
use vstd::{
    arithmetic::power2::is_pow2,
    prelude::*,
    resource::{Loc, set::GhostSubset},
};
use vstd_extra::{
    once::OnceImpl, range::RangeExtraFns, resource::range::GhostSubRange,
    resource_invariant::TrivialResourceInvariant,
};

use crate::specs::arch::PAGE_SIZE;
use crate::util::range_alloc::RangeAllocatorPermits;

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
            Tracked(permit): Tracked<GhostSubRange<usize>>,
        requires
            range.start < range.end <= usize::MAX - (PAGE_SIZE - 1),
            io_mem_range_registered(range),
            permit.range() == range,
            self.has_free_permission(permit.id(), range),
        ensures
            result matches Some(io_mem) ==> {
                &&& io_mem.paddr() == range.start
                &&& io_mem.length() == range.end - range.start
            },
            result is Some,
    )]
    pub fn acquire(&self, range: Range<usize>) -> Option<IoMem> {
        /* Original Rust:
        find_allocator(&self.allocators, &range)?
            .alloc_specific(&range)
            .ok()?;
        */
        let allocator = find_allocator(&self.allocators, &range)?;
        proof! {
            use_type_invariant(self);
        }
        proof_decl! {
            let tracked allocated: Option<GhostSubRange<usize>>;
        }
        let result = #[verus_spec(with Tracked(permit) => Tracked(allocated))]
        allocator.alloc_specific(&range);
        result.ok()?;

        /* debug!("Acquiring MMIO range:{:x?}..{:x?}", range.start, range.end); */

        proof! {
            // PAGE_SIZE = 4096 = 2^12: 13 unfoldings of the opaque `is_pow2`.
            reveal_with_fuel(is_pow2, 13);
        }

        // SAFETY: The created `IoMem` is guaranteed not to access physical memory or system device I/O.
        /* Original Rust: PageFlags::RW */
        unsafe { Some(IoMem::new(range, PageFlags::RW(), CachePolicy::Uncacheable)) }
    }

    /// Recycles an MMIO range.
    ///
    /// # Safety
    ///
    /// The caller must have ownership of the MMIO region through the `IoMemAllocator::get` interface.
    #[expect(dead_code)]
    #[verifier::external_body]
    #[verus_spec(
        with
            Tracked(allocated): Tracked<GhostSubRange<usize>>,
        requires
            range.start < range.end,
            self.covers_range(range),
            allocated.range() == range,
            self.has_allocation(allocated.id()),
    )]
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
        with
            -> state_out: Tracked<RangeAllocatorPermits>,
        requires
            usize_ranges_ordered(ranges@),
            usize_ranges_match_registered(ranges@),
        ensures
            ret.type_inv(),
            ret.state_matches(state_out@),
    )]
    pub(crate) unsafe fn new(ranges: Vec<Range<usize>>) -> Self {
        /* info!(
            "Creating new I/O memory allocator builder, ranges: {:#x?}",
            ranges
        ); */
        let mut allocators: Vec<RangeAllocator> = Vec::with_capacity(ranges.len());
        proof_decl! {
            let tracked mut state = Seq::tracked_empty();
        }
        #[verus_spec(it =>
            invariant
                allocators@.len() == it.index(),
                forall|j: int| #![trigger it.seq()[j]] 0 <= j < it.index() ==> {
                    &&& allocators@[j]@.start == it.seq()[j].start
                    &&& allocators@[j]@.end == it.seq()[j].end
                },
                usize_ranges_ordered(it.seq()),
                usize_ranges_match_registered(it.seq()),
                forall|j: int| #![trigger registered_io_mem_windows()[j]] 0 <= j < it.index() ==>
                    allocators@[j]@ == registered_io_mem_windows()[j],
                windows_ordered(allocators@),
                allocator_states_match(allocators@, state),
                state.len() == it.index(),
        )]
        for range in ranges {
            proof_decl! {
                let tracked permit: GhostSubset<usize>;
            }
            allocators.push(
                #[verus_spec(with => Tracked(permit))]
                RangeAllocator::new(range),
            );
            proof! {
                state.tracked_push(permit);
                assert forall|i: int| #![trigger allocators@[i]]
                    0 <= i < allocators@.len() - 1
                    implies allocators@[i]@.end <= range.start by {
                    assert(it.seq()[i].end <= it.seq()[i + 1].start);
                }
            }
        }
        proof_with!(|= Tracked(state));
        Self { allocators }
    }

    /// Removes access to a specific memory I/O range.
    ///
    /// All drivers in OSTD must use this method to prevent peripheral drivers from accessing illegal memory I/O range.
    ///
    /// # Verified Properties
    ///
    /// ## Safety
    /// - No unsafe code; panics are proved impossible whenever the supplied
    ///   permission covers the requested range ([`Self::can_remove`]).
    ///
    /// ## Preconditions
    /// - The range is non-empty and registered as a boot-time MMIO window.
    /// - The permission sequence matches this builder's allocator windows.
    ///
    /// ## Postconditions
    /// - Only the requested range is removed from its window's permission;
    ///   every other permission remains available.
    #[verus_spec(
        with Tracked(state): Tracked<&mut RangeAllocatorPermits>,
        requires
            range.start < range.end,
            self.can_remove(*old(state), range),
            io_mem_range_registered(range),
            self.state_matches(*old(state)),
        ensures
            self.state_matches(*final(state)),
    )]
    pub(crate) fn remove(&self, range: Range<usize>) {
        let Some(allocator) = find_allocator(&self.allocators, &range) else {
            vstd_extra::panic!(
                "Allocator for the system device's MMIO was not found. Range: {:x?}",
                range
            );
        };

        proof_decl! {
            let ghost state_before = *state;
            let ghost k = choose|k: int|
                #![trigger self.allocators@[k]]
                0 <= k < self.allocators@.len() && k < state_before.len() && {
                    let candidate = self.allocators@[k];
                    &&& candidate@.start <= range.start < range.end <= candidate@.end
                    &&& state_before[k].id() == candidate.free_id()
                    &&& range.view_set() <= state_before[k]@
                };
            let tracked mut window_permit = state.tracked_remove(k);
            let tracked range_permit = window_permit.split(range.view_set());
            state.tracked_insert(k, window_permit);
            let tracked permit = GhostSubRange::tracked_new(range_permit, range);
        }
        proof! {
            use_type_invariant(self);
        }
        proof_decl! {
            let tracked allocated: Option<GhostSubRange<usize>>;
        }

        if let Err(err) = #[verus_spec(with Tracked(permit) => Tracked(allocated))]
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

/// The I/O Memory allocator of the system.
// Original Rust: pub static IO_MEM_ALLOCATOR: Once<IoMemAllocator> = Once::new();
verus! {

broadcast use vstd::std_specs::vec::group_vec_axioms;

/// The registered MMIO windows are pairwise ordered: every window ends at or before the start
/// of the next one, so no window can partially cover a range that is contained in another one.
pub open spec fn windows_ordered(allocators: Seq<RangeAllocator>) -> bool {
    forall|i: int, j: int|
        #![trigger allocators[i], allocators[j]]
        0 <= i < j < allocators.len() ==> allocators[i]@.end <= allocators[j]@.start
}

/// The ranges handed to [`IoMemAllocatorBuilder::new`] are pairwise ordered.
pub open spec fn usize_ranges_ordered(ranges: Seq<Range<usize>>) -> bool {
    forall|i: int, j: int|
        #![trigger ranges[i], ranges[j]]
        0 <= i < j < ranges.len() ==> ranges[i].end <= ranges[j].start
}

/// The abstract MMIO windows registered by platform boot code.
pub uninterp spec fn registered_io_mem_windows() -> Seq<Range<usize>>;

/// The concrete range allocators represent the abstract boot-time windows exactly.
pub open spec fn windows_match_registered(allocators: Seq<RangeAllocator>) -> bool {
    &&& allocators.len() == registered_io_mem_windows().len()
    &&& forall|i: int|
        #![trigger registered_io_mem_windows()[i]]
        0 <= i < allocators.len() ==> allocators[i]@ == registered_io_mem_windows()[i]
}

/// The ranges passed across the unsafe builder boundary represent the abstract windows.
pub open spec fn usize_ranges_match_registered(ranges: Seq<Range<usize>>) -> bool {
    &&& ranges.len() == registered_io_mem_windows().len()
    &&& forall|i: int|
        #![trigger ranges[i]]
        0 <= i < ranges.len() ==> {
            &&& ranges[i].start <= ranges[i].end
            &&& ranges[i].start == registered_io_mem_windows()[i].start
            &&& ranges[i].end == registered_io_mem_windows()[i].end
        }
}

/// Every window has a matching free-address permission.
closed spec fn allocator_states_match(
    allocators: Seq<RangeAllocator>,
    state: RangeAllocatorPermits,
) -> bool {
    &&& state.len() == allocators.len()
    &&& forall|i: int|
        #![trigger allocators[i]]
        0 <= i < allocators.len() ==> {
            &&& state[i].id() == allocators[i].free_id()
            &&& state[i]@ <= allocators[i]@.view_set()
        }
}

impl IoMemAllocatorBuilder {
    /// Whether some matching window permission covers `range`, proving that
    /// `remove` succeeds without panicking.
    pub closed spec fn can_remove(self, state: RangeAllocatorPermits, range: Range<usize>) -> bool {
        exists|i: int|
            #![trigger self.allocators@[i]]
            0 <= i < self.allocators@.len() && i < state.len() && {
                let allocator = self.allocators@[i];
                &&& allocator@.start <= range.start < range.end <= allocator@.end
                &&& state[i].id() == allocator.free_id()
                &&& range.view_set() <= state[i]@
            }
    }

    /// Whether every window has a permission with the matching identity.
    pub closed spec fn state_matches(self, state: RangeAllocatorPermits) -> bool {
        allocator_states_match(self.allocators@, state)
    }

    /// The builder always holds the ordered windows handed to [`IoMemAllocatorBuilder::new`].
    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        windows_ordered(self.allocators@) && windows_match_registered(self.allocators@)
    }
}

impl IoMemAllocator {
    /// Whether `id` is the free-permission identity of a window containing `range`.
    pub closed spec fn has_free_permission(self, id: Loc, range: Range<usize>) -> bool {
        exists|i: int|
            #![trigger self.allocators@[i]]
            0 <= i < self.allocators@.len() && self.allocators@[i].free_id() == id
                && self.allocators@[i]@.start <= range.start < range.end <= self.allocators@[i]@.end
    }

    /// Whether `id` is the allocation-token identity of one of the windows.
    pub closed spec fn has_allocation(self, id: Loc) -> bool {
        exists|i: int|
            #![trigger self.allocators@[i]]
            0 <= i < self.allocators@.len() && self.allocators@[i].id() == id
    }

    /// Whether some window wholly covers `range`.
    pub closed spec fn covers_range(self, range: Range<usize>) -> bool {
        exists|k: int|
            #![trigger self.allocators@[k]]
            0 <= k < self.allocators@.len() && {
                let window = self.allocators@[k]@;
                &&& window.start <= range.start
                &&& range.end <= window.end
            }
    }

    /// The allocator inherits the ordered windows of the builder it was built from.
    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        windows_ordered(self.allocators@) && windows_match_registered(self.allocators@)
    }
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
        exists|k: int| #![trigger windows@[k]] 0 <= k < windows@.len() && windows@[k]@ == found@,
    ensures
        found@.start <= range.start && range.end <= found@.end,
{
    // The trusted [`io_mem_range_registered`] existential, made concrete as the index of
    // the registered window containing `range`.
    let container_idx = choose|m: int|
        #![trigger registered_io_mem_windows()[m]]
        0 <= m < registered_io_mem_windows().len() && registered_io_mem_windows()[m].start
            <= range.start && range.end <= registered_io_mem_windows()[m].end;
    let found_idx = choose|k: int|
        #![trigger windows@[k]]
        0 <= k < windows@.len() && windows@[k]@ == found@;
    if found_idx < container_idx {
        assert(false);
    } else if found_idx == container_idx {
    } else {
        assert(false);
    }
}

/// A range is registered when one abstract boot-time MMIO window contains it.
pub open spec fn io_mem_range_registered(range: Range<usize>) -> bool {
    exists|m: int|
        #![trigger registered_io_mem_windows()[m]]
        0 <= m < registered_io_mem_windows().len() && registered_io_mem_windows()[m].start
            <= range.start && range.end <= registered_io_mem_windows()[m].end
}

/// Whether the global I/O memory allocator has been initialized.
pub uninterp spec fn io_mem_allocator_initialized() -> bool;

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
            &&& exists|k: int| #![trigger allocators@[k]]
                0 <= k < allocators@.len()
                    && allocators@[k]@ == res@
                    && allocators@[k].free_id() == res.free_id()
        },
        ret is None ==> forall|i: int| #![trigger allocators@[i]] 0 <= i < allocators@.len()
            ==> allocators@[i]@.start >= range.end || allocators@[i]@.end <= range.start,
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
        /* Verus does not yet support `continue` in `for` loops.
        Original Rust:
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

// Auxiliary permission lemma backing the allocator proofs above.
verus! {

/// The found ordered window has the permission identity of the unique containing window.
proof fn lemma_found_permission_matches(
    allocators: &Vec<RangeAllocator>,
    found: &RangeAllocator,
    permit_id: Loc,
    range: Range<usize>,
)
    requires
        windows_ordered(allocators@),
        found@.start <= range.start < range.end <= found@.end,
        exists|found_idx: int|
            #![trigger allocators@[found_idx]]
            0 <= found_idx < allocators@.len() && allocators@[found_idx]@ == found@
                && allocators@[found_idx].free_id() == found.free_id(),
        exists|permit_idx: int|
            #![trigger allocators@[permit_idx]]
            0 <= permit_idx < allocators@.len() && allocators@[permit_idx].free_id() == permit_id
                && allocators@[permit_idx]@.start <= range.start < range.end
                <= allocators@[permit_idx]@.end,
    ensures
        found.free_id() == permit_id,
{
    let found_idx = choose|i: int|
        0 <= i < allocators@.len() && #[trigger] allocators@[i]@ == found@
            && allocators@[i].free_id() == found.free_id();
    let permit_idx = choose|i: int|
        0 <= i < allocators@.len() && allocators@[i].free_id() == permit_id
            && #[trigger] allocators@[i]@.start <= range.start < range.end <= allocators@[i]@.end;
    if found_idx < permit_idx {
        assert(false);
    } else if permit_idx < found_idx {
        assert(false);
    } else {
    }
}

} // verus!
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
