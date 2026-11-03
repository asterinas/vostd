// SPDX-License-Identifier: MPL-2.0
//! Shared model of the system CPU count.
use vstd::prelude::*;

verus! {

/// The trusted value of the system CPU count. The exec reads `NUM_CPUS`, a `u32`
/// initialized to 1 and set once at boot (never decreased, no hot-plug), so it is a
/// stable constant; Verus cannot mention an `exec static` in a spec, so this uninterp
/// is the explicit specification boundary (mirrors io_port's num_cpus-style pattern).
pub uninterp spec fn cpu_count() -> int;

/// The count is a positive value that fits a `u32` (the exec reads `static NUM_CPUS: u32`),
/// hence also a `usize`; the `u32` bound is what lets a `CpuSet` bitset fit in its backing
/// `SmallVec` without overflowing `isize::MAX`.
pub broadcast axiom fn axiom_cpu_count_bounds()
    ensures
        #![trigger cpu_count()]
        1 <= cpu_count() <= u32::MAX,
;

} // verus!
