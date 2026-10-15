use vstd::{arithmetic::power2::pow2, prelude::*};
use vstd_extra::ownership::*;

use crate::specs::arch::MAX_PADDR;

use super::*;
use crate::mm::{Paddr, Vaddr, page_prop::PageProperty};
use core::{marker::PhantomData, ops::Range};

verus! {

/// A `Mapping` maps a virtual address range to a physical address range.
/// Its size, `page_size`, is fixed and must be one of 4096, 2097152, 1073741824.
/// The `va_range` and `pa_range` must be of size `page_size` and aligned on a
/// page boundary.
/// The `property` is a bitfield of flags that describe the properties of the mapping.
///
/// `va_range` is `Range<int>` rather than `Range<Vaddr>` because the
/// canonical upper-half kernel range can reach `usize::MAX + 1` for its
/// exclusive end (`2^64`), which cannot be represented in `usize`. The
/// `Mapping::inv` predicate bounds `va_range.end` by `pow2(64)` so all
/// concretely realized mappings stay within the addressable space; this
/// is a no-op constraint for user mappings and the essential cap for
/// kernel mappings.
pub ghost struct Mapping {
    pub va_range: Range<int>,
    pub pa_range: Range<Paddr>,
    pub page_size: usize,
    pub property: PageProperty,
}

/// A view of the page table is simply the set of mappings that it contains.
/// Its [invariant](PageTableView::inv) is a crucial property for memory correctness.
pub ghost struct PageTableView {
    pub mappings: Set<Mapping>,
}

impl Mapping {
    pub open spec fn disjoint_vaddrs(m1: Mapping, m2: Mapping) -> bool {
        m1.va_range.end <= m2.va_range.start || m2.va_range.end <= m1.va_range.start
    }

    pub open spec fn disjoint_paddrs(m1: Mapping, m2: Mapping) -> bool {
        m1.pa_range.end <= m2.pa_range.start || m2.pa_range.end <= m1.pa_range.start
    }

    pub open spec fn inv(self) -> bool {
        &&& set![4096, 2097152, 1073741824].contains(self.page_size)
        &&& self.pa_range.start % self.page_size == 0
        &&& self.pa_range.start + self.page_size == self.pa_range.end
        &&& self.pa_range.end <= MAX_PADDR
        &&& self.va_range.start % self.page_size as int == 0
        &&& self.va_range.start + self.page_size as int == self.va_range.end
        &&& 0
            <= self.va_range.start
        // VA range fits in the 64-bit addressable space. `va_range.end` may
        // equal `pow2(64)` for a kernel mapping at the top of the canonical
        // high half; `va_range.start` is strictly less than `pow2(64)`
        // because `start + page_size == end <= pow2(64)` and `page_size > 0`.
        &&& self.va_range.end <= pow2(
            64,
        )
        // Per-config VA range bounds are enforced by `CursorView<C>::inv`
        // via `vaddr_range_spec<C>`, not here — a single
        // config-agnostic `Mapping::inv` cannot express them.

    }
}

/// Every mapping in the set satisfies its intrinsic invariant.
pub open spec fn mappings_well_formed(mappings: Set<Mapping>) -> bool {
    forall|m: Mapping| #[trigger] mappings.contains(m) ==> m.inv()
}

/// Distinct mappings in the set have disjoint virtual address ranges.
pub open spec fn mappings_disjoint_vaddrs(mappings: Set<Mapping>) -> bool {
    forall|m: Mapping, n: Mapping|
        #![trigger mappings.contains(m), mappings.contains(n)]
        mappings.contains(m) && mappings.contains(n) && m != n ==> Mapping::disjoint_vaddrs(m, n)
}

/// Distinct mappings in the set have disjoint physical address ranges.
pub open spec fn mappings_disjoint_paddrs(mappings: Set<Mapping>) -> bool {
    forall|m: Mapping, n: Mapping|
        #![trigger mappings.contains(m), mappings.contains(n)]
        mappings.contains(m) && mappings.contains(n) && m != n ==> Mapping::disjoint_paddrs(m, n)
}

/// A valid view contains well-formed mappings with disjoint VA and PA ranges.
impl PageTableView {
    pub open spec fn inv(self) -> bool {
        &&& mappings_well_formed(self.mappings)
        &&& mappings_disjoint_vaddrs(self.mappings)
        &&& mappings_disjoint_paddrs(self.mappings)
    }
}

} // verus!
