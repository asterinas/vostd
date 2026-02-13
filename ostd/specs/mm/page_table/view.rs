use vstd::prelude::*;

use vstd_extra::ownership::*;

use core::marker::PhantomData;
use core::ops::Range;

use crate::mm::page_prop::PageProperty;
use crate::mm::{Paddr, Vaddr};
use crate::specs::arch::mm::{MAX_PADDR, MAX_USERSPACE_VADDR};

use super::*;

verus! {

/// A `Mapping` maps a virtual address range to a physical address range.
/// Its size, `page_size`, is fixed and must be one of 4096, 2097152, 1073741824.
/// The `va_range` and `pa_range` must of size `page_size` and aligned on a page boundary.
/// The `property` is a bitfield of flags that describe the properties of the mapping.
pub tracked struct Mapping {
    pub va_range: Range<Vaddr>,
    pub pa_range: Range<Paddr>,
    pub page_size: usize,
    pub property: PageProperty,
}

/// A view of the page table is simply the set of mappings that it contains.
/// Its [invariant](PageTableView::inv) is a crucial property for memory correctness.
pub ghost struct PageTableView {
    pub mappings: Set<Mapping>
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
        &&& self.pa_range.end % self.page_size == 0
        &&& self.pa_range.start + self.page_size == self.pa_range.end
        &&& self.pa_range.start <= self.pa_range.end < MAX_PADDR
        &&& self.va_range.start % self.page_size == 0
        &&& self.va_range.end % self.page_size == 0
        &&& self.va_range.start + self.page_size == self.va_range.end
        &&& 0 < self.va_range.start <= self.va_range.end < MAX_USERSPACE_VADDR
    }
}

/// In addition to requiring that individual mappings be well-formed, a valid `PageTableView` must
/// not have any overlapping mappings, in the physical or virtual address space.
/// The virtual ranges not overlapping is a consequence of the structure of the page table.
/// The physical ranges not overlapping must be maintained by the page table implementation.
impl PageTableView {
    pub open spec fn inv(self) -> bool {
        &&& forall|m: Mapping| #![auto] self.mappings has m ==> m.inv()
        &&& forall|m: Mapping, n:Mapping| #![auto]
            self.mappings has m ==>
            self.mappings has n ==>
            m != n ==> {
                &&& m.va_range.end <= n.va_range.start || n.va_range.end <= m.va_range.start
                &&& m.pa_range.end <= n.pa_range.start || n.pa_range.end <= m.pa_range.start
            }
    }
}

} // verus!
