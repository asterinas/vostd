use vstd::prelude::*;

use vstd_extra::ownership::*;

use core::marker::PhantomData;
use core::ops::Range;

use crate::mm::page_prop::PageProperty;
use crate::mm::{Paddr, Vaddr};
use crate::specs::arch::mm::{MAX_PADDR, MAX_USERSPACE_VADDR};

use super::*;

verus! {

pub ghost struct PageTableView<C: PageTableConfig> {
    pub leaves: Seq<FrameView<C>>
}

pub tracked struct Mapping {
    pub va_range: Range<Vaddr>,
    pub pa_range: Range<Paddr>,
    pub page_size: usize,
    pub property: PageProperty,
}

impl Mapping {
    pub open spec fn inv(self) -> bool {
        &&& set![4096, 2097152, 1073741824].contains(self.page_size)
        &&& self.pa_range.start % self.page_size == 0
        &&& self.pa_range.end % self.page_size == 0
        &&& self.pa_range.start + self.page_size == self.pa_range.end
        &&& self.pa_range.start <= self.pa_range.end < MAX_PADDR()
        &&& self.va_range.start % self.page_size == 0
        &&& self.va_range.end % self.page_size == 0
        &&& self.va_range.start + self.page_size == self.va_range.end
        &&& 0 < self.va_range.start <= self.va_range.end < MAX_USERSPACE_VADDR()
    }
}

} // verus!
