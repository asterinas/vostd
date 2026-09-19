use vstd::prelude::*;
use vstd_extra::prelude::*;

use crate::boot::memory_region::MemoryRegion;

verus! {

pub ghost struct MemoryRegionArrayModel<const LEN: usize> {
    pub regions: Seq<MemoryRegion>,
}

impl<const LEN: usize> MemoryRegionArrayModel<LEN> {
    pub open spec fn new() -> Self {
        MemoryRegionArrayModel { regions: Seq::empty() }
    }

    pub open spec fn push(self, region: MemoryRegion) -> Self {
        MemoryRegionArrayModel { regions: self.regions.push(region) }
    }

    pub open spec fn full(self) -> bool {
        self.regions.len() == LEN
    }
}

} // verus!
