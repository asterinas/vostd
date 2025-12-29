use crate::aster_common::CONST_MAX_PADDR;
use vstd::prelude::*;
use vstd_extra::prelude::*;

verus! {

pub ghost struct MemRegionModel {
    pub ghost base: int,
    pub ghost end: int,
    pub ghost typ: int,
}

impl Inv for MemRegionModel {
    open spec fn inv(self) -> bool {
        0 <= self.base <= self.end <= CONST_MAX_PADDR && 0 <= self.typ < 9
    }
}

impl MemRegionModel {
    pub open spec fn is_sub_region(self, old_region: Self) -> bool {
        self.typ == old_region.typ && old_region.base <= self.base <= self.end <= old_region.end
    }

    pub open spec fn is_separate(self, region: Self) -> bool {
        self.end <= region.base || region.end <= self.base
    }

    pub open spec fn bad() -> Self {
        MemRegionModel { base: 0, end: 0, typ: 0 }
    }
}

pub ghost struct MemoryRegionArrayModel<const LEN: usize> {
    pub ghost regions: Seq<MemRegionModel>,
}

impl<const LEN: usize> Inv for MemoryRegionArrayModel<LEN> {
    open spec fn inv(self) -> bool {
        &&& self.regions.len() <= LEN
    }
}

impl<const LEN: usize> MemoryRegionArrayModel<LEN> {
    pub open spec fn new() -> Self {
        MemoryRegionArrayModel { regions: Seq::empty() }
    }

    pub open spec fn push(self, region: MemRegionModel) -> Self {
        MemoryRegionArrayModel { regions: self.regions.push(region) }
    }

    pub open spec fn full(self) -> bool {
        self.regions.len() == LEN
    }
}

} // verus!
