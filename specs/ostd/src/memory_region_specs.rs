use vstd::prelude::*;
use vstd_extra::prelude::*;
use aster_common::prelude::MAX_PADDR;

verus! {

pub ghost struct MemRegionModel {
    pub ghost base: int,
    pub ghost end: int,
    pub ghost typ: int,
}

impl Inv for MemRegionModel {
    open spec fn inv(self) -> bool {
        0 <= self.base <= self.end <= MAX_PADDR() && 0 <= self.typ < 9
    }
}

impl MemRegionModel {
    pub open spec fn is_sub_region(self, old_region: Self) -> bool {
        self.typ == old_region.typ && old_region.base <= self.base <= self.end <= old_region.end
    }

    pub open spec fn is_separate(self, region: Self) -> bool {
        self.end <= region.base || region.end <= self.base
    }
}

pub ghost struct MemoryRegionArrayModel<const LEN: usize> {
    pub ghost regions: Seq<MemRegionModel>,
    pub ghost count: int,
}
}