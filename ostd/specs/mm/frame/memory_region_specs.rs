use vstd::prelude::*;
use vstd_extra::prelude::*;

use crate::specs::arch::{MAX_PADDR, PAGE_SIZE};

verus! {

pub ghost struct MemRegionModel {
    pub ghost base: int,
    pub ghost end: int,
    pub ghost typ: int,
}

impl Inv for MemRegionModel {
    open spec fn inv(self) -> bool {
        0 <= self.base <= self.end <= MAX_PADDR && 0 <= self.typ < 9
    }
}

impl MemRegionModel {
    pub open spec fn is_sub_region(self, old_region: Self) -> bool {
        self.typ == old_region.typ && old_region.base <= self.base <= self.end <= old_region.end
    }

    pub open spec fn is_separate(self, region: Self) -> bool {
        self.end <= region.base || region.end <= self.base
    }

    /// Whether the region is empty.
    pub open spec fn is_empty(self) -> bool {
        self.base == self.end
    }

    /// Whether both boundaries of the region are multiples of `align`.
    pub open spec fn aligned(self, align: int) -> bool {
        self.base % align == 0 && self.end % align == 0
    }

    pub open spec fn bad() -> Self {
        MemRegionModel { base: 0, end: 0, typ: 0 }
    }

    /// The inward alignment of the region: `base` grows up to and `end`
    /// shrinks down to the enclosing `PAGE_SIZE` boundaries (used for
    /// `Usable` regions so that partially usable pages are excluded).
    pub open spec fn align_inward(self) -> Self {
        MemRegionModel {
            base: nat_align_up(self.base as nat, PAGE_SIZE as nat) as int,
            end: nat_align_down(self.end as nat, PAGE_SIZE as nat) as int,
            typ: self.typ,
        }
    }

    /// The outward alignment of the region: `base` shrinks down to and `end`
    /// grows up to the enclosing `PAGE_SIZE` boundaries (used for non-`Usable`
    /// regions so that partially non-usable pages are wholly excluded).
    pub open spec fn align_outward(self) -> Self {
        MemRegionModel {
            base: nat_align_down(self.base as nat, PAGE_SIZE as nat) as int,
            end: nat_align_up(self.end as nat, PAGE_SIZE as nat) as int,
            typ: self.typ,
        }
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
