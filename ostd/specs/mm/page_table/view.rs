use vstd::prelude::*;

use vstd_extra::ownership::*;

use core::marker::PhantomData;

use crate::mm::page_prop::PageProperty;
use crate::mm::{Paddr, Vaddr};

use super::*;

verus! {

pub ghost struct PageTableView<C: PageTableConfig> {
    pub leaves: Seq<FrameView<C>>
}

pub tracked struct Mapping {
    pub va: Vaddr,
    pub pa: Paddr,
    pub page_size: usize,
    pub property: PageProperty,
}

impl Mapping {
    pub open spec fn inv(self) -> bool {
        &&& set![4096, 2097152, 1073741824].contains(self.page_size)
        &&& self.pa % self.page_size == 0
    }
}

} // verus!
