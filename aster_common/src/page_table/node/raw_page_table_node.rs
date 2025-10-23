use vstd::prelude::*;

use core::marker::PhantomData;

use crate::prelude::Paddr;
use crate::prelude::{PageTableEntry, PagingConsts, PagingLevel};

verus! {

#[rustc_has_incoherent_inherent_impls]
#[derive(Debug)]
pub struct RawPageTableNode {
    pub raw: Paddr,
    pub level: PagingLevel,
    pub _phantom: PhantomData<(PageTableEntry, PagingConsts)>,
}

impl RawPageTableNode {
    pub open spec fn inv(self) -> bool {
        true
    }

    #[vstd::contrib::auto_spec]
    pub fn paddr(&self) -> (res: Paddr) {
        self.raw
    }

    #[vstd::contrib::auto_spec]
    pub fn level(&self) -> (res: PagingLevel) {
        self.level
    }
}

} // verus!
