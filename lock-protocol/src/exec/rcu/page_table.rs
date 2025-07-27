use vstd::prelude::*;
use vstd::tokens::*;
use vstd::atomic_ghost::*;

use crate::spec::{common::*, utils::*, rcu::*};
use super::{common::*, types::*};
use super::node::PageTableNode;

verus! {

pub struct PageTable {
    pub root: PageTableNode,
    pub inst: Tracked<SpecInstance>,
}

impl PageTable {
    pub open spec fn wf(&self) -> bool {
        &&& self.root.wf()
        &&& self.inst@.cpu_num() == GLOBAL_CPU_NUM
    }
}

} // verus!
