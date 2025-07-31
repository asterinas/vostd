use core::fmt::Debug;

use vstd::prelude::*;
use vstd::tokens::*;
use vstd::atomic_ghost::*;

use crate::spec::{common::*, utils::*, rw::*};
use super::{common::*, types::*, frame::*};
use super::node::PageTableNode;

verus! {

pub struct PageTable {
    pub root: PageTableNode,
    pub inst: Tracked<SpecInstance>,
}

impl PageTable {
    pub open spec fn wf(&self) -> bool {
        &&& self.root.wf()
        &&& self.root.inst@.id() == self.inst@.id()
        &&& self.root.nid@ == NodeHelper::root_id()
        &&& self.root.level_spec() == 4
        &&& self.inst@.cpu_num() == GLOBAL_CPU_NUM
    }
}

} // verus!
