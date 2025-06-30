use core::fmt::Debug;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::tokens::*;
use vstd::atomic_ghost::*;

use crate::spec::{common::*, utils::*, tree::*};
use super::{common::*, types::*, mem_content::*};
use super::node::PageTableNode;

verus! {

pub struct PageTable {
    pub root: PageTableNode,
    pub inst: Tracked<SpecInstance>,
}

impl PageTable {
    pub open spec fn wf(&self, mem: &MemContent) -> bool {
        &&& self.root.wf(mem)
        &&& self.inst@.cpu_num() == GLOBAL_CPU_NUM
    }
}

} // verus!
