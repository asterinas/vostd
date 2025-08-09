use std::marker::PhantomData;

use vstd::prelude::*;
use vstd::tokens::*;
use vstd::atomic_ghost::*;

use crate::spec::{common::*, utils::*, rcu::*};
use super::{common::*, types::*};
use super::node::PageTableNode;
use crate::mm::page_table::PageTableConfig;

verus! {

pub struct PageTable<C: PageTableConfig> {
    pub root: PageTableNode<C>,
    pub inst: Tracked<SpecInstance>,
    pub _phantom: PhantomData<C>,
}

impl<C: PageTableConfig> PageTable<C> {
    pub open spec fn wf(&self) -> bool {
        &&& self.root.wf()
        &&& self.inst@.cpu_num() == GLOBAL_CPU_NUM
    }
}

} // verus!
