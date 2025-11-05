pub mod cursor;
pub mod node;
pub mod pte;

use std::marker::PhantomData;

use vstd::prelude::*;

use common::mm::page_table::{PageTableConfig, PagingConstsTrait};
use common::spec::node_helper::{self};
use common::configs::GLOBAL_CPU_NUM;

use crate::mm::page_table::node::PageTableNode;
use crate::spec::rw::SpecInstance;

verus! {

/// A handle to a page table.
/// A page table can track the lifetime of the mapped physical pages.
// TODO: Debug for PageTable
// #[derive(Debug)]
pub struct PageTable<C: PageTableConfig> {
    pub root: PageTableNode<C>,
    pub inst: Tracked<SpecInstance<C>>,
    pub _phantom: PhantomData<C>,
}

impl<C: PageTableConfig> PageTable<C> {
    pub open spec fn wf(&self) -> bool {
        &&& self.root.wf()
        &&& self.root.nid@ == node_helper::root_id::<C>()
        &&& self.root.level_spec() == C::NR_LEVELS()
        &&& self.root.inst@.id() == self.inst@.id()
        &&& self.inst@.cpu_num() == GLOBAL_CPU_NUM
    }
}

} // verus!
