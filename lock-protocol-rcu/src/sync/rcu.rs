use vstd::prelude::*;

use common::mm::{page_table::PageTableConfig, Vaddr};

use crate::mm::page_table::{node::PageTableNode, pte::Pte};

verus! {

#[verifier::external_body]
pub fn rcu_load_pte<C: PageTableConfig>(
    // ptr: *const Pte,
    va: Vaddr,
    idx: usize,
    node: Ghost<PageTableNode<C>>,
    offset: Ghost<nat>,
) -> (res: Pte<C>)
    ensures
        res.wf_with_node(node@, offset@),
{
    unimplemented!()
}

} // verus!
