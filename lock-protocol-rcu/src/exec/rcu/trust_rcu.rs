use vstd::prelude::*;

use crate::spec::{common::*, utils::*, rcu::*};
use super::{common::*, types::*};
use super::pte::Pte;
use super::node::PageTableNode;
use crate::mm::page_table::PageTableConfig;

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
