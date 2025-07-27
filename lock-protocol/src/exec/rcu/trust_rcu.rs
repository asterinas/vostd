use vstd::prelude::*;

use crate::spec::{common::*, utils::*, rcu::*};
use super::{common::*, types::*};
use super::pte::Pte;
use super::node::PageTableNode;

verus! {

#[verifier::external_body]
pub fn rcu_load_pte(
    // ptr: *const Pte,
    va: Vaddr,
    idx: usize,
    node: Ghost<PageTableNode>,
    offset: Ghost<nat>,
) -> (res: Pte)
    ensures
        res.wf_with_node(node@, offset@),
{
    unimplemented!()
}

} // verus!
