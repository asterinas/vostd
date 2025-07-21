use builtin::*;
use builtin_macros::*;
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
        res.wf(),
        res.wf_with_node_info(node@.level_spec(), node@.inst@.id(), node@.nid@, offset@),
{
    unimplemented!()
}

} // verus!
