use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use super::common::*;
use super::node::PageTableNode;

verus! {

#[verifier::external_body]
pub fn alloc(
    level: PagingLevel,
) -> (res: PageTableNode)
    requires
    ensures
{
    unimplemented!()
}

}