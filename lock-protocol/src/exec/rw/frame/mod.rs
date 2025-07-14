// mod common;
// mod allocator;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::rwlock::*;
use vstd::vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::atomic_ghost::AtomicU64;

use vstd_extra::manually_drop::*;
use crate::spec::{common::*, utils::*, rw::*};
use super::{common::*, types::*, mem_content::*};
use super::node::PageTableNode;

verus! {

#[verifier::external_body]  // TODO
pub fn allocate_pt(level: PagingLevel, inst: Tracked<SpecInstance>, nid: Ghost<NodeId>) -> (res:
    PageTableNode)
    requires
// Root of the page table can not be allocated.

        1 <= level < 4,
    ensures
        res.wf(),
        res.inst@.cpu_num() == GLOBAL_CPU_NUM,
        res.inst@.id() == inst@.id(),
        res.nid@ == nid@,
{
    unimplemented!()
}

} // verus!
