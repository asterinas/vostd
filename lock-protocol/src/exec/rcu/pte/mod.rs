pub mod page_prop;
pub mod page_table_entry;
pub mod page_table_entry_trait;
pub mod page_table_flags;

use vstd::prelude::*;

use crate::spec::{common::*, utils::*};
use super::{common::*, types::*};
use super::node::PageTableNode;
use page_prop::PageProperty;
use page_table_entry::PageTableEntry;
pub use page_table_entry_trait::*;

verus! {

// Pte rules:
//  1. !pte.is_present() && pte.paddr() == 0 implies void entry.
//  2. !pte.is_present() && pte.paddr() != 0 implies marked entry.
//  3. pte.is_present() && !pte.is_last(level) implies page table node entry.
//  4. pte.is_present() && pte.is_last(level) implies frame entry.
pub struct Pte {
    // We only concerned about:
    //  (1) is_present
    //  (2) paddr
    //  (3) is_last
    pub inner: PageTableEntry,
    // The nid and inst fields should be consistent
    // with the corresponding page table node.
    pub nid: Ghost<Option<NodeId>>,
    pub inst: Tracked<Option<SpecInstance>>,
}

impl Pte {
    pub open spec fn is_none(&self) -> bool {
        !self.inner.is_present() && self.inner.paddr() == 0
    }

    pub open spec fn is_pt(&self, level: PagingLevel) -> bool {
        self.inner.is_present() && !self.inner.is_last(level)
    }

    pub open spec fn is_marked(&self) -> bool {
        !self.inner.is_present() && self.inner.paddr() != 0
    }

    pub open spec fn is_frame(&self, level: PagingLevel) -> bool {
        self.inner.is_present() && self.inner.is_last(level)
    }

    pub open spec fn wf(&self, level: PagingLevel) -> bool {
        &&& if self.is_pt(level) {
            self.nid@ is Some && self.inst@ is Some
        } else {
            self.nid@ is None && self.inst@ is None
        }
        &&& self.nid@ is Some ==> NodeHelper::valid_nid(self.nid@->Some_0)
        &&& self.inst@ is Some ==> self.inst@->Some_0.cpu_num() == GLOBAL_CPU_NUM
    }

    pub open spec fn wf_with_node(&self, node: PageTableNode, offset: nat) -> bool {
        &&& self.wf(node.level_spec())
        &&& self.nid@ is Some ==> self.nid@->Some_0 == NodeHelper::get_child(node.nid@, offset)
        &&& self.inst@ is Some ==> self.inst@->Some_0.id() == node.inst@.id()
    }

    pub open spec fn wf_with_node_info(
        &self,
        level: PagingLevel,
        inst_id: InstanceId,
        nid: NodeId,
        offset: nat,
    ) -> bool {
        &&& self.wf(level)
        &&& self.nid@ is Some ==> self.nid@->Some_0 == NodeHelper::get_child(nid, offset)
        &&& self.inst@ is Some ==> self.inst@->Some_0.id() == inst_id
    }

    pub proof fn lemma_wf_node_imply_wf_node_info(&self, node: PageTableNode, offset: nat)
        requires
            self.wf_with_node(node, offset),
        ensures
            self.wf_with_node_info(node.level_spec(), node.inst@.id(), node.nid@, offset),
    {
    }

    pub open spec fn nid(&self) -> NodeId
        recommends
            self.nid@ is Some,
    {
        self.nid@->Some_0
    }

    pub open spec fn inst_id(&self) -> InstanceId
        recommends
            self.inst@ is Some,
    {
        self.inst@->Some_0.id()
    }

    pub proof fn tracked_inst(tracked &self) -> (tracked res: SpecInstance)
        requires
            self.inst@ is Some,
        ensures
            res =~= self.inst@->Some_0,
    {
        self.inst.borrow().tracked_borrow().clone()
    }

    pub open spec fn wf_new_absent(&self) -> bool {
        &&& self.inner =~= PageTableEntry::new_absent_spec()
        &&& self.nid@ is None
        &&& self.inst@ is None
    }

    #[verifier::external_body]
    pub fn new_absent() -> (res: Self)
        ensures
            res.wf_new_absent(),
            res.is_none(),
    {
        Self { inner: PageTableEntry::new_absent(), nid: Ghost(None), inst: Tracked(None) }
    }

    pub open spec fn wf_new_page(
        &self,
        paddr: Paddr,
        level: PagingLevel,
        prop: PageProperty,
    ) -> bool {
        &&& self.inner =~= PageTableEntry::new_page_spec(paddr, level, prop)
        &&& self.nid@ is None
        &&& self.inst@ is None
    }

    #[verifier::external_body]
    pub fn new_page(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> (res: Self)
        requires
            valid_paddr(paddr),
            level == 1,
        ensures
            res.wf_new_page(paddr, level, prop),
            res.is_frame(level) || res.is_marked(),
    {
        Self {
            inner: PageTableEntry::new_page(paddr, level, prop),
            nid: Ghost(None),
            inst: Tracked(None),
        }
    }

    pub open spec fn wf_new_pt(&self, paddr: Paddr, inst: SpecInstance, nid: NodeId) -> bool {
        &&& self.inner =~= PageTableEntry::new_pt_spec(paddr)
        &&& self.nid@ is Some
        &&& self.nid@->Some_0 == nid
        &&& self.inst@ is Some
        &&& self.inst@->Some_0 =~= inst
    }

    #[verifier::external_body]
    pub fn new_pt(paddr: Paddr, inst: Tracked<SpecInstance>, nid: Ghost<NodeId>) -> (res: Self)
        requires
            valid_paddr(paddr),
            inst@.cpu_num() == GLOBAL_CPU_NUM,
            NodeHelper::valid_nid(nid@),
        ensures
            res.wf_new_pt(paddr, inst@, nid@),
            res.is_pt((PageTableNode::from_raw_spec(paddr).level_spec() + 1) as PagingLevel),
            res.inner.paddr() == paddr,
    {
        Self {
            inner: PageTableEntry::new_pt(paddr),
            nid: Ghost(Some(nid@)),
            inst: Tracked(Some(inst.get())),
        }
    }
}

impl Clone for Pte {
    fn clone(&self) -> (res: Self)
        ensures
            res =~= *self,
    {
        Self {
            inner: self.inner.clone(),
            nid: Ghost(self.nid@),
            inst: Tracked(*self.inst.borrow()),
        }
    }
}

impl Copy for Pte {

}

} // verus!
