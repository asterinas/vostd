use core::ops::Deref;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::spec::{common::*, utils::*};
use super::super::types::*;
use super::{PageTableNode, PageTableNodeRef, PageTableGuard};
use super::child::*;
use super::super::pte::Pte;

verus! {

pub struct Entry {
    /// The page table entry.
    ///
    /// We store the page table entry here to optimize the number of reads from
    /// the node. We cannot hold a `&mut E` reference to the entry because that
    /// other CPUs may modify the memory location for accessed/dirty bits. Such
    /// accesses will violate the aliasing rules of Rust and cause undefined
    /// behaviors.
    pub pte: Pte,
    /// The index of the entry in the node.
    pub idx: usize,
}

impl Entry {
    pub open spec fn wf(&self) -> bool {
        &&& self.pte.wf()
        &&& 0 <= self.idx < 512
    }

    pub open spec fn wf_with_node(&self, node: PageTableGuard) -> bool {
        let _node: &PageTableNode = &node.deref().deref();

        self.pte.wf_with_node_info(
            _node.level_spec(),
            _node.inst@.id(),
            _node.nid@,
            self.idx as nat,
        )
    }

    // /// Returns if the entry does not map to anything.
    // pub fn is_none(&self) -> bool {
    //     !self.pte.is_present() && self.pte.paddr() == 0
    // }
    // /// Returns if the entry maps to a page table node.
    // pub fn is_node(&self) -> bool {
    //     self.pte.is_present() && !self.pte.is_last(self.node.level())
    // }
    /// Gets a reference to the child.
    pub fn to_ref<'rcu>(&'rcu self, node: &PageTableGuard<'rcu>) -> (res: ChildRef<'rcu>)
        requires
            self.wf(),
            self.wf_with_node(*node),
            node.wf(),
        ensures
            res.wf(),
            res is Frame ==> res->Frame_1 == node.deref().deref().level_spec(),
    {
        ChildRef::from_pte(&self.pte, node.deref().deref().level())
    }

    /// Replaces the entry with a new child.
    ///
    /// The old child is returned.
    pub fn replace(&mut self, new_child: Child, node: &mut PageTableGuard) -> (res: Child)
        requires
            old(self).wf(),
            old(self).wf_with_node(*old(node)),
            new_child.wf(),
            new_child.wf_with_node(old(self).idx as nat, *old(node)),
            old(node).wf(),
        ensures
            self.wf(),
            self.wf_with_node(*node),
            new_child.wf_into_pte(self.pte),
            self.idx == old(self).idx,
            node.wf(),
            node.inst_id() == old(node).inst_id(),
            node.nid() == old(node).nid(),
            res.wf_from_pte(old(self).pte, old(node).inner.deref().level_spec()),
    {
        let old_child = Child::from_pte(self.pte, node.inner.deref().level());

        let pte = new_child.into_pte();
        node.write_pte(self.idx, pte);

        self.pte = pte;

        old_child
    }

    /// Create a new entry at the node with guard.
    pub fn new_at(idx: usize, node: &PageTableGuard) -> (res: Self)
        requires
            0 <= idx < 512,
            node.wf(),
        ensures
            res.wf(),
            res.wf_with_node(*node),
            res.idx == idx,
    {
        let pte = node.read_pte(idx);
        Self { pte, idx }
    }
}

} // verus!
