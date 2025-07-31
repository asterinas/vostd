use vstd::prelude::*;

use crate::spec::{common::*, utils::*};
use super::super::{types::*, frame::*};
use super::PageTableWriteLock;
use super::child::*;
use super::super::pte::Pte;

verus! {

/// A view of an entry in a page table node.
///
/// It can be borrowed from a node using the [`PageTableWriteLock::entry`] method.
///
/// This is a static reference to an entry in a node that does not account for
/// a dynamic reference count to the child. It can be used to create a owned
/// handle, which is a [`Child`].
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

    pub open spec fn wf_with_node(&self, node: PageTableWriteLock) -> bool {
        let _node = node.frame->Some_0;

        self.pte.wf_with_node_info(
            _node.level_spec(),
            _node.inst@.id(),
            _node.nid@,
            self.idx as nat,
        )
    }

    pub open spec fn nid(&self, node: PageTableWriteLock) -> NodeId {
        NodeHelper::get_child(node.nid(), self.idx as nat)
    }

    pub open spec fn is_none_spec(&self) -> bool {
        self.pte.is_none()
    }

    /// Returns if the entry does not map to anything.
    #[verifier::when_used_as_spec(is_none_spec)]
    pub fn is_none(&self) -> bool
        returns
            self.pte.is_none(),
    {
        !self.pte.inner.is_present() && self.pte.inner.paddr() == 0
    }

    pub open spec fn is_node_spec(&self, node: &PageTableWriteLock) -> bool {
        self.pte.is_pt(node.deref().deref().level_spec())
    }

    /// Returns if the entry maps to a page table node.
    #[verifier::when_used_as_spec(is_node_spec)]
    pub fn is_node(&self, node: &PageTableWriteLock) -> bool
        requires
            self.wf(*node),
            node.wf(),
        returns
            self.is_node_spec(node),
    {
        &&& self.pte.inner.is_present()
        &&& !self.pte.inner.is_last(node.deref().deref().level())
    }

    /// Gets a reference to the child.
    pub fn to_ref(&self, node: &PageTableWriteLock) -> (res: Child)
        requires
            self.wf(*node),
            node.wf(),
        ensures
            res.wf(),
            res.wf_from_pte(self.pte, node.deref().deref().level_spec()),
    {
        ChildRef::from_pte(&self.pte, node.deref().deref().level())
    }

    /// Replaces the entry with a new child.
    ///
    /// The old child is returned.
    pub fn replace(&mut self, new_child: Child, node: &mut PageTableWriteLock) -> (res: Child)
        requires
            old(self).wf(*old(node)),
            new_child.wf(),
            new_child.wf_with_node(old(self).idx as nat, *old(node)),
            !(new_child is PageTable),
            old(node).wf(),
            old(node).guard->Some_0.stray_perm@.value() == false,
        ensures
            self.wf(*node),
            new_child.wf_into_pte(self.pte),
            self.idx == old(self).idx,
            if res is PageTable {
                &&& node.wf_except(self.idx as nat)
                &&& node.guard->Some_0.pte_token@->Some_0.value().is_alive(self.idx as nat)
            } else {
                node.wf()
            },
            node.inst_id() == old(node).inst_id(),
            node.nid() == old(node).nid(),
            node.inner.deref().level_spec() == old(node).inner.deref().level_spec(),
            res.wf_from_pte(old(self).pte, old(node).inner.deref().level_spec()),
    {
        let old_child = Child::from_pte(self.pte, node.inner.deref().level());

        self.pte = new_child.into_pte();
        node.write_pte(self.idx, self.pte);

        old_child
    }

    /// Create a new entry at the node with guard.
    pub fn new_at(idx: usize, node: &PageTableWriteLock) -> (res: Self)
        requires
            0 <= idx < 512,
            node.wf(),
        ensures
            res.wf(*node),
            res.idx == idx,
    {
        let pte = node.read_pte(idx);
        Self { pte, idx }
    }
}

} // verus!
