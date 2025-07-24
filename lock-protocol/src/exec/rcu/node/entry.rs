use core::ops::Deref;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::spec::{common::*, utils::*};
use super::super::{common::*, types::*, cpu::*};
use super::{PageTableNode, PageTableNodeRef, PageTableGuard};
use super::child::*;
use super::super::pte::{Pte, page_table_entry_trait::*};

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
    pub open spec fn wf(&self, node: PageTableGuard) -> bool {
        &&& self.pte.wf_with_node(*(node.deref().deref()), self.idx as nat)
        &&& 0 <= self.idx < 512
        &&& node.guard is Some ==> node.guard->Some_0.perms@.relate_pte(self.pte, self.idx as nat)
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

    pub open spec fn is_node_spec(&self, node: &PageTableGuard) -> bool {
        self.pte.is_pt(node.deref().deref().level_spec())
    }

    /// Returns if the entry maps to a page table node.
    #[verifier::when_used_as_spec(is_node_spec)]
    pub fn is_node(&self, node: &PageTableGuard) -> bool
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
    pub fn to_ref<'rcu>(&'rcu self, node: &PageTableGuard<'rcu>) -> (res: ChildRef<'rcu>)
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
    pub fn replace(&mut self, new_child: Child, node: &mut PageTableGuard) -> (res: Child)
        requires
            old(self).wf(*old(node)),
            new_child.wf(),
            new_child.wf_with_node(old(self).idx as nat, *old(node)),
            old(node).wf(),
        ensures
            self.wf(*node),
            new_child.wf_into_pte(self.pte),
            self.idx == old(self).idx,
            node.wf(),
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

    /// Allocates a new child page table node and replaces the entry with it.
    ///
    /// If the old entry is not none, the operation will fail and return `None`.
    /// Otherwise, the lock guard of the new child page table node is returned.
    #[verifier::external_body]
    pub fn alloc_if_none<'rcu>(
        &mut self,
        guard: &'rcu (),  // TODO
        node: &mut PageTableGuard<'rcu>,
    ) -> (res: Option<PageTableGuard<'rcu>>)
        requires
            old(self).wf(*old(node)),
            old(node).wf(),
        ensures
            self.wf(*node),
            self.idx == old(self).idx,
            node.wf(),
            node.inst_id() == old(node).inst_id(),
            node.nid() == old(node).nid(),
            node.inner.deref().level_spec() == old(node).inner.deref().level_spec(),
            !(old(self).is_none() && old(node).inner.deref().level_spec() > 1) <==> res is None,
            res is Some ==> {
                &&& res->Some_0.wf()
                &&& res->Some_0.inst_id() == node.inst_id()
                &&& res->Some_0.nid() == NodeHelper::get_child(node.nid(), self.idx as nat)
                &&& res->Some_0.inner.deref().level_spec() + 1 == node.inner.deref().level_spec()
                &&& res->Some_0.guard->Some_0.in_protocol@ == false
            },
    {
        if !(self.is_none() && node.level() > 1) {
            return None;
        }
        let level = node.level();
        // let new_page = RcuDrop::new(PageTableNode::alloc(level - 1));
        let new_page = PageTableNode::alloc(level - 1);
        let paddr = new_page.start_paddr();

        let pt_ref = PageTableNodeRef::borrow_paddr(
            paddr,
            Ghost(new_page.nid@),
            Ghost(new_page.inst@.id()),
            Ghost(new_page.level_spec()),
        );
        // Lock before writing the PTE, so no one else can operate on it.
        let pt_lock_guard = pt_ref.normal_lock(guard);

        self.pte = Child::PageTable(new_page).into_pte();

        node.write_pte(self.idx, self.pte);

        // *self.node.nr_children_mut() += 1;

        Some(pt_lock_guard)
    }

    /// Create a new entry at the node with guard.
    pub fn new_at(idx: usize, node: &PageTableGuard) -> (res: Self)
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
