use core::ops::Deref;

use vstd::prelude::*;

use crate::spec::{common::*, utils::*};
use super::super::{common::*, types::*, cpu::*};
use super::{PageTableNode, PageTableNodeRef, PageTableGuard};
use super::child::*;
use super::stray::*;
use super::super::pte::{Pte, page_table_entry_trait::*};
use crate::sync::rcu::RcuDrop;

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

    pub open spec fn nid(&self, node: PageTableGuard) -> NodeId {
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

    /// Allocates a new child page table node and replaces the entry with it.
    ///
    /// If the old entry is not none, the operation will fail and return `None`.
    /// Otherwise, the lock guard of the new child page table node is returned.
    pub fn normal_alloc_if_none<'rcu>(
        &mut self,
        guard: &'rcu (),  // TODO
        node: &mut PageTableGuard<'rcu>,
    ) -> (res: Option<PageTableGuard<'rcu>>)
        requires
            old(self).wf(*old(node)),
            old(node).wf(),
            NodeHelper::is_not_leaf(old(node).nid()),
            old(node).guard->Some_0.stray_perm@.value() == false,
            old(node).guard->Some_0.in_protocol@ == false,
        ensures
            self.wf(*node),
            self.idx == old(self).idx,
            node.wf(),
            node.inst_id() == old(node).inst_id(),
            node.nid() == old(node).nid(),
            node.inner.deref().level_spec() == old(node).inner.deref().level_spec(),
            node.guard->Some_0.in_protocol == old(node).guard->Some_0.in_protocol,
            !(old(self).is_none() && old(node).inner.deref().level_spec() > 1) <==> res is None,
            res is Some ==> {
                &&& res->Some_0.wf()
                &&& res->Some_0.inst_id() == node.inst_id()
                &&& res->Some_0.nid() == NodeHelper::get_child(node.nid(), self.idx as nat)
                &&& res->Some_0.inner.deref().level_spec() + 1 == node.inner.deref().level_spec()
                &&& res->Some_0.guard->Some_0.stray_perm@.value() == false
                &&& res->Some_0.guard->Some_0.in_protocol@ == false
            },
    {
        if !(self.is_none() && node.inner.deref().level() > 1) {
            return None;
        }
        let level = node.inner.deref().level();
        let ghost cur_nid = self.nid(*node);
        let mut lock_guard = node.guard.take().unwrap();
        let tracked node_token = lock_guard.node_token.get().tracked_unwrap();
        let tracked pte_token = lock_guard.pte_token.get().tracked_unwrap();
        assert(node_token.value() is LockedOutside);
        assert(pte_token.value().is_void(self.idx as nat));
        assert(cur_nid != NodeHelper::root_id()) by {
            assert(cur_nid == NodeHelper::get_child(node.nid(), self.idx as nat));
            NodeHelper::lemma_get_child_sound(node.nid(), self.idx as nat);
            NodeHelper::lemma_is_child_nid_increasing(node.nid(), cur_nid);
        };
        assert(NodeHelper::valid_nid(cur_nid)) by {
            assert(cur_nid == NodeHelper::get_child(node.nid(), self.idx as nat));
            NodeHelper::lemma_get_child_sound(node.nid(), self.idx as nat);
        };

        let tracked_inst = node.tracked_pt_inst();
        let tracked inst = tracked_inst.get();
        assert(level - 1 == NodeHelper::nid_to_level(cur_nid)) by {
            NodeHelper::lemma_get_child_sound(node.nid(), self.idx as nat);
            NodeHelper::lemma_is_child_level_relation(node.nid(), cur_nid);
        };
        let res = PageTableNode::normal_alloc(
            level - 1,
            Ghost(cur_nid),
            Tracked(inst),
            Ghost(node.nid()),
            Ghost(self.idx as nat),
            Tracked(&node_token),
            Tracked(pte_token),
        );
        let new_page = RcuDrop::new(res.0);
        let tracked pte_token = res.1.get();
        lock_guard.node_token = Tracked(Some(node_token));
        lock_guard.pte_token = Tracked(Some(pte_token));
        node.guard = Some(lock_guard);
        let paddr = new_page.start_paddr();

        let pt_ref = PageTableNodeRef::borrow_paddr(
            paddr,
            Ghost(new_page.nid@),
            Ghost(new_page.inst@.id()),
            Ghost(new_page.level_spec()),
        );
        // Lock before writing the PTE, so no one else can operate on it.
        let tracked pa_pte_array_token = node.tracked_borrow_guard().tracked_borrow_pte_token();
        assert(pt_ref.nid@ == NodeHelper::get_child(node.nid(), self.idx as nat));
        assert(NodeHelper::get_parent(pt_ref.nid@) == node.nid()) by {
            NodeHelper::lemma_get_child_sound(node.nid(), self.idx as nat);
        };
        assert(NodeHelper::get_offset(pt_ref.nid@) == self.idx as nat) by {
            NodeHelper::lemma_get_child_sound(node.nid(), self.idx as nat);
        };
        let pt_lock_guard = pt_ref.normal_lock_new_allocated_node(
            guard,
            Tracked(pa_pte_array_token),
        );

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
