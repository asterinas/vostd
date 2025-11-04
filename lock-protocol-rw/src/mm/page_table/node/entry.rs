use core::ops::Deref;
use std::marker::PhantomData;

use vstd::prelude::*;

use common::{
    mm::{
        page_table::{PagingConstsTrait, PageTableEntryTrait, PageTableConfig},
        nr_subpage_per_huge,
    },
    task::DisabledPreemptGuard,
};
use common::spec::{
    node_helper::{self, group_node_helper_lemmas},
    common::NodeId,
};

use crate::mm::page_table::node::{
    child::{Child, ChildRef},
    PageTableNode, PageTableNodeRef, PageTableReadLock, PageTableWriteLock,
};
use crate::mm::page_table::pte::Pte;
use crate::spec::{lock_protocol::LockProtocolModel};

verus! {

pub struct Entry<C: PageTableConfig> {
    /// The page table entry.
    ///
    /// We store the page table entry here to optimize the number of reads from
    /// the node. We cannot hold a `&mut E` reference to the entry because that
    /// other CPUs may modify the memory location for accessed/dirty bits. Such
    /// accesses will violate the aliasing rules of Rust and cause undefined
    /// behaviors.
    pub pte: Pte<C>,
    /// The index of the entry in the node.
    pub idx: usize,
}

impl<C: PageTableConfig> Entry<C> {
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
}

impl<'g, C: PageTableConfig> Entry<C> {
    pub open spec fn wf_read(&self, node: PageTableReadLock<'g, C>) -> bool {
        &&& self.pte.wf_with_node(*(node.deref().deref()), self.idx as nat)
        &&& 0 <= self.idx < nr_subpage_per_huge::<C>()
        &&& node.guard is Some ==> node.guard->Some_0.view_perms().relate_pte(
            self.pte,
            self.idx as nat,
        )
    }

    pub open spec fn nid_read(&self, node: PageTableReadLock<'g, C>) -> NodeId {
        node_helper::get_child::<C>(node.nid(), self.idx as nat)
    }

    pub open spec fn is_node_read_spec(&self, node: &PageTableReadLock<'g, C>) -> bool {
        self.pte.is_pt(node.deref().deref().level_spec())
    }

    /// Returns if the entry maps to a page table node.
    #[verifier::when_used_as_spec(is_node_read_spec)]
    pub fn is_node_read(&self, node: &PageTableReadLock<'g, C>) -> bool
        requires
            self.wf_read(*node),
            node.wf(),
        returns
            self.is_node_read_spec(node),
    {
        &&& self.pte.inner.is_present()
        &&& !self.pte.inner.is_last(node.deref().deref().level())
    }

    /// Gets a reference to the child.
    pub fn to_ref_read(&self, node: &PageTableReadLock<'g, C>) -> (res: ChildRef<'g, C>)
        requires
            self.wf_read(*node),
            node.wf(),
        ensures
            res.wf(),
            res.wf_from_pte(self.pte, node.deref().deref().level_spec()),
    {
        ChildRef::<'g, C>::from_pte(&self.pte, node.deref().deref().level())
    }

    /// Create a new entry at the node with guard.
    pub fn new_at_read(idx: usize, node: &PageTableReadLock<'g, C>) -> (res: Entry<C>)
        requires
            0 <= idx < 512,
            node.wf(),
        ensures
            res.wf_read(*node),
            res.idx == idx,
    {
        let pte = node.read_pte(idx);
        Self { pte, idx }
    }
}

impl<'g, C: PageTableConfig> Entry<C> {
    pub open spec fn wf_write(&self, node: PageTableWriteLock<'g, C>) -> bool {
        &&& self.pte.wf_with_node(*(node.deref().deref()), self.idx as nat)
        &&& 0 <= self.idx < nr_subpage_per_huge::<C>()
        &&& node.guard is Some ==> node.guard->Some_0.perms@.relate_pte(self.pte, self.idx as nat)
    }

    pub open spec fn nid_write(&self, node: PageTableWriteLock<'g, C>) -> NodeId {
        node_helper::get_child::<C>(node.nid(), self.idx as nat)
    }

    pub open spec fn is_node_write_spec(&self, node: &PageTableWriteLock<'g, C>) -> bool {
        self.pte.is_pt(node.deref().deref().level_spec())
    }

    /// Returns if the entry maps to a page table node.
    #[verifier::when_used_as_spec(is_node_write_spec)]
    pub fn is_node_write(&self, node: &PageTableWriteLock<'g, C>) -> bool
        requires
            self.wf_write(*node),
            node.wf(),
        returns
            self.is_node_write_spec(node),
    {
        &&& self.pte.inner.is_present()
        &&& !self.pte.inner.is_last(node.deref().deref().level())
    }

    /// Gets a reference to the child.
    pub fn to_ref_write(&self, node: &PageTableWriteLock<'g, C>) -> (res: ChildRef<'g, C>)
        requires
            self.wf_write(*node),
            node.wf(),
        ensures
            res.wf(),
            res.wf_from_pte(self.pte, node.deref().deref().level_spec()),
    {
        ChildRef::<'g, C>::from_pte(&self.pte, node.deref().deref().level())
    }

    /// Replaces the entry with a new child.
    ///
    /// The old child is returned.
    // pub fn replace(&mut self, new_child: Child, node: &mut PageTableWriteLock<'g>) -> (res: Child)
    //     requires
    //         old(self).wf_write(*old(node)),
    //         new_child.wf(),
    //         new_child.wf_with_node(old(self).idx as nat, *(old(node).inner.deref())),
    //         !(new_child is PageTable),
    //         old(node).wf(),
    //         old(node).guard->Some_0.stray_perm@.value() == false,
    //     ensures
    //         self.wf_write(*node),
    //         new_child.wf_into_pte(self.pte),
    //         self.idx == old(self).idx,
    //         if res is PageTable {
    //             &&& node.wf_except(self.idx as nat)
    //             &&& node.guard->Some_0.pte_token@->Some_0.value().is_alive(self.idx as nat)
    //         } else {
    //             node.wf()
    //         },
    //         node.inst_id() == old(node).inst_id(),
    //         node.nid() == old(node).nid(),
    //         node.inner.deref().level_spec() == old(node).inner.deref().level_spec(),
    //         res.wf_from_pte(old(self).pte, old(node).inner.deref().level_spec()),
    // {
    //     let old_child = Child::from_pte(self.pte, node.inner.deref().level());
    //     self.pte = new_child.into_pte();
    //     node.write_pte(self.idx, self.pte);
    //     old_child
    // }
    /// Allocates a new child page table node and replaces the entry with it.
    ///
    /// If the old entry is not none, the operation will fail and return `None`.
    /// Otherwise, the lock guard of the new child page table node is returned.
    pub fn alloc_if_none(
        &mut self,
        guard: &'g DisabledPreemptGuard,
        node: &mut PageTableWriteLock<'g, C>,
        Tracked(m): Tracked<&LockProtocolModel<C>>,
    ) -> (res: Option<PageTableWriteLock<'g, C>>)
        requires
            old(self).wf_write(*old(node)),
            old(node).wf(),
            node_helper::is_not_leaf::<C>(old(node).nid()),
            m.inv(),
            m.inst_id() == old(node).inst_id(),
            m.state() is WriteLocked,
            m.node_is_locked(old(node).nid()),
        ensures
            self.wf_write(*node),
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
                &&& res->Some_0.nid() == node_helper::get_child::<C>(node.nid(), self.idx as nat)
                &&& res->Some_0.inner.deref().level_spec() + 1 == node.inner.deref().level_spec()
                &&& res->Some_0.guard->Some_0.in_protocol@ == true
            },
    {
        broadcast use group_node_helper_lemmas;

        if !(self.is_none() && node.inner.deref().level() > 1) {
            return None;
        }
        let level = node.inner.deref().level();
        let ghost cur_nid = self.nid_write(*node);
        let mut lock_guard = node.guard.take().unwrap();
        let tracked node_token = lock_guard.node_token.get();
        let tracked pte_array_token = lock_guard.pte_array_token.get();
        assert(node_token.value().is_write_locked());
        assert(pte_array_token.value().is_void(self.idx as nat));
        assert(cur_nid != node_helper::root_id::<C>()) by {
            assert(cur_nid == node_helper::get_child::<C>(node.nid(), self.idx as nat));
            node_helper::lemma_is_child_nid_increasing::<C>(node.nid(), cur_nid);
        };
        let tracked_inst = node.tracked_pt_inst();
        let tracked inst = tracked_inst.get();
        assert(level - 1 == node_helper::nid_to_level::<C>(cur_nid)) by {
            node_helper::lemma_get_child_sound::<C>(node.nid(), self.idx as nat);
            node_helper::lemma_is_child_level_relation::<C>(node.nid(), cur_nid);
        };
        let res = PageTableNode::<C>::alloc(
            level - 1,
            Ghost(cur_nid),
            Tracked(inst),
            Ghost(node.nid()),
            Ghost(self.idx as nat),
            Tracked(&node_token),
            Tracked(pte_array_token),
        );
        let new_page = res.0;
        let tracked pte_array_token = res.1.get();
        lock_guard.node_token = Tracked(node_token);
        lock_guard.pte_array_token = Tracked(pte_array_token);
        node.guard = Some(lock_guard);

        let paddr = new_page.start_paddr();
        let pt_ref = PageTableNodeRef::<C>::borrow_paddr(
            paddr,
            Ghost(new_page.nid@),
            Ghost(new_page.inst@.id()),
            Ghost(new_page.level_spec()),
        );

        // The child is implicitly write locked because the parent is write locked.
        let pt_lock_guard = pt_ref.make_write_guard_unchecked(guard, Tracked(m));

        self.pte = Child::<C>::PageTable(new_page).into_pte();

        // core::sync::atomic::fence(Ordering::Release);
        node.write_pte(self.idx, self.pte);

        // *self.node.nr_children_mut() += 1;

        Some(pt_lock_guard)
    }

    /// Create a new entry at the node with guard.
    pub fn new_at_write(idx: usize, node: &PageTableWriteLock<'g, C>) -> (res: Self)
        requires
            0 <= idx < nr_subpage_per_huge::<C>(),
            node.wf(),
        ensures
            res.wf_write(*node),
            res.idx == idx,
    {
        let pte = node.read_pte(idx);
        Self { pte, idx }
    }
}

} // verus!
