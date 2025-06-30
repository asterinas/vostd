use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::spec::{common::*, utils::*};
use super::super::{types::*, mem_content::*};
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

    pub open spec fn wf_with_node(
        &self,
        node: PageTableWriteLock,
    ) -> bool {
        let _node = node.frame->Some_0;

        self.pte.wf_with_node_info(
            _node.start_paddr_spec(), 
            _node.level_spec(),
            _node.inst@.id(), 
            _node.nid@, 
            self.idx as nat,
        )
    }

    /// Gets a reference to the child.
    pub fn to_ref(
        &self,
        node: &PageTableWriteLock,
        mem: &MemContent,
    ) -> (res: Child) 
        requires
            self.wf(),
            self.wf_with_node(*node),
            node.wf(mem),
        ensures
            res.wf(mem),
            !(res is PageTable),
            res is Frame ==> res->Frame_1 == node.level_spec(),
    {
        // SAFETY: The entry structure represents an existent entry with the
        // right node information.
        // unsafe { Child::ref_from_pte(&self.pte, self.node.level(), self.node.is_tracked(), false) }
        Child::ref_from_pte(&self.pte, node.level(mem), /*self.node.is_tracked(),*/ false, mem)
    }

    /// Replaces the entry with a new child.
    ///
    /// The old child is returned.
    ///
    /// # Panics
    ///
    /// The method panics if the given child is not compatible with the node.
    /// The compatibility is specified by the [`Child::is_compatible`].
    #[verifier::external_body] // TODO
    pub fn replace(
        self, 
        new_child: Child,
        node: &mut PageTableWriteLock,
        mem: &MemContent,
    ) 
        requires
            self.wf(),
            self.wf_with_node(*old(node)),
            new_child.wf(mem),
            old(node).wf(mem),
        ensures
            node.wf(mem),
            node.inst_id() == old(node).inst_id(),
            node.nid() == old(node).nid(),
    {
        // assert!(new_child.is_compatible(self.node.level(), self.node.is_tracked()));

        // SAFETY: The entry structure represents an existent entry with the
        // right node information. The old PTE is overwritten by the new child
        // so that it is not used anymore.
        // let old_child =
            // unsafe { Child::from_pte(self.pte, self.node.level(), self.node.is_tracked()) };
            // Child::from_pte(self.pte, self.node.level(), /*self.node.is_tracked()*/);

        // if old_child.is_none() && !new_child.is_none() {
        //     *self.node.nr_children_mut() += 1;
        // } else if !old_child.is_none() && new_child.is_none() {
        //     *self.node.nr_children_mut() -= 1;
        // }

        // SAFETY:
        //  1. The index is within the bounds.
        //  2. The new PTE is compatible with the page table node, as asserted above.
        // unsafe { self.node.write_pte(self.idx, new_child.into_pte()) };
        let pte = new_child.into_pte(mem);
        node.write_pte(self.idx, pte, mem);

        // old_child
    }

    /// Create a new entry at the node.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the index is within the bounds of the node.
    pub fn new_at(
        idx: usize,
        node: &PageTableWriteLock,
        mem: &MemContent,
    ) -> (res: Self)
        requires
            0 <= idx < 512,
            node.wf(mem),
        ensures
            res.wf(),
            res.wf_with_node(*node),
    {
        // SAFETY: The index is within the bound.
        // let pte = unsafe { node.read_pte(idx) };
        let pte = node.read_pte(idx, mem);
        Self { pte, idx }
    }
}

}