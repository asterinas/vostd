use vstd::prelude::*;

use crate::mm::{
    cursor::spec_helpers::{self, frame_keys_do_not_change},
    meta::AnyFrameMeta,
    nr_subpage_per_huge,
    page_prop::PageProperty,
    page_size,
    vm_space::Token,
    PageTableConfig, PageTableEntryTrait, PagingConstsTrait, PagingLevel,
};

use super::{Child, MapTrackingStatus, PageTableLockTrait, PageTableNode};

use crate::exec;

use crate::spec::simple_page_table;

verus! {

/// A view of an entry in a page table node.
///
/// It can be borrowed from a node using the [`PageTableLock::entry`] method.
///
/// This is a static reference to an entry in a node that does not account for
/// a dynamic reference count to the child. It can be used to create a owned
/// handle, which is a [`Child`].
pub struct Entry<'a, C: PageTableConfig, PTL: PageTableLockTrait<C>> {
    /// The page table entry.
    ///
    /// We store the page table entry here to optimize the number of reads from
    /// the node. We cannot hold a `&mut E` reference to the entry because that
    /// other CPUs may modify the memory location for accessed/dirty bits. Such
    /// accesses will violate the aliasing rules of Rust and cause undefined
    /// behaviors.
    pub pte: C::E,
    /// The index of the entry in the node.
    pub idx: usize,
    /// The node that contains the entry.
    // node: &'a mut PageTableLock<C>,
    pub node: &'a PTL,
    pub phantom: std::marker::PhantomData<(C)>,
}

impl<'a, C: PageTableConfig, PTL: PageTableLockTrait<C>> Entry<'a, C, PTL> {
    /// Gets a reference to the child.
    pub(in crate::mm) fn to_ref(&self, spt: &exec::SubPageTable) -> (res: Child<C>)
        requires
            spt.wf(),
            self.pte.pte_paddr() == exec::get_pte_from_addr(self.pte.pte_paddr(), spt).pte_addr,
            self.pte.frame_paddr() == exec::get_pte_from_addr(self.pte.pte_paddr(), spt).frame_pa,
        ensures
            if (spt.ptes@.value().contains_key(self.pte.pte_paddr() as int)) {
                match res {
                    Child::PageTableRef(pt) => pt == self.pte.frame_paddr() as usize
                        && spt.frames@.value().contains_key(pt as int),
                    _ => false,
                }
            } else {
                match res {
                    Child::None => true,
                    _ => false,
                }
            },
    {
        // SAFETY: The entry structure represents an existent entry with the
        // right node information.
        // unsafe { Child::ref_from_pte(&self.pte, self.node.level(), self.node.is_tracked(), false) }
        let c = Child::ref_from_pte(
            &self.pte,
            // self.node.level(),
            self.node.is_tracked(),
            false,
            spt,
        );
        c
    }

    /// Operates on the mapping properties of the entry.
    ///
    /// It only modifies the properties if the entry is present.
    // TODO: Implement protect
    #[verifier::external_body]
    pub(in crate::mm) fn protect(
        &mut self,
        prot_op: &mut impl FnMut(&mut PageProperty),
        token_op: &mut impl FnMut(&mut Token),
    ) {
        unimplemented!()
    }

    /// Replaces the entry with a new child.
    ///
    /// The old child is returned.
    ///
    /// # Panics
    ///
    /// The method panics if the given child is not compatible with the node.
    /// The compatibility is specified by the [`Child::is_compatible`].
    // TODO: Implement replace
    // #[verifier::external_body]
    pub(in crate::mm) fn replace(
        self,
        new_child: Child<C>,
        spt: &mut exec::SubPageTable,
        level: PagingLevel,
        ghost_index: usize,  // TODO: make it ghost
        used_pte_addr_token: Tracked<simple_page_table::SimplePageTable::unused_pte_addrs>,
    ) -> (res: Child<C>)
        requires
            !old(spt).ptes@.value().contains_key(self.pte.pte_paddr() as int),
            old(spt).wf(),
            self.idx < nr_subpage_per_huge(),
            spec_helpers::mpt_not_contains_not_allocated_frames(old(spt), ghost_index),
            used_pte_addr_token@.instance_id() == old(spt).instance@.id(),
            used_pte_addr_token@.element() == self.node.paddr() + self.idx
                * exec::SIZEOF_PAGETABLEENTRY as int,
        ensures
            spt.ptes@.value().contains_key(self.pte.pte_paddr() as int),
            spt.instance@.id() == old(spt).instance@.id(),
            spt.wf(),
            frame_keys_do_not_change(spt, old(spt)),
            spec_helpers::mpt_not_contains_not_allocated_frames(spt, ghost_index),
            match new_child {
                // Child::PageTable(pt) => self.pte.frame_paddr() == pt.ptr as usize, // TODO: ?
                _ => true,
            },
    {
        // // assert!(new_child.is_compatible(self.node.level(), self.node.is_tracked()));
        // SAFETY: The entry structure represents an existent entry with the
        // right node information. The old PTE is overwritten by the new child
        // so that it is not used anymore.
        let old_child =
            // unsafe { Child::from_pte(self.pte, self.node.level(), self.node.is_tracked()) };
        Child::from_pte(
            self.pte,
            // self.node.level(),
            self.node.is_tracked(),
            spt,
        );

        if old_child.is_none() && !new_child.is_none() {
            // *self.node.nr_children_mut() += 1;
            self.node.change_children(1);
        } else if !old_child.is_none() && new_child.is_none() {
            // *self.node.nr_children_mut() -= 1;
            self.node.change_children(-1);
        }
        assert(spec_helpers::mpt_not_contains_not_allocated_frames(spt, ghost_index));
        // SAFETY:
        //  1. The index is within the bounds.
        //  2. The new PTE is compatible with the page table node, as asserted above.
        // unsafe { self.node.write_pte(self.idx, new_child.into_pte()) };
        self.node.write_pte(
            self.idx,
            new_child.into_pte(spt, ghost_index),
            spt,
            level,
            ghost_index,
            used_pte_addr_token,
        );

        // TODO: P0
        assume(spt.ptes@.value().contains_key(self.pte.pte_paddr() as int));

        old_child
        // unimplemented!()

    }

    /// Create a new entry at the node.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the index is within the bounds of the node.
    // pub(super) unsafe fn new_at(node: &'a mut PageTableLock<C>, idx: usize) -> Self {
    pub fn new_at(node: &'a PTL, idx: usize, spt: &exec::SubPageTable) -> (res: Self)
        requires
            idx < nr_subpage_per_huge(),
            spt.wf(),
        ensures
            res.pte.pte_paddr() == node.paddr() as usize + idx * exec::SIZEOF_PAGETABLEENTRY,
            res.pte.pte_paddr() == exec::get_pte_from_addr_spec(res.pte.pte_paddr(), spt).pte_addr,
            res.pte.frame_paddr() == exec::get_pte_from_addr_spec(
                res.pte.pte_paddr(),
                spt,
            ).frame_pa,
            res.idx == idx,
            res.pte.frame_paddr() == 0 ==> !spt.ptes@.value().contains_key(
                res.pte.pte_paddr() as int,
            ),
            res.pte.frame_paddr() != 0 ==> {
                &&& spt.ptes@.value().contains_key(res.pte.pte_paddr() as int)
                &&& spt.ptes@.value()[res.pte.pte_paddr() as int].frame_pa
                    == res.pte.frame_paddr() as int
                &&& spt.frames@.value().contains_key(res.pte.frame_paddr() as int)
            },
    {
        // SAFETY: The index is within the bound.
        // let pte = unsafe { node.read_pte(idx) };
        let pte = node.read_pte(idx, spt);
        Self { pte, idx, node, phantom: std::marker::PhantomData }
    }
}

} // verus!
