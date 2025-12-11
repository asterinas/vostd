use std::clone;
use std::marker::PhantomData;
use std::mem::ManuallyDrop;

use vstd::prelude::*;

use crate::mm::frame::meta::AnyFrameMeta;
use crate::mm::{
    frame::Frame,
    page_prop::PageProperty,
    page_table::{
        cursor::spec_helpers, entry_local::EntryLocal, PageTableConfig, PageTableEntryTrait,
    },
    vm_space::Token,
    Paddr, PagingConsts, PagingConstsTrait, PagingLevel,
};

use crate::spec::sub_pt::state_machine::IntermediatePageTableEntryView;

use std::ops::Deref;

use crate::sync::rcu::RcuDrop;

use super::{PageTableNode, PageTableNodeRef};

use crate::exec;
use crate::spec::sub_pt::SubPageTable;
use crate::spec::sub_pt::level_is_in_range;

verus! {

/// A page table entry that owns the child of a page table node if present.
pub(in crate::mm) enum ChildLocal<C: PageTableConfig> {
    /// A child page table node.
    PageTable(RcuDrop<PageTableNode<C>>),
    /// Physical address of a mapped physical frame.
    ///
    /// It is associated with the virtual page property and the level of the
    /// mapping node, which decides the size of the frame.
    Frame(Paddr, PagingLevel, PageProperty),
    None,
}

impl<C: PageTableConfig> ChildLocal<C> {
    /// Returns whether the child is not present.
    #[verifier::allow_in_spec]
    pub(in crate::mm) fn is_none(&self) -> bool
        returns
            self is None,
    {
        match self {
            ChildLocal::None => true,
            _ => false,
        }
    }

    pub(super) fn into_pte_local(self) -> (res: C::E) {
        match self {
            ChildLocal::PageTable(node) => {
                let paddr = node.start_paddr_local();
                let _ = ManuallyDrop::new(node);
                C::E::new_pt(paddr)
            },
            ChildLocal::Frame(paddr, level, prop) => {
                assert(level == 1) by {
                    admit();
                };
                C::E::new_page(paddr, level, prop)
            },
            ChildLocal::None => C::E::new_absent(),
        }
    }

    /// # Safety
    ///
    /// The provided PTE must be the output of [`Self::into_pte`], and the PTE:
    ///  - must not be used to created a [`Child`] twice;
    ///  - must not be referenced by a living [`ChildRef`].
    ///
    /// The level must match the original level of the child.
    #[verifier::external_body]
    pub(super) fn from_pte_local(
        pte: C::E,
        level: PagingLevel,
        Tracked(spt): Tracked<&SubPageTable<C>>,
    ) -> Self {
        if !pte.is_present() {
            return ChildLocal::None;
        }
        let paddr = pte.frame_paddr();

        if !pte.is_last(level) {
            let node = PageTableNode::from_raw_local(paddr, Tracked(&spt.alloc_model));
            return ChildLocal::PageTable(RcuDrop::new(node));
        }
        ChildLocal::Frame(paddr, level, pte.prop())
    }
}

/// A reference to the child of a page table node.
pub(in crate::mm) enum ChildRefLocal<'a, C: PageTableConfig> {
    /// A child page table node.
    PageTable(PageTableNodeRef<'a, C>),
    /// Physical address of a mapped physical frame.
    ///
    /// It is associated with the virtual page property and the level of the
    /// mapping node, which decides the size of the frame.
    Frame(Paddr, PagingLevel, PageProperty),
    None,
}

impl<'a, C: PageTableConfig> ChildRefLocal<'a, C> {
    /// Converts a PTE to a child.
    ///
    /// # Safety
    ///
    /// The PTE must be the output of a [`ChildLocal::into_pte`], where the child
    /// outlives the reference created by this function.
    ///
    /// The provided level must be the same with the level of the page table
    /// node that contains this PTE.
    pub(super) fn from_pte_local(
        pte: &C::E,
        level: PagingLevel,
        Tracked(spt): Tracked<&SubPageTable<C>>,
        entry: &EntryLocal<C>,  // TODO: should be ghost
    ) -> (res: Self)
        requires
            spt.wf(),
            pte == entry.pte,
            entry.wf_local(spt),
            level == entry.node.level_local_spec(&spt.alloc_model),
        ensures
            res.child_entry_spt_wf(entry, spt),
    {
        if !pte.is_present() {
            return ChildRefLocal::None;
        }
        let paddr = pte.frame_paddr();

        if !pte.is_last(level) {
            let node = PageTableNodeRef::borrow_paddr_local(paddr, Tracked(&spt.alloc_model));
            // debug_assert_eq!(node.level(), level - 1);
            let res = ChildRefLocal::PageTable(node);
            return res;
        }
        ChildRefLocal::Frame(paddr, level, pte.prop())
    }

    #[verifier::inline]
    pub(in crate::mm) open spec fn child_entry_spt_wf(
        &self,
        entry: &EntryLocal<C>,
        spt: &SubPageTable<C>,
    ) -> bool {
        &&& self is PageTable <==> match self {
            ChildRefLocal::PageTable(pt) => {
                &&& spt.i_ptes.value().contains_key(entry.pte.pte_paddr() as int)
                &&& pt.wf_local(&spt.alloc_model)
                &&& pt.deref().start_paddr_local() == entry.pte.frame_paddr() as usize
                &&& pt.level_local_spec(&spt.alloc_model) == entry.node.level_local_spec(
                    &spt.alloc_model,
                ) - 1
                &&& spt.alloc_model.meta_map.contains_key(pt.deref().start_paddr_local() as int)
                &&& spt.alloc_model.meta_map[pt.deref().start_paddr_local() as int].pptr()
                    == pt.meta_ptr_l
                &&& spt.frames.value().contains_key(pt.deref().start_paddr_local() as int)
                &&& spt.frames.value()[pt.deref().start_paddr_local() as int].ancestor_chain
                    == spt.frames.value()[entry.node.paddr_local() as int].ancestor_chain.insert(
                    entry.node.level_local_spec(&spt.alloc_model) as int,
                    IntermediatePageTableEntryView {
                        map_va: entry.va as int,
                        frame_pa: entry.node.paddr_local() as int,
                        in_frame_index: entry.idx as int,
                        map_to_pa: pt.deref().start_paddr_local() as int,
                        level: entry.node.level_local_spec(&spt.alloc_model),
                        phantom: PhantomData,
                    },
                )
            },
            _ => false,
        }
        &&& self is Frame <==> match self {
            ChildRefLocal::Frame(pa, level, prop) => {
                &&& pa == entry.pte.frame_paddr() as usize
                &&& spt.ptes.value().contains_key(entry.pte.pte_paddr() as int)
                &&& spt.ptes.value()[entry.pte.pte_paddr() as int].map_to_pa == pa
            },
            _ => false,
        }
        &&& (self is PageTable || self is Frame) <==> entry.pte.is_present_spec()
        &&& self is None <==> match self {
            ChildRefLocal::None => true,
            _ => false,
        }
    }
}

} // verus!
