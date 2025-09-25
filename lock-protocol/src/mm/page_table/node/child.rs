use std::clone;
use std::marker::PhantomData;
use std::mem::ManuallyDrop;

use vstd::prelude::*;

use crate::mm::cursor::spec_helpers;
use crate::mm::entry::Entry;
use crate::mm::meta::AnyFrameMeta;
use crate::mm::page_prop::PageProperty;
use crate::mm::vm_space::Token;
use crate::mm::Frame;
use crate::mm::Paddr;
use crate::mm::PageTableConfig;
use crate::mm::PageTableEntryTrait;
use crate::mm::PagingConstsTrait;
use crate::mm::PagingConsts;
use crate::mm::PagingLevel;
use crate::spec::sub_pt::state_machine::IntermediatePageTableEntryView;
use std::ops::Deref;

use crate::sync::rcu::RcuDrop;

use super::{PageTableNode, PageTableNodeRef};

use crate::exec;
use crate::spec::sub_pt::SubPageTable;

// use crate::prelude::{RawPageTableNode, PageProperty, Paddr, PagingLevel, DynPage};

verus! {

/// A page table entry that owns the child of a page table node if present.
pub(in crate::mm) enum Child<C: PageTableConfig> {
    /// A child page table node.
    PageTable(RcuDrop<PageTableNode<C>>),
    /// Physical address of a mapped physical frame.
    ///
    /// It is associated with the virtual page property and the level of the
    /// mapping node, which decides the size of the frame.
    Frame(Paddr, PagingLevel, PageProperty),
    None,
}

impl<C: PageTableConfig> Child<C> {
    /// Returns whether the child is not present.
    #[verifier::allow_in_spec]
    pub(in crate::mm) fn is_none(&self) -> bool
        returns
            self is None,
    {
        match self {
            Child::None => true,
            _ => false,
        }
    }

    pub(super) fn into_pte(self) -> (res: C::E) {
        match self {
            Child::PageTable(node) => {
                let paddr = node.start_paddr();
                let _ = ManuallyDrop::new(node);
                C::E::new_pt(paddr)
            },
            Child::Frame(paddr, level, prop) => C::E::new_page(paddr, level, prop),
            Child::None => C::E::new_absent(),
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
    pub(super) fn from_pte(
        pte: C::E,
        level: PagingLevel,
        Tracked(spt): Tracked<&SubPageTable<C>>,
    ) -> Self {
        if !pte.is_present() {
            return Child::None;
        }
        let paddr = pte.frame_paddr();

        if !pte.is_last(level) {
            let node = PageTableNode::from_raw(paddr, Tracked(&spt.alloc_model));
            return Child::PageTable(RcuDrop::new(node));
        }
        Child::Frame(paddr, level, pte.prop())
    }
}

/// A reference to the child of a page table node.
pub(in crate::mm) enum ChildRef<'a, C: PageTableConfig> {
    /// A child page table node.
    PageTable(PageTableNodeRef<'a, C>),
    /// Physical address of a mapped physical frame.
    ///
    /// It is associated with the virtual page property and the level of the
    /// mapping node, which decides the size of the frame.
    Frame(Paddr, PagingLevel, PageProperty),
    None,
}

impl<'a, C: PageTableConfig> ChildRef<'a, C> {
    /// Converts a PTE to a child.
    ///
    /// # Safety
    ///
    /// The PTE must be the output of a [`Child::into_pte`], where the child
    /// outlives the reference created by this function.
    ///
    /// The provided level must be the same with the level of the page table
    /// node that contains this PTE.
    pub(super) fn from_pte(
        pte: &C::E,
        level: PagingLevel,
        Tracked(spt): Tracked<&SubPageTable<C>>,
        entry: &Entry<C>,  // TODO: should be ghost
    ) -> (res: Self)
        requires
            spt.wf(),
            pte == entry.pte,
            entry.wf(spt),
            level == entry.node.level_spec(&spt.alloc_model),
        ensures
            res.child_entry_spt_wf(entry, spt),
    {
        if !pte.is_present() {
            return ChildRef::None;
        }
        let paddr = pte.frame_paddr();

        if !pte.is_last(level) {
            assert(spt.alloc_model.invariants());
            assert(spt.alloc_model.meta_map.contains_key(paddr as int));
            let node = PageTableNodeRef::borrow_pt_paddr(paddr, Tracked(&spt.alloc_model));
            // debug_assert_eq!(node.level(), level - 1);
            assert(node.wf(&spt.alloc_model));
            let res = ChildRef::PageTable(node);
            assert(spt.i_ptes.value().contains_key(entry.pte.pte_paddr() as int));
            assert(node.level_spec(&spt.alloc_model) == entry.node.level_spec(&spt.alloc_model) - 1);
            assert(res.child_entry_spt_wf(entry, spt));
            assert(!(res is None));
            assert(pte.is_present());
            return res;
        }
        let res = ChildRef::Frame(paddr, level, pte.prop());
        assume(spt.ptes.value().contains_key(entry.pte.pte_paddr() as int));
        assume(spt.ptes.value()[entry.pte.pte_paddr() as int].map_to_pa == paddr);
        res
    }

    #[verifier::inline]
    pub(in crate::mm) open spec fn child_entry_spt_wf(
        &self,
        entry: &Entry<C>,
        spt: &SubPageTable<C>,
    ) -> bool {
        &&& self is PageTable <==> match self {
            ChildRef::PageTable(pt) => {
                &&& spt.i_ptes.value().contains_key(entry.pte.pte_paddr() as int)
                &&& pt.wf(&spt.alloc_model)
                &&& pt.deref().start_paddr() == entry.pte.frame_paddr() as usize
                &&& pt.level_spec(&spt.alloc_model) == entry.node.level_spec(&spt.alloc_model) - 1
                &&& spt.alloc_model.meta_map.contains_key(pt.deref().start_paddr() as int)
                &&& spt.alloc_model.meta_map[pt.deref().start_paddr() as int].pptr() == pt.meta_ptr
                &&& spt.frames.value().contains_key(pt.deref().start_paddr() as int)
                &&& spt.frames.value()[pt.deref().start_paddr() as int].ancestor_chain
                    == spt.frames.value()[entry.node.paddr() as int].ancestor_chain.insert(
                    entry.node.level_spec(&spt.alloc_model) as int,
                    IntermediatePageTableEntryView {
                        map_va: entry.va as int,
                        frame_pa: entry.node.paddr() as int,
                        in_frame_index: entry.idx as int,
                        map_to_pa: pt.deref().start_paddr() as int,
                        level: entry.node.level_spec(&spt.alloc_model),
                        phantom: PhantomData,
                    },
                )
            },
            _ => false,
        }
        &&& self is Frame <==> match self {
            ChildRef::Frame(pa, level, prop) => {
                &&& pa == entry.pte.frame_paddr() as usize
                &&& spt.ptes.value().contains_key(entry.pte.pte_paddr() as int)
                &&& spt.ptes.value()[entry.pte.pte_paddr() as int].map_to_pa == pa
            },
            _ => false,
        }
        &&& (self is PageTable || self is Frame) <==> entry.pte.is_present_spec()
        &&& self is None <==> {
            // &&& !spt.i_ptes.value().contains_key(entry.pte.pte_paddr() as int)
            // &&& !spt.ptes.value().contains_key(entry.pte.pte_paddr() as int)
            &&& !entry.pte.is_present_spec()
        }
        &&& self is None <==> match self {
            ChildRef::None => true,
            _ => false,
        }
    }
}

} // verus!
