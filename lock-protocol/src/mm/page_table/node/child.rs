use std::clone;
use std::marker::PhantomData;
use std::mem::ManuallyDrop;

use vstd::prelude::*;

use crate::mm::cursor::spec_helpers;
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
    #[verifier::external_body]
    pub(super) fn from_pte(
        pte: &C::E,
        level: PagingLevel,
        Tracked(spt): Tracked<&SubPageTable<C>>,
    ) -> Self {
        if !pte.is_present() {
            return ChildRef::None;
        }
        let paddr = pte.frame_paddr();

        if !pte.is_last(level) {
            let node = PageTableNodeRef::borrow_paddr(paddr, Tracked(&spt.alloc_model));
            // debug_assert_eq!(node.level(), level - 1);
            return ChildRef::PageTable(node);
        }
        ChildRef::Frame(paddr, level, pte.prop())
    }
}

} // verus!
