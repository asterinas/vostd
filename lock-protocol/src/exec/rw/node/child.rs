use core::mem::ManuallyDrop;
use core::ops::Deref;

use vstd::prelude::*;
use vstd::vpanic;

use crate::spec::{common::*, utils::*};
use super::super::{common::*, types::*, frame::*};
use super::super::pte::{Pte, page_prop::PageProperty, page_table_entry_trait::*};
use super::{PageTableNode, PageTableNodeRef, PageTableWriteLock};

verus! {

/// A page table entry that owns the child of a page table node if present.
// #[derive(Debug)]
pub enum Child {
    /// A child page table node.
    PageTable(PageTableNode),
    /// Physical address of a mapped physical frame.
    ///
    /// It is associated with the virtual page property and the level of the
    /// mapping node, which decides the size of the frame.
    Frame(Paddr, PagingLevel, PageProperty),
    None,
}

impl Child {
    pub axiom fn axiom_no_huge_page(self)
        ensures
            self is Frame ==> self->Frame_1 == 1,
    ;

    pub open spec fn wf(&self) -> bool {
        match *self {
            Self::PageTable(node) => { node.wf() },
            Self::Frame(pa, level, _) => {
                &&& valid_paddr(pa)
                &&& level == 1  // TODO: We don't support huge pages yet.

            },
            _ => true,
        }
    }

    pub open spec fn wf_with_node(&self, idx: nat, node: PageTableNode) -> bool {
        match *self {
            Child::PageTable(pt) => {
                &&& node.level_spec() == (pt.level_spec() + 1) as PagingLevel
                &&& node.inst@.id() == pt.inst@.id()
                &&& NodeHelper::get_child(node.nid@, idx) == pt.nid@
            },
            Child::Frame(paddr, level, prop) => node.level_spec() == level,
            Child::None => true,
        }
    }

    #[verifier::allow_in_spec]
    pub fn is_none(&self) -> bool
        requires
            self.wf(),
        returns
            self is None,
    {
        if let Child::None = *self {
            true
        } else {
            false
        }
    }

    pub open spec fn wf_into_pte(&self, pte: Pte) -> bool {
        match *self {
            Child::PageTable(node) => {
                &&& pte.wf_new_pt(node.start_paddr(), node.inst@, node.nid@)
                &&& pte.is_pt((node.level_spec() + 1) as PagingLevel)
                &&& pte.inner.paddr() == node.start_paddr()
            },
            Child::Frame(paddr, level, prop) => {
                &&& pte.wf_new_page(paddr, level, prop)
                &&& pte.is_frame(level) || pte.is_marked()
            },
            Child::None => {
                &&& pte.wf_new_absent()
                &&& pte.is_none()
            },
        }
    }

    pub fn into_pte(self) -> (res: Pte)
        requires
            self.wf(),
        ensures
            self.wf_into_pte(res),
    {
        match self {
            Child::PageTable(pt) => {
                let paddr: Paddr = pt.start_paddr();
                let tracked inst = pt.inst.borrow().clone();
                let ghost nid = pt.nid@;
                let _ = ManuallyDrop::new(pt);
                Pte::new_pt(paddr, Tracked(inst), Ghost(nid))
            },
            Child::Frame(paddr, level, prop) => { Pte::new_page(paddr, level, prop) },
            Child::None => Pte::new_absent(),
        }
    }

    pub open spec fn wf_from_pte(&self, pte: Pte, level: PagingLevel) -> bool {
        if pte.is_none() {
            *self is None
        } else if pte.is_pt(level) {
            &&& *self is PageTable
            &&& self->PageTable_0 =~= PageTableNode::from_raw_spec(pte.inner.paddr())
            &&& self->PageTable_0.start_paddr() == pte.inner.paddr()
            &&& self->PageTable_0.nid@ == pte.nid()
            &&& self->PageTable_0.inst@.cpu_num() == GLOBAL_CPU_NUM
            &&& self->PageTable_0.inst@.id() == pte.inst_id()
            &&& self->PageTable_0.level_spec() == (level - 1) as PagingLevel
        } else {
            &&& *self is Frame
            &&& self->Frame_0 == pte.inner.paddr()
            &&& self->Frame_1 == level
            &&& self->Frame_2 =~= pte.inner.prop()
        }
    }

    pub fn from_pte(pte: Pte, level: PagingLevel) -> (res: Self)
        requires
            pte.wf(level),
            1 <= level <= 4,
        ensures
            res.wf(),
            res.wf_from_pte(pte, level),
    {
        let paddr = pte.inner.paddr();
        if !pte.inner.is_present() && paddr == 0 {
            return Child::None;
        }
        if pte.inner.is_present() && !pte.inner.is_last(level) {
            let node = PageTableNode::from_raw(
                paddr,
                Ghost(pte.nid()),
                Ghost(pte.inst_id()),
                Ghost((level - 1) as PagingLevel),
            );
            return Child::PageTable(node);
        }
        let res = Child::Frame(paddr, level, pte.inner.prop());
        proof {
            res.axiom_no_huge_page();
        }
        res
    }
}

pub enum ChildRef<'a> {
    /// A child page table node.
    PageTable(PageTableNodeRef<'a>),
    /// Physical address of a mapped physical frame.
    ///
    /// It is associated with the virtual page property and the level of the
    /// mapping node, which decides the size of the frame.
    Frame(Paddr, PagingLevel, PageProperty),
    None,
}

impl<'a> ChildRef<'a> {
    pub axiom fn axiom_no_huge_page(self)
        ensures
            self is Frame ==> self->Frame_1 == 1,
    ;

    pub open spec fn wf(&self) -> bool {
        match *self {
            Self::PageTable(node_ref) => { node_ref.wf() },
            Self::Frame(pa, level, _) => {
                &&& valid_paddr(pa)
                &&& level == 1  // TODO: We don't support huge pages yet.

            },
            _ => true,
        }
    }

    pub open spec fn wf_from_pte(&self, pte: Pte, level: PagingLevel) -> bool {
        if pte.is_none() {
            *self is None
        } else if pte.is_pt(level) {
            &&& *self is PageTable
            &&& self->PageTable_0 == PageTableNodeRef::borrow_paddr_spec(pte.inner.paddr())
            &&& self->PageTable_0.deref().start_paddr() == pte.inner.paddr()
            &&& self->PageTable_0.deref().nid@ == pte.nid()
            &&& self->PageTable_0.deref().inst@.cpu_num() == GLOBAL_CPU_NUM
            &&& self->PageTable_0.deref().inst@.id() == pte.inst_id()
            &&& self->PageTable_0.deref().level_spec() == (level - 1) as PagingLevel
        } else {
            &&& *self is Frame
            &&& self->Frame_0 == pte.inner.paddr()
            &&& self->Frame_1 == level
            &&& self->Frame_2 =~= pte.inner.prop()
        }
    }

    pub fn from_pte<'b>(pte: &'b Pte, level: PagingLevel) -> (res: ChildRef<'a>)
        requires
            pte.wf(level),
            1 <= level <= 4,
        ensures
            res.wf(),
            res.wf_from_pte(*pte, level),
    {
        let paddr = pte.inner.paddr();
        if !pte.inner.is_present() && paddr == 0 {
            return ChildRef::None;
        }
        if pte.inner.is_present() && !pte.inner.is_last(level) {
            let node = PageTableNodeRef::borrow_paddr(
                paddr,
                Ghost(pte.nid()),
                Ghost(pte.inst_id()),
                Ghost((level - 1) as PagingLevel),
            );
            return ChildRef::PageTable(node);
        }
        let res = ChildRef::Frame(paddr, level, pte.inner.prop());
        proof {
            res.axiom_no_huge_page();
        }
        res
    }
}

} // verus!
