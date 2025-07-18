use core::mem::ManuallyDrop;
use core::ops::Deref;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::vpanic;

use crate::spec::{common::*, utils::*};
use super::super::{common::*, types::*};
use super::super::pte::{Pte, page_prop::PageProperty, page_table_entry_trait::*};
use super::{PageTableNode, PageTableNodeRef, PageTableGuard};

verus! {

/// A page table entry that owns the child of a page table node if present.
// #[derive(Debug)]
pub enum Child {
    /// A child page table node.
    // PageTable(RcuDrop<PageTableNode>, Tracked<SpecInstance>, Ghost<NodeId>),
    PageTable(PageTableNode, Tracked<SpecInstance>, Ghost<NodeId>),
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
            Self::PageTable(node, inst, nid) => {
                &&& node.wf()
                &&& node.inst@.id() == inst@.id()
                &&& node.nid@ == nid@
                &&& inst@.cpu_num() == GLOBAL_CPU_NUM
                &&& NodeHelper::valid_nid(nid@)
            },
            Self::Frame(pa, level, _) => {
                &&& valid_paddr(pa)
                &&& level == 1  // TODO: We don't support huge pages yet.

            },
            _ => true,
        }
    }

    pub open spec fn wf_with_node(&self, idx: nat, node: PageTableGuard) -> bool {
        match *self {
            Child::PageTable(pt, inst, nid) => {
                &&& node.deref().deref().level_spec() == (pt.level_spec() + 1) as PagingLevel
                &&& node.inst_id() == inst@.id()
                &&& NodeHelper::get_child(node.nid(), idx) == nid@
            },
            Child::Frame(paddr, level, prop) => { &&& node.deref().deref().level_spec() == level },
            Child::None => true,
        }
    }

    pub open spec fn wf_into_pte(&self, pte: Pte) -> bool {
        match *self {
            Child::PageTable(node, inst, nid) => {
                &&& pte.wf_new_pt(node.start_paddr(), inst@, nid@)
                &&& pte.inner.is_present()
                &&& !pte.inner.is_last((node.level_spec() + 1) as PagingLevel)
            },
            Child::Frame(paddr, level, prop) => {
                &&& pte.wf_new_page(paddr, level, prop)
                &&& pte.inner.is_present()
                &&& pte.inner.is_last(level)
            },
            Child::None => {
                &&& pte.wf_new_absent()
                &&& !pte.inner.is_present()
            },
        }
    }

    pub fn into_pte(self) -> (res: Pte)
        requires
            self.wf(),
        ensures
            self.wf_into_pte(res),
            res.wf(),
    {
        match self {
            Child::PageTable(node, inst, nid) => {
                let paddr = node.start_paddr();
                let _ = ManuallyDrop::new(node);
                Pte::new_pt(paddr, inst, nid)
            },
            Child::Frame(paddr, level, prop) => { Pte::new_page(paddr, level, prop) },
            Child::None => Pte::new_absent(),
        }
    }

    pub open spec fn wf_from_pte(&self, pte: Pte, level: PagingLevel) -> bool {
        if !pte.inner.is_present() && pte.inner.paddr() == 0 {
            *self is None
        } else if pte.inner.is_present() && !pte.inner.is_last(level) {
            &&& *self is PageTable
            &&& self->PageTable_0 =~= PageTableNode::from_raw_spec(pte.inner.paddr())
            &&& self->PageTable_1@ =~= pte.inst@->Some_0
            &&& self->PageTable_2@ =~= pte.nid()
        } else {
            &&& *self is Frame
            &&& self->Frame_0 == pte.inner.paddr()
            &&& self->Frame_1 == level
            &&& self->Frame_2 =~= pte.inner.prop()
        }
    }

    pub fn from_pte(pte: Pte, level: PagingLevel) -> (res: Self)
        requires
            pte.wf(),
            pte.wf_with_node_level(level),
            1 <= level <= 4,
        ensures
            res.wf(),
            res.wf_from_pte(pte, level),
            res is Frame ==> res->Frame_1 == level,
    {
        let paddr = pte.inner.paddr();
        if !pte.inner.is_present() && paddr == 0 {
            return Child::None;
        }
        if pte.inner.is_present() && !pte.inner.is_last(level) {
            let node = PageTableNode::from_raw(paddr, Ghost(pte.nid()), Ghost(pte.inst_id()));
            return Child::PageTable(node, Tracked(pte.tracked_inst()), Ghost(pte.nid()));
        }
        let res = Child::Frame(paddr, level, pte.inner.prop());
        proof {
            res.axiom_no_huge_page();
        }
        res
    }
}

/// A reference to the child of a page table node.
// #[derive(Debug)]
pub enum ChildRef<'a> {
    /// A child page table node.
    PageTableRef(PageTableNodeRef<'a>, Tracked<SpecInstance>, Ghost<NodeId>),
    /// Physical address of a mapped physical frame.
    ///
    /// It is associated with the virtual page property and the level of the
    /// mapping node, which decides the size of the frame.
    Frame(Paddr, PagingLevel, PageProperty),
    None,
}

impl ChildRef<'_> {
    pub axiom fn axiom_no_huge_page(self)
        ensures
            self is Frame ==> self->Frame_1 == 1,
    ;

    pub open spec fn wf(&self) -> bool {
        match *self {
            Self::PageTableRef(node_ref, inst, nid) => {
                &&& node_ref.wf()
                &&& node_ref.inst@.id() == inst@.id()
                &&& node_ref.nid@ == nid@
                &&& inst@.cpu_num() == GLOBAL_CPU_NUM
                &&& NodeHelper::valid_nid(nid@)
            },
            Self::Frame(pa, level, _) => {
                &&& valid_paddr(pa)
                &&& level == 1  // TODO: We don't support huge pages yet.

            },
            _ => true,
        }
    }

    pub open spec fn wf_from_pte(&self, pte: Pte, level: PagingLevel) -> bool {
        if !pte.inner.is_present() && pte.inner.paddr() == 0 {
            *self is None
        } else if pte.inner.is_present() && !pte.inner.is_last(level) {
            &&& *self is PageTableRef
            &&& self->PageTableRef_0 == PageTableNodeRef::borrow_paddr_spec(pte.inner.paddr())
            &&& self->PageTableRef_1@ =~= pte.inst@->Some_0
            &&& self->PageTableRef_2@ =~= pte.nid()
        } else {
            &&& *self is Frame
            &&& self->Frame_0 == pte.inner.paddr()
            &&& self->Frame_1 == level
            &&& self->Frame_2 =~= pte.inner.prop()
        }
    }

    pub fn from_pte<'a>(pte: &'a Pte, level: PagingLevel) -> (res: ChildRef<'a>)
        requires
            pte.wf(),
            pte.wf_with_node_level(level),
            1 <= level <= 4,
        ensures
            res.wf(),
            res.wf_from_pte(*pte, level),
            res is Frame ==> res->Frame_1 == level,
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
            );
            return ChildRef::PageTableRef(node, Tracked(pte.tracked_inst()), Ghost(pte.nid()));
        }
        let res = ChildRef::Frame(paddr, level, pte.inner.prop());
        proof {
            res.axiom_no_huge_page();
        }
        res
    }
}

} // verus!
