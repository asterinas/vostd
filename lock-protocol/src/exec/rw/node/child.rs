use core::mem::ManuallyDrop;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::vpanic;

use crate::spec::{common::*, utils::*};
use super::super::{common::*, types::*, mem_content::*};
use super::super::pte::{
    Pte, 
    page_prop::PageProperty,
    page_table_entry_trait::*,
};
use super::PageTableNode;

verus! {

/// A child of a page table node.
// #[derive(Debug)]
pub enum Child {
    /// A owning handle to a raw page table node.
    PageTable(PageTableNode, Tracked<SpecInstance>, Ghost<NodeId>),
    /// A reference of a child page table node, in the form of a physical
    /// address.
    PageTableRef(Paddr, Tracked<SpecInstance>, Ghost<NodeId>),
    /// A mapped frame.
    // Frame(Frame<dyn AnyFrameMeta>, PageProperty),
    Frame(Paddr, PagingLevel, PageProperty),
    /// Mapped frames that are not tracked by handles.
    // Untracked(Paddr, PagingLevel, PageProperty),
    // Status(Status),
    None,

    Unimplemented,
}

impl Child {
    #[verifier::external_body]
    pub proof fn axiom_no_huge_page(self)
        ensures 
            self is Frame ==> self->Frame_1 == 1,
    {}

    pub open spec fn wf(&self, mem: &MemContent) -> bool {
        match *self {
            Self::PageTable(pt, inst, nid) => {
                &&& pt.wf(mem)
                &&& inst@.cpu_num() == GLOBAL_CPU_NUM
                &&& NodeHelper::valid_nid(nid@)
            },
            Self::PageTableRef(pa, inst, nid) => {
                &&& valid_paddr(pa)
                &&& inst@.cpu_num() == GLOBAL_CPU_NUM
                &&& NodeHelper::valid_nid(nid@)
            },
            Self::Frame(pa, level, _) => {
                &&& valid_paddr(pa)
                &&& level == 1 // TODO: We don't support huge pages yet.
            }
            _ => true,
        }
    }

    pub open spec fn wf_into_pte(
        &self,
        pte: Pte,
    ) -> bool 
    {
        match *self {
            Child::PageTable(pt, inst, nid) =>
                pte.wf_new_pt(pt.start_paddr_spec(), inst@, nid@),
            Child::PageTableRef(_, _, _) => true,
            Child::Frame(paddr, level, prop) =>
                pte.wf_new_page(paddr, level, prop),
            Child::None => pte.wf_new_absent(),
            Child::Unimplemented => pte.wf_new_absent(),
        }
    }

    /// Converts a child into a owning PTE.
    ///
    /// By conversion it loses information about whether the page is tracked
    /// or not. Also it loses the level information. However, the returned PTE
    /// takes the ownership (reference count) of the child.
    ///
    /// Usually this is for recording the PTE into a page table node. When the
    /// child is needed again by reading the PTE of a page table node, extra
    /// information should be provided using the [`Child::from_pte`] method.
    pub fn into_pte(
        self,
        mem: &MemContent,
    ) -> (res: Pte)
        requires
            self.wf(mem),
            !(self is PageTableRef),
        ensures
            self.wf_into_pte(res),
    {
        match self {
            Child::PageTable(pt, inst, nid) => {
                let paddr: Paddr = pt.start_paddr(mem);
                let pt = ManuallyDrop::new(pt);
                Pte::new_pt(paddr, inst, nid)
            },
            Child::PageTableRef(_, _, _) => {
                // vpanic!("`PageTableRef` should not be converted to PTE");
                unreached()
            },
            // Child::Frame(page, prop) => {
            //     let level = page.map_level();
            //     Pte::new_page(page.into_raw(), level, prop)
            // }
            Child::Frame(paddr, level, prop) => {
                Pte::new_page(paddr, level, prop)
            },
            // Child::Untracked(pa, level, prop) => Pte::new_page(pa, level, prop),
            Child::None => Pte::new_absent(),
            // Child::Status(status) => Pte::new_status(status),

            Child::Unimplemented => Pte::new_absent(),
        }
    }

    pub open spec fn wf_from_pte(
        &self, 
        pte: Pte,
        level: PagingLevel,
    ) -> bool {
        if !pte.inner.is_present() {
            if pte.inner.paddr() == 0 { *self is None }
            else { *self is Unimplemented }
        } else { // pte.inner.is_present()
            if !pte.inner.is_last(level) {
                &&& *self is PageTable
                &&& self->PageTable_0 =~= 
                    PageTableNode::from_raw_spec(pte.inner.paddr())
                &&& self->PageTable_1@ =~= pte.inst@->Some_0
                &&& self->PageTable_2@ =~= pte.nid()
            } else { // pte.inner.is_last(level)
                &&& *self is Frame
                &&& self->Frame_0 == pte.inner.paddr()
                &&& self->Frame_1 == level
                &&& self->Frame_2 =~= pte.inner.prop()
            }
        }
    }

    /// Converts a PTE back to a child.
    ///
    /// # Safety
    ///
    /// The provided PTE must be originated from [`Child::into_pte`]. And the
    /// provided information (level and tracking status) must be the same with
    /// the lost information during the conversion. Strictly speaking, the
    /// provided arguments must be compatible with the original child (
    /// specified by [`Child::is_compatible`]).
    ///
    /// This method should be only used no more than once for a PTE that has
    /// been converted from a child using the [`Child::into_pte`] method.
    pub fn from_pte(
        pte: Pte,
        level: PagingLevel,
        // is_tracked: MapTrackingStatus,
        mem: &MemContent,
    ) -> (res: Self) 
        requires
            pte.wf(),
            pte.wf_with_node_level(level),
            1 <= level <= 4,
        ensures
            res.wf(mem),
            res.wf_from_pte(pte, level),
            !(res is PageTableRef),
            res is Frame ==> res->Frame_1 == level,
    {
        if !pte.inner.is_present() {
            let paddr = pte.inner.paddr();
            if paddr == 0 {
                return Child::None;
            } else {
                // SAFETY: The physical address is written as a valid status.
                // return Child::Status(unsafe { Status::from_raw_inner(paddr) });
                return Child::Unimplemented;
            }
        }

        let paddr = pte.inner.paddr();

        if !pte.inner.is_last(level) {
            // SAFETY: The physical address points to a valid page table node
            // at the given level.
            // let pt = unsafe { PageTableNode::from_raw(paddr) };
            // debug_assert_eq!(pt.level(), level - 1);
            let pt = PageTableNode::from_raw(
                paddr, 
                mem, 
                Ghost(pte.nid()),
                Ghost(pte.inst_id()),
            );
            assert(pte.inst@ is Some);
            assert(pte.nid@ is Some);
            return Child::PageTable(
                pt,
                Tracked(pte.tracked_inst()), 
                Ghost(pte.nid()),
            );
        }

        // match is_tracked {
        //     MapTrackingStatus::Tracked => {
        //         // SAFETY: The physical address points to a valid page.
        //         let page = unsafe { Frame::<dyn AnyFrameMeta>::from_raw(paddr) };
        //         Child::Frame(page, pte.prop())
        //     }
        //     MapTrackingStatus::Untracked => Child::Untracked(paddr, level, pte.prop()),
        //     MapTrackingStatus::NotApplicable => panic!("Invalid tracking status"),
        // }
        Child::Frame(pte.inner.paddr(), level, pte.inner.prop())
    }


    pub open spec fn wf_ref_from_pte(
        &self,
        pte: Pte,
        level: PagingLevel,
        clone_raw: bool,
    ) -> bool {
        if !pte.inner.is_present() {
            if pte.inner.paddr() == 0 { *self is None }
            else { *self is Unimplemented }
        } else { // pte.inner.is_present()
            if !pte.inner.is_last(level) {
                if clone_raw {
                    &&& *self is PageTable
                    &&& self->PageTable_0 =~= 
                        PageTableNode::from_raw_spec(pte.inner.paddr())
                    &&& self->PageTable_1@ =~= pte.inst@->Some_0
                    &&& self->PageTable_2@ =~= pte.nid()
                } else {
                    &&& *self is PageTableRef
                    &&& self->PageTableRef_0 == pte.inner.paddr()
                    &&& self->PageTableRef_1@ =~= pte.inst@->Some_0
                    &&& self->PageTableRef_2@ =~= pte.nid()
                }
            } else { // pte.inner.is_last(level)
                &&& *self is Frame
                &&& self->Frame_0 == pte.inner.paddr()
                &&& self->Frame_1 == level
                &&& self->Frame_2 =~= pte.inner.prop()
            }
        }
    }

    /// Gains an extra reference to the child.
    ///
    /// If the child is a frame, it increases the reference count of the frame.
    ///
    /// If the child is a page table node, the returned value depends on
    /// `clone_raw`:
    ///  - If `clone_raw` is `true`, it returns a new owning handle to the page
    ///    table node ([`Child::PageTable`]).
    ///  - If `clone_raw` is `false`, it returns a reference to the page table
    ///    node ([`Child::PageTableRef`]).
    ///
    /// # Safety
    ///
    /// The provided PTE must be originated from [`Child::into_pte`], which is
    /// the same requirement as the [`Child::from_pte`] method.
    ///
    /// This method must not be used with a PTE that has been restored to a
    /// child using the [`Child::from_pte`] method.
    pub fn ref_from_pte(
        pte: &Pte,
        level: PagingLevel,
        // is_tracked: MapTrackingStatus,
        clone_raw: bool,
        mem: &MemContent,
    ) -> (res: Self) 
        requires
            pte.wf(),
            pte.wf_with_node_level(level),
            1 <= level <= 4,
        ensures
            res.wf(mem),
            res.wf_ref_from_pte(*pte, level, clone_raw),
            !clone_raw ==> !(res is PageTable),
            res is Frame ==> res->Frame_1 == level,
    {
        if !pte.inner.is_present() {
            let paddr = pte.inner.paddr();
            if paddr == 0 {
                return Child::None;
            } else {
                // SAFETY: The physical address is written as a valid status.
                // return Child::Status(unsafe { Status::from_raw_inner(paddr) });
                return Child::Unimplemented;
            }
        }

        let paddr = pte.inner.paddr();

        if !pte.inner.is_last(level) {
            if clone_raw {
                // SAFETY: The physical address is valid and the PTE already owns
                // the reference to the page.
                // unsafe { inc_frame_ref_count(paddr) };
                // SAFETY: The physical address points to a valid page table node
                // at the given level.
                // let pt = unsafe { PageTableNode::from_raw(paddr) };
                let pt = PageTableNode::from_raw(
                    paddr, 
                    mem,
                    Ghost(pte.nid()),
                    Ghost(pte.inst_id()),
                );
                // debug_assert_eq!(pt.level(), level - 1);
                assert(pte.inst@ is Some);
                assert(pte.nid@ is Some);
                return Child::PageTable(
                    pt, 
                    Tracked(pte.tracked_inst()), 
                    Ghost(pte.nid()),
                );
            } else {
                assert(pte.inst@ is Some);
                assert(pte.nid@ is Some);
                return Child::PageTableRef(
                    paddr,
                    Tracked(pte.tracked_inst()), 
                    Ghost(pte.nid()),
                );
            }
        }

        // match is_tracked {
        //     MapTrackingStatus::Tracked => {
        //         // SAFETY: The physical address is valid and the PTE already owns
        //         // the reference to the page.
        //         // unsafe { inc_frame_ref_count(paddr) };
        //         // SAFETY: The physical address points to a valid page.
        //         // let page = unsafe { Frame::<dyn AnyFrameMeta>::from_raw(paddr) };
        //         // Child::Frame(page, pte.prop())
        //         Child::Frame;
        //     }
        //     MapTrackingStatus::Untracked => {
        //         // Child::Untracked(paddr, level, pte.prop())
        //         Child::Unimplemented
        //     },
        //     MapTrackingStatus::NotApplicable => panic!("Invalid tracking status"),
        // }
        Child::Frame(pte.inner.paddr(), level, pte.inner.prop())
    }

}

}