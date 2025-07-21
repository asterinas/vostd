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

use super::MapTrackingStatus;
use super::PageTableNode;

use crate::exec;
use crate::spec::sub_pt::SubPageTable;

// use crate::prelude::{RawPageTableNode, PageProperty, Paddr, PagingLevel, DynPage};

verus! {

/// A child of a page table node.
///
/// This is a owning handle to a child of a page table node. If the child is
/// either a page table node or a page, it holds a reference count to the
/// corresponding page.
// #[derive(Debug)] // TODO: Debug for Child
pub enum Child<C: PageTableConfig> {
    /// A owning handle to a raw page table node.
    PageTable(PageTableNode),
    /// A reference of a child page table node, in the form of a physical
    /// address.
    PageTableRef(Paddr),
    /// A mapped frame.
    Frame(Frame, PageProperty),
    /// Mapped frames that are not tracked by handles.
    Untracked(Paddr, PagingLevel, PageProperty),
    Token(Token, PhantomData<C>),
    None,
}

// impl Child {
impl<C: PageTableConfig> Child<C> {
    #[verifier::allow_in_spec]
    pub fn is_none(&self) -> bool
        returns
            self is None,
    {
        match self {
            Child::None => true,
            _ => false,
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
    pub(super) fn into_pte(self) -> (res: C::E) {
        match self {
            Child::PageTable(pt) => {
                // let pt = ManuallyDrop::new(pt);
                C::E::new_pt(pt.start_paddr())
            },
            Child::PageTableRef(_) => {
                // panic!("`PageTableRef` should not be converted to PTE");
                // TODO
                C::E::new_absent()
            },
            Child::Frame(page, prop) => {
                let level = page.map_level();
                C::E::new_page(page.into_raw(), level, prop)
            },
            Child::Untracked(pa, level, prop) => C::E::new_page(pa, level, prop),
            Child::None => C::E::new_absent(),
            Child::Token(token, _) => C::E::new_token(token),
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
    // TODO: Implement the conversion from PTE.
    #[verifier::external_body]
    pub(super) fn from_pte(
        pte: C::E,
        level: PagingLevel,
        Tracked(spt): Tracked<&SubPageTable>,
    ) -> Self {
        if !pte.is_present(Tracked(spt)) {
            // let paddr = pte.paddr();
            // if paddr == 0 {
            //     return Child::None;
            // } else {
            //     // SAFETY: The physical address is written as a valid token.
            //     return Child::Token(unsafe { Token::from_raw_inner(paddr) });
            // }
            // TODO: We currently do not model Child::Token
            return Child::None;
        }
        let paddr = pte.frame_paddr();

        // TODO: Model is_last
        // if !pte.is_last(level) {
        // SAFETY: The physical address is valid and the PTE already owns
        // the reference to the page.
        // unsafe { inc_frame_ref_count(paddr) }; // TODO
        // SAFETY: The physical address points to a valid page table node
        // at the given level.
        // let pt = unsafe { PageTableNode::from_raw(paddr) };
        let pt = PageTableNode::from_raw(paddr);
        assert(pt.ptr == paddr);
        assert(paddr == pte.frame_paddr());
        assert(pt.ptr == pte.frame_paddr());
        // debug_assert_eq!(pt.level(), level - 1);
        return Child::PageTable(pt);
        // }

        // TODO: model is_tracked
        // match is_tracked {
        //     MapTrackingStatus::Tracked => {
        //         // SAFETY: The physical address points to a valid page.
        //         let page = unsafe { Frame::<dyn AnyFrameMeta>::from_raw(paddr) };
        //         Child::Frame(page, pte.prop())
        //     }
        //     MapTrackingStatus::Untracked => Child::Untracked(paddr, level, pte.prop()),
        //     MapTrackingStatus::NotApplicable => panic!("Invalid tracking status"),
        // }
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
    // TODO: Implement the conversion from PTE.
    // #[verifier::external_body]
    pub(super) fn ref_from_pte(
        pte: &C::E,
        level: PagingLevel,
        clone_raw: bool,
        Tracked(spt): Tracked<&SubPageTable>,
    ) -> (res: Self)
        requires
            spt.wf(),
            pte.pte_paddr() == exec::get_pte_from_addr_spec(pte.pte_paddr(), spt).pte_addr,
            pte.frame_paddr() == exec::get_pte_from_addr_spec(pte.pte_paddr(), spt).frame_pa,
        ensures
            if (spt.ptes.value().contains_key(pte.pte_paddr() as int)) {
                if (clone_raw) {
                    match res {
                        Child::PageTable(_) => true,
                        _ => false,
                    }
                } else {
                    match res {
                        Child::PageTableRef(pt) => pt == pte.frame_paddr() as usize
                            && spt.frames.value().contains_key(pt as int),
                        _ => false,
                    }
                }
            } else {
                match res {
                    Child::None => true,
                    _ => false,
                }
            },
    {
        if !pte.is_present(Tracked(spt)) {
            // let paddr = pte.paddr();
            // if paddr == 0 {
            //     return Child::None;
            // } else {
            //     // SAFETY: The physical address is written as a valid token.
            //     return Child::Token(unsafe { Token::from_raw_inner(paddr) });
            // }
            // TODO: We currently do not model Child::Token
            return Child::None;
        }
        let paddr = pte.frame_paddr();

        // TODO: Model is_last
        // if !pte.is_last(level) {
        if clone_raw {
            // SAFETY: The physical address is valid and the PTE already owns
            // the reference to the page.
            // unsafe { inc_frame_ref_count(paddr) }; // TODO
            // SAFETY: The physical address points to a valid page table node
            // at the given level.
            // let pt = unsafe { PageTableNode::from_raw(paddr) };
            let pt = PageTableNode::from_raw(paddr);
            assert(pt.ptr == paddr);
            assert(paddr == pte.frame_paddr());
            assert(pt.ptr == pte.frame_paddr());
            // debug_assert_eq!(pt.level(), level - 1);
            return Child::PageTable(pt);
        } else {
            return Child::PageTableRef(paddr);
        }
        // }

        // TODO: model is_tracked
        // match is_tracked {
        //     MapTrackingStatus::Tracked => {
        //         // SAFETY: The physical address is valid and the PTE already owns
        //         // the reference to the page.
        //         // unsafe { inc_frame_ref_count(paddr) }; // TODO
        //         // SAFETY: The physical address points to a valid page.
        //         let page = unsafe { Frame::<T>::from_raw(paddr) };
        //         Child::Frame(page, pte.prop())
        //     }
        //     MapTrackingStatus::Untracked => Child::Untracked(paddr, level, pte.prop()),
        //     MapTrackingStatus::NotApplicable =>
        //         // panic!("Invalid tracking status"),
        //         Child::None, // TODO

        // }
    }
}

} // verus!
