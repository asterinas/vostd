// SPDX-License-Identifier: MPL-2.0
//! This module specifies the type of the children of a page table node.
use vstd::prelude::*;

use aster_common::prelude::frame::*;
use aster_common::prelude::page_table::*;
use aster_common::prelude::*;

use vstd_extra::cast_ptr::*;
use vstd_extra::ownership::*;

use ostd_specs::*;

use crate::{
    mm::{Paddr, PagingLevel},
    //    sync::RcuDrop,
};
use core::mem::ManuallyDrop;

verus! {

impl<C: PageTableConfig> Child<C> {
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(owner): Tracked<&EntryOwner<C>>
    )]
    pub fn into_pte(self) -> (res: C::E)
        requires
            owner.inv(),
            self.wf(*owner),
/*            self is PageTable ==> {
                &&& slot_own is Some
                &&& slot_own.unwrap()@.inv()
                &&& slot_perm is Some
                &&& slot_perm.unwrap()@.addr() == self.get_node().unwrap().ptr.addr()
                &&& slot_perm.unwrap()@.points_to.addr() == self.get_node().unwrap().ptr.addr()
                &&& slot_perm.unwrap()@.is_init()
                &&& slot_perm.unwrap()@.points_to.value().wf(*slot_own.unwrap()@)
                &&& slot_perm.unwrap()@.addr() == slot_own.unwrap()@.self_addr
            }*/
        ensures
/*            self is PageTable ==> res == self.into_pte_pt_spec(*slot_own.unwrap()@),
            self is Frame ==> res == self.into_pte_frame_spec(self.get_frame_tuple().unwrap()),
            self is None ==> res == self.into_pte_none_spec(),*/
    {
        match self {
            Child::PageTable(node) => {
                #[verus_spec(with Tracked(&owner.node.tracked_borrow().as_node.meta_perm.points_to))]
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
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(entry_own): Tracked<&EntryOwner<C>>,
    )]
    pub fn from_pte(pte: C::E, level: PagingLevel) -> (res: Self)
        requires
            pte.paddr() % PAGE_SIZE() == 0,
            pte.paddr() < MAX_PADDR(),
            old(regions).inv(),
            !old(regions).slots.contains_key(frame_to_index(pte.paddr())),
            old(regions).dropped_slots.contains_key(frame_to_index(pte.paddr())),
        ensures
            regions.inv(),
            !pte.is_present() ==> res == Child::<C>::None,
            pte.is_present() && pte.is_last(level) ==> res == Child::<C>::from_pte_frame_spec(
                pte,
                level,
            ),
            pte.is_present() && !pte.is_last(level) ==> res == Child::<C>::from_pte_pt_spec(
                pte.paddr(),
                *regions,
            ),
    {
        if !pte.is_present() {
            return Child::None;
        }
        let paddr = pte.paddr();

        if !pte.is_last(level) {
            assert(entry_own.is_node()) by { admit() };

            // SAFETY: The caller ensures that this node was created by
            // `into_pte`, so that restoring the forgotten reference is safe.
            #[verus_spec(with Tracked(regions), Tracked(&entry_own.node.tracked_borrow().as_node.meta_perm))]
            let node = PageTableNode::from_raw(paddr);
            //            debug_assert_eq!(node.level(), level - 1);
            return Child::PageTable(  /*RcuDrop::new(*/ node  /*)*/ );
        }
        Child::Frame(paddr, level, pte.prop())
    }
}

impl<C: PageTableConfig> ChildRef<'_, C> {
    /// Converts a PTE to a child.
    ///
    /// # Safety
    ///
    /// The PTE must be the output of a [`Child::into_pte`], where the child
    /// outlives the reference created by this function.
    ///
    /// The provided level must be the same with the level of the page table
    /// node that contains this PTE.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(
        with Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(entry_owner): Tracked<&EntryOwner<C>>
    )]
    pub fn from_pte(pte: &C::E, level: PagingLevel) -> (res: Self)
        requires
//            pte.wf(*entry_owner),
            entry_owner.inv(),
            pte.paddr() % PAGE_SIZE() == 0,
            pte.paddr() < MAX_PADDR(),
            !old(regions).slots.contains_key(frame_to_index(pte.paddr())),
            old(regions).dropped_slots.contains_key(frame_to_index(pte.paddr())),
            old(regions).inv(),
        ensures
            regions.inv(),
            res.wf(*entry_owner)
    {
        if !pte.is_present() {
            assert(entry_owner.is_absent()) by { admit() };
            return ChildRef::None;
        }
        let paddr = pte.paddr();

        if !pte.is_last(level) {
            assert(entry_owner.is_node()) by { admit() };

            // SAFETY: The caller ensures that the lifetime of the child is
            // contained by the residing node, and the physical address is
            // valid since the entry is present.
            #[verus_spec(with Tracked(regions), Tracked(&entry_owner.node.tracked_borrow().as_node.meta_perm))]
            let node = PageTableNodeRef::borrow_paddr(paddr);

            assert(node.inner.0.ptr.addr() == entry_owner.node.unwrap().as_node.meta_perm.addr()) by { admit() };

            // debug_assert_eq!(node.level(), level - 1);
            return ChildRef::PageTable(node);
        }

        assert(entry_owner.is_frame()) by { admit() };
        assert(entry_owner.frame.unwrap().mapped_pa == paddr) by { admit() };
        assert(entry_owner.frame.unwrap().prop == pte.prop()) by { admit() };

        ChildRef::Frame(paddr, level, pte.prop())
    }
}

} // verus!
