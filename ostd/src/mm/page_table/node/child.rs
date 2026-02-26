// SPDX-License-Identifier: MPL-2.0
//! This module specifies the type of the children of a page table node.
use vstd::prelude::*;
use vstd_extra::external::manually_drop_deref_spec;

use crate::mm::frame::meta::mapping::{frame_to_index, meta_addr, meta_to_frame};
use crate::mm::frame::Frame;
use crate::mm::page_table::*;
use crate::specs::arch::mm::{NR_ENTRIES, NR_LEVELS, PAGE_SIZE};
use crate::specs::arch::paging_consts::PagingConsts;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;

use vstd_extra::cast_ptr::*;
use vstd_extra::drop_tracking::*;
use vstd_extra::ownership::*;

use crate::specs::*;

use crate::{
    mm::{page_prop::PageProperty, Paddr, PagingConstsTrait, PagingLevel, Vaddr},
    //    sync::RcuDrop,
};
use vstd_extra::drop_tracking::ManuallyDrop;

use super::*;

verus! {

/// A page table entry that owns the child of a page table node if present.
pub enum Child<C: PageTableConfig> {
    /// A child page table node.
    pub PageTable(PageTableNode<C>),
    /// Physical address of a mapped physical frame.
    ///
    /// It is associated with the virtual page property and the level of the
    /// mapping node, which decides the size of the frame.
    pub Frame(Paddr, PagingLevel, PageProperty),
    pub None,
}

impl<C: PageTableConfig> Child<C> {
    pub open spec fn get_node(self) -> Option<PageTableNode<C>> {
        match self {
            Self::PageTable(node) => Some(node),
            _ => None,
        }
    }

    pub open spec fn get_frame_tuple(self) -> Option<(Paddr, PagingLevel, PageProperty)> {
        match self {
            Self::Frame(paddr, level, prop) => Some((paddr, level, prop)),
            _ => None,
        }
    }

    /// Returns whether the child is not present.
    #[vstd::contrib::auto_spec]
    pub fn is_none(&self) -> (b: bool) {
        matches!(self, Child::None)
    }
}

/// A reference to the child of a page table node.
pub enum ChildRef<'a, C: PageTableConfig> {
    /// A child page table node.
    PageTable(PageTableNodeRef<'a, C>),
    /// Physical address of a mapped physical frame.
    ///
    /// It is associated with the virtual page property and the level of the
    /// mapping node, which decides the size of the frame.
    Frame(Paddr, PagingLevel, PageProperty),
    None,
}

impl<'a, C: PageTableConfig> Inv for ChildRef<'a, C> {
    open spec fn inv(self) -> bool {
        true
    }
}

impl<'a, C: PageTableConfig> OwnerOf for ChildRef<'a, C> {
    type Owner = EntryOwner<C>;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        match self {
            Self::PageTable(node) => {
                &&& owner.is_node()
                &&& node.inner.0.ptr.addr() == owner.node.unwrap().meta_perm.addr()
            },
            Self::Frame(paddr, level, prop) => {
                &&& owner.is_frame()
                &&& owner.frame.unwrap().mapped_pa == paddr
                &&& owner.frame.unwrap().prop == prop
            },
            Self::None => owner.is_absent(),
        }
    }
}

impl<'a, C: PageTableConfig> Inv for Child<C> {
    open spec fn inv(self) -> bool {
        true
    }
}

impl<C: PageTableConfig> OwnerOf for Child<C> {
    type Owner = EntryOwner<C>;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        match self {
            Self::PageTable(node) => {
                &&& owner.is_node()
                &&& node.ptr.addr() == owner.node.unwrap().meta_perm.addr()
                &&& node.index() == frame_to_index(meta_to_frame(node.ptr.addr()))
            },
            Self::Frame(paddr, level, prop) => {
                &&& owner.is_frame()
                &&& owner.frame.unwrap().mapped_pa == paddr
                &&& owner.frame.unwrap().prop == prop
                &&& level == owner.parent_level
            },
            Self::None => owner.is_absent(),
        }
    }
}

impl<C: PageTableConfig> Child<C> {
    #[verus_spec(
        with Tracked(owner): Tracked<&EntryOwner<C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>
    )]
    pub fn into_pte(self) -> (res: C::E)
        requires
            owner.inv(),
            old(regions).inv(),
            self.wf(*owner),
            owner.is_node() ==> old(regions).slots.contains_key(
                frame_to_index(owner.meta_slot_paddr().unwrap()),
            ),
        ensures
            regions.inv(),
            res.paddr() % PAGE_SIZE == 0,
            res.paddr() < MAX_PADDR,
            owner.match_pte(res, owner.parent_level),
            owner.is_node() ==> !regions.slots.contains_key(
                frame_to_index(owner.meta_slot_paddr().unwrap()),
            ),
            owner.is_node() ==> regions.slots =~= old(regions).slots.remove(
                frame_to_index(owner.meta_slot_paddr().unwrap()),
            ),
            owner.is_node() ==> forall|i: usize|
                #![trigger regions.slot_owners[i]]
                i != frame_to_index(owner.meta_slot_paddr().unwrap()) ==> regions.slot_owners[i]
                    == old(regions).slot_owners[i],
            !owner.is_node() ==> *regions =~= *old(regions),
    {
        proof {
            C::E::new_properties();
        }

        match self {
            Child::PageTable(node) => {
                let ghost node_owner = owner.node.unwrap();

                #[verus_spec(with Tracked(&owner.node.tracked_borrow().meta_perm.points_to))]
                let paddr = node.start_paddr();

                let ghost node_index = frame_to_index(meta_to_frame(node.ptr.addr()));

                proof {
                    let tracked _slot_perm = regions.slots.tracked_remove(node_index);
                }

                let _ = ManuallyDrop::new(node, Tracked(regions));

                proof {
                    assert(regions.slots =~= old(regions).slots.remove(node_index));
                    assert(regions.slot_owners[node_index].inv()) by { admit(); }
                    assert forall|i: usize| #[trigger]
                        regions.slot_owners.contains_key(i) implies {
                            &&& regions.slot_owners[i].inv()
                        } by {
                        if i == node_index {
                        } else {
                            assert(old(regions).slot_owners[i] == regions.slot_owners[i]);
                        }
                    };
                    assert forall|i: usize| #[trigger]
                        regions.slots.contains_key(i) implies {
                            &&& regions.slot_owners.contains_key(i)
                            &&& regions.slot_owners[i].inv()
                            &&& regions.slots[i].is_init()
                            &&& regions.slots[i].addr() == meta_addr(i)
                            &&& regions.slots[i].value().wf(regions.slot_owners[i])
                            &&& regions.slot_owners[i].self_addr == regions.slots[i].addr()
                        } by {
                        assert(i != node_index);
                        assert(old(regions).slots.contains_key(i));
                    };
                    assert(regions.inv());
                }

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
    #[verus_spec(
        with Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(entry_own): Tracked<&EntryOwner<C>>,
    )]
    pub fn from_pte(pte: C::E, level: PagingLevel) -> (res: Self)
        requires
            pte.paddr() % PAGE_SIZE == 0,
            pte.paddr() < MAX_PADDR,
            old(regions).inv(),
            entry_own.inv(),
            entry_own.relate_region(*old(regions)),
        ensures
            regions.inv(),
            res.wf(*entry_own),
            !pte.is_present() ==> res == Child::<C>::None,
            pte.is_present() && pte.is_last(level) ==> res == Child::<C>::from_pte_frame_spec(
                pte,
                level,
            ),
            pte.is_present() && !pte.is_last(level) ==> res == Child::<C>::from_pte_pt_spec(
                pte.paddr(),
                *regions,
            ),
            entry_own.relate_region(*regions),
            regions.slot_owners =~= old(regions).slot_owners,
            !entry_own.is_node() ==> *regions =~= *old(regions),
            entry_own.is_node() ==> forall|i: usize|
                i != frame_to_index(entry_own.meta_slot_paddr().unwrap()) ==> (
                regions.slots.contains_key(i) == old(regions).slots.contains_key(i)),
    {
        if !pte.is_present() {
            return Child::None;
        }
        let paddr = pte.paddr();

        if !pte.is_last(level) {
            // SAFETY: The caller ensures that this node was created by
            // `into_pte`, so that restoring the forgotten reference is safe.
            #[verus_spec(with Tracked(regions), Tracked(&entry_own.node.tracked_borrow().meta_perm))]
            let node = PageTableNode::from_raw(paddr);
            //            debug_assert_eq!(node.level(), level - 1);

            return Child::PageTable(node);
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
    #[verus_spec(
        with Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(entry_owner): Tracked<&EntryOwner<C>>
    )]
    pub fn from_pte(pte: &C::E, level: PagingLevel) -> (res: Self)
        requires
            entry_owner.match_pte(*pte, level),
            entry_owner.inv(),
            pte.paddr() % PAGE_SIZE == 0,
            pte.paddr() < MAX_PADDR,
            old(regions).inv(),
            entry_owner.relate_region(*old(regions)),
        ensures
            regions.inv(),
            res.wf(*entry_owner),
            entry_owner.relate_region(*regions),
            *regions =~= *old(regions),
    {
        if !pte.is_present() {
            assert(entry_owner.is_absent());
            return ChildRef::None;
        }
        let paddr = pte.paddr();

        if !pte.is_last(level) {
            let ghost regions0 = *regions;

            // SAFETY: The caller ensures that the lifetime of the child is
            // contained by the residing node, and the physical address is
            // valid since the entry is present.
            #[verus_spec(with Tracked(regions), Tracked(&entry_owner.node.tracked_borrow().meta_perm))]
            let node = PageTableNodeRef::borrow_paddr(paddr);

            assert(node.inner.0.ptr.addr() == entry_owner.node.unwrap().meta_perm.addr());

            proof {
                // borrow_paddr preserves slots, slot_owners
                assert(regions.slots =~= regions0.slots);
                assert(regions.slot_owners =~= regions0.slot_owners);

                // Since regions is unchanged, relate_region is trivially preserved
                assert(*regions =~= regions0);
            }
            // debug_assert_eq!(node.level(), level - 1);
            return ChildRef::PageTable(node);
        }
        ChildRef::Frame(paddr, level, pte.prop())
    }
}

} // verus!
