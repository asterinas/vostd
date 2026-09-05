// SPDX-License-Identifier: MPL-2.0
//! This module specifies the type of the children of a page table node.
use core::marker::PhantomData;
use core::mem::ManuallyDrop;

use vstd::prelude::*;
use vstd::simple_pptr::PPtr;

use crate::arch::mm::PagingConsts;
use crate::mm::frame::Frame;
use crate::mm::frame::meta::REF_COUNT_UNUSED;
use crate::mm::frame::meta::mapping::{frame_to_meta, meta_to_frame};
use crate::mm::page_table::*;
use crate::specs::arch::*;
use crate::specs::mm::frame::{
    mapping::{group_page_meta, meta_to_index},
    meta_region_owners::MetaRegionOwners,
};

use vstd_extra::cast_ptr::*;
use vstd_extra::ownership::*;

use crate::specs::*;

use crate::{
    mm::{Paddr, PagingConstsTrait, PagingLevel, Vaddr, page_prop::PageProperty},
    //    sync::RcuDrop,
};

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

#[verus_verify]
impl<C: PageTableConfig> Child<C> {
    /// Returns whether the child is not present.
    #[vstd::contrib::auto_spec]
    pub(in crate::mm) fn is_none(&self) -> (b: bool) {
        matches!(self, Child::None)
    }

    /// Converts the child to a raw PTE value.
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: all [safety invariants](Child::invariants) must hold on the child.
    /// - **Safety**: the entry's must be marked as a child, which implies that it has a `raw_count` of 0.
    /// ## Postconditions
    /// - **Safety Invariants**: the `PTE`'s [safety invariants](EntryOwner::pte_invariants) are preserved.
    /// - **Safety**: the entry's raw count is incremented by 1.
    /// - **Safety**: No frame other than the target entry's (if applicable) is impacted by the call.
    /// - **Correctness**: the `PTE` is equivalent to the original `Child`.
    /// ## Safety
    /// The `PTE` safety invariants ensure that the raw pointer to the entry is tracked correctly
    /// so that we can guarantee the safety condition on `from_pte`.
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&mut EntryOwner<C>>,
             Tracked(regions): Tracked<&mut MetaRegionOwners>,
        requires
            self.invariants(*old(owner), *old(regions)),
        ensures
            final(owner).pte_invariants(res, *final(regions)),
            *final(regions) == old(owner).into_pte_regions_spec(*old(regions)),
            *final(owner) == old(owner).into_pte_owner_spec(),
            old(owner).is_node() ==> res == C::E::new_pt_spec(
                meta_to_frame(old(owner).node().meta_vaddr()),
            ),
    )]
    pub fn into_pte(self) -> C::E {
        proof {
            C::E::lemma_page_table_entry_properties();
        }

        match self {
            Child::PageTable(node) => {
                let ghost node_owner = owner.node();

                let paddr = node.start_paddr();

                let _ = ManuallyDrop::new(node);

                proof {
                    // `MD::new` removed one entry at `node_index`, matching
                    // `into_pte_regions_spec`'s `.remove(index)`.
                    let spec_regions = owner.into_pte_regions_spec(*old(regions));
                }

                C::E::new_pt(paddr)
            },
            Child::Frame(paddr, level, prop) => { C::E::new_page(paddr, level, prop) },
            Child::None => { C::E::new_absent() },
        }
    }

    /// Converts a `PTE` to a `Child`.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: the `PTE`'s [safety invariants](EntryOwner::pte_invariants) must hold.
    /// - **Safety**: `level` must match the original level of the child.
    /// ## Postconditions
    /// - **Safety Invariants**: the [safety invariants](Child::invariants) are preserved.
    /// - **Safety**: the `EntryOwner` is aware that it is tracking an entry in `Child` form.
    /// - **Safety**: No frame other than the target entry's (if applicable) is impacted by the call.
    /// - **Correctness**: the `Child` is equivalent to the original `PTE`.
    /// ## Safety
    /// The `PTE` safety invariants require that the `PTE` was previously obtained using [`Self::into_pte`]
    /// (or another function that calls `ManuallyDrop::new`, which is sufficient for safety).
    #[verus_spec(res =>
        with Tracked(regions): Tracked<&mut MetaRegionOwners>,
             Tracked(entry_own): Tracked<&mut EntryOwner<C>>,
        requires
            old(entry_own).pte_invariants(pte, *old(regions)),
            level == old(entry_own).parent_level,
        ensures
            res.invariants(*final(entry_own), *final(regions)),
            res == Child::<C>::from_pte_spec(pte, level, *final(regions)),
            *final(entry_own) == old(entry_own).from_pte_owner_spec(),
            *final(regions) == final(entry_own).from_pte_regions_spec(*old(regions)),
    )]
    pub unsafe fn from_pte(pte: C::E, level: PagingLevel) -> Self {
        if !pte.is_present() {
            return Child::None;
        }
        let paddr = pte.paddr();

        if !pte.is_last(level) {
            proof {
                broadcast use group_page_meta;

                regions.lemma_contains_valid_frame_paddr(paddr);
            }
            let tracked slot_perm = regions.tracked_borrow_slot(paddr);

            let node = PageTableNode::<C> {
                ptr: PPtr::from_addr(frame_to_meta(paddr)),
                _marker: PhantomData,
                #[cfg(verus_keep_ghost_body)]
                tracked_slot_perm: Tracked(slot_perm),
                #[cfg(verus_keep_ghost_body)]
                tracked_metadata_perm: Tracked(None),
            };

            return Child::PageTable(node);
        }
        Child::Frame(paddr, level, pte.prop())
    }
}

/// A reference to the child of a page table node.
/// # Verification Design
/// If the child is itself a page table node, it is represented by a [`PageTableNodeRef`],
/// because a reference to it must be treated as a potentially shared reference of the appropriate lifetime.
/// By contrast, a mapped frame can be referenced by just carrying its values, and an absent one is just a simple tag.
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

#[verus_verify]
impl<C: PageTableConfig> ChildRef<'_, C> {
    /// Converts a PTE to a reference to a child.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: the `PTE`'s [safety invariants](EntryOwner::pte_invariants) must hold.
    /// - **Safety**: `level` must match the original level of the child.
    /// ## Postconditions
    /// - **Safety Invariants**: the [safety invariants](ChildRef::invariants) are preserved.
    /// - **Correctness**: the `ChildRef` is equivalent to the original `PTE`.
    /// - **Safety**: No frame other than the target entry's (if applicable) is impacted by the call.
    /// ## Safety
    /// - The `PTE` safety invariants require that the `PTE` was previously obtained using [`Self::from_pte`]
    /// - The soundness of using the resulting `ChildRef` as a reference follows from `FrameRef` safety.
    #[verus_spec(res =>
        with Tracked(regions): Tracked<&mut MetaRegionOwners>,
             Tracked(entry_owner): Tracked<&EntryOwner<C>>,
        requires
            entry_owner.pte_invariants(*pte, *old(regions)),
            level == entry_owner.parent_level,
        ensures
            res.invariants(*entry_owner, *final(regions)),
            final(regions).slot_owners == old(regions).slot_owners,
            forall|k: int|
                old(regions).slots.contains_key(k) ==> #[trigger] final(regions).slots.contains_key(
                    k,
                ),
            forall|k: int|
                old(regions).slots.contains_key(k) ==> old(regions).slots[k]
                    == #[trigger] final(regions).slots[k],
    )]
    pub unsafe fn from_pte(pte: &C::E, level: PagingLevel) -> Self {
        if !pte.is_present() {
            return ChildRef::None;
        }
        let paddr = pte.paddr();

        if !pte.is_last(level) {
            proof {
                broadcast use group_page_meta;

            }

            let tracked node_owner = entry_owner.tracked_borrow_node();
            let tracked slot_perm = *regions.slots.tracked_borrow(node_owner.slot_index);
            let node = unsafe {
                #[verus_spec(with Tracked(slot_perm), Tracked(&node_owner.frame_permission))]
                PageTableNodeRef::borrow_paddr(paddr)
            };

            return ChildRef::PageTable(node);
        }
        ChildRef::Frame(paddr, level, pte.prop())
    }
}

} // verus!
