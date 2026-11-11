// SPDX-License-Identifier: MPL-2.0
//! This module specifies the type of the children of a page table node.
use vstd::prelude::*;
use vstd_extra::ownership::*;

use crate::specs::{
    arch::*,
    mm::frame::{
        frame_specs::FrameRawPerms,
        mapping::{group_page_meta, meta_to_index},
        meta_region_owners::MetaRegionOwners,
    },
    *,
};

use super::*;
use crate::arch::mm::PagingConsts;
use crate::mm::frame::Frame;
use crate::mm::frame::meta::REF_COUNT_UNUSED;
use crate::mm::frame::meta::mapping::meta_to_frame;
use crate::mm::page_table::*;
use crate::{
    mm::{Paddr, PagingConstsTrait, PagingLevel, Vaddr, page_prop::PageProperty},
    //    sync::RcuDrop,
};
use core::mem::ManuallyDrop;

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

    /// # Verified Properties
    /// ## Preconditions
    /// - The child must match the supplied entry owner. For a page table node,
    ///   the owning frame must hold the metadata permission and the
    ///   entry owner's `node_permission` must be `None`.
    /// - A mapped frame must satisfy the PTE implementation's
    ///   [`new_page_req`](PageTableEntryTrait::new_page_req) requirements.
    /// ## Postconditions
    /// - For a page table node, its metadata permission moves into the
    ///   entry owner's `node_permission`. All other owner fields are preserved;
    ///   for a mapped frame or absent child, the owner is unchanged.
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&mut EntryOwner<C>>,
        requires
            old(owner).inv(),
            self.wf(*old(owner)),
            self matches Child::Frame(paddr, level, prop) ==> C::E::new_page_req(paddr, level, prop),
        ensures
            final(owner).inv(),
            final(owner).match_pte(res, final(owner).parent_level),
            *final(owner) == old(owner).into_pte_owner_spec(self),
            old(owner).is_node() ==> res == C::E::new_pt_spec(
                meta_to_frame(old(owner).node().slot_vaddr()),
            ),
    )]
    pub fn into_pte(self) -> C::E {
        proof {
            C::E::lemma_page_table_entry_properties();
        }

        match self {
            /* `mut` only permits transferring the erased token before forgetting the handle.
             * Origin Rust: Child::PageTable(node) => {
             */
            Child::PageTable(mut node) => {
                let paddr = node.start_paddr();
                proof {
                    owner.node_permission = Some(node.tracked_metadata_perm.tracked_take());
                }
                let _ = ManuallyDrop::new(node);
                C::E::new_pt(paddr)
            },
            Child::Frame(paddr, level, prop) => { C::E::new_page(paddr, level, prop) },
            Child::None => { C::E::new_absent() },
        }
    }

    /// # Safety
    ///
    /// The provided PTE must be the output of [`Self::into_pte`], and the PTE:
    ///  - must not be used to created a [`Child`] twice;
    ///  - must not be referenced by a living [`ChildRef`].
    ///
    /// The level must match the original level of the child.
    /// # Verified Properties
    /// ## Preconditions
    /// - The PTE, entry owner, and metadata region must satisfy
    ///   [`EntryOwner::pte_invariants`], including ownership of the counted
    ///   metadata permission for a page table node.
    /// - `level` must equal the entry owner's parent level.
    /// ## Postconditions
    /// - For a page table node, the returned frame takes the entry owner's
    ///   metadata permission, leaving `node_permission` as `None`.
    ///   All other owner fields are preserved; for a mapped frame or absent
    ///   entry, the owner is unchanged.
    /// - The returned child satisfies [`Child::invariants`] with the updated
    ///   entry owner and the supplied metadata region.
    #[verus_spec(res =>
        with Tracked(regions): Tracked<& MetaRegionOwners>,
             Tracked(entry_own): Tracked<&mut EntryOwner<C>>,
        requires
            old(entry_own).pte_invariants(pte, *regions),
            level == old(entry_own).parent_level,
        ensures
            res.invariants(*final(entry_own), *regions),
            res == Child::<C>::from_pte_spec(pte, level, *regions, old(entry_own).node_permission),
            *final(entry_own) == old(entry_own).from_pte_owner_spec(),
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

            let tracked permission = entry_own.tracked_take_node_permission();
            // SAFETY: The caller ensures that this node was created by
            // `into_pte`, so that restoring the forgotten reference is safe.
            let node = unsafe {
                #[verus_spec(with Tracked(FrameRawPerms {
                    slot_perm,
                    metadata_perm: permission,
                }))]
                PageTableNode::<C>::from_raw(paddr)
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
impl<'a, C: PageTableConfig> ChildRef<'a, C> {
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
    /// - The caller guarantees the physical node remains alive for `'a`.
    /// - A node result is a raw handle without a retained count borrow. Metadata
    ///   access requires an actual external permission; it does not satisfy
    ///   `FrameRef::inv()` by itself.
    #[verus_spec(res =>
        with Tracked(regions): Tracked<&MetaRegionOwners>,
             Tracked(entry_owner): Tracked<&EntryOwner<C>>,
        requires
            entry_owner.pte_invariants(*pte, *regions),
            level == entry_owner.parent_level,
        ensures
            res.invariants(*entry_owner, *regions),
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
                #[verus_spec(with Tracked(slot_perm), Tracked(None))]
                PageTableNodeRef::borrow_paddr(paddr)
            };

            return ChildRef::PageTable(node);
        }
        ChildRef::Frame(paddr, level, pte.prop())
    }
}

} // verus!
