// SPDX-License-Identifier: MPL-2.0
//! This module specifies the type of the children of a page table node.
use vstd::prelude::*;

use crate::mm::frame::meta::mapping::{frame_to_index, frame_to_meta, meta_addr, meta_to_frame};
use crate::mm::frame::Frame;
use crate::mm::frame::meta::has_safe_slot;
use crate::mm::page_table::*;
use crate::specs::arch::mm::{NR_ENTRIES, NR_LEVELS, PAGE_SIZE};
use crate::specs::arch::paging_consts::PagingConsts;
use crate::specs::mm::frame::meta_owners::REF_COUNT_UNUSED;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;

use vstd_extra::cast_ptr::*;
use vstd_extra::drop_tracking::*;
use vstd_extra::ownership::*;

use crate::specs::*;

use crate::{
    mm::{page_prop::PageProperty, Paddr, PagingConstsTrait, PagingLevel, Vaddr},
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
    #[verus_spec(
        with Tracked(owner): Tracked<&mut EntryOwner<C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>
    )]
    pub fn into_pte(self) -> (res: C::E)
        requires
            self.invariants(*old(owner), *old(regions)),
            old(owner).in_scope,
        ensures
            final(owner).pte_invariants(res, *final(regions)),
            *final(regions) == old(owner).into_pte_regions_spec(*old(regions)),
            *final(owner) == old(owner).into_pte_owner_spec(),
            old(owner).node is Some ==>
                res == C::E::new_pt_spec(meta_to_frame(old(owner).node.unwrap().meta_perm.addr())),
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

                let _ = ManuallyDrop::new(node, Tracked(regions));

                proof {
                    let node_index = frame_to_index(meta_to_frame(node.ptr.addr()));
                    let spec_regions = owner.into_pte_regions_spec(*old(regions));
                    assert(regions.slot_owners =~= spec_regions.slot_owners);
                    owner.in_scope = false;
                }

                C::E::new_pt(paddr)
            },
            Child::Frame(paddr, level, prop) => {
                proof { owner.in_scope = false; }
                C::E::new_page(paddr, level, prop)
            },
            Child::None => {
                proof { owner.in_scope = false; }
                C::E::new_absent()
            },
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
    #[verus_spec(
        with Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(entry_own): Tracked<&mut EntryOwner<C>>,
    )]
    pub fn from_pte(pte: C::E, level: PagingLevel) -> (res: Self)
        requires
            old(entry_own).pte_invariants(pte, *old(regions)),
            level == old(entry_own).parent_level,
        ensures
            res.invariants(*final(entry_own), *final(regions)),
            res == Child::<C>::from_pte_spec(pte, level, *final(regions)),
            *final(entry_own) == old(entry_own).from_pte_owner_spec(),
            *final(regions) == final(entry_own).from_pte_regions_spec(*old(regions)),
    {
        if !pte.is_present() {
            proof {
                entry_own.in_scope = true;
            }
            return Child::None;
        }
        let paddr = pte.paddr();

        if !pte.is_last(level) {
            proof {
                broadcast use crate::mm::frame::meta::mapping::group_page_meta;
                regions.inv_implies_correct_addr(paddr);
            }

            proof_decl! {
                let tracked from_raw_debt: crate::specs::mm::frame::frame_specs::BorrowDebt;
            }

            #[verus_spec(with Tracked(regions), Tracked(&entry_own.node.tracked_borrow().meta_perm) => Tracked(from_raw_debt))]
            let node = PageTableNode::from_raw(paddr);

            proof {
                // raw_count was 1 (node was in a PTE via into_raw), so discharge trivially.
                from_raw_debt.discharge_bookkeeping();

                entry_own.in_scope = true;

                assert(regions.slot_owners =~= entry_own.from_pte_regions_spec(*old(regions)).slot_owners);
                assert(regions.slots =~= entry_own.from_pte_regions_spec(*old(regions)).slots);
            }

            return Child::PageTable(node);
        }
        proof {
            entry_own.in_scope = true;
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
    #[verus_spec(
        with Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(entry_owner): Tracked<&EntryOwner<C>>
    )]
    pub fn from_pte(pte: &C::E, level: PagingLevel) -> (res: Self)
        requires
            entry_owner.pte_invariants(*pte, *old(regions)),
            level == entry_owner.parent_level,
        ensures
            res.invariants(*entry_owner, *final(regions)),
            final(regions).slot_owners =~= old(regions).slot_owners,
            forall |k: usize| old(regions).slots.contains_key(k) ==> #[trigger] final(regions).slots.contains_key(k),
            forall |k: usize| old(regions).slots.contains_key(k) ==> old(regions).slots[k] == #[trigger] final(regions).slots[k],
    {
        if !pte.is_present() {
            return ChildRef::None;
        }
        let paddr = pte.paddr();

        if !pte.is_last(level) {
            proof {
                broadcast use crate::mm::frame::meta::mapping::group_page_meta;
                regions.inv_implies_correct_addr(paddr);
            }

            #[verus_spec(with Tracked(regions), Tracked(&entry_owner.node.tracked_borrow().meta_perm))]
            let node = PageTableNodeRef::borrow_paddr(paddr);

            proof {
                // borrow_paddr postcondition gives raw_count == 1 and field-by-field preservation.
                // Since raw_count was already 1 (entry is in PTE, in_scope == false),
                // slot_owners[idx] == old(slot_owners[idx]) follows field by field.
                assert(regions.slot_owners =~= old(regions).slot_owners);
                // slots: borrow_paddr inserts at borrow_idx. Prove existing keys preserved.
                // The node's slot was NOT in old.slots: by active_entry_not_in_free_pool,
                // a node entry's index can't equal any free-pool index.
                let borrow_idx = frame_to_index(paddr);
                assert(entry_owner.is_node());
                let ghost entry_snap = *entry_owner;
                assert(!old(regions).slots.contains_key(borrow_idx)) by {
                    if old(regions).slots.contains_key(borrow_idx) {
                        EntryOwner::<C>::active_entry_not_in_free_pool(entry_snap, *old(regions), borrow_idx);
                        // gives borrow_idx != borrow_idx — contradiction
                    }
                };
                // Since borrow_idx was not in old.slots, insert preserves all old keys.
                assert forall |k: usize| old(regions).slots.contains_key(k)
                    implies old(regions).slots[k] == #[trigger] regions.slots[k] by {
                    assert(k != borrow_idx);
                    // regions.slots == old.slots.insert(borrow_idx, _), and k != borrow_idx
                };
            }

            return ChildRef::PageTable(node);
        }
        ChildRef::Frame(paddr, level, pte.prop())
    }
}

} // verus!
