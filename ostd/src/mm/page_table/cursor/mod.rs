// SPDX-License-Identifier: MPL-2.0
//! The page table cursor for mapping and querying over the page table.
//!
//! # The page table lock protocol
//!
//! We provide a fine-grained ranged mutual-exclusive lock protocol to allow
//! concurrent accesses to non-overlapping virtual ranges in the page table.
//!
//! [`CursorMut::new`] will lock a range in the virtual space and all the
//! operations on the range with the cursor will be atomic as a transaction.
//!
//! The guarantee of the lock protocol is that, if two cursors' ranges overlap,
//! all of one's operation must be finished before any of the other's
//! operation. The order depends on the scheduling of the threads. If a cursor
//! is ordered after another cursor, it will see all the changes made by the
//! previous cursor.
//!
//! The implementation of the lock protocol resembles two-phase locking (2PL).
//! [`CursorMut::new`] accepts an address range, which indicates the page table
//! entries that may be visited by this cursor. Then, [`CursorMut::new`] finds
//! an intermediate page table (not necessarily the last-level or the top-
//! level) which represents an address range that fully contains the whole
//! specified address range. Then it locks all the nodes in the sub-tree rooted
//! at the intermediate page table node, with a pre-order DFS order. The cursor
//! will only be able to access the page table entries in the locked range.
//! Upon destruction, the cursor will release the locks in the reverse order of
//! acquisition.
mod locking;

use vstd::prelude::*;

use vstd::arithmetic::power2::pow2;
use vstd::math::abs;
use vstd::simple_pptr::*;

use vstd_extra::arithmetic::*;
use vstd_extra::drop_tracking::ManuallyDrop;
use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;
use vstd_extra::{assert, assert_eq};
use vstd_extra::panic::*;

use crate::mm::frame::Frame;
use crate::mm::page_table::*;
use crate::mm::{Paddr, Vaddr, MAX_NR_LEVELS, MAX_PADDR};
use crate::specs::arch::kspace::FRAME_METADATA_RANGE;
use crate::specs::mm::frame::mapping::{
    frame_to_index, frame_to_index_spec, frame_to_meta, max_meta_slots,
    meta_addr, meta_to_frame, META_SLOT_SIZE
};
use crate::specs::mm::frame::meta_owners::{MetaSlotOwner, REF_COUNT_MAX, REF_COUNT_UNUSED};
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::page_table::cursor::page_size_lemmas::*;

use core::{fmt::Debug, marker::PhantomData, ops::Range};

use align_ext::AlignExt;

use crate::{
    mm::{page_prop::PageProperty, page_table::is_valid_range},
    specs::task::InAtomicMode,
};

use super::{
    pte_index, Child, ChildRef, Entry, EntryOwner, FrameView, PageTable, PageTableConfig,
    PageTableError, PageTableGuard, PageTablePageMeta, PagingConstsTrait, PagingLevel,
};


verus! {

/// The state of virtual pages represented by a page table.
///
/// This is the return type of the [`Cursor::query`] method.
pub type PagesState<C> = (Range<Vaddr>, Option<<C as PageTableConfig>::Item>);

/// The cursor for traversal over the page table.
///
/// A slot is a PTE at any levels, which correspond to a certain virtual
/// memory range sized by the "page size" of the current level.
///
/// A cursor is able to move to the next slot, to read page properties,
/// and even to jump to a virtual address directly.
pub struct Cursor<'rcu, C: PageTableConfig, A: InAtomicMode> {
    /// The current path of the cursor.
    ///
    /// The level 1 page table lock guard is at index 0, and the level N page
    /// table lock guard is at index N - 1.
    pub path: [Option<PageTableGuard<'rcu, C>>; NR_LEVELS],
    /// The cursor should be used in a RCU read side critical section.
    pub rcu_guard: &'rcu A,
    /// The level of the page table that the cursor currently points to.
    pub level: PagingLevel,
    /// The top-most level that the cursor is allowed to access.
    ///
    /// From `level` to `guard_level`, the nodes are held in `path`.
    pub guard_level: PagingLevel,
    /// The virtual address that the cursor currently points to.
    pub va: Vaddr,
    /// The virtual address range that is locked.
    pub barrier_va: Range<Vaddr>,
    pub _phantom: PhantomData<&'rcu PageTable<C>>,
}

/// The cursor of a page table that is capable of map, unmap or protect pages.
///
/// It has all the capabilities of a [`Cursor`], which can navigate over the
/// page table corresponding to the address range. A virtual address range
/// in a page table can only be accessed by one cursor, regardless of the
/// mutability of the cursor.
pub struct CursorMut<'rcu, C: PageTableConfig, A: InAtomicMode>(pub Cursor<'rcu, C, A>);

impl<C: PageTableConfig, A: InAtomicMode> Iterator for Cursor<'_, C, A> {
    type Item = PagesState<C>;

    #[verifier::external_body]
    fn next(&mut self) -> Option<Self::Item> {
        unimplemented!()
    }
}

/// Reborrow the inner `PageTableGuard` of `path[idx]` (which must be `Some`).
///
/// `external_body` because Verus's mut-ref model can't see through the
/// `array[idx].as_mut()` reborrow chain to conclude that the array's structure
/// is preserved. The Rust body is just `path[idx].as_mut().unwrap()`. The
/// trust boundary captures: (i) the inner guard pointed to by `res` equals
/// the original inner guard at `path[idx]`, and (ii) the array's structure is
/// unchanged. Both follow from `Option::as_mut`'s vstd spec composed with
/// array indexing — Verus just won't compose them automatically.
#[verifier::external_body]
#[verus_spec(res =>
    requires
        idx < NR_LEVELS,
        old(path)[idx as int] is Some,
    ensures
        *res == old(path)[idx as int].unwrap(),
        *final(res) == old(path)[idx as int].unwrap(),
        *final(path) == *old(path),
)]
fn path_slot_as_mut<'a, 'rcu, C: PageTableConfig>(
    path: &'a mut [Option<PageTableGuard<'rcu, C>>; NR_LEVELS],
    idx: usize,
) -> &'a mut PageTableGuard<'rcu, C> {
    path[idx].as_mut().unwrap()
}

pub open spec fn page_size_spec(level: PagingLevel) -> usize {
    (PAGE_SIZE * pow2(
        (nr_subpage_per_huge::<PagingConsts>().ilog2() * (level - 1)) as nat,
    )) as usize
}

/// The page size at a given level.
#[verifier::when_used_as_spec(page_size_spec)]
#[verifier::external_body]
pub fn page_size(level: PagingLevel) -> (ret: usize)
    requires
        1 <= level <= NR_LEVELS + 1,
    ensures
        ret == page_size_spec(level),
        exists|e| ret == pow2(e),
        ret >= PAGE_SIZE,
{
    PAGE_SIZE << (nr_subpage_per_huge::<PagingConsts>().ilog2() as usize * (level as usize - 1))
}

/// Borrows a live `PageTableNode` as a `PageTableNodeRef` without requiring
/// `raw_count == 1`.
///
/// ## Justification
/// `Child::from_pte` (called inside `Entry::replace`) invokes `PageTableNode::from_raw`,
/// which sets `regions.slot_owners[idx].raw_count = 0` and marks the entry owner
/// `in_scope = true`.  Consequently `metaregion_sound` reports `raw_count == 0`, but
/// `Frame::borrow` / `FrameRef::borrow_paddr` require `raw_count == 1`.
///
/// This function bridges that gap: we have unique ownership of the live frame `pt`
/// (just returned from `Entry::replace`), so borrowing it as a `PageTableNodeRef`
/// is semantically sound.  The `raw_count == 1` requirement in `borrow_paddr` is an
/// accounting invariant designed for *forgotten* frames stored in PTEs; it does not
/// apply to live frames held directly.
///
/// ## Fix path
/// The proper fix is:
///   1. Add `ensures old(owner).is_node() ==> regions.slots.contains_key(...)` to
///      `Entry::replace` (derivable from `Child::from_pte`'s `from_pte_regions_spec`).
///   2. Replace this call with `pt.into_raw()` + `PageTableNodeRef::borrow_paddr()`.

/// A fragment of a page table that can be taken out of the page table.
pub enum PageTableFrag<C: PageTableConfig> {
    /// A mapped page table item.
    Mapped { va: Vaddr, item: C::Item },
    /// A sub-tree of a page table that is taken out of the page table.
    ///
    /// The caller is responsible for dropping it after TLB coherence.
    StrayPageTable {
        pt: Frame<PageTablePageMeta<C>>,  // TODO: this was a dyn AnyFrameMeta, but we can't support that...
        va: Vaddr,
        len: usize,
        num_frames: usize,
    },
}

impl<C: PageTableConfig> PageTableFrag<C> {
    #[cfg(ktest)]
    pub fn va_range(&self) -> Range<Vaddr> {
        match self {
            PageTableFrag::Mapped { va, item } => {
                let (pa, level, prop) = C::item_into_raw(item.clone());
                // SAFETY: All the arguments match those returned from the previous call
                // to `item_into_raw`, and we are taking ownership of the cloned item.
                drop(unsafe { C::item_from_raw(pa, level, prop) });
                *va..*va + page_size(level)
            },
            PageTableFrag::StrayPageTable { va, len, .. } => *va..*va + *len,
        }
    }
}

#[verus_verify]
impl<'rcu, C: PageTableConfig, A: InAtomicMode> Cursor<'rcu, C, A> {

    #[verus_spec(
        with Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Ghost(pa): Ghost<Paddr>)]
    pub fn clone_item(item: &C::Item) -> (res: C::Item)
        requires
            item.clone_requires(*old(regions)),
            C::item_into_raw_spec(*item).0 == pa,
        ensures
            res == *item,
            item.clone_ensures(*old(regions), *final(regions), res),
            final(regions).inv(),
            final(regions).slots =~= old(regions).slots,
            final(regions).slot_owners.dom() =~= old(regions).slot_owners.dom(),
            forall|i: usize| i != frame_to_index(pa) ==>
                (#[trigger] final(regions).slot_owners[i] == old(regions).slot_owners[i]),
            // The frame's slot: bumped if the item is ref-counted, otherwise unchanged.
            C::tracked(*item) ==> {
                &&& final(regions).slot_owners[frame_to_index(pa)].inner_perms.ref_count.id()
                    == old(regions).slot_owners[frame_to_index(pa)].inner_perms.ref_count.id()
                &&& final(regions).slot_owners[frame_to_index(pa)].inner_perms.storage
                    == old(regions).slot_owners[frame_to_index(pa)].inner_perms.storage
                &&& final(regions).slot_owners[frame_to_index(pa)].inner_perms.vtable_ptr
                    == old(regions).slot_owners[frame_to_index(pa)].inner_perms.vtable_ptr
                &&& final(regions).slot_owners[frame_to_index(pa)].inner_perms.in_list
                    == old(regions).slot_owners[frame_to_index(pa)].inner_perms.in_list
                &&& final(regions).slot_owners[frame_to_index(pa)].paths_in_pt
                    == old(regions).slot_owners[frame_to_index(pa)].paths_in_pt
                &&& final(regions).slot_owners[frame_to_index(pa)].self_addr
                    == old(regions).slot_owners[frame_to_index(pa)].self_addr
                &&& final(regions).slot_owners[frame_to_index(pa)].raw_count
                    == old(regions).slot_owners[frame_to_index(pa)].raw_count
                &&& final(regions).slot_owners[frame_to_index(pa)].usage
                    == old(regions).slot_owners[frame_to_index(pa)].usage
                &&& final(regions).slot_owners[frame_to_index(pa)].inner_perms.ref_count.value()
                    == old(regions).slot_owners[frame_to_index(pa)].inner_perms.ref_count.value() + 1
            },
            !C::tracked(*item) ==>
                final(regions).slot_owners[frame_to_index(pa)]
                    == old(regions).slot_owners[frame_to_index(pa)],
    {
        let res = item.clone(Tracked(regions));
        proof {
            C::clone_ensures_concrete(*item, pa, *old(regions), *regions, res);
        }
        res
    }

    /// Creates a cursor claiming exclusive access over the given range.
    ///
    /// The cursor created will only be able to query or jump within the given
    /// range. Out-of-bound accesses will result in panics or errors as return values,
    /// depending on the access method.
    #[verus_spec(r =>
        with Tracked(pt_own): Tracked<PageTableOwner<C>>,
            Ghost(root_guard): Ghost<PageTableGuard<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            pt_own.inv(),
            // Per-config tightening: e.g. `KernelPtConfig` overrides
            // `LOCKED_END_BOUND_spec` to `FRAME_METADATA_BASE_VADDR`. Callers
            // for `KernelPtConfig` (KVirtArea, etc.) discharge this from the
            // `kvirt_alloc_range_bounds` axiom; default-config callers
            // (UserPtConfig) get this for free since the default bound is
            // `usize::MAX + 1`.
            va.end as int <= C::LOCKED_END_BOUND_spec(),
        ensures
            Self::cursor_new_success_conditions(va) ==> {
                &&& r is Ok
                &&& r.unwrap().0.invariants(*r.unwrap().1, *final(regions), *final(guards))
                &&& r.unwrap().1.in_locked_range()
                &&& r.unwrap().0.level == r.unwrap().0.guard_level
                &&& r.unwrap().0.va < r.unwrap().0.barrier_va.end
                &&& r.unwrap().0.va == va.start
                &&& r.unwrap().0.barrier_va == *va
                &&& r.unwrap().1@.as_page_table_owner() == pt_own
                &&& r.unwrap().1@.continuations[3].path() == pt_own.0.value.path
            },
            !Self::cursor_new_success_conditions(va) ==> r is Err,
            // Cursor::new inherits lock_range's weakened preservation: only
            // slots that were non-UNUSED before the call keep their
            // paths_in_pt (new PT allocations come from UNUSED slots).
            forall|idx: usize| #![trigger final(regions).slot_owners[idx].paths_in_pt]
                old(regions).slot_owners[idx].inner_perms.ref_count.value()
                    != crate::specs::mm::frame::meta_owners::REF_COUNT_UNUSED
                ==> final(regions).slot_owners[idx].paths_in_pt
                        == old(regions).slot_owners[idx].paths_in_pt,
            forall|item: C::Item| #![trigger CursorMut::<C, A>::item_not_mapped(item, *old(regions))]
                CursorMut::<C, A>::item_not_mapped(item, *old(regions)) ==>
                CursorMut::<C, A>::item_not_mapped(item, *final(regions)),
            // Non-saturation preservation.
            (forall |i: usize| #![trigger old(regions).slot_owners[i]]
                old(regions).slot_owners.contains_key(i)
                && old(regions).slot_owners[i].inner_perms.ref_count.value()
                    != crate::specs::mm::frame::meta_owners::REF_COUNT_UNUSED
                ==> old(regions).slot_owners[i].inner_perms.ref_count.value() + 1
                    < crate::specs::mm::frame::meta_owners::REF_COUNT_MAX)
            ==>
            (forall |i: usize| #![trigger final(regions).slot_owners[i]]
                final(regions).slot_owners.contains_key(i)
                && final(regions).slot_owners[i].inner_perms.ref_count.value()
                    != crate::specs::mm::frame::meta_owners::REF_COUNT_UNUSED
                ==> final(regions).slot_owners[i].inner_perms.ref_count.value() + 1
                    < crate::specs::mm::frame::meta_owners::REF_COUNT_MAX),
    )]
    pub fn new(pt: &'rcu PageTable<C>, guard: &'rcu A, va: &Range<Vaddr>)
    -> Result<(Self, Tracked<CursorOwner<'rcu, C>>), PageTableError>
    {
        let valid = is_valid_range::<C>(va);
        if !valid || va.start >= va.end {
            return Err(PageTableError::InvalidVaddrRange(va.start, va.end));
        }
        if va.start % C::BASE_PAGE_SIZE() != 0 || va.end % C::BASE_PAGE_SIZE() != 0 {
            return Err(PageTableError::UnalignedVaddr);
        }
        //        const { assert!(C::NR_LEVELS() as usize <= MAX_NR_LEVELS) };

        proof {
            assert(pt_own.0.value.is_node());
            assert forall|i: int| 0 <= i < NR_ENTRIES implies pt_own.0.children[i] is Some by {
                pt_own.pt_inv_unroll(i);
            };
        }

        Ok(
            #[verus_spec(with Tracked(pt_own), Ghost(root_guard), Tracked(regions), Tracked(guards))]
            locking::lock_range(pt, guard, va),
        )
    }

    /// Gets the current virtual address.
    pub fn virt_addr(&self) -> Vaddr
        returns
            self.va,
    {
        self.va
    }

    /// Queries the mapping at the current virtual address.
    ///
    /// If the cursor is pointing to a valid virtual address that is locked,
    /// it will return the virtual address range and the item at that slot.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: the global safety invariants ([Self::invariants])
    /// must hold before the call.
    /// ## Postconditions
    /// - **Safety Invariants**: the global safety invariants hold after the call
    /// - **Correctness**: if the cursor is within the locked range, the result will be `Ok`;
    /// otherwise it will be an error.
    /// - **Correctness**: if there is a mapping present ([Self::query_some_condition]),
    /// then the second field of the result will `Some(item)`, where `item` is the mapping,
    /// and the first field will give its range.
    /// - **Correctness**: if there is no mapping present, then the second field of the result will be
    /// 'None'.
    /// - **Safety**: all frames' relations with the metadata region are preserved.
    /// ## Safety
    /// - The global invariants ensure that the first node we pass through is already locked,
    /// and the loop invariant makes the same guarantee for subsequent nodes.
    /// - This function does not change anything in the metadata region except for incrementing 
    /// the reference counts of nodes when it descends into them.
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            old(self).invariants(*old(owner), *old(regions), *old(guards)),
            old(owner).in_locked_range(),
        ensures
            final(self).invariants(*final(owner), *final(regions), *final(guards)),
            old(owner).in_locked_range() ==> res is Ok,
            res matches Ok(state) ==>
                final(self).query_some_condition(*final(owner)) ==>
                final(self).query_some_ensures(*final(owner), state),
            res matches Ok(state) ==>
                !final(self).query_some_condition(*final(owner)) ==>
                final(self).query_none_ensures(*final(owner), state),
            old(owner)@.mappings == final(owner)@.mappings,
            final(self).va == old(self).va,
    )]
    #[verifier::rlimit(200)]
    pub fn query(&mut self) -> Result<PagesState<C>, PageTableError> {
        if self.va >= self.barrier_va.end {
            proof {
                owner.va.reflect_prop(self.va);
            }
            return Err(PageTableError::InvalidVaddr(self.va));
        }
        let rcu_guard = self.rcu_guard;

        let ghost initial_va = self.va;

        #[verifier::spinoff_prover]
        loop
            invariant
                self.invariants(*owner, *regions, *guards),
                owner.in_locked_range(),
                self.va == initial_va,
                initial_va == old(self).va,
                old(owner)@.mappings == owner@.mappings,
                regions.slot_owners.dom() == old(regions).slot_owners.dom(),
                forall|idx: usize| #![trigger regions.slot_owners[idx]]
                    old(regions).slot_owners.contains_key(idx) ==> {
                        &&& regions.slot_owners[idx].paths_in_pt == old(regions).slot_owners[idx].paths_in_pt
                        &&& regions.slot_owners[idx].self_addr == old(regions).slot_owners[idx].self_addr
                        &&& regions.slot_owners[idx].usage == old(regions).slot_owners[idx].usage
                        &&& regions.slot_owners[idx].raw_count == old(regions).slot_owners[idx].raw_count
                        &&& regions.slot_owners[idx].inner_perms.ref_count.id()
                            == old(regions).slot_owners[idx].inner_perms.ref_count.id()
                        &&& regions.slot_owners[idx].inner_perms.ref_count.value()
                            >= old(regions).slot_owners[idx].inner_perms.ref_count.value()
                        &&& regions.slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                            || old(regions).slot_owners[idx].inner_perms.ref_count.value() == REF_COUNT_UNUSED
                        &&& regions.slot_owners[idx].inner_perms.storage.id()
                            == old(regions).slot_owners[idx].inner_perms.storage.id()
                        &&& regions.slot_owners[idx].inner_perms.vtable_ptr.pptr()
                            == old(regions).slot_owners[idx].inner_perms.vtable_ptr.pptr()
                        &&& regions.slot_owners[idx].inner_perms.in_list.id()
                            == old(regions).slot_owners[idx].inner_perms.in_list.id()
                    },
                forall|k: usize| old(regions).slots.contains_key(k)
                    ==> #[trigger] regions.slots.contains_key(k),
                forall|k: usize| old(regions).slots.contains_key(k)
                    ==> old(regions).slots[k] == #[trigger] regions.slots[k],
            decreases self.level,
        {
            let cur_va = self.va;
            let level = self.level;

            #[verus_spec(with Tracked(owner), Tracked(regions))]
            let entry = self.cur_entry();

            let ghost owner_snap = *owner;
            let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
            let ghost cont0 = continuation;
            let tracked child_owner = continuation.take_child();
            let tracked parent_owner = continuation.entry_own.node.tracked_borrow();
            let ghost regions_before_ref = *regions;

            #[verus_spec(with Tracked(&child_owner.value), Tracked(&parent_owner), Tracked(regions))]
            let cur_child = entry.to_ref();

            proof {
                continuation.put_child(child_owner);
                cont0.take_put_child();
                owner.continuations.tracked_insert(owner.level - 1, continuation);
                owner.metaregion_slot_owners_preserved(regions_before_ref, *regions);
            }

            let item = match cur_child {
                ChildRef::PageTable(pt) => {
                    let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
                    let tracked mut child_owner = continuation.take_child();
                    let tracked mut child_node = child_owner.value.node.tracked_take();

                    let ghost guards0 = *guards;

                    // SAFETY: The `pt` must be locked and no other guards exist.

                    #[verus_spec(with Tracked(&child_node), Tracked(guards))]
                    let guard = pt.make_guard_unchecked(rcu_guard);

                    proof {
                        child_owner.value.node = Some(child_node);
                        continuation.put_child(child_owner);
                        owner.continuations.tracked_insert(owner.level - 1, continuation);

                        owner.map_children_implies(
                            CursorOwner::node_unlocked(guards0),
                            CursorOwner::node_unlocked_except(*guards, child_node.meta_perm.addr()),
                        );
                        owner.cur_entry_node_implies_level_gt_1();
                    }
                    #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
                    self.push_level(guard);

                    continue ;
                },
                ChildRef::None => {
                    proof { owner.cur_entry_absent_not_present(); }
                    None
                },
                ChildRef::Frame(pa, ch_level, prop) => {
                    proof { owner.cur_entry_frame_present(); }

                    // debug_assert_eq!(ch_level, level);
                    // SAFETY:
                    // This is part of (if `split_huge` happens) a page table item mapped
                    // with a previous call to `C::item_into_raw`, where:
                    //  - The physical address and the paging level match it;
                    //  - The item part is still mapped so we don't take its ownership.
                    //
                    // For page table configs that require the `AVAIL1` flag to be kept
                    // (currently, only kernel page tables), the callers of the unsafe
                    // `protect_next` method uphold this invariant.
                    let item =   /*ManuallyDrop::new(unsafe {*/
                    C::item_from_raw(pa, level, prop)  /*})*/
                    ;

                    proof {
                        C::item_roundtrip(item, pa, level, prop);
                    }

                    assert(pa == owner.cur_entry_owner().frame.unwrap().mapped_pa);

                    let ghost old_regions = *regions;

                    proof {
                        let idx = frame_to_index(pa);
                        assert(owner.path_metaregion_sound(*regions));
                        assert(owner.cur_entry_owner().metaregion_sound(*regions));
                        assert(regions.slot_owners.contains_key(idx));
                        assert(owner.cur_entry_owner().inv_base());
                        EntryOwner::<C>::axiom_frame_is_tracked_matches_item(
                            owner.cur_entry_owner());
                        owner.cur_frame_clone_requires(item, pa, level, prop, *regions);
                    }

                    #[verus_spec(with Tracked(regions), Ghost(pa))]
                    let cloned = Self::clone_item(&item);

                    proof {
                        let idx = frame_to_index(pa);
                        broadcast use crate::specs::mm::frame::meta_owners::axiom_mmio_usage_iff_mmio_paddr;
                        assert(owner.path_metaregion_sound(old_regions));
                        assert(owner.cur_entry_owner().metaregion_sound(old_regions));
                        assert(old_regions.slot_owners.contains_key(idx));
                        if C::tracked(item) {
                            EntryOwner::<C>::axiom_frame_is_tracked_matches_item(
                                owner.cur_entry_owner());
                            EntryOwner::<C>::axiom_frame_is_tracked_iff_not_mmio(
                                owner.cur_entry_owner());
                            assert(old_regions.slot_owners[idx].self_addr
                                == crate::mm::frame::meta::mapping::meta_addr(idx));
                            assert(old_regions.slot_owners[idx].inner_perms.ref_count.value()
                                != REF_COUNT_UNUSED);
                            assert(0 < old_regions.slot_owners[idx].inner_perms.ref_count.value());
                            assert(regions.slot_owners[idx].inv());
                            assert(regions.slot_owners[idx].inner_perms.ref_count.value()
                                == old_regions.slot_owners[idx].inner_perms.ref_count.value() + 1);
                            assert(regions.slot_owners[idx].inner_perms.ref_count.value()
                                <= REF_COUNT_MAX);
                            owner.clone_item_preserves_invariants(old_regions, *regions, idx);
                        } else {
                            assert(regions.slots =~= old_regions.slots);
                            assert(regions.slot_owners =~= old_regions.slot_owners);
                            assert(*regions == old_regions);
                        }
                        assert(regions.inv());
                        assert(owner.metaregion_sound(*regions));
                        assert(regions.slot_owners.dom() =~= old_regions.slot_owners.dom());
                    }

                    Some(cloned)
                },
            };

            let size = page_size(level);

            proof {
                if owner.cur_entry_owner().is_frame() {
                    owner.cur_entry_frame_present();
                    owner.cur_va_range_reflects_view();
                }
                assert forall |e: EntryOwner<C>|
                    #[trigger] e.inv() && e.metaregion_sound(*old(regions)) implies e.metaregion_sound(*regions)
                by {
                    if e.is_node() || e.is_frame() {
                        regions.inv_implies_correct_addr(e.meta_slot_paddr().unwrap());
                    }
                    if e.is_frame() && e.parent_level > 1 {
                        broadcast use crate::specs::mm::frame::meta_owners::axiom_mmio_usage_iff_mmio_paddr;
                        let pa = e.frame.unwrap().mapped_pa;
                        let nr_pages = page_size(e.parent_level) / PAGE_SIZE;
                        assert forall |j: usize| #![trigger frame_to_index((pa + j * PAGE_SIZE) as usize)]
                            0 < j < nr_pages implies {
                            let sub_idx = frame_to_index((pa + j * PAGE_SIZE) as usize);
                            &&& regions.slots.contains_key(sub_idx)
                            &&& regions.slot_owners[sub_idx].usage
                                    != crate::specs::mm::frame::meta_owners::PageUsage::MMIO ==> {
                                &&& regions.slot_owners[sub_idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                                &&& regions.slot_owners[sub_idx].inner_perms.ref_count.value() > 0
                            }
                        } by {
                            let sub_idx = frame_to_index((pa + j * PAGE_SIZE) as usize);
                            assert(old(regions).slots.contains_key(sub_idx));
                            assert(regions.slots.contains_key(sub_idx));
                        }
                    }
                };
            }

            return Ok(
                (#[verus_spec(with Tracked(owner))]
                self.cur_va_range(), item),
            );
        }
    }

    /// Moves the cursor forward to the next mapped virtual address.
    ///
    /// Scans forward from the cursor's current position through up to `len`
    /// bytes looking for a mapped (non-absent) leaf entry. If one is found,
    /// returns `Some(va)` where `va` is that entry's address and the cursor
    /// stops there. Otherwise returns `None` and the cursor advances past
    /// the search window.
    ///
    /// This is equivalent to [`find_next_impl`](Self::find_next_impl) with
    /// `find_unmap_subtree = false` and `split_huge = false`: the cursor only
    /// stops at leaf (frame) entries and never splits huge pages.
    ///
    /// # Panics
    ///
    /// Panics if:
    ///  - the length is longer than the remaining range of the cursor;
    ///  - the length is not page-aligned.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: the global safety invariants ([Self::invariants]) must hold.
    /// - **Liveness**: the function will panic if `len` is not page aligned or exceeds
    ///   the remaining locked range ([Self::find_next_panic_condition]).
    /// ## Postconditions
    /// - **Safety Invariants**: the global safety invariants hold after the call.
    /// - **Correctness**: if a frame is found, the returned address equals the cursor's
    ///   current position, the owner is within the locked range, and the cursor level
    ///   is below the guard level.
    /// - **Correctness**: the found entry is always a frame (never a node or absent).
    ///   If the old entry at the same VA was also a frame, its `prop` field is preserved.
    /// - **Correctness**: if no entry is found, the cursor advances at least `len` bytes
    ///   past its starting position.
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
    )]
    pub fn find_next(&mut self, len: usize) -> (res: Option<Vaddr>)
        requires
            old(self).invariants(*old(owner), *old(regions), *old(guards)),
        ensures
            !old(self).find_next_panic_condition(len),
            final(self).invariants(*final(owner), *final(regions), *final(guards)),
            res is Some ==> {
                &&& res.unwrap() == final(self).va
                &&& final(owner).level <= final(owner).guard_level
                &&& final(owner).in_locked_range()
            },
            res is Some ==> Self::find_not_unmap_subtree_ensures(*old(owner), *final(owner)),
            res is None ==> {
                &&& final(self).va >= old(self).va + len
            },
    {
        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.find_next_impl(len, false, false)
    }

    pub open spec fn find_not_unmap_subtree_ensures(old_owner: CursorOwner<C>, new_owner: CursorOwner<C>) -> bool
    {
        let old_cur_entry = old_owner.cur_entry_owner();
        let new_cur_entry = new_owner.cur_entry_owner();
        {
            &&& new_cur_entry.is_frame()
            &&& old_cur_entry.is_frame() ==>
                new_cur_entry.frame.unwrap().prop == old_cur_entry.frame.unwrap().prop
        }
    }

    /// Moves the cursor forward to the next fragment in the range.
    ///
    /// See [`Self::find_next`] for more details. Other than the semantics
    /// provided by [`Self::find_next`], this method also supports finding non-
    /// leaf entries and splitting huge pages if necessary.
    ///
    /// `find_unmap_subtree` specifies whether the cursor should stop at the
    /// highest possible level for unmapping. If `false`, the cursor will only
    /// stop at leaf entries.
    ///
    /// `split_huge` specifies whether the cursor should split huge pages when
    /// it finds a huge page that is mapped over the required range (`len`).
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: the global safety invariants ([Self::invariants]) must hold.
    /// - **Liveness**: the function will panic if `len` is not page aligned or exceeds
    /// the remaining locked range ([Self::find_next_panic_condition]).
    /// ## Postconditions
    /// - **Safety Invariants**: the global safety invariants hold after the call.
    /// - **Safety**: the cursor's VA never decreases.
    /// - **Correctness**: the returned address reflects the cursor's position after the call.
    /// - **Correctness**: if the result is `Some`, then the current entry is not absent.
    /// - **Correctness**: the `split_huge` flag ensures that the current entry fits the remaining
    /// range, and the cursor position is aligned to `page_size(level)`.
    /// - **Correctness**: if the `split_huge` flag was used, the mappings in the page table
    /// are updated by splitting the next frame to the appropriate size.
    /// - **Correctness**: if the `find_unmap_subtree` flag is false, the found entry is a frame
    /// - **Correctness**: if the `find_unmap_subtree` flag is false, the found frame has the same
    /// `prop` field as the previous frame in that va (even if it is the result of a split).
    /// - **Correctness**: mappings in the page table are preserved except for the possible split.
    /// - **Correctness**: if no entry is found, the cursor advances at least `len` bytes past its starting position.
    /// - **Correctness**: no mappings exist prior to the found entry within the search range. If no
    /// entry is found, then no mappings exist in the search range at all.
    /// - **Liveness**: The cursor is within the locked range, at a safe level, and properly aligned,
    /// ready to map or protect a new frame.
    /// ## Safety
    /// - This function never accesses nodes outside the locked range, because it is impossible to
    /// create a cursor below the range, and if the cursor is above the range this function will always panic.
    #[verifier::rlimit(800)]
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            old(self).invariants(*old(owner), *old(regions), *old(guards)),
        ensures
            !old(self).find_next_panic_condition(len),
            final(self).invariants(*final(owner), *final(regions), *final(guards)),
            final(self).barrier_va == old(self).barrier_va,
            final(self).guard_level == old(self).guard_level,
            final(self).va >= old(self).va,
            res is Some ==> {
                &&& res.unwrap() == final(self).va
                &&& final(owner).level <= final(owner).guard_level
                &&& final(owner).in_locked_range()
                &&& final(self).va < old(self).va + len
            },
            res is Some ==> !final(owner).cur_entry_owner().is_absent(),
            // VA alignment: when split_huge, the found entry's VA is aligned to page_size(level).
            // split_huge forces cur_entry_fits_range at the Frame return, meaning cur_va == align_down(cur_va, page_size).
            res is Some && split_huge ==> {
                &&& final(owner)@.mappings =~= old(owner)@.split_while_huge(page_size_spec(final(self).level)).mappings
                &&& final(self).va + page_size_spec(final(self).level) <= old(self).va + len
                &&& nat_align_down(final(self).va as nat, page_size_spec(final(self).level) as nat) as usize == final(self).va
            },
            res is Some && !find_unmap_subtree ==> Self::find_not_unmap_subtree_ensures(*old(owner), *final(owner)),
            res is Some && final(owner).cur_entry_owner().is_node() ==>
                final(owner)@.mappings =~= old(owner)@.mappings,
            old(owner)@.mappings.filter(|m: Mapping|
                old(self).va <= m.va_range.start < final(self).va) =~= Set::<Mapping>::empty(),
            res is None ==> {
                &&& final(self).va >= old(self).va + len
                &&& final(owner)@.mappings == old(owner)@.mappings
            },
            // If the found entry is past old_va, old_va was not covered by any mapping.
            res is Some && final(self).va > old(self).va ==> !old(owner)@.present(),
    )]
    fn find_next_impl(&mut self, len: usize, find_unmap_subtree: bool, split_huge: bool) -> Option<Vaddr>
    {
        vstd_extra::assert_eq!(len % PAGE_SIZE, 0);

        //*** KNOWN BUG: `self.va + len` could overflow. For now assume that it doesn't. ***
        assume(self.va + len <= usize::MAX);
        let end = self.va + len;

        vstd_extra::assert!(end <= self.barrier_va.end);

        assert(!self.find_next_panic_condition(len));
        assert(!old(self).find_next_panic_condition(len));

        let end = self.va + len;

        let ghost barrier_va = self.barrier_va;
        assert(barrier_va == old(self).barrier_va);

        let rcu_guard = self.rcu_guard;

        proof {
            owner.va.reflect_prop(self.va);
            owner.view_preserves_inv();
        }
        let ghost old_owner_cur_va: Vaddr = owner@.cur_va;

        // Track whether a split occurred during the loop.
        // If a split occurred, the next iteration returns Some (never None).
        let ghost mut split_happened: bool = false;

        while self.va < end
            invariant
                owner.inv(),
                self.inv(),
                self.wf(*owner),
                regions.inv(),
                self.inv(),
                old(owner)@.inv(),
                owner.in_locked_range() || self.va >= end,
                self.va >= old(self).va,
                end == old(self).va + len,
                end % PAGE_SIZE == 0,
                end <= self.barrier_va.end,
                !old(self).find_next_panic_condition(len),
                self.barrier_va == barrier_va,
                barrier_va == old(self).barrier_va,
                self.guard_level == old(self).guard_level,
                owner.children_not_locked(*guards),
                owner.nodes_locked(*guards),
                owner.metaregion_sound(*regions),
                !owner.popped_too_high,
                old_owner_cur_va == old(owner)@.cur_va,
                old_owner_cur_va == old(self).va,
                // Mapping preservation: if no split happened, mappings are unchanged.
                !split_happened ==> owner@.mappings == old(owner)@.mappings,
                !split_happened ==> owner@.mappings.filter(|m: Mapping|
                    old(self).va <= m.va_range.start < self.va) =~= Set::<Mapping>::empty(),
                old(owner)@.mappings.filter(|m: Mapping|
                    old(self).va <= m.va_range.start < self.va) =~= Set::<Mapping>::empty(),
                split_happened ==> owner.cur_entry_owner().is_frame(),
                split_happened ==> self.va < end,
                split_happened && old(owner).cur_entry_owner().is_frame() ==>
                    owner.cur_entry_owner().frame.unwrap().prop
                        == old(owner).cur_entry_owner().frame.unwrap().prop,
                split_happened ==>
                    owner@.mappings =~= old(owner)@.split_while_huge(page_size_spec(self.level)).mappings,
                !split_happened && old(owner).cur_entry_owner().is_frame() ==>
                    owner.cur_entry_owner().is_frame() &&
                    owner.cur_entry_owner().frame.unwrap().prop
                        == old(owner).cur_entry_owner().frame.unwrap().prop,
                (self.va > old(self).va && !split_happened) ==> !old(owner)@.present(),
                split_happened ==> self.va == old(self).va,
            decreases owner.max_steps(),
        {
            proof {
                owner.in_locked_range_level_le_nr_levels();
            }

            let ghost owner0 = *owner;

            let cur_va = self.va;
            #[verus_spec(with Tracked(owner))]
            let cur_va_range = self.cur_va_range();
            let cur_entry_fits_range = cur_va == cur_va_range.start && cur_va_range.end <= end;

            #[verus_spec(with Tracked(owner), Tracked(regions))]
            let mut cur_entry = self.cur_entry();
            assert(cur_entry.idx == owner0.index());

            let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
            let ghost cont0 = continuation;
            let tracked child_owner = continuation.take_child();
            let tracked node_owner = continuation.entry_own.node.tracked_borrow();

            let ghost regions_before_ref = *regions;

            #[verus_spec(with Tracked(&child_owner.value), Tracked(&node_owner), Tracked(regions))]
            let cur_child = cur_entry.to_ref();

            proof {
                continuation.put_child(child_owner);
                assert(continuation.children == cont0.children);
                owner.continuations.tracked_insert(owner.level - 1, continuation);
                assert(owner.continuations == owner0.continuations);
                owner.metaregion_slot_owners_preserved(regions_before_ref, *regions);
            }

            match cur_child {
                ChildRef::PageTable(pt) => {
                    if find_unmap_subtree && cur_entry_fits_range && (C::TOP_LEVEL_CAN_UNMAP()
                        || self.level != C::NR_LEVELS()) {

                        proof {
                            owner.va.reflect_prop(self.va);
                            if split_huge {
                                if self.va as usize == old(self).va as usize {
                                    owner.split_while_huge_at_level_noop();
                                }
                                owner.in_locked_range_level_le_nr_levels();
                                if self.level < NR_LEVELS {
                                    owner.va.align_down_inv(self.level as int);
                                    owner.va.align_down_concrete(self.level as int);
                                    owner.va.align_down(self.level as int).reflect_prop(
                                        nat_align_down(self.va as nat, page_size_spec(self.level) as nat) as Vaddr);
                                } else {
                                    owner.va.align_down_concrete(self.level as int);
                                    owner.va.align_down(self.level as int).reflect_prop(
                                        nat_align_down(self.va as nat, page_size_spec(self.level) as nat) as Vaddr);
                                }
                            }
                            // !present postcondition: split_happened ==> self.va == old(self).va,
                            // so self.va > old(self).va ==> !split_happened ==> !old(owner)@.present().
                        }
                        return Some(cur_va);
                    }
                    assert(owner.children_not_locked(*guards));

                    let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
                    let ghost cont0 = continuation;
                    let tracked mut child_owner = continuation.take_child();

                    let tracked mut parent_node_owner = continuation.entry_own.node.tracked_take();
                    let tracked mut child_node_owner = child_owner.value.node.tracked_take();

                    let ghost guards0 = *guards;

                    // SAFETY: The `pt` must be locked and no other guards exist.
                    #[verus_spec(with Tracked(&child_node_owner), Tracked(guards))]
                    let mut pt_guard = pt.make_guard_unchecked(rcu_guard);

                    #[verus_spec(with Tracked(&mut child_node_owner))]
                    let nr_children = pt_guard.nr_children();

                    proof {
                        child_owner.value.node = Some(child_node_owner);
                        continuation.put_child(child_owner);
                        continuation.entry_own.node = Some(parent_node_owner);
                        assert(cont0.children == continuation.children);
                        owner.continuations.tracked_insert(self.level - 1, continuation);
                        assert(owner.continuations == owner0.continuations);

                        owner.map_children_implies(
                            CursorOwner::node_unlocked(guards0),
                            CursorOwner::node_unlocked_except(*guards, child_node_owner.meta_perm.addr()));
                    }

                    assert(owner.only_current_locked(*guards));

                    if (nr_children != 0) {
                        proof { owner.cur_entry_node_implies_level_gt_1(); }

                        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
                        self.push_level(pt_guard);
                    } else {
                        let ghost guards_before_drop = *guards;
                        let ghost locked_addr = child_node_owner.meta_perm.addr();

                        let _ = ManuallyDrop::new(pt_guard, Tracked(guards));

                        proof {
                            owner.map_children_implies(
                                CursorOwner::node_unlocked_except(guards_before_drop, locked_addr),
                                CursorOwner::node_unlocked(*guards));
                            owner.move_forward_increases_va();
                            owner.move_forward_not_popped_too_high();
                            let ghost subtree = owner.cur_subtree();
                            PageTableOwner(subtree).view_rec_nr_children_zero_empty(subtree.value.path);
                            owner.cur_subtree_eq_filtered_mappings();
                        }

                        let ghost cur_slot_size = page_size_spec(self.level);
                        let ghost owner_before_move = *owner;
                        proof {
                            owner.va.reflect_prop(self.va);
                        }
                        let ghost va_before_move = self.va;
                        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
                        self.move_forward();

                        proof {
                            owner.va.reflect_prop(self.va);
                            assert(*owner == owner_before_move.move_forward_owner_spec());
                            owner_before_move.move_forward_owner_preserves_mappings();
                            if !split_happened {
                                assert(owner@.mappings == old(owner)@.mappings);
                                let ghost aligned_start = nat_align_down(va_before_move as nat, cur_slot_size as nat) as Vaddr;
                                assert(old(owner)@.mappings.filter(|m: Mapping|
                                    aligned_start <= m.va_range.start < aligned_start + cur_slot_size as usize)
                                    =~= Set::<Mapping>::empty());
                                lemma_nat_align_down_sound(va_before_move as nat, cur_slot_size as nat);
                                owner_before_move.va_plus_page_size_no_overflow(
                                    owner_before_move.level);
                                owner_before_move.va.align_up_advances_general(owner_before_move.level as int);
                                assert(self.va == (nat_align_down(va_before_move as nat, cur_slot_size as nat)
                                    + cur_slot_size as nat) as Vaddr);
                                assert(self.va <= aligned_start + cur_slot_size as usize);

                                assert(owner@.mappings.filter(|m: Mapping|
                                    old(self).va <= m.va_range.start < self.va)
                                    =~= Set::<Mapping>::empty()) by {
                                    assert forall |m: Mapping|
                                        !(#[trigger] old(owner)@.mappings.contains(m)
                                        && old(self).va <= m.va_range.start
                                        && m.va_range.start < self.va) by {
                                        if old(owner)@.mappings.contains(m)
                                            && old(self).va <= m.va_range.start
                                            && m.va_range.start < self.va {
                                            if m.va_range.start < va_before_move {
                                                assert(old(owner)@.mappings.filter(|m2: Mapping|
                                                    old(self).va <= m2.va_range.start < va_before_move)
                                                    .contains(m));
                                            } else {
                                                assert(old(owner)@.mappings.filter(|m2: Mapping|
                                                    aligned_start <= m2.va_range.start < aligned_start + cur_slot_size as usize)
                                                    .contains(m));
                                            }
                                        }
                                    };
                                };
                                if va_before_move as usize == old(self).va as usize {
                                    owner_before_move.cur_subtree_empty_not_present();
                                }
                            }
                        }
                    }

                    continue ;
                },
                ChildRef::None => {
                    let ghost cur_slot_size = page_size_spec(self.level);
                    proof {
                        owner.move_forward_increases_va();
                        owner.move_forward_not_popped_too_high();
                        let ghost subtree = owner.cur_subtree();
                        PageTableOwner(subtree).view_rec_absent_empty(subtree.value.path);
                        owner.cur_subtree_eq_filtered_mappings();
                    }

                    let ghost owner_before_move = *owner;
                    proof {
                        owner.va.reflect_prop(self.va);
                    }
                    let ghost va_before_move = self.va;
                    #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
                    self.move_forward();

                    proof {
                        owner.va.reflect_prop(self.va);
                        assert(*owner == owner_before_move.move_forward_owner_spec());
                        owner_before_move.move_forward_owner_preserves_mappings();
                        if !split_happened {
                            assert(owner@.mappings == old(owner)@.mappings);
                            let ghost aligned_start = nat_align_down(va_before_move as nat, cur_slot_size as nat) as Vaddr;
                            assert(old(owner)@.mappings.filter(|m: Mapping|
                                aligned_start <= m.va_range.start < aligned_start + cur_slot_size as usize)
                                =~= Set::<Mapping>::empty());
                            lemma_nat_align_down_sound(va_before_move as nat, cur_slot_size as nat);
                            owner_before_move.va_plus_page_size_no_overflow(
                                owner_before_move.level);
                            owner_before_move.va.align_up_advances_general(owner_before_move.level as int);
                            assert(self.va == (nat_align_down(va_before_move as nat, cur_slot_size as nat)
                                + cur_slot_size as nat) as Vaddr);
                            assert(self.va <= aligned_start + cur_slot_size as usize);

                            assert(owner@.mappings.filter(|m: Mapping|
                                old(self).va <= m.va_range.start < self.va)
                                =~= Set::<Mapping>::empty()) by {
                                assert forall |m: Mapping|
                                    !(#[trigger] old(owner)@.mappings.contains(m)
                                    && old(self).va <= m.va_range.start
                                    && m.va_range.start < self.va) by {
                                    if old(owner)@.mappings.contains(m)
                                        && old(self).va <= m.va_range.start
                                        && m.va_range.start < self.va {
                                        if m.va_range.start < va_before_move {
                                            assert(old(owner)@.mappings.filter(|m2: Mapping|
                                                old(self).va <= m2.va_range.start < va_before_move)
                                                .contains(m));
                                        } else {
                                            assert(old(owner)@.mappings.filter(|m2: Mapping|
                                                aligned_start <= m2.va_range.start < aligned_start + cur_slot_size as usize)
                                                .contains(m));
                                        }
                                    }
                                };
                            };
                            if va_before_move as usize == old(self).va as usize {
                                owner_before_move.cur_entry_absent_not_present();
                            }
                        }
                    }
                    continue ;
                },
                ChildRef::Frame(_, _, _) => {
                    assert(owner.max_steps() == owner0.max_steps());
                    if cur_entry_fits_range || !split_huge {
                        assert(!find_unmap_subtree && old(owner).cur_entry_owner().is_frame() ==>
                            owner.cur_entry_owner().frame.unwrap().prop
                            == old(owner).cur_entry_owner().frame.unwrap().prop) by {
                            if !find_unmap_subtree && old(owner).cur_entry_owner().is_frame() {
                                if !split_happened {
                                    assert(owner.continuations == owner0.continuations);
                                    assert(owner.level == owner0.level);
                                }
                            }
                        };
                        proof {
                            if split_huge {
                                if !split_happened && self.va as usize == old(self).va as usize {
                                    owner.split_while_huge_at_level_noop();
                                }
                                owner.in_locked_range_level_le_nr_levels();
                                owner.va.reflect_prop(self.va);
                                owner.va.align_down_inv(self.level as int);
                                owner.va.align_down_concrete(self.level as int);
                                owner.va.align_down(self.level as int).reflect_prop(
                                    nat_align_down(self.va as nat, page_size_spec(self.level) as nat) as Vaddr);
                            }
                        }
                        return Some(cur_va);
                    }
                    let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
                    let ghost cont_pre_split = continuation;
                    let ghost parent_pre_split = continuation.entry_own.node.unwrap();
                    let tracked mut child_owner = continuation.take_child();
                    let tracked mut parent_owner = continuation.entry_own.node.tracked_take();

                    proof {
                        assert(parent_owner.level > 1) by {
                            owner0.cur_va_range().start.reflect_prop(cur_va_range.start);
                            owner0.cur_va_range().end.reflect_prop(cur_va_range.end);
                            assert(cur_entry_fits_range == (
                                cur_va == owner0.cur_va_range().start.to_vaddr()
                                && owner0.cur_va_range().end.to_vaddr() <= end));
                            assert(cur_va == owner0.cur_va()) by {
                                owner0.va.reflect_prop(cur_va);
                            };
                            owner0.frame_not_fits_implies_level_gt_1(cur_entry_fits_range, cur_va, end);
                        };
                    }

                    proof {
                        assert(child_owner.value.metaregion_sound(*regions));
                        if child_owner.value.is_frame() {
                            assert(child_owner.value.frame_sub_pages_valid(*regions));
                        }
                    }
                    let split_child = (
                    #[verus_spec(with Tracked(&mut child_owner), Tracked(&mut parent_owner), Tracked(regions),
                        Tracked(guards))]
                    cur_entry.split_if_mapped_huge(rcu_guard)).expect(
                        "The entry must be a huge page",
                    );
                    let ghost child_owner_children = child_owner.children;
                    proof {
                        assert(forall |j: int| 0 <= j < NR_ENTRIES ==>
                            (#[trigger] child_owner_children[j]).unwrap().value.is_frame());
                    }

                    proof {
                        let ghost child_not_in_scope = !child_owner.value.in_scope;
                        assert(cur_entry.idx == cont0.idx);
                        let ghost reconstructed_entry_own = EntryOwner { node: Some(parent_owner), ..cont0.entry_own };
                        CursorContinuation::<'rcu, C>::rel_children_from_node_matching(
                            &cur_entry, child_owner.value, parent_owner, continuation.guard,
                            reconstructed_entry_own, cont0.idx);

                        continuation.put_child(child_owner);
                        continuation.entry_own.node = Some(parent_owner);
                        continuation.continuation_inv_holds_after_child_restore(
                            cont_pre_split, parent_pre_split);
                        owner.continuations.tracked_insert(owner.level - 1, continuation);

                        owner0.max_steps_partial_inv(*owner, owner.level as usize);
                        owner.cur_entry_node_implies_level_gt_1();
                    }

                    let ghost owner_before_push = *owner;
                    let ghost split_child_ghost = split_child;

                    #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
                    self.push_level(split_child);

                    proof {
                        split_happened = true;

                        let old_level = owner_before_push.level;
                        let cont = owner_before_push.continuations[old_level - 1];
                        let idx_below = owner_before_push.va.index[old_level - 2] as usize;
                        let (child_cont, _) = cont.make_cont_spec(idx_below, split_child_ghost);

                        assert(child_cont.children =~= child_owner_children);
                        assert(owner.cur_entry_owner().is_frame());

                        let ghost old_view = if split_happened {
                            old(owner)@.split_while_huge(page_size_spec(owner_before_push.level))
                        } else {
                            old(owner)@
                        };
                        owner.find_next_split_push_equals_split_while_huge(old_view);
                    }

                    continue ;
                },
            }
        }

        assert(self.va >= end);

        proof {
            assert(old(owner)@.mappings.filter(|m: Mapping|
                old(self).va <= m.va_range.start < old(self).va + len)
                =~= Set::<Mapping>::empty()) by {

                assert(owner@.mappings == old(owner)@.mappings);
                let scanned = owner@.mappings.filter(|m: Mapping|
                    old(self).va <= m.va_range.start < self.va);
                let target = old(owner)@.mappings.filter(|m: Mapping|
                    old(self).va <= m.va_range.start < old(self).va + len);
                assert forall |m: Mapping| target.contains(m) implies scanned.contains(m) by {
                    assert(old(self).va <= m.va_range.start < old(self).va + len);
                    assert(old(self).va + len <= self.va);
                    assert(m.va_range.start < self.va);
                };
            };
        }

        None
    }

    /// Jumps to the given virtual address.
    /// If the target address is out of the range, this method will return `Err`.
    ///
    /// # Panics
    ///
    /// This method panics if the address has bad alignment.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: the global safety invariants ([Self::invariants]) must hold.
    /// - **Safety**: the function will panic if `va` is not page aligned ([Self::jump_panic_condition]).
    /// ## Postconditions
    /// - **Safety Invariants**: the global safety invariants hold after the call.
    /// - **Correctness**: if `va` is within the barrier range, the result is `Ok` and the
    ///   cursor's VA is set to exactly `va`.
    /// - **Correctness**: if `va` is outside the barrier range, the result is `Err`.
    /// ## Safety
    /// - The mappings in the page table are unchanged; `jump` only repositions the cursor
    ///   by ascending to a common ancestor and updating the slot index within a node.
    /// - On a successful jump the cursor is guaranteed to be within the locked range, so
    ///   it will be safe to use.
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            old(self).invariants(*old(owner), *old(regions), *old(guards)),
            old(owner).in_locked_range(),
        ensures
            !old(self).jump_panic_condition(va),
            final(self).invariants(*final(owner), *final(regions), *final(guards)),
            final(self).barrier_va.start <= va < final(self).barrier_va.end ==> {
                &&& res is Ok
                &&& final(self).va == va
            },
            !(final(self).barrier_va.start <= va < final(self).barrier_va.end) ==> res is Err,
    )]
    pub fn jump(&mut self, va: Vaddr) -> Result<(), PageTableError>
    {
        vstd_extra::assert_eq!(va % PAGE_SIZE, 0);
        assert(!self.jump_panic_condition(va));
        assert(!old(self).jump_panic_condition(va));
        if !self.barrier_va.contains(&va) {
            return Err(PageTableError::InvalidVaddr(va));
        }
        loop
            invariant
                self.invariants(*owner, *regions, *guards),
                owner.in_locked_range(),
                self.level <= self.guard_level,
                self.barrier_va.start <= va < self.barrier_va.end,
                va % PAGE_SIZE == 0,
            decreases self.guard_level - self.level,
        {
            let node_size = page_size(self.level + 1);
            let node_start = self.va.align_down(node_size);

            proof {
                AbstractVaddr::reflect_prop(owner.va, self.va);

                if owner.in_locked_range() && self.level < self.guard_level {
                    owner.node_within_locked_range(self.level);
                }
            }

            // If the address is within the current node, we can jump directly.
            if node_start <= va && va - node_start < node_size {
                let ghost owner0 = *owner;
                let ghost new_va = AbstractVaddr::from_vaddr(va);
                let ghost old_va = self.va;
                self.va = va;
                proof {
                    AbstractVaddr::from_vaddr_wf(va);

                    lemma_nat_align_down_sound(old_va as nat, node_size as nat);

                    // At level == NR_LEVELS the quantifier in set_va_in_node is vacuous.
                    if self.level < NR_LEVELS as PagingLevel {
                        AbstractVaddr::same_node_indices_match(va, old_va, node_start, self.level);
                    }
                    AbstractVaddr::from_vaddr_to_vaddr_roundtrip(va);

                    owner.set_va_in_node(new_va);
                }

                return Ok(());
            }

            proof {
                owner.in_locked_range_level_le_guard_level();
                if owner.level < owner.guard_level {
                    owner.jump_not_in_node_level_lt_guard_minus_one(self.level, va, node_start);
                }
            }

            // When level == guard_level, the VA target is within the guard node
            // (barrier_va ⊂ locked_range ⊂ guard_node), so the if-check succeeds
            // and we return Ok before reaching here. Thus level < guard_level.
            proof {
                if self.level == self.guard_level {
                    let gl = self.guard_level as PagingLevel;
                    let ns = node_size as nat;
                    let ps_gl = page_size(gl) as nat;
                    lemma_page_size_ge_page_size((gl + 1) as PagingLevel);
                    lemma_page_size_ge_page_size(gl);
                    lemma_nat_align_down_sound(self.va as nat, ns);
                    lemma_nat_align_down_sound(owner.prefix.to_vaddr() as nat, ps_gl);
                    owner.prefix.align_down_concrete(gl as int);
                    owner.prefix.align_down(gl as int).reflect_prop(
                        nat_align_down(owner.prefix.to_vaddr() as nat, ps_gl) as Vaddr);
                    lemma_page_size_divides(gl, (gl + 1) as PagingLevel);
                    owner.in_locked_range_guard_index_eq_prefix();
                    lemma_nat_align_down_sound(owner.prefix.to_vaddr() as nat, ns);
                    lemma_nat_align_down_monotone(owner.prefix.to_vaddr() as nat, ps_gl, ns);

                    let pv = owner.prefix.to_vaddr() as nat;
                    let ad_ns = nat_align_down(pv, ns);
                    lemma_nat_align_down_within_block(pv, ps_gl, ns);
                    let ad_gl = nat_align_down(pv, ps_gl);
                    let au_gl = ad_gl + ps_gl;
                    assert(au_gl <= ad_gl + ps_gl);
                    assert(self.va as nat >= ad_gl);
                    assert(va < self.barrier_va.end);
                    assert(self.barrier_va.end == owner.locked_range().end);
                    assert(self.va < self.barrier_va.end);

                    owner.prefix_aligned_to_guard_level();
                    owner.prefix_plus_ps_no_overflow();
                    owner.prefix.aligned_align_up_advances(gl as int);
                    AbstractVaddr::to_vaddr_from_vaddr_roundtrip(owner.prefix.align_up(gl as int));
                    owner.prefix.align_up(gl as int).reflect_prop(au_gl as Vaddr);
                    assert(self.barrier_va.end == au_gl as usize);
                    assert(ad_ns <= self.va as nat) by(nonlinear_arith)
                        requires ad_gl >= ad_ns, self.va as nat >= ad_gl;
                    assert((self.va as nat) < ad_ns + ns) by(nonlinear_arith)
                        requires (self.va as nat) < au_gl, au_gl <= ad_gl + ps_gl,
                                 ad_gl + ps_gl <= ad_ns + ns;
                    lemma_nat_align_down_sound(self.va as nat, ns);

                    let r_va = self.va as nat - ad_ns;
                    assert(0 <= r_va && r_va < ns);
                    assert(self.va as nat == (ad_ns / ns) * ns + r_va) by {
                        lemma_nat_align_down_sound(pv, ns);
                        assert(ad_ns % ns == 0);
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ad_ns as int, ns as int);
                        vstd::arithmetic::mul::lemma_mul_is_commutative(ad_ns as int / ns as int, ns as int);
                    };
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                        self.va as int, ns as int, (ad_ns / ns) as int, r_va as int);
                    assert(nat_align_down(self.va as nat, ns) == ad_ns);
                    assert(node_start <= va);

                    owner.prefix.align_up(gl as int).reflect_prop(au_gl as Vaddr);
                    crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_monotone(
                        gl, (gl + 1) as PagingLevel);
                    assert(va - node_start < node_size);
                    assert(false);
                }
            }
            #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
            self.pop_level();
        }
    }

    /// Traverses forward to the end of [`Self::cur_va_range`].
    ///
    /// Advances the cursor past the current slot. If the current slot is the
    /// last entry in its page-table node, the cursor pops up one or more
    /// levels (via [`Self::pop_level`]) until it reaches a node with a
    /// subsequent entry, then positions itself at that entry.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: the object invariants for the cursor and metadata regions
    ///   must hold.
    /// - **Correctness**: the cursor must be within the locked range before the call.
    /// ## Postconditions
    /// - **Safety Invariants**: all safety invariants are preserved.
    /// - **Correctness**: cursor advances forward a slot, and pops levels if necessary.
    /// ## Safety
    /// - This function is safe because it only manipulates the cursor, it does not modify
    ///   any of the entries. It can advance the cursor outside of the locked range, however.
    #[verifier::rlimit(800)]
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
    )]
    fn move_forward(&mut self)
        requires
            old(owner).inv(),
            old(self).wf(*old(owner)),
            old(self).inv(),
            old(regions).inv(),
            old(owner).children_not_locked(*old(guards)),
            old(owner).nodes_locked(*old(guards)),
            old(owner).metaregion_sound(*old(regions)),
            old(owner).in_locked_range(),
            !old(owner).popped_too_high,
        ensures
            final(owner).inv(),
            final(self).wf(*final(owner)),
            final(self).inv(),
            final(regions).inv(),
            *final(owner) == old(owner).move_forward_owner_spec(),
            final(owner).max_steps() < old(owner).max_steps(),
            final(self).barrier_va == old(self).barrier_va,
            final(self).guard_level == old(self).guard_level,
            !final(owner).popped_too_high,
            final(owner).in_locked_range() || final(owner).above_locked_range(),
            final(owner).children_not_locked(*final(guards)),
            final(owner).nodes_locked(*final(guards)),
            final(owner).metaregion_sound(*final(regions)),
            final(owner).va == old(owner).va.align_up(old(self).level as int),
            final(self).va <= old(self).va + page_size_spec(old(self).level),
            // move_forward only calls pop_level, which does not touch regions.
            forall|idx: usize| #![trigger final(regions).slot_owners[idx].paths_in_pt]
                final(regions).slot_owners[idx].paths_in_pt == old(regions).slot_owners[idx].paths_in_pt,
            // Slots and slot_owners fully unchanged (pop_level is purely cursor manipulation).
            final(regions).slots =~= old(regions).slots,
            forall|idx: usize| #![trigger final(regions).slot_owners[idx]]
                final(regions).slot_owners[idx] == old(regions).slot_owners[idx],
    {
        let ghost owner0 = *owner;
        let ghost regions0 = *regions;
        proof {
            owner.in_locked_range_guard_index_eq_prefix();
            owner.move_forward_owner_decreases_steps();
            old(owner).move_forward_not_popped_too_high();
        }

        let ghost start_level = self.level;
        let ghost guard_level = self.guard_level;
        let ghost barrier_va = self.barrier_va;
        let ghost va = self.va;

        let next_va = (#[verus_spec(with Tracked(owner))]
            self.cur_va_range()).end;

        let ghost abs_va_down = owner0.va.align_down(start_level as int);
        let ghost abs_next_va = AbstractVaddr::from_vaddr(next_va);

        proof {
            AbstractVaddr::reflect_from_vaddr(next_va);
            owner0.va.reflect_prop(va);
            owner0.va.align_down_inv(start_level as int);
            owner0.va.align_down_concrete(start_level as int);
            owner0.va.align_down(start_level as int).reflect_prop(
                nat_align_down(va as nat, page_size(start_level as PagingLevel) as nat) as Vaddr);
            abs_next_va.reflect_prop(next_va);

            AbstractVaddr::reflect_eq(abs_next_va, owner0.va.align_up(start_level as int), next_va);

            AbstractVaddr::from_vaddr_wf(self.va);
            abs_va_down.next_index_wrap_condition(start_level as int);
        }

        while self.level < self.guard_level && pte_index::<C>(next_va, self.level) == 0
            invariant
                owner.inv(),
                self.wf(*owner),
                self.inv(),
                regions.inv(),
                self.guard_level == guard_level,
                self.barrier_va == barrier_va,
                owner0.va.reflect(va),
                abs_next_va == AbstractVaddr::from_vaddr(next_va),
                owner.move_forward_owner_spec() == owner0.move_forward_owner_spec(),
                abs_va_down.next_index(start_level as int) == abs_next_va,
                abs_va_down.wrapped(start_level as int, self.level as int),
                1 <= start_level <= self.level <= self.guard_level <= NR_LEVELS,
                owner.va == owner0.va,
                forall|i: int|
                    start_level <= i < NR_LEVELS ==> #[trigger] owner0.va.index[i - 1]
                        == abs_va_down.index[i - 1],
                forall|i: int|
                    self.level <= i < NR_LEVELS ==> #[trigger] owner0.va.index[i - 1]
                        == owner.continuations[i - 1].idx,
                owner.in_locked_range(),
                owner.children_not_locked(*guards),
                owner.nodes_locked(*guards),
                owner.metaregion_sound(*regions),
                *regions == regions0,
            decreases self.guard_level - self.level,
        {
            proof {
                assert(abs_next_va.index[self.level - 1] == 0);
                abs_va_down.wrapped_unwrap(start_level as int, self.level as int);
                abs_va_down.use_wrapped(start_level as int, self.level as int);
                assert(owner0.va.index[self.level - 1] + 1 == NR_ENTRIES);
                assert(owner.move_forward_owner_spec()
                    == owner.pop_level_owner_spec().0.move_forward_owner_spec());
                owner.pop_level_owner_preserves_invs(*guards, *regions);
            }

            #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
            self.pop_level();
        }

        let ghost index = abs_next_va.index[self.level - 1];

        self.va = next_va;

        proof {
            // Discharge do_inc_index's relaxed boundary precondition (idx + 1 <= top_end at
            // level NR_LEVELS). va doesn't change in the pop loop, so owner.va == owner0.va,
            // and owner0 had !popped_too_high && in_locked_range, which forces va below
            // locked_range.end and hence idx[NR_LEVELS-1] < top_end (strict).
            assert(owner.va == owner0.va);
            if owner.level == NR_LEVELS {
                owner0.in_locked_range_top_index_lt_top_end();
                assert(owner0.va.index[NR_LEVELS - 1]
                    < C::TOP_LEVEL_INDEX_RANGE_spec().end);
                assert(owner.continuations[owner.level - 1].idx + 1
                    <= C::TOP_LEVEL_INDEX_RANGE_spec().end);
            }
            owner.do_inc_index();
            owner.zero_preserves_all_but_va();
            owner.do_zero_below_level();
            owner0.move_forward_va_is_align_up();
            if owner.level < owner.guard_level {
                owner.prefix_in_locked_range();
            }
        }
    }

    /// Ascends one level in the page table by restoring the parent
    /// continuation and releasing the child node's lock.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: the object invariants for the cursor and metadata regions
    ///   must hold.
    /// - The cursor must be below the guard level (`level < guard_level`).
    /// ## Postconditions
    /// - **Safety Invariants**: all safety invariants are preserved; the metadata region is
    ///   completely unchanged.
    /// - **Correctness**: the ghost owner state restores the continuation of the current page
    ///   table node.
    /// ## Safety
    /// - It is safe to pop the cursor as long as it is not already at the top level,
    ///   but if it pops above the guard level, it is not safe to access the page table.
    ///   This is represented by the "popped too high" flag which must be cleared by the caller.
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
    )]
    fn pop_level(&mut self)
        requires
            old(self).level < old(self).guard_level,
            old(self).inv(),
            old(owner).inv(),
            old(regions).inv(),
            old(self).wf(*old(owner)),
            old(owner).in_locked_range(),
            old(owner).children_not_locked(*old(guards)),
            old(owner).nodes_locked(*old(guards)),
            old(owner).metaregion_sound(*old(regions)),
        ensures
            final(self).inv(),
            final(self).wf(*final(owner)),
            final(regions).inv(),
            final(owner).inv(),
            final(owner).children_not_locked(*final(guards)),
            final(owner).nodes_locked(*final(guards)),
            final(owner).metaregion_sound(*final(regions)),
            final(self).guard_level == old(self).guard_level,
            final(self).barrier_va == old(self).barrier_va,
            *final(owner) == old(owner).pop_level_owner_spec().0,
            final(owner).in_locked_range(),
            *final(regions) == *old(regions),
    {
        proof {
            let ghost child_cont = owner.continuations[owner.level - 1];
            assert(child_cont.all_some());
            assert(child_cont.inv());
            assert(self.path[self.level as usize - 1] is Some);
            assert(self.path[self.level as usize - 1].unwrap()
                == owner.continuations[owner.level - 1].guard);
            assert(guards.lock_held(
                owner.continuations[owner.level - 1].guard.inner.inner@.ptr.addr(),
            ));
            owner.pop_level_owner_preserves_invs(*guards, *regions);
        }
        let tracked guard = owner.pop_level_owner();

        let ghost owner0 = *owner;
        let ghost guards0 = *guards;

        let taken = self.path[self.level as usize - 1].take().unwrap();
        let _ = ManuallyDrop::new(taken, Tracked(guards));

        proof {
            owner.never_drop_restores_children_not_locked(guard, guards0, *guards);
            let ghost pre_pop = *old(owner);
            let ghost dropped_addr = guard.inner.inner@.ptr.addr();
            assert forall|i: int| #![trigger owner.continuations[i]] owner.level - 1 <= i < NR_LEVELS implies
                owner.continuations[i].guard.inner.inner@.ptr.addr() != dropped_addr by { };
            owner.never_drop_restores_nodes_locked(guard, guards0, *guards);
        }

        self.level = self.level + 1;

        assert(self.wf(*owner));
    }

    /// Descends one level into a child page-table node, acquiring its lock.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: the object invariants for the cursor and metadata regions
    ///   must hold.
    /// - **Correctness**: The current entry must be a node (`cur_entry_owner().is_node()`).
    /// - **Safety**: The caller must provide a guard permission with which to lock the child.
    /// ## Postconditions
    /// - **Safety Invariants**: all safety invariants are preserved.
    /// - **Correctness**: `self.level` decreases by 1, `self.va` is unchanged,
    ///   and abstract mappings are preserved.
    /// - **Correctness**: the ghost owner state creates a new continuation out of the pushed child node.
    /// - **Liveness**: the `popped_too_high` flag is cleared.
    /// ## Safety
    /// - This function locks the node that it descends to, ensuring that it is free from data races
    ///   until popped.
    /// - It otherwise does not change the page table or metadata regions.
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&MetaRegionOwners>,
            Tracked(guards): Tracked<&Guards<'rcu, C>>
    )]
    fn push_level(&mut self, child_pt: PageTableGuard<'rcu, C>)
        requires
            old(owner).inv(),
            regions.inv(),
            old(self).inv(),
            old(self).wf(*old(owner)),
            old(owner).cur_entry_owner().is_node(),
            old(owner).cur_entry_owner().node.unwrap().relate_guard(child_pt),
            old(owner).level > 1,
            old(owner).only_current_locked(*guards),
            old(owner).nodes_locked(*guards),
            old(owner).metaregion_sound(*regions),
            !old(owner).popped_too_high,
            old(owner).in_locked_range(),
            guards.lock_held(child_pt.inner.inner@.ptr.addr()),
        ensures
            final(owner).inv(),
            final(owner).children_not_locked(*guards),
            final(owner).nodes_locked(*guards),
            final(owner).metaregion_sound(*regions),
            final(self).inv(),
            final(self).wf(*final(owner)),
            final(self).guard_level == old(self).guard_level,
            final(self).barrier_va == old(self).barrier_va,
            final(self).level == old(self).level - 1,
            final(self).va == old(self).va,
            *final(owner) == old(owner).push_level_owner_spec(child_pt),
            final(owner).max_steps() < old(owner).max_steps(),
            old(owner)@.mappings == final(owner)@.mappings,
    {
        assert(owner.va.index.contains_key(owner.level - 2)) by {
            assert(owner.level >= 2 && owner.va.inv());
        };

        self.level = self.level - 1;
        // debug_assert_eq!(self.level, child_pt.level());

        // let old = self.path.get(self.level as usize - 1);
        self.path.set(self.level as usize - 1, Some(child_pt));

        proof {
            owner.in_locked_range_level_le_guard_level();
            owner.push_level_owner_preserves_invs(child_pt, *regions, *guards);
            owner.push_level_owner_decreases_steps(child_pt);
            owner.push_level_owner_preserves_va(child_pt);
            owner.push_level_owner_preserves_mappings(child_pt);
            owner.push_level_owner(child_pt);
        }
        // debug_assert!(old.is_none());
    }

    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&MetaRegionOwners>
    )]
    fn cur_entry(&mut self) -> (res: Entry<'_, 'rcu, C>)
        requires
            old(self).inv(),
            old(owner).inv(),
            old(owner).in_locked_range(),
            old(self).wf(*old(owner)),
            1 <= old(self).level <= 4,
            old(self).path[old(self).level as int - 1] is Some,
            old(owner).metaregion_sound(*regions),
        ensures
            final(owner).inv(),
            final(self).inv(),
            final(self).wf(*final(owner)),
            res.wf(final(owner).cur_entry_owner()),
            *final(self) == *old(self),
            *final(owner) == *old(owner),
            final(owner).metaregion_sound(*regions),
            res.idx == final(owner).continuations[final(owner).level - 1].idx,
            final(owner).continuations[final(owner).level - 1].entry_own.node.unwrap()
                .relate_guard(*res.node),
    {
        let ghost owner0 = *owner;

        let node = path_slot_as_mut(&mut self.path, self.level as usize - 1);
        let tracked mut parent_continuation = owner.continuations.tracked_remove(owner.level - 1);

        assert(parent_continuation.inv());
        let ghost cont0 = parent_continuation;
        let tracked child = parent_continuation.take_child();
        let tracked parent_own = parent_continuation.entry_own.node.tracked_take();

        let ghost index = frame_to_index(meta_to_frame(parent_own.meta_perm.addr()));

        let ghost ptei = AbstractVaddr::from_vaddr(self.va).index[owner.level - 1];

        proof {
            AbstractVaddr::from_vaddr_wf(self.va);
            owner0.va.reflect_prop(self.va);
        }

        #[verus_spec(with Tracked(&parent_own),
            Tracked(&child.value))]
        let res = node.entry(pte_index::<C>(self.va, self.level));

        proof {
            parent_continuation.entry_own.node = Some(parent_own);
            parent_continuation.put_child(child);
            assert(parent_continuation.children == cont0.children);
            owner.continuations.tracked_insert((owner.level - 1) as int, parent_continuation);
            assert(owner.continuations == owner0.continuations);
        }

        res
    }

    /// Gets the virtual address range that the current entry covers.
    ///
    /// Returns `[align_down(va, page_size(level)) .. align_down(va, page_size(level)) + page_size(level))`,
    /// i.e. the slot at the cursor's current level that contains the cursor's VA.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: the cursor owner must be valid (`owner.inv()`) and
    ///   the cursor must be well-formed w.r.t. the owner (`self.wf(*owner)`).
    /// ## Postconditions
    /// - **Correctness**: the returned range corresponds to the abstract `owner.cur_va_range()`.
    /// - **Correctness**: the range contains the cursor's va.
    /// - **Correctness**: when the cursor is at the start of the slot (`res.start == self.va`),
    ///   the range is exactly `[self.va .. self.va + page_size(level))`.
    /// ## Safety
    /// - This function does not modify any relevant structures, so it is perfectly safe.
    #[verus_spec(
        with Tracked(owner): Tracked<&CursorOwner<C>>
    )]
    fn cur_va_range(&self) -> (res: Range<Vaddr>)
        requires
            owner.inv(),
            self.wf(*owner),
            owner.in_locked_range(),
            1 <= self.level <= owner.guard_level,
        ensures
            owner.cur_va_range().start.reflect(res.start),
            owner.cur_va_range().end.reflect(res.end),
            res.start <= self.va,
            res.end <= self.va + page_size_spec(self.level),
            res.start == self.va ==> res.end == self.va + page_size_spec(self.level),
    {
        let page_size = page_size(self.level);
        let start = self.va.align_down(page_size);

        proof {
            owner.va.reflect_prop(self.va);
            owner.va.align_down_concrete(self.level as int);
            vstd_extra::arithmetic::lemma_nat_align_down_sound(
                owner.va.to_vaddr() as nat, page_size as nat);
            // `va + page_size(level) <= usize::MAX` from the cursor invariant; combined
            // with `nat_align_down(va, ps) <= va`, the aligned end stays below MAX.
            owner.va_plus_page_size_no_overflow(self.level);
            owner.va.align_up_advances_general(self.level as int);
            // align_up.to_vaddr() as nat == nat_align_down(va, ps) + ps.
            // start as nat == nat_align_down(va, ps) (from align_down_concrete + reflect).
            // So align_up.to_vaddr() == (start + page_size) as Vaddr.
            assert(owner.cur_va_range().start.reflect(start));
            // Bridge: align_up reflects its own to_vaddr, which == start + page_size.
            owner.cur_va_range().end.reflect_to_vaddr();
            assert(owner.cur_va_range().end.to_vaddr()
                == (start + page_size) as Vaddr);
        }

        start..start + page_size
    }
}

/*
impl<C: PageTableConfig> Drop for Cursor<'_, C> {
    fn drop(&mut self) {
        locking::unlock_range(self);
    }
}
*/

#[verus_verify]
impl<'rcu, C: PageTableConfig, A: InAtomicMode> CursorMut<'rcu, C, A> {
    /// Creates a cursor claiming exclusive access over the given range.
    ///
    /// The cursor created will only be able to map, query or jump within the given
    /// range. Out-of-bound accesses will result in panics or errors as return values,
    /// depending on the access method.
    #[verus_spec(r =>
        with Tracked(pt_own): Tracked<PageTableOwner<C>>,
            Ghost(root_guard): Ghost<PageTableGuard<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            pt_own.inv(),
            // Per-config tightening; see `Cursor::new`.
            va.end as int <= C::LOCKED_END_BOUND_spec(),
        ensures
            Cursor::<C, A>::cursor_new_success_conditions(va) ==> {
                &&& r is Ok
                &&& r.unwrap().0.0.invariants(*r.unwrap().1, *final(regions), *final(guards))
                &&& r.unwrap().1.in_locked_range()
                &&& r.unwrap().0.0.level == r.unwrap().0.0.guard_level
                &&& r.unwrap().0.0.va < r.unwrap().0.0.barrier_va.end
                &&& r.unwrap().0.0.va == va.start
                &&& r.unwrap().0.0.barrier_va == *va
            },
            !Cursor::<C, A>::cursor_new_success_conditions(va) ==> r is Err,
            // cursor_mut only acquires locks on page-table node slots; it does not
            // set paths_in_pt for data-frame slots. Any frame that was item_not_mapped
            // before the call remains item_not_mapped after.
            forall |item: C::Item| #![trigger Self::item_not_mapped(item, *old(regions))]
                Self::item_not_mapped(item, *old(regions)) ==>
                Self::item_not_mapped(item, *final(regions)),
            // CursorMut::new inherits the weakened Cursor::new preservation:
            // PT-node allocations come from UNUSED slots, so any slot that
            // was already in use keeps its paths_in_pt.
            forall |idx: usize| #![trigger final(regions).slot_owners[idx].paths_in_pt]
                old(regions).slot_owners[idx].inner_perms.ref_count.value()
                    != crate::specs::mm::frame::meta_owners::REF_COUNT_UNUSED
                ==> final(regions).slot_owners[idx].paths_in_pt
                        == old(regions).slot_owners[idx].paths_in_pt,
    )]
    pub fn new(pt: &'rcu PageTable<C>, guard: &'rcu A, va: &Range<Vaddr>)
    -> Result<(Self, Tracked<CursorOwner<'rcu, C>>), PageTableError> {
        let res = #[verus_spec(with Tracked(pt_own), Ghost(root_guard), Tracked(regions), Tracked(guards))]
        Cursor::new(pt, guard, va);
        match res {
            Ok((inner_cursor, tracked_owner)) => {
                proof {
                    // In the Ok branch, cursor_new_success_conditions(va) holds
                    // (from !conditions ==> Err, contrapositive gives Ok ==> conditions).
                    // Therefore the success-case ensures apply, giving us invariants.
                    assert(inner_cursor.invariants(*tracked_owner, *regions, *guards));
                    assert(CursorMut::<C, A>(inner_cursor).0.invariants(*tracked_owner, *regions, *guards));
                }
                Ok((Self(inner_cursor), tracked_owner))
            }
            Err(e) => Err(e),
        }
    }

    /// Moves the cursor forward to the next mapped virtual address.
    ///
    /// Scans forward from the cursor's current position through up to `len`
    /// bytes looking for a mapped (non-absent) leaf entry. If one is found,
    /// returns `Some(va)` where `va` is that entry's address and the cursor
    /// stops there. Otherwise returns `None` and the cursor advances past
    /// the search window.
    ///
    /// This is the same as [`Cursor::find_next`]. The cursor only stops at
    /// leaf (frame) entries and never splits huge pages.
    ///
    /// # Panics
    ///
    /// Panics if:
    ///  - the length is longer than the remaining range of the cursor;
    ///  - the length is not page-aligned.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: the global safety invariants ([`Cursor::invariants`]) must hold.
    /// - **Liveness**: the function will panic if `len` is not page aligned or exceeds
    ///   the remaining locked range ([`Cursor::find_next_panic_condition`]).
    /// ## Postconditions
    /// - **Safety Invariants**: the global safety invariants hold after the call.
    /// - **Correctness**: if a frame is found, the returned address equals the cursor's
    ///   current position, the owner is within the locked range, and the cursor level
    ///   is below the guard level.
    /// - **Correctness**: the found entry is always a frame (never a node or absent).
    ///   If the old entry at the same VA was also a frame, its `prop` field is preserved.
    /// - **Correctness**: if no entry is found, the cursor advances at least `len` bytes
    ///   past its starting position.
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
    )]
    pub fn find_next(&mut self, len: usize) -> (res: Option<Vaddr>)
        requires
            old(self).0.invariants(*old(owner), *old(regions), *old(guards)),
        ensures
            !old(self).0.find_next_panic_condition(len),
            final(self).0.invariants(*final(owner), *final(regions), *final(guards)),
            res is Some ==> {
                &&& res.unwrap() == final(self).0.va
                &&& final(owner).level <= final(owner).guard_level
                &&& final(owner).in_locked_range()
            },
    {
        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.0.find_next(len)
    }

    /// Jumps to the given virtual address.
    ///
    /// This is the same as [`Cursor::jump`].
    ///
    /// # Panics
    ///
    /// This method panics if the address is out of the range where the cursor is required to operate,
    /// or has bad alignment.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: the global safety invariants ([`Cursor::invariants`]) must hold.
    /// - **Correctness**: the function will panic if `va` is not page aligned
    ///   ([`Cursor::jump_panic_condition`]).
    /// ## Postconditions
    /// - **Safety Invariants**: the global safety invariants hold after the call.
    /// - **Correctness**: if `va` is within the barrier range, the result is `Ok` and the
    ///   cursor's VA is set to exactly `va`.
    /// - **Correctness**: if `va` is outside the barrier range, the result is `Err`.
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
    )]
    pub fn jump(&mut self, va: Vaddr) -> (res: Result<(), PageTableError>)
        requires
            old(self).0.invariants(*old(owner), *old(regions), *old(guards)),
            old(owner).in_locked_range(),
        ensures
            !old(self).0.jump_panic_condition(va),
            final(self).0.invariants(*final(owner), *final(regions), *final(guards)),
            final(self).0.barrier_va.start <= va < final(self).0.barrier_va.end ==> {
                &&& res is Ok
                &&& final(self).0.va == va
            },
            !(final(self).0.barrier_va.start <= va < final(self).0.barrier_va.end) ==> res is Err,
    {
        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.0.jump(va)
    }

    /// Gets the current virtual address.
    pub fn virt_addr(&self) -> Vaddr
        returns
            self.0.va,
    {
        self.0.virt_addr()
    }

    /// Queries the mapping at the current virtual address.
    ///
    /// If the cursor is pointing to a valid virtual address that is locked,
    /// it will return the virtual address range and the item at that slot.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: the global safety invariants ([Self::invariants])
    /// must hold before the call.
    /// ## Postconditions
    /// - **Safety Invariants**: the global safety invariants hold after the call
    /// - **Correctness**: if the cursor is within the locked range, the result will be `Ok`;
    /// otherwise it will be an error.
    /// - **Correctness**: if there is a mapping present ([Self::query_some_condition]),
    /// then the second field of the result will `Some(item)`, where `item` is the mapping,
    /// and the first field will give its range.
    /// - **Correctness**: if there is no mapping present, then the second field of the result will be
    /// 'None'.
    /// - **Safety**: all frames' relations with the metadata region are preserved.
    /// ## Safety
    /// - The global invariants ensure that the first node we pass through is already locked,
    /// and the loop invariant makes the same guarantee for subsequent nodes.
    /// - This function does not change anything in the metadata region except for incrementing 
    /// the reference counts of nodes when it descends into them.
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            old(self).0.invariants(*old(owner), *old(regions), *old(guards)),
            old(owner).in_locked_range(),
        ensures
            final(self).0.invariants(*final(owner), *final(regions), *final(guards)),
            old(owner).in_locked_range() ==> res is Ok,
            res matches Ok(state) ==>
                final(self).0.query_some_condition(*final(owner)) ==>
                final(self).0.query_some_ensures(*final(owner), state),
            res matches Ok(state) ==>
                !final(self).0.query_some_condition(*final(owner)) ==>
                final(self).0.query_none_ensures(*final(owner), state),
            old(owner)@.mappings == final(owner)@.mappings,
    )]
    pub fn query(&mut self) -> (res: Result<PagesState<C>, PageTableError>) {
        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.0.query()
    }

    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            old(self).0.invariants(*old(owner), *old(regions), *old(guards)),
            old(owner).in_locked_range(),
            ChildRef::PageTable(pt).wf(old(owner).cur_entry_owner())
        ensures
            final(self).0.invariants(*final(owner), *final(regions), *final(guards)),
            final(owner).in_locked_range(),
            final(owner).va == old(owner).va,
            final(self).0.level == old(self).0.level - 1,
            final(self).0.guard_level == old(self).0.guard_level,
            final(self).0.barrier_va == old(self).0.barrier_va,
            final(owner)@ == old(owner)@,
            *final(regions) == *old(regions),
    )]
    fn map_branch_pt(&mut self, pt: PageTableNodeRef<'rcu, C>, rcu_guard: &'rcu A) {

        let ghost guards0 = *guards;

        let ghost level_key = owner.level as int - 1;
        let ghost cont_orig = owner.continuations[level_key];

        let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
        let tracked mut child_owner = continuation.take_child();
        let ghost orig_child_owner = child_owner;
        let tracked mut child_node = child_owner.value.node.tracked_take();

        // SAFETY: The `pt` must be locked and no other guards exist.
        #[verus_spec(with Tracked(&child_node), Tracked(guards))]
        let pt_guard = pt.make_guard_unchecked(rcu_guard);

        proof {
            child_owner.value.node = Some(child_node);
            assert(child_owner == orig_child_owner);
            continuation.put_child(child_owner);
            cont_orig.take_put_child();
            assert(continuation == cont_orig);
            owner.continuations.tracked_insert(owner.level - 1, continuation);
            assert(owner.continuations =~= old(owner).continuations);
            assert(*owner == *old(owner));

            owner.map_children_implies(
                CursorOwner::node_unlocked(guards0),
                CursorOwner::node_unlocked_except(*guards, child_node.meta_perm.addr()),
            );

            owner.cur_entry_node_implies_level_gt_1();
        }
        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.0.push_level(pt_guard);

        proof { assert(owner@ == old(owner)@); }
    }

    #[verifier::rlimit(200)]
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            old(self).0.invariants(*old(owner), *old(regions), *old(guards)),
            old(owner).in_locked_range(),
            level < old(self).0.guard_level,
            level >= 1,
        ensures
            final(self).0.invariants(*final(owner), *final(regions), *final(guards)),
            final(owner).va == old(owner).va,
            final(self).0.guard_level == old(self).0.guard_level,
            final(self).0.barrier_va == old(self).0.barrier_va,
            final(self).0.level == level,
            final(owner).in_locked_range(),
            final(owner)@ == old(owner)@.split_while_huge(page_size(level)),
            forall |item: C::Item| #![trigger Self::item_slot_in_regions(item, *old(regions))]
                Self::item_slot_in_regions(item, *old(regions)) ==>
                Self::item_slot_in_regions(item, *final(regions)),
            (level <= old(self).0.level && old(owner).cur_entry_owner().is_absent()) ==> final(owner).cur_entry_owner().is_absent(),
            forall|idx: usize|
                old(regions).slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED ==>
                (#[trigger] final(regions).slot_owners[idx]) == old(regions).slot_owners[idx],
            // `regions.slots` is monotonic — PT-node allocation removes-and-re-inserts
            // each slot it touches, so all old keys are preserved.
            forall|idx: usize| #![trigger final(regions).slots.contains_key(idx)]
                old(regions).slots.contains_key(idx) ==> final(regions).slots.contains_key(idx),
    )]
    pub fn map_loop(&mut self, level: PagingLevel, rcu_guard: &'rcu A) {
        let ghost guard_level = self.0.guard_level;
        let ghost barrier_va = self.0.barrier_va;
        let ghost owner0 = *owner;
        proof {
            assert(owner0.inv());
            owner0.view_preserves_inv();
            owner0.split_while_huge_at_level_noop();
        }

        while self.0.level != level
            invariant
                owner.inv(),
                owner0.inv(),
                owner.va == owner0.va,
                self.0.wf(*owner),
                regions.inv(),
                self.0.inv(),
                self.0.guard_level == guard_level,
                self.0.barrier_va == barrier_va,
                level < self.0.guard_level,
                level >= 1,
                owner.in_locked_range(),
                owner.children_not_locked(*guards),
                owner.nodes_locked(*guards),
                owner.metaregion_sound(*regions),
                !owner.popped_too_high,
                owner@ == owner0@.split_while_huge(page_size(self.0.level)),
                forall |item: C::Item| #![trigger Self::item_slot_in_regions(item, *old(regions))]
                    Self::item_slot_in_regions(item, *old(regions)) ==>
                    Self::item_slot_in_regions(item, *regions),
                (self.0.level <= owner0.level && owner0.cur_entry_owner().is_absent()) ==> owner.cur_entry_owner().is_absent(),
                self.0.level <= owner0.level || self.0.level <= level,
                self.0.level < level ==> self.0.level >= owner0.level,
                self.0.level < level ==> owner@ =~= owner0@,
                forall|idx: usize|
                    old(regions).slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED ==>
                    (#[trigger] regions.slot_owners[idx]) == old(regions).slot_owners[idx],
                forall|idx: usize| #![trigger regions.slots.contains_key(idx)]
                    old(regions).slots.contains_key(idx) ==> regions.slots.contains_key(idx),
            decreases abs(level - self.0.level),
        {
            if self.0.level < level {
                let ghost owner_pre_pop = *owner;
                let ghost level_pre_pop = self.0.level;

                proof {
                    owner.pop_level_owner_preserves_invs(*guards, *regions);
                }

                #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
                self.0.pop_level();

                proof {
                    owner_pre_pop.pop_level_owner_preserves_mappings();
                    assert(owner@ =~= owner0@);
                    owner.split_while_huge_at_level_noop();
                    assert(owner@ == owner0@.split_while_huge(page_size(self.0.level)));
                    assert(self.0.level > owner0.level);
                }
                continue ;
            }
            // We are at a higher level, go down.

            let ghost cur_level = self.0.level;
            #[verus_spec(with Tracked(owner), Tracked(regions))]
            let mut cur_entry = self.0.cur_entry();

            let ghost owner1 = *owner;
            let ghost regions0 = *regions;
            let ghost cont0 = owner.continuations[owner.level - 1];

            let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
            let tracked child_owner = continuation.take_child();
            let ghost child_entry_val = child_owner.value;
            let tracked parent_owner = continuation.entry_own.node.tracked_borrow();

            let ghost regions_before_ref = *regions;

            #[verus_spec(with Tracked(&child_owner.value), Tracked(&parent_owner),
                Tracked(regions))]
            let cur_child = cur_entry.to_ref();

            proof {
                cont0.take_put_child();
                continuation.put_child(child_owner);
                assert(continuation == cont0);
                owner.continuations.tracked_insert(owner.level - 1, continuation);

                assert(owner.continuations =~= owner1.continuations);
                owner1.metaregion_slot_owners_preserved(regions_before_ref, *regions);
            }

            let ghost regions_after_ref = *regions;

            match cur_child {
                ChildRef::PageTable(pt) => {
                    let ghost owner_pre_pt = *owner;
                    let ghost level_pre_pt = self.0.level;

                    #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
                    self.map_branch_pt(pt, rcu_guard);

                    proof {
                        lemma_page_size_monotone(self.0.level, level_pre_pt);
                        crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_ge_page_size(level_pre_pt);
                        owner0.view_preserves_inv();
                        owner0@.split_while_huge_compose(page_size(level_pre_pt), page_size(self.0.level));
                        owner_pre_pt.split_while_huge_node_noop();
                        assert(child_entry_val == owner1.cur_entry_owner());
                        assert(level_pre_pt <= owner0.level);
                    }

                    continue ;
                },
                ChildRef::None => {
                    let ghost owner_pre_none = *owner;
                    let ghost level_pre_none = cur_level;
                    let ghost guards_pre_none = *guards;

                    let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
                    let ghost cont_pre_alloc = continuation;
                    let tracked mut child_owner = continuation.take_child();
                    let ghost old_child_value = child_owner.value;
                    let tracked mut parent_owner = continuation.entry_own.node.tracked_take();
                    proof {
                        assert(cur_entry.node_matching(
                            child_owner.value, parent_owner, continuation.guard));
                    }

                    let child_guard = (
                    #[verus_spec(with Tracked(&mut child_owner), Tracked(&mut parent_owner), Tracked(regions), Tracked(guards))]
                    cur_entry.alloc_if_none(rcu_guard)).unwrap();

                    let ghost new_node_addr = child_owner.value.node.unwrap().meta_perm.addr();
                    let ghost new_child_value = child_owner.value;

                    let ghost new_pt_idx = frame_to_index(new_child_value.meta_slot_paddr().unwrap());
                    let ghost child_owner_children = child_owner.children;

                    proof {
                        assert(forall|i: int| 0 <= i < NR_ENTRIES ==>
                            (#[trigger] child_owner_children[i]) is Some
                            && child_owner_children[i].unwrap().value.is_absent());

                        let ghost child_not_in_scope = !child_owner.value.in_scope;
                        let ghost reconstructed_entry_own = EntryOwner { node: Some(parent_owner), ..cont_pre_alloc.entry_own };
                        CursorContinuation::<'rcu, C>::rel_children_from_node_matching(
                            &cur_entry, child_owner.value, parent_owner, continuation.guard,
                            reconstructed_entry_own, cont_pre_alloc.idx);

                        cont_pre_alloc.take_put_child();
                        continuation.entry_own.node = Some(parent_owner);
                        continuation.put_child(child_owner);
                        owner.continuations.tracked_insert(owner.level - 1, continuation);

                        assert(owner.cur_entry_owner().node.unwrap().meta_perm.addr() == new_node_addr);

                        assert forall|i: int|
                            owner_pre_none.level <= i < NR_LEVELS implies #[trigger] owner.continuations[i]
                            == owner_pre_none.continuations[i] by {};

                        let f_unlocked = CursorOwner::<'rcu, C>::node_unlocked(guards_pre_none);
                        let g_unlocked = CursorOwner::<'rcu, C>::node_unlocked_except(*guards, new_node_addr);
                        let f_sound = PageTableOwner::<C>::metaregion_sound_pred(regions_after_ref);
                        let g_sound = PageTableOwner::<C>::metaregion_sound_pred(*regions);

                        Entry::<C>::alloc_if_none_metaregion_sound_preserved(old_child_value, new_child_value, regions_after_ref, *regions);

                        let idx = cont_pre_alloc.idx as int;
                        let cont_final = owner.continuations[owner.level - 1];

                        assert forall|i: int|
                            #![auto]
                            owner.level <= i < NR_LEVELS implies
                                owner.continuations[i].map_children(g_unlocked)
                                && owner.continuations[i].map_children(g_sound)
                        by {
                            owner_pre_none.continuations[i].map_children_lift(f_unlocked, g_unlocked);
                            owner_pre_none.continuations[i].map_children_lift(f_sound, g_sound);
                        };

                        cont_final.map_children_lift_skip_idx(cont_pre_alloc, idx, f_unlocked, g_unlocked);
                        cont_final.map_children_lift_skip_idx(cont_pre_alloc, idx, f_sound, g_sound);

                        assert(owner.path_metaregion_sound(*regions)) by {
                            let new_pt_idx = frame_to_index(new_child_value.meta_slot_paddr().unwrap());
                            assert forall|i: int| #![trigger owner.continuations[i]]
                                owner.level - 1 <= i < NR_LEVELS implies
                                    owner.continuations[i].entry_own.metaregion_sound(*regions) by {
                                if i >= owner.level as int {
                                    assert(owner.continuations[i] == owner_pre_none.continuations[i]);
                                }
                                owner_pre_none.inv_continuation(i);
                                let eo = owner_pre_none.continuations[i].entry_own;
                                assert(eo.inv() && eo.is_node());
                                assert(eo.metaregion_sound(regions_after_ref));
                                let eo_idx = frame_to_index(eo.meta_slot_paddr().unwrap());
                                assert(regions_after_ref.slot_owners[eo_idx].inner_perms.ref_count.value()
                                    != REF_COUNT_UNUSED);
                                assert(eo_idx != new_pt_idx);
                                assert(regions.slot_owners[eo_idx] == regions_after_ref.slot_owners[eo_idx]);
                            };
                        };

                        assert(owner.continuations[owner.level - 1].all_some()) by {
                            let cont_new = owner.continuations[owner.level - 1];
                            assert(cont_new.children[cont_new.idx as int] is Some);
                            assert forall|i: int| 0 <= i < NR_ENTRIES implies cont_new.children[i] is Some by {
                                if i != cont_new.idx as int {
                                    assert(cont_pre_alloc.children[i] is Some);
                                }
                            };
                        };
                        assert(owner.continuations[owner.level - 1].inv()) by {
                            let cont_new = owner.continuations[owner.level - 1];
                            assert(cont_new.entry_own.inv());
                            assert(cont_new.level() == cont_pre_alloc.level());
                            assert(cont_new.tree_level == INC_LEVELS - cont_new.level() - 1);
                            cont_new.continuation_inv_holds_after_child_restore(
                                cont_pre_alloc, cont_pre_alloc.entry_own.node.unwrap());
                        };
                        owner.map_branch_none_inv_holds(owner_pre_none);
                    }

                    let ghost owner_pre_push = *owner;
                    #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
                    self.0.push_level(child_guard);

                    proof {
                        owner_pre_push.map_branch_none_no_new_mappings(owner_pre_none);
                        assert(owner.continuations[owner.level - 1].children == child_owner_children);
                        owner.map_branch_none_cur_entry_absent();

                        lemma_page_size_monotone(self.0.level, level_pre_none);
                        crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_ge_page_size(level_pre_none);
                        owner0.view_preserves_inv();
                        owner0@.split_while_huge_compose(page_size(level_pre_none), page_size(self.0.level));
                        owner_pre_none.split_while_huge_absent_noop(page_size(self.0.level));
                        assert(owner@ == owner0@.split_while_huge(page_size(self.0.level)));
                    }

                    assert forall |item: C::Item|
                        Self::item_slot_in_regions(item, *old(regions))
                        implies #[trigger] Self::item_slot_in_regions(item, *regions)
                    by {
                        assert(Self::item_slot_in_regions(item, regions0));
                        let idx = frame_to_index(C::item_into_raw(item).0);
                        assert(regions_after_ref.slots.contains_key(idx));
                        assert(Self::item_slot_in_regions(item, regions_after_ref));
                    };

                    continue ;
                },
                ChildRef::Frame(_, _, _) => {
                    let ghost owner_before_frame = *owner;
                    let ghost level_before_frame = cur_level;

                    let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
                    let ghost cont_pre_split = continuation;
                    let ghost parent_pre_split = continuation.entry_own.node.unwrap();
                    let tracked mut child_owner = continuation.take_child();
                    let tracked mut parent_owner = continuation.entry_own.node.tracked_take();

                    proof {
                        assert(child_owner.value.metaregion_sound(*regions));
                        if child_owner.value.is_frame() {
                            assert(child_owner.value.frame_sub_pages_valid(*regions));
                        }
                    }
                    let split_child = (
                    #[verus_spec(with Tracked(&mut child_owner), Tracked(&mut parent_owner), Tracked(regions),
                            Tracked(guards))]
                    cur_entry.split_if_mapped_huge(rcu_guard)).unwrap();

                    proof {
                        continuation.put_child(child_owner);
                        continuation.entry_own.node = Some(parent_owner);
                        owner.continuations.tracked_insert(owner.level - 1, continuation);
                        assert(owner.continuations[owner.level - 1].inv()) by {
                            let cont_new = owner.continuations[owner.level - 1];
                            cont_new.continuation_inv_holds_after_child_restore(
                                cont_pre_split, parent_pre_split);
                        };
                        owner.map_branch_none_inv_holds(owner_before_frame);
                    }

                    #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
                    self.0.push_level(split_child);

                    proof {
                        owner.map_branch_frame_split_while_huge(owner0, owner_before_frame, level_before_frame as int);
                        assert(owner@ == owner0@.split_while_huge(page_size(self.0.level)));
                    }

                    assert forall |item: C::Item|
                        Self::item_slot_in_regions(item, *old(regions))
                        implies #[trigger] Self::item_slot_in_regions(item, *regions)
                    by {
                        assert(Self::item_slot_in_regions(item, regions0));
                        let idx = frame_to_index(C::item_into_raw(item).0);
                        assert(regions_after_ref.slots.contains_key(idx));
                        assert(Self::item_slot_in_regions(item, regions_after_ref));
                    };
                    assert forall|idx: usize|
                        old(regions).slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
                    implies
                        (#[trigger] regions.slot_owners[idx]) == old(regions).slot_owners[idx]
                    by {
                        assert(regions0.slot_owners[idx] == old(regions).slot_owners[idx]);
                        assert(regions_after_ref.slot_owners[idx] == regions0.slot_owners[idx]);
                    };
                    assert(!owner0.cur_entry_owner().is_absent()) by {
                        assert(child_entry_val == owner1.cur_entry_owner());
                        assert(level_before_frame <= owner0.level);
                    };
                    continue ;
                },
            }
        }
        assert((level <= owner0.level && old(owner).cur_entry_owner().is_absent()) ==> owner.cur_entry_owner().is_absent());
    }

    /// Maps the item starting from the current address to a physical address range.
    ///
    /// Writes a page-table entry for `item` at the cursor's current slot,
    /// descending through intermediate levels as needed. If the slot already
    /// contains a mapping, the old entry is replaced and returned as
    /// `Err(PageTableFrag)` for the caller to drop after TLB coherence.
    /// If the slot was absent, returns `Ok(())`.
    ///
    /// After the call the cursor has advanced past the mapped region.
    ///
    /// # Panics
    ///
    /// This function will panic if
    ///  - the virtual address range to be mapped is out of the locked range;
    ///  - the current virtual address is not aligned to the page size of the
    ///    item to be mapped.
    ///
    /// # Safety
    ///
    /// The caller should ensure that
    ///  - the range being mapped does not affect kernel's memory safety;
    ///  - the physical address to be mapped is valid and safe to use.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: the global safety invariants ([`Cursor::invariants`]) must hold.
    /// - **Safety**: the cursor must be within the locked range, below the
    ///   guard level, and before the barrier end ([`Self::map_cursor_requires`]).
    /// - **Correctness**: the entry owner must be valid and the item's level must
    ///   fit within the guard level ([`Self::item_wf`]).
    /// - **Safety**: the item's metadata slot must exist in the region
    ///   tracking structure ([`Self::item_slot_in_regions`]).
    /// - **Safety**: the function will panic if the VA is out of range or
    ///   misaligned for the item's page size ([`Self::map_panic_conditions`]).
    /// ## Postconditions
    /// - **Safety Invariants**: the global safety invariants hold after the call.
    /// - **Correctness**: the abstract cursor view is updated by exactly the
    ///   `map_spec` operation — a single mapping is inserted at the current VA.
    /// - **Correctness**: if the cursor is still before the barrier end, it
    ///   remains ready for further map operations ([`Self::map_cursor_requires`]).
    /// - **Correctness**: if the old entry was absent, the result is `Ok(())`.
    /// - **Correctness**: `paths_in_pt` is preserved for all metadata slots
    ///   other than the newly mapped frame.
    /// ## Safety
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(entry_owner): Tracked<EntryOwner<C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            old(self).0.invariants(*old(owner), *old(regions), *old(guards)),
            old(owner).in_locked_range(),
            old(self).item_wf(item, entry_owner),
            Self::item_slot_in_regions(item, *old(regions)),
        ensures
            !old(self).map_panic_conditions(item),
            final(self).0.invariants(*final(owner), *final(regions), *final(guards)),
            old(self).map_item_ensures(
                item,
                old(self).0.model(*old(owner)),
                final(self).0.model(*final(owner)),
            ),
            (C::item_into_raw(item).1 <= old(self).0.level
                && old(owner).cur_entry_owner().is_absent()) ==> res.is_ok(),
            res is Err && res.unwrap_err() is StrayPageTable ==> C::item_into_raw(item).1 > 1,
            // For non-UNUSED indices other than the mapped frame, paths_in_pt is preserved.
            forall|idx: usize| #![trigger final(regions).slot_owners[idx].paths_in_pt]
                idx != frame_to_index(C::item_into_raw(item).0) &&
                old(regions).slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED ==>
                final(regions).slot_owners[idx].paths_in_pt == old(regions).slot_owners[idx].paths_in_pt,
            // For non-UNUSED indices, ref_count stays non-UNUSED across the map.
            // (map_loop only allocates new PT nodes from previously-UNUSED slots, so
            // any slot already in use stays in use; replace_cur_entry replaces the
            // current entry without dropping refcounts of unrelated slots.)
            forall|idx: usize| #![trigger final(regions).slot_owners[idx].inner_perms.ref_count.value()]
                old(regions).slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED ==>
                final(regions).slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED,
            // ref_count is preserved exactly at non-mapped, non-UNUSED indices.
            // map_loop preserves slot_owners fully at non-UNUSED slots, new_child
            // only mutates the new mapped frame's slot, and replace_cur_entry
            // preserves ref_count for all slots (per its own postcondition at
            // [mod.rs:3380]). Lets callers re-derive `item_slot_in_regions`
            // for unrelated paddrs.
            forall|idx: usize| #![trigger final(regions).slot_owners[idx].inner_perms.ref_count.value()]
                idx != frame_to_index(C::item_into_raw(item).0) &&
                old(regions).slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED ==>
                final(regions).slot_owners[idx].inner_perms.ref_count.value()
                    == old(regions).slot_owners[idx].inner_perms.ref_count.value(),
            // At the mapped index, ref_count > 0 is preserved (incremented if
            // already > 0). Together with `slots.contains_key` monotonicity,
            // gives `item_slot_in_regions(item, *final(regions))` post-map.
            (C::tracked(item)
                && old(regions).slot_owners[
                    frame_to_index(C::item_into_raw(item).0)].inner_perms.ref_count.value() > 0)
                ==>
                final(regions).slot_owners[
                    frame_to_index(C::item_into_raw(item).0)].inner_perms.ref_count.value() > 0,
            // `regions.slots` is monotonic — slot existence is preserved through map.
            forall|idx: usize| #![trigger final(regions).slots.contains_key(idx)]
                old(regions).slots.contains_key(idx) ==> final(regions).slots.contains_key(idx),
            final(self).0.guard_level == old(self).0.guard_level,
            final(self).0.barrier_va == old(self).0.barrier_va,
    )]
    #[verifier::rlimit(1200)]
    pub fn map(&mut self, item: C::Item) -> (res: Result<(), PageTableFrag<C>>) {

        let ghost self0 = *self;
        let ghost owner0 = *owner;

        vstd_extra::assert!(self.0.va < self.0.barrier_va.end);
        let (pa, level, prop) = C::item_into_raw(item);
        vstd_extra::assert!(level <= C::HIGHEST_TRANSLATION_LEVEL());
        vstd_extra::assert!(level < self.0.guard_level);
        if !C::TOP_LEVEL_CAN_UNMAP() {
            vstd_extra::assert!(level < NR_LEVELS as u8);
        }
        let size = page_size(level);
        vstd_extra::assert_eq!(self.0.va % size, 0);

        // `self.0.va + size <= usize::MAX` from the cursor invariant: since
        // `owner.in_locked_range()` and `1 <= level <= guard_level`, there is
        // enough slack in `locked_range().end == prefix + page_size(guard_level)`
        // to absorb another `page_size(level)`.
        proof {
            owner.va.reflect_prop(self.0.va);
            owner.va_plus_page_size_no_overflow(level);
        }
        let end = self.0.va + size;
        vstd_extra::assert!(end <= self.0.barrier_va.end);

        assert(!self.map_panic_conditions(item));
        assert(!old(self).map_panic_conditions(item));

        let ghost target = Mapping {
            va_range: owner@.cur_slot_range(size),
            pa_range: pa..(pa + size) as usize,
            page_size: size,
            property: prop,
        };

        let rcu_guard = self.0.rcu_guard;

        proof {
            owner.in_locked_range_level_le_guard_level();
        }

        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.map_loop(level, rcu_guard);

        let ghost owner1 = *owner;
        let ghost regions_before_new_child = *regions;

        let ghost is_tracked = C::tracked(item);
        let tracked new_owner = owner.continuations.tracked_borrow(owner.level - 1).new_child(pa, prop, is_tracked, regions);

        let ghost regions_after_new_child = *regions;

        proof {
            // Hoist common facts about new_owner from new_child postcondition.
            let cont = owner1.continuations[owner1.level as int - 1];
            assert(new_owner.value == EntryOwner::<C>::new_frame_spec(
                pa,
                cont.path().push_tail(cont.idx as usize),
                cont.level(),
                prop,
                is_tracked,
            ).set_in_scope(false));
            assert(new_owner.value.is_frame());
            assert(new_owner.value.frame.unwrap().mapped_pa == pa);

            assert(PageTableOwner(new_owner)@.mappings == set![target]) by {
                assert(owner1.level == level);
                owner1.new_child_mappings_eq_target(new_owner, pa, level, prop);
                assert(owner@.cur_slot_range(size) == owner1@.cur_slot_range(page_size(level)));
            };

            assert(pa % PAGE_SIZE == 0) by {
                assert(new_owner.inv());
            };

            OwnerSubtree::new_val_tree_predicate_map(new_owner, new_owner.value.path,
                CursorOwner::<'rcu, C>::node_unlocked(*guards));

            let ghost pa_idx_install = frame_to_index(pa);
            let ghost new_frame_path = new_owner.value.path;
            let tracked mut pa_slot_install = regions.slot_owners.tracked_remove(pa_idx_install);
            pa_slot_install.paths_in_pt = pa_slot_install.paths_in_pt.insert(new_frame_path);
            regions.slot_owners.tracked_insert(pa_idx_install, pa_slot_install);

            assert(regions_before_new_child.slots.contains_key(pa_idx_install)) by {
                assert(Self::item_slot_in_regions(item, regions_before_new_child));
            };
            owner1.no_node_at_idx_from_slot_key(regions_before_new_child, pa_idx_install);
            owner1.metaregion_preserved_under_path_insert(
                regions_before_new_child, *regions, pa_idx_install, new_frame_path);

            assert(new_owner.value.metaregion_sound(*regions)) by {
                broadcast use crate::specs::mm::frame::meta_owners::axiom_mmio_usage_iff_mmio_paddr;
                assert(Self::item_slot_in_regions(item, regions_before_new_child));
                assert(regions.slot_owners[pa_idx_install].paths_in_pt
                    .contains(new_frame_path));
                // Bridge `C::tracked(item) <=> usage != MMIO` for sub-pages, via:
                //   axiom_frame_is_tracked_iff_not_mmio (is_tracked <=> !is_mmio_paddr(pa))
                //   axiom_mmio_paddr_huge_page_closed (sub_paddr inherits MMIO-ness)
                //   axiom_mmio_usage_iff_mmio_paddr (usage == MMIO <=> is_mmio_paddr)
                EntryOwner::<C>::axiom_frame_is_tracked_iff_not_mmio(new_owner.value);
                if level > 1 {
                    assert forall |j: usize|
                        #![trigger frame_to_index((pa + j * PAGE_SIZE) as usize)]
                        0 < j < page_size(level) / PAGE_SIZE implies {
                        let sub_idx = frame_to_index((pa + j * PAGE_SIZE) as usize);
                        regions.slot_owners[sub_idx].usage
                            != crate::specs::mm::frame::meta_owners::PageUsage::MMIO
                            ==> C::tracked(item)
                    } by {
                        let sub_pa = (pa + j * PAGE_SIZE) as usize;
                        crate::specs::mm::frame::meta_owners::axiom_mmio_paddr_huge_page_closed(
                            pa, page_size(level), (j * PAGE_SIZE) as usize);
                    }
                }
                assert(new_owner.value.frame_sub_pages_valid(*regions));
            };

            assert(regions.inv()) by {
                assert(regions.slots =~= regions_before_new_child.slots);
                assert forall |i: usize| #[trigger] regions.slots.contains_key(i) implies {
                    &&& regions.slot_owners.contains_key(i)
                    &&& regions.slot_owners[i].inv()
                    &&& regions.slots[i].is_init()
                    &&& regions.slots[i].addr() == meta_addr(i)
                    &&& regions.slots[i].value().wf(regions.slot_owners[i])
                    &&& regions.slot_owners[i].self_addr == regions.slots[i].addr()
                } by {
                    assert(regions_before_new_child.slots.contains_key(i));
                    if i == pa_idx_install {
                        assert(regions_before_new_child.slot_owners[pa_idx_install].inv());
                    }
                };
                assert forall |i: usize| #[trigger] regions.slot_owners.contains_key(i) implies
                    regions.slot_owners[i].inv() by {
                    if i != pa_idx_install {
                    } else {
                        assert(regions_before_new_child.slot_owners[pa_idx_install].inv());
                    }
                };
                assert forall |i: usize| i < max_meta_slots() <==> #[trigger] regions.slot_owners.contains_key(i) by {};
                assert forall |i: usize| #[trigger] regions.slots.contains_key(i) implies i < max_meta_slots() by {
                    assert(regions_before_new_child.slots.contains_key(i));
                };
            };
        }

        // replace_cur_entry handles both node and non-node old entries:
        // - node old: uses neq_old_from_path_disjoint
        // - non-node old: uses metaregion_sound_preserved
        #[verus_spec(with Tracked(owner), Tracked(new_owner), Tracked(regions), Tracked(guards))]
        let frag = self.replace_cur_entry(Child::Frame(pa, level, prop));

        let ghost owner2 = *owner;
        let ghost regions_after_replace = *regions;
        // Capture owner2's va-alignment from the original map() precondition.
        // Chain: owner0.va.to_vaddr() == old(self).0.va, owner0.va == owner1.va (map_loop)
        //        == owner2.va (replace_cur_entry), so owner2.va.to_vaddr() == old(self).0.va,
        //        which was asserted size-aligned.
        proof {
            owner0.va.reflect_prop(old(self).0.va);
            assert(owner0.va == owner1.va);
            assert(owner1.va == owner2.va);
        }
        assert(owner2.va.to_vaddr() == old(self).0.va);
        assert(old(self).0.va % size == 0);
        assert(old(self).0.va + size <= usize::MAX);
        assert(size == page_size(level));
        assert(owner2@.mappings == owner1@.mappings - PageTableOwner(owner1.cur_subtree())@.mappings
            + PageTableOwner(new_owner)@.mappings);

        proof {
            owner1.cur_subtree_eq_filtered_mappings();
            owner.move_forward_owner_preserves_mappings();
        }

        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.0.move_forward();

        proof {
            owner.va.reflect_prop(self.0.va);
            // owner.va == owner2.va.align_up(level) (from move_forward ensure).
            lemma_page_size_ge_page_size(level as PagingLevel);
            // Bridge: owner2.va.to_vaddr() == old(self).0.va, which was size-aligned and fit.
            assert(owner2.va.to_vaddr() == old(self).0.va);
            assert(old(self).0.va % size == 0);
            assert(old(self).0.va + size <= usize::MAX);
            assert(size == page_size(level));
            assert(owner2.va.to_vaddr() as nat % page_size(level) as nat == 0);
            assert(owner2.va.to_vaddr() + page_size(level) <= usize::MAX);
            vstd_extra::arithmetic::lemma_nat_align_down_sound(
                owner2.va.to_vaddr() as nat, page_size(level) as nat);
            owner2.va.aligned_align_up_advances(level as int);
            // owner2.va.align_up(level).to_vaddr() == owner2.cur_va + page_size(level).
        }

        assert(owner@.cur_va == owner2@.align_up_spec(page_size(level)));
        assert(owner@ == owner0@.map_spec(pa, page_size(level), prop));
        assert(self0.map_item_ensures(item, owner0@, owner@));

        proof {
            assert(self.0.va >= self.0.barrier_va.end
                || owner.in_locked_range()) by {
                if !owner.above_locked_range() {
                    owner2.move_forward_increases_va();
                }
            };
            let ghost pa_idx2 = frame_to_index(C::item_into_raw(item).0);
            assert forall|idx: usize|
                idx != pa_idx2 &&
                old(regions).slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
            implies
                #[trigger] regions.slot_owners[idx].paths_in_pt == old(regions).slot_owners[idx].paths_in_pt
            by {
                assert(regions_after_new_child.slot_owners =~= regions_before_new_child.slot_owners);
            };
            // Slots monotonicity derivation. Chain:
            //   old → regions_before_new_child (via map_loop's monotonic-slots ensures)
            //   regions_before_new_child → regions_after_new_child (new_child only mutates
            //     slot_owners[pa_idx2].paths_in_pt; slots untouched)
            //   regions_after_new_child → regions_after_replace (via replace_cur_entry's
            //     monotonic-slots ensures)
            //   regions_after_replace → regions (move_forward doesn't touch regions)
            assert(regions_before_new_child.slots =~= regions_after_new_child.slots);
            assert(forall |k: usize| #![trigger regions_after_replace.slots.contains_key(k)]
                regions_after_new_child.slots.contains_key(k)
                ==> regions_after_replace.slots.contains_key(k));
            assert(forall |k: usize| #![trigger regions.slots.contains_key(k)]
                regions_after_replace.slots.contains_key(k) ==> regions.slots.contains_key(k));
            assert forall|idx: usize|
                old(regions).slots.contains_key(idx)
            implies
                #[trigger] regions.slots.contains_key(idx)
            by {
                assert(regions_before_new_child.slots.contains_key(idx));
                assert(regions_after_new_child.slots.contains_key(idx));
                assert(regions_after_replace.slots.contains_key(idx));
            };
        }

        if let Some(frag) = frag {
            proof {
                if frag is StrayPageTable {
                    assert(owner1.cur_entry_owner().is_node());
                    owner1.cur_entry_node_implies_level_gt_1();
                    assert(level == owner1.level);
                    assert(level > 1);
                }
            }
            Err(frag)
        } else {
            Ok(())
        }
    }

    /// Finds and removes the first page table entry in the following range.
    ///
    /// Scans forward from the cursor's current position through up to `len`
    /// bytes. If a mapped entry is found (frame or page-table subtree), it is
    /// removed and returned as a [`PageTableFrag`]. The cursor advances past
    /// the removed entry. If no mapped entries exist in the range, returns
    /// `None` and the cursor advances past the search window.
    ///
    /// The returned fragment is either `Mapped` (a single frame was removed)
    /// or `StrayPageTable` (an entire subtree was removed). The caller should
    /// handle TLB coherence before dropping the fragment.
    ///
    /// Internally calls `find_next_impl(len, true, true)`: it stops at the
    /// highest possible level for unmapping and splits huge pages as needed.
    ///
    /// # Safety
    ///
    /// The caller should ensure that the range being unmapped does not affect
    /// kernel's memory safety.
    ///
    /// # Panics
    ///
    /// Panics if:
    ///  - the length is longer than the remaining range of the cursor;
    ///  - the length is not page-aligned.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: the global safety invariants ([`Cursor::invariants`]) must hold.
    /// - **Safety**: the function will panic if `len` is not page aligned or exceeds
    ///   the remaining locked range ([`Cursor::find_next_panic_condition`]).
    /// ## Postconditions
    /// - **Safety Invariants**: the global safety invariants hold after the call.
    /// - **Correctness**: the cursor's VA never decreases, stays page-aligned, and
    ///   the barrier range is preserved.
    /// - **Correctness**: if an entry is found within `[old_va, old_va + len]`,
    ///   it is replaced by an absent entry, and the original entry is returned.
    /// - **Correctness**: if the entry represents a huge page whose size exceeds `len`,
    ///   it is split into pages at the next level and the first of those is replaced instead.
    /// - **Correctness**: the returned `StrayPageYable` has a `num_frames` field equal to
    ///   the number of removed mappings.
    /// - **Correctness**: if the result is `None`, there must have been no frames mapped in the range.
    /// - **Correctness**: if the result is `None`, the page table's abstract mappings are unchanged.
    /// ## Safety
    /// - It is always safe to unmap frames, but it is important to flush the TLB before mapping any
    ///   new frames in that range.
    /// - TODO: If this function is going to be called in a context where the stray page table will be
    ///   re-mapped or otherwise used for a purpose except flushing the TLB, we should also return
    ///   an owner object for that sub-tree.
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            old(self).0.invariants(*old(owner), *old(regions), *old(guards)),
        ensures
            !old(self).0.find_next_panic_condition(len),
            final(self).0.invariants(*final(owner), *final(regions), *final(guards)),
            final(self).0.va >= old(self).0.va,
            final(self).0.va % PAGE_SIZE == 0,
            final(self).0.barrier_va == old(self).0.barrier_va,
            res is Some ==> final(self).0.va <= old(self).0.va + len,
            res is Some ==> final(self).0.va > old(self).0.va,
            res is Some ==> final(owner).in_locked_range() || final(owner).above_locked_range(),
            res is None ==> {
                &&& final(owner)@.cur_va >= (old(owner)@.cur_va + len) as Vaddr
                &&& final(owner)@.mappings =~= old(owner)@.mappings
                &&& old(owner)@.mappings.filter(|m: Mapping|
                    old(owner)@.cur_va <= m.va_range.start < (old(owner)@.cur_va + len) as Vaddr) =~= Set::<Mapping>::empty()
            },
            res is Some && res.unwrap() is Mapped ==>
                old(owner)@.mappings.filter(|m: Mapping|
                    old(self).0.va <= m.va_range.start < res.unwrap()->Mapped_va)
                    =~= Set::<Mapping>::empty(),
            res is Some && res.unwrap() is StrayPageTable ==>
                old(owner)@.mappings.filter(|m: Mapping|
                    old(self).0.va <= m.va_range.start < res.unwrap()->StrayPageTable_va)
                    =~= Set::<Mapping>::empty(),
            res is Some && res.unwrap() is Mapped ==> {
                let m = CursorView::<C>::item_into_mapping(
                    res.unwrap()->Mapped_va, res.unwrap()->Mapped_item);
                final(owner)@.mappings.filter(|m2: Mapping|
                    res.unwrap()->Mapped_va <= m2.va_range.start < final(self).0.va)
                    =~= Set::<Mapping>::empty()
            },
            res is Some && res.unwrap() is StrayPageTable ==>
                final(owner)@.mappings.filter(|m2: Mapping|
                    res.unwrap()->StrayPageTable_va <= m2.va_range.start < final(self).0.va)
                    =~= Set::<Mapping>::empty(),
            // F2c-stable: mappings with start in [old_va, frag_va) are unchanged.
            // (Splits only affect the entry at frag_va; entries before it are untouched.)
            res is Some && res.unwrap() is Mapped ==>
                forall |m2: Mapping|
                    #![auto] final(owner)@.mappings.contains(m2) && old(self).0.va <= m2.va_range.start
                    && m2.va_range.start < res.unwrap()->Mapped_va
                    ==> old(owner)@.mappings.contains(m2),
            res is Some && res.unwrap() is StrayPageTable ==>
                forall |m2: Mapping|
                    #![auto] final(owner)@.mappings.contains(m2) && old(self).0.va <= m2.va_range.start
                    && m2.va_range.start < res.unwrap()->StrayPageTable_va
                    ==> old(owner)@.mappings.contains(m2),
            res is Some && res.unwrap() is Mapped ==>
                res.unwrap()->Mapped_va >= old(self).0.va
                && (res.unwrap()->Mapped_va as usize) < old(self).0.va + len,
            res is Some && res.unwrap() is StrayPageTable ==> {
                &&& res.unwrap()->StrayPageTable_va >= old(self).0.va
                &&& res.unwrap()->StrayPageTable_va + res.unwrap()->StrayPageTable_len
                    <= old(self).0.va + len
            },
            res is Some && res.unwrap() is Mapped ==> {
                let va = res.unwrap()->Mapped_va;
                let item = res.unwrap()->Mapped_item;
                let m = CursorView::<C>::item_into_mapping(va, item);
                let view = CursorView::<C> {
                    cur_va: va as Vaddr,
                    mappings: old(owner)@.mappings,
                    phantom: PhantomData,
                };
                &&& final(owner)@.mappings =~= view.split_while_huge(m.page_size).mappings - set![m]
                &&& view.split_while_huge(m.page_size).mappings.contains(m)
                &&& m.page_size >= PAGE_SIZE
            },
            res is Some && res.unwrap() is StrayPageTable ==> {
                let va = res.unwrap()->StrayPageTable_va;
                let len_frag = res.unwrap()->StrayPageTable_len;
                let subtree = old(owner)@.mappings.filter(
                    |m: Mapping| va <= m.va_range.start < va + len_frag);
                &&& final(owner)@.mappings =~= old(owner)@.mappings.difference(subtree)
                &&& subtree.len() == (res.unwrap()->StrayPageTable_num_frames) as nat
            },
    )]
    #[verifier::rlimit(1000)]
    pub unsafe fn take_next(&mut self, len: usize) -> (r: Option<PageTableFrag<C>>) {
        proof {
            owner.va.reflect_prop(self.0.va);
        }
        let ghost old_cur_va = owner@.cur_va;
        let ghost old_va = self.0.va;

        let find_result = #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.0.find_next_impl(len, true, true);

        if find_result.is_none() {
            proof {
                owner.va.reflect_prop(self.0.va);
                assert(old(owner)@.mappings.filter(|m: Mapping|
                    old(owner)@.cur_va <= m.va_range.start < (old(owner)@.cur_va + len) as Vaddr) =~= Set::<Mapping>::empty());
            }
            return None;
        }

        let tracked mut absent_entry_owner = EntryOwner::new_absent(
            owner.cur_entry_owner().path,
            owner.level,
        );
        proof { absent_entry_owner.in_scope = false; }
        let tracked subtree = OwnerSubtree::new_val_tracked(absent_entry_owner,
            (owner.continuations[owner.level - 1].tree_level + 1) as nat);

        assert(subtree.value.meta_slot_paddr() is None);
        proof {
            owner.absent_not_in_tree(subtree.value);
            reveal(CursorContinuation::inv_children);
        }

        let ghost owner_before_replace = *owner;
        let ghost va_after_find = self.0.va;
        let ghost level_after_find = self.0.level;

        proof {
            // subtree.value is absent, so not_in_tree is vacuously true.
            owner.absent_not_in_tree(subtree.value);
            OwnerSubtree::new_val_tree_predicate_map(subtree, subtree.value.path,
                CursorOwner::<'rcu, C>::node_unlocked(*guards));
        }
        #[verus_spec(with Tracked(owner), Tracked(subtree), Tracked(regions), Tracked(guards))]
        let frag = self.replace_cur_entry(Child::None);

        proof {
            owner.move_forward_increases_va();
            owner.move_forward_not_popped_too_high();
            owner.va.reflect_prop(self.0.va);
        }
        let ghost owner_before_move = *owner;

        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.0.move_forward();

        proof {
            assert(self.0.barrier_va == old(self).0.barrier_va);
            owner.va.reflect_prop(self.0.va);

            owner_before_move.move_forward_owner_preserves_mappings();
            assert(owner_before_replace@.mappings =~=
                old(owner)@.split_while_huge(page_size_spec(level_after_find)).mappings);

            let ghost old_cur_subtree_mappings = PageTableOwner(owner_before_replace.cur_subtree())@.mappings;
            PageTableOwner(subtree).view_rec_absent_empty(subtree.value.path);
            let ghost new_subtree_mappings = PageTableOwner(subtree)@.mappings;
            assert(new_subtree_mappings =~= Set::<Mapping>::empty());

            if frag.unwrap() is Mapped {
                let va = frag.unwrap()->Mapped_va;
                let item = frag.unwrap()->Mapped_item;
                let m = CursorView::<C>::item_into_mapping(va, item);
                assert(va == va_after_find);
                assert(m.page_size == page_size_spec(level_after_find));

                let ghost cur_st = owner_before_replace.cur_subtree();
                owner_before_replace.cur_subtree_inv();
                owner_before_replace.new_child_mappings_eq_target(
                    cur_st, cur_st.value.frame.unwrap().mapped_pa,
                    level_after_find, cur_st.value.frame.unwrap().prop);
                owner_before_replace.va.reflect_prop(va_after_find);

                let view = CursorView::<C> {
                    cur_va: va as Vaddr,
                    mappings: old(owner)@.mappings,
                    phantom: PhantomData,
                };
                old(owner).view_preserves_inv();
                owner_before_replace.view_preserves_inv();
                assert(view.inv());
                if !old(owner)@.present() && view.present() {
                    owner_before_replace.split_while_huge_at_level_noop();
                    owner_before_replace@.split_while_huge_noop_implies_page_size_le(
                        page_size_spec(level_after_find));
                }
                CursorOwner::<'rcu, C>::split_while_huge_cur_va_independent(
                    old(owner)@, view, page_size_spec(level_after_find));

                owner_before_replace.cur_subtree_eq_filtered_mappings();
                let ghost target = Mapping {
                    va_range: owner_before_replace@.cur_slot_range(m.page_size),
                    pa_range: cur_st.value.frame.unwrap().mapped_pa
                        ..(cur_st.value.frame.unwrap().mapped_pa + m.page_size) as usize,
                    page_size: m.page_size,
                    property: cur_st.value.frame.unwrap().prop,
                };
                assert(PageTableOwner(cur_st)@.mappings == set![target]);
                assert(owner_before_replace@.mappings.filter(
                    |m2: Mapping| owner_before_replace@.cur_va <= m2.va_range.start
                        < owner_before_replace@.cur_va + m.page_size).contains(target));
                assert(owner_before_replace@.mappings.contains(target));
                assert(m == target);
                assert(owner_before_replace@.mappings.contains(m));
                assert(view.split_while_huge(m.page_size).mappings.contains(m));
            }
            if frag.unwrap() is StrayPageTable {
                let va = frag.unwrap()->StrayPageTable_va;
                let len_frag = frag.unwrap()->StrayPageTable_len;
                let subtree_mappings = old(owner)@.mappings.filter(
                    |m: Mapping| va <= m.va_range.start < va + len_frag);

                owner_before_replace.va.reflect_prop(va_after_find);
                owner_before_replace.cur_subtree_eq_filtered_mappings();

                assert(old_cur_subtree_mappings =~= subtree_mappings);
            }

            let ghost frag_va: Vaddr = va_after_find;
            if frag.unwrap() is Mapped {
                assert(frag.unwrap()->Mapped_va == frag_va);
            }
            if frag.unwrap() is StrayPageTable {
                assert(frag.unwrap()->StrayPageTable_va == frag_va);
            }
            assert(old(owner)@.mappings.filter(|m: Mapping|
                old_va <= m.va_range.start < frag_va) =~= Set::<Mapping>::empty());

            let ghost ps = page_size_spec(level_after_find);
            assert forall |m: Mapping|
                #![auto] owner@.mappings.contains(m) && old_va <= m.va_range.start
                && m.va_range.start < frag_va
            implies old(owner)@.mappings.contains(m)
            by {
                assert(owner_before_replace@.mappings.contains(m));
                let view = CursorView::<C> {
                    cur_va: frag_va as Vaddr,
                    mappings: old(owner)@.mappings,
                    phantom: PhantomData,
                };
                old(owner).view_preserves_inv();
                owner_before_replace.view_preserves_inv();
                if !old(owner)@.mappings.contains(m) {
                    assert(view.inv());
                    assert(ps >= PAGE_SIZE) by {
                        crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_ge_page_size(level_after_find);
                    };
                    assert(view.split_while_huge(ps).mappings.contains(m));
                    view.split_while_huge_refinement(ps, m);
                    let p = choose |p: Mapping| #[trigger] old(owner)@.mappings.contains(p)
                        && p.va_range.start <= m.va_range.start
                        && m.va_range.end <= p.va_range.end;
                    if p.va_range.start >= old_va && p.va_range.start < frag_va {
                        assert(old(owner)@.mappings.filter(|m2: Mapping|
                            old_va <= m2.va_range.start < frag_va).contains(p));
                    } else if p.va_range.start < old_va {
                        assert(frag_va > old_va);
                        assert(!old(owner)@.present());
                        let ghost cover_filter = old(owner)@.mappings.filter(
                            |m2: Mapping| m2.va_range.start <= old(owner)@.cur_va
                                && old(owner)@.cur_va < m2.va_range.end);
                        assert(cover_filter.contains(p));
                        vstd::set::axiom_set_intersect_finite::<Mapping>(
                            old(owner)@.mappings,
                            Set::new(|m2: Mapping| m2.va_range.start <= old(owner)@.cur_va
                                && old(owner)@.cur_va < m2.va_range.end));
                        vstd::set::axiom_set_choose_len(cover_filter);
                        assert(old(owner)@.present());
                    } else {
                        assert(m.va_range.start >= frag_va);
                    }
                }
            };

            owner_before_replace.va.reflect_prop(va_after_find);
            owner_before_replace.cur_subtree_eq_filtered_mappings();
            let ghost ps = page_size_spec(level_after_find);
            let ghost obr_subtree = PageTableOwner(owner_before_replace.cur_subtree())@.mappings;
            assert(owner@.mappings =~= owner_before_replace@.mappings - obr_subtree);
            assert(obr_subtree =~=
                owner_before_replace@.mappings.filter(|m: Mapping| frag_va <= m.va_range.start < (frag_va + ps) as Vaddr));
            assert(self.0.va <= (frag_va + ps) as Vaddr);
            assert(owner@.mappings.filter(|m: Mapping| frag_va <= m.va_range.start < self.0.va) =~=
                Set::<Mapping>::empty());
        }

        frag
    }

    /// Applies a property-changing operation to the next mapped frame in the range.
    ///
    /// Scans forward from the cursor's current position through up to `len`
    /// bytes looking for a mapped frame (using `find_next_impl` with
    /// `split_huge = true`). If found, applies `op` to the frame's
    /// [`PageProperty`], advances the cursor past it, and returns the
    /// protected VA range. If no mapped frame exists in the range, returns
    /// `None` and the cursor advances past the search window.
    ///
    /// # Safety
    ///
    /// The caller should ensure that:
    ///  - the range being protected with the operation does not affect
    ///    kernel's memory safety;
    ///  - the privileged flag `AVAIL1` should not be altered if in the kernel
    ///    page table (the restriction may be lifted in the future).
    ///
    /// # Panics
    ///
    /// Panics if:
    ///  - the length is longer than the remaining range of the cursor;
    ///  - the length is not page-aligned.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: the global safety invariants ([`Cursor::invariants`]) must hold.
    /// - **Liveness**: the function will panic if `len` is not page aligned or exceeds
    ///   the remaining locked range ([`Cursor::find_next_panic_condition`]).
    /// - **Correctness**: the current entry must be a frame, and `op` must be callable
    ///   on its current property (vacuously true unless we're verifying the caller).
    /// ## Postconditions
    /// - **Safety Invariants**: the global safety invariants hold after the call.
    /// ## Safety
    /// - It is safe to call this function, but depending on the details of `op`, it may be necessary
    ///   to flush the TLB afterward. We do not model the behavior of `op`.
    ///
    /// Note: a previous version of this function had a postcondition asserting that the
    /// modified frame's mapping appears in `owner@.mappings` with the new property. That
    /// postcondition was structurally inconsistent with the split case (when find_next_impl
    /// splits a huge mapping, the resulting cursor frame is a sub-mapping NOT in the original
    /// `old(owner)@.mappings`), so it has been removed. A correct postcondition would
    /// reference `old(owner)@.split_while_huge(...).mappings` rather than `old(owner)@.mappings`.
    #[verifier::rlimit(200)]
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            old(self).0.invariants(*old(owner), *old(regions), *old(guards)),
            forall |p: PageProperty| op.requires((p,)),
            // POTENTIALLY UNSOUND PATCH: see `Entry::protect` for rationale.
            // `op` must preserve `C::tracked` of the reconstructed item so that
            // `axiom_frame_is_tracked_matches_item` remains consistent across the
            // prop change. Quantified over `(pa, level)` because `find_next_impl`
            // may descend to any frame in the range. For UserPtConfig
            // (`tracked == true` always) this is trivial; for KernelPtConfig it
            // reduces to "op preserves AVAIL1".
            forall |pa: Paddr, level: PagingLevel, p_in: PageProperty, p_out: PageProperty| #![auto]
                op.ensures((p_in,), p_out) ==>
                    C::tracked(C::item_from_raw_spec(pa, level, p_out))
                    == C::tracked(C::item_from_raw_spec(pa, level, p_in)),
        ensures
            !old(self).0.find_next_panic_condition(len),
            final(self).0.invariants(*final(owner), *final(regions), *final(guards)),
            final(self).0.barrier_va == old(self).0.barrier_va,
    )]
    pub unsafe fn protect_next(
        &mut self,
        len: usize,
        op: impl FnOnce(PageProperty) -> PageProperty,
    ) -> Option<Range<Vaddr>> {
        (#[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.0.find_next_impl(len, false, true))?;

        assert(owner.cur_entry_owner().is_frame());

        let ghost owner_after_find = *owner;

        #[verus_spec(with Tracked(owner), Tracked(regions))]
        let mut entry = self.0.cur_entry();

        proof {
            assert(entry.pte.prop() == owner.cur_entry_owner().frame.unwrap().prop) by {
                owner.cur_subtree_inv();
                assert(owner.cur_entry_owner().match_pte(entry.pte, owner.cur_entry_owner().parent_level));
            };
        }

        let ghost owner0 = *owner;

        let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
        let ghost cont0 = continuation;
        // entry.idx == cont0.idx from cur_entry postcondition (entry.idx == owner0.cont[level-1].idx)
        // and cont0 == owner0.cont[level-1] from tracked_remove.
        assert(entry.idx == cont0.idx as usize);
        let tracked mut child_owner = continuation.take_child();
        let tracked mut parent_owner = continuation.entry_own.node.tracked_take();

        #[verus_spec(with Tracked(&mut child_owner.value), Tracked(&mut parent_owner))]
        entry.protect(op);

        let ghost new_prop = child_owner.value.frame.unwrap().prop;

        let ghost child_owner_path = child_owner.value.path;
        let ghost child_owner_mapped_pa = child_owner.value.frame.unwrap().mapped_pa;
        let ghost child_owner_parent_level = child_owner.value.parent_level;

        proof {
            let ghost child_not_in_scope = !child_owner.value.in_scope;

            continuation.put_child(child_owner);
            continuation.entry_own.node = Some(parent_owner);
            cont0.take_put_child();
            owner.continuations.tracked_insert(owner.level - 1, continuation);
            assert(owner.continuations[owner.level - 1].all_some()) by {
                let cont_new = owner.continuations[owner.level - 1];
                assert forall|i: int| 0 <= i < NR_ENTRIES implies cont_new.children[i] is Some by {
                    if i != cont_new.idx as int { assert(cont0.children[i] is Some); }
                };
            };
            assert(owner.continuations[owner.level - 1].inv()) by {
                let cont_new = owner.continuations[owner.level - 1];
                assert(child_not_in_scope);
                cont_new.continuation_inv_holds_after_child_restore(
                    cont0, cont0.entry_own.node.unwrap());
            };
            owner0.protect_preserves_cursor_inv_metaregion(*owner, *regions);
        }

        #[verus_spec(with Tracked(owner))]
        let protected_va = self.0.cur_va_range();

        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.0.move_forward();

        Some(protected_va)
    }

    /// Replaces the current entry with `new_child` and returns the old entry
    /// as a [`PageTableFrag`], or `None` if the old entry was absent.
    ///
    /// This is the low-level primitive used by [`Self::map`] and
    /// [`Self::take_next`]. It swaps the page-table entry at the cursor's
    /// current slot, updating the ghost ownership tree accordingly. The
    /// cursor position and level are unchanged after the call.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - **Safety Invariants**: the global safety invariants ([`Cursor::invariants`]) must hold,
    ///   with the owner in the locked range and not `popped_too_high`.
    /// - **New entry validity**: `new_owner` must be a valid ownership subtree at the
    ///   correct tree level and path, with `new_child.wf(new_owner.value)`.
    /// - **Disjointness**: every existing entry in the cursor's tree must have a
    ///   different physical metadata address than `new_owner.value`.
    /// - **Region tracking**: `new_owner.value` must already satisfy `metaregion_sound`.
    /// ## Postconditions
    /// - **Safety Invariants**: the global safety invariants hold after the call.
    /// - **Correctness**: the abstract mappings are updated by removing the old
    ///   subtree's mappings and inserting `new_owner`'s mappings.
    /// - **Correctness**: the cursor's VA, level, guard level, and barrier range are
    ///   all unchanged.
    /// - **Correctness**: if the old entry was absent, `None` is returned; otherwise
    ///   `Some(frag)` is returned. A `Mapped` fragment carries the old frame's
    ///   paddr, level, and property. A `StrayPageTable` fragment carries the old
    ///   subtree's VA range and mapping count.
    /// - **Correctness**: `paths_in_pt` is preserved for all metadata slots except
    ///   the one belonging to `new_owner.value`.
    #[verifier::rlimit(800)]
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(new_owner): Tracked<OwnerSubtree<C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
    )]
    #[verifier::rlimit(10000)]
    fn replace_cur_entry(&mut self, new_child: Child<C>) -> (res: Option<PageTableFrag<C>>)
        requires
            old(self).0.invariants(*old(owner), *old(regions), *old(guards)),
            old(owner).in_locked_range(),
            !old(owner).popped_too_high,
            new_owner.inv(),
            !new_owner.value.is_node(),
            new_owner.level == old(owner).continuations[old(owner).level - 1].tree_level + 1,
            new_owner.value.parent_level == old(owner).continuations[old(owner).level - 1].child().value.parent_level,
            new_owner.value.path == old(owner).continuations[old(owner).level - 1].path().push_tail(
                old(owner).continuations[old(owner).level - 1].idx as usize,
            ),
            new_child.wf(new_owner.value),
            new_owner == OwnerSubtree::new_val(new_owner.value, new_owner.level as nat),
            new_owner.value.metaregion_sound(*old(regions)),
            new_owner.tree_predicate_map(
                new_owner.value.path,
                CursorOwner::<'rcu, C>::node_unlocked(*old(guards)),
            ),
        ensures
            // Runtime panic in the `Child::PageTable` arm guarantees: when
            // a `StrayPageTable` fragment is produced (the only path that
            // unmaps a kernel-shared PT) and the config forbids top-level
            // unmaps, the cursor's level was strictly below NR_LEVELS.
            res matches Some(PageTableFrag::StrayPageTable { .. })
                && !C::TOP_LEVEL_CAN_UNMAP_spec()
                ==> old(owner).level < NR_LEVELS,
            final(owner)@.mappings == old(owner)@.mappings - PageTableOwner(
                old(owner).cur_subtree(),
            )@.mappings + PageTableOwner(new_owner)@.mappings,
            final(self).0.invariants(*final(owner), *final(regions), *final(guards)),
            final(self).0.barrier_va == old(self).0.barrier_va,
            final(owner).va == old(owner).va,
            final(self).0.va == old(self).0.va,
            final(self).0.level == old(self).0.level,
            final(owner).guard_level == old(owner).guard_level,
            final(owner).in_locked_range(),
            // The old fragment is returned iff the current entry was not absent.
            old(owner).cur_entry_owner().is_absent() ==> res is None,
            !old(owner).cur_entry_owner().is_absent() ==> res is Some,
            // Mapped result implies old entry was a frame.
            res is Some && res.unwrap() is Mapped ==> old(owner).cur_entry_owner().is_frame(),
            // The returned fragment's VA and level match the cursor's state at call time.
            res is Some && res.unwrap() is Mapped ==> res.unwrap()->Mapped_va == old(self).0.va,
            res is Some && res.unwrap() is Mapped ==> {
                let (pa, lvl, prop) = C::item_into_raw_spec(res.unwrap()->Mapped_item);
                &&& lvl == old(self).0.level
                &&& pa == old(owner).cur_entry_owner().frame.unwrap().mapped_pa
                &&& prop == old(owner).cur_entry_owner().frame.unwrap().prop
            },
            // StrayPageTable: VA and len match cursor state at call time.
            res is Some && res.unwrap() is StrayPageTable ==> {
                &&& res.unwrap()->StrayPageTable_va == old(self).0.va
                &&& res.unwrap()->StrayPageTable_len == page_size_spec(old(self).0.level)
            },
            // StrayPageTable implies old entry was a node (PT).
            res is Some && res.unwrap() is StrayPageTable ==> old(owner).cur_entry_owner().is_node(),
            // StrayPageTable: num_frames equals the number of mappings in the old subtree.
            res is Some && res.unwrap() is StrayPageTable ==>
                (res.unwrap()->StrayPageTable_num_frames) as nat ==
                    PageTableOwner(old(owner).cur_subtree())@.mappings.len(),
            // paths_in_pt is changed only for new_owner's slot; all others are preserved.
            // (new_owner.value here is the post-into_pte state; meta_slot_paddr() is unchanged.)
            forall|idx: usize| #![trigger final(regions).slot_owners[idx].paths_in_pt]
                (new_owner.value.is_absent() || idx != frame_to_index(new_owner.value.meta_slot_paddr().unwrap()))
                    ==> final(regions).slot_owners[idx].paths_in_pt == old(regions).slot_owners[idx].paths_in_pt,
            // `regions.slots` keys are monotonic across the entry replacement.
            forall|idx: usize| #![trigger final(regions).slots.contains_key(idx)]
                old(regions).slots.contains_key(idx) ==> final(regions).slots.contains_key(idx),
            // ref_count is preserved per-slot across the whole replace_cur_entry call.
            // The body only touches regions via `Entry::replace` (which preserves
            // ref_count by spec); `dfs_mark_stray_and_unlock` doesn't take regions at
            // all, so the StrayPageTable branch can't perturb refcounts either.
            forall|idx: usize| #![trigger final(regions).slot_owners[idx].inner_perms.ref_count.value()]
                final(regions).slot_owners[idx].inner_perms.ref_count.value()
                    == old(regions).slot_owners[idx].inner_perms.ref_count.value(),
            // When `res is None` (⇔ pre-replace cur_entry was absent), `Entry::replace`
            // fully preserves `regions.slots` (and `slot_owners`, but the latter is
            // `Map<usize, MetaSlotOwner>` where `MetaSlotOwner` is a tracked struct
            // whose `==` doesn't propagate across function boundaries — only extensional
            // `=~=` does, and that requires per-idx instantiation at the call site,
            // which Verus's quantifier instantiator doesn't do reliably here).
            res is None ==> final(regions).slots == old(regions).slots,
    {

        let ghost owner0 = *owner;
        let ghost regions0 = *regions;
        let ghost guard_level = owner.guard_level;
        let rcu_guard = self.0.rcu_guard;

        let tracked mut new_owner = new_owner;

        let va = self.0.va;
        let level = self.0.level;

        #[verus_spec(with Tracked(owner), Tracked(regions))]
        let mut cur_entry = self.0.cur_entry();

        let tracked mut continuation = owner.continuations.tracked_remove((owner.level - 1) as int);
        let ghost cont0 = continuation;
        let ghost owner1 = *owner;

        let tracked old_child_owner = continuation.take_child();

        let ghost cont1 = continuation;
        assert(cont1.view_mappings() == cont0.view_mappings() - cont0.view_mappings_take_child_spec()) by {
            cont0.view_mappings_take_child();
            assert(cont1 == cont0.take_child_spec().1);
        }
        assert(owner.continuations == owner0.continuations.remove(owner.level - 1));

        let tracked mut parent_owner = continuation.entry_own.node.tracked_take();

        let ghost pre_new_owner_value = new_owner.value;
        // Capture the old child value before Entry::replace mutates it (from_pte_owner_spec
        // only changes in_scope, so meta_slot_paddr() is unchanged, but we need the pre-replace
        // value to match Entry::metaregion_sound_neq_preserved's old(owner) parameter).
        let ghost old_child_pre_replace = old_child_owner.value;

        proof { new_owner.value.in_scope = true; }

        #[verus_spec(with Tracked(regions),
            Tracked(&mut old_child_owner.value),
            Tracked(&mut new_owner.value),
            Tracked(&mut parent_owner),
        )]
        let old = cur_entry.replace(new_child);
        let ghost old_child_snap = old; // ghost alias to avoid `old(...)` keyword ambiguity in proofs

        assert(Entry::<C>::metaregion_sound_neq_preserved(
            old_child_pre_replace,
            pre_new_owner_value,
            regions0,
            *regions,
        ));

        let ghost regions_after_replace = *regions;
        // When old child was absent (⇒ res is None), Entry::replace's ensures
        // gives full regions preservation; surface the slots equality (as Map ==)
        // for use at call sites.
        proof {
            if old_child_pre_replace.is_absent() {
                assert(regions.slots =~= regions0.slots);
            }
        }
        assert(cur_entry.idx == continuation.idx) by {
            assert(cur_entry.idx == owner0.continuations[(owner0.level - 1) as int].idx);
        };

        proof {
            continuation.entry_own.node = Some(parent_owner);
            continuation.put_child(new_owner);
            cont1.view_mappings_put_child(new_owner);

            let ghost final_cont = continuation;
            owner.continuations.tracked_insert((owner.level - 1) as int, continuation);

            CursorOwner::view_mappings_replace_lowest(owner0, *owner, cont0, final_cont);

            // Bridge view_mappings to view().mappings via open-spec unfolding,
            // and connect cont0/final_cont to PageTableOwner views by path equality.
            assert(owner0.cur_subtree().value.path == cont0.path().push_tail(cont0.idx as usize));
            assert(new_owner.value.path == cont1.path().push_tail(cont1.idx as usize));
            assert(owner@.mappings =~= owner0@.mappings
                - PageTableOwner(owner0.cur_subtree())@.mappings
                + PageTableOwner(new_owner)@.mappings);

            let level = owner0.level;
            let idx = cont0.idx as int;

            assert forall|j: int|
                #![trigger final_cont.children[j]]
                0 <= j < NR_ENTRIES && j != idx implies final_cont.children[j]
                == cont0.children[j] by {
                assert(cont1.children[j] == cont0.children[j]);
            };

            assert(new_owner.value.meta_slot_paddr() == pre_new_owner_value.meta_slot_paddr());

            let f_neq_old = |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                entry.meta_slot_paddr_neq(old_child_pre_replace);
            let f_sound = PageTableOwner::<C>::metaregion_sound_pred(regions0);
            let g_sound = PageTableOwner::<C>::metaregion_sound_pred(*regions);

            assert(Entry::<C>::metaregion_sound_neq_old_preserved(
                old_child_pre_replace, regions0, *regions));

            // Higher-level continuations: metaregion_sound
            assert forall|i: int| #![auto] owner0.level <= i < NR_LEVELS implies {
                owner.continuations[i].map_children(g_sound)
            } by {
                assert(owner.continuations[i] == owner0.continuations[i]);
                let cont = owner0.continuations[i];
                if old_child_pre_replace.is_node() {
                    // Old child is a node: use neq_old_from_path_disjoint + neq_old_preserved.
                    assert forall|j: int|
                        #![auto]
                        0 <= j < NR_ENTRIES && cont.children[j] is Some
                    implies cont.children[j].unwrap().tree_predicate_map(cont.path().push_tail(j as usize), g_sound)
                    by {
                        cont.inv_children_unroll(j);
                        let subtree = cont.children[j].unwrap();
                        let path_j = cont.path().push_tail(j as usize);
                        owner0.cursor_path_nesting(i, owner0.level as int - 1);
                        cont0.path().push_tail_property_index(idx as usize);
                        cont.path().push_tail_property_index(j as usize);
                        PageTableOwner::<C>::neq_old_from_path_disjoint(subtree, path_j, old_child_pre_replace, regions0);
                        OwnerSubtree::map_implies_and(subtree, path_j, f_sound, f_neq_old, g_sound);
                    };
                } else {
                    // Old child is absent or frame: metaregion_sound_preserved.
                    cont.map_children_lift(f_sound, g_sound);
                }
            };

            assert(new_owner.value.metaregion_sound(*regions));
            let child_path = final_cont.path().push_tail(idx as usize);
            assert(new_owner.tree_predicate_map(child_path, g_sound)) by {
                OwnerSubtree::new_val_tree_predicate_map(new_owner, child_path, g_sound);
            };

            // Bottom continuation siblings: metaregion_sound
            if old_child_pre_replace.is_node() {
                assert(final_cont.map_children(g_sound)) by {
                    assert forall|j: int|
                        #![auto]
                        0 <= j < NR_ENTRIES
                            && final_cont.children[j] is Some implies final_cont.children[j].unwrap().tree_predicate_map(
                    final_cont.path().push_tail(j as usize), g_sound) by {
                        if j != idx as int {
                            cont0.inv_children_unroll(j);
                            let subtree = cont0.children[j].unwrap();
                            let path_j = final_cont.path().push_tail(j as usize);
                            cont0.path().push_tail_property_index(j as usize);
                            cont0.path().push_tail_property_index(idx as usize);
                            cont0.path().push_tail_property_len(j as usize);
                            PageTableOwner::<C>::neq_old_from_path_disjoint(
                                subtree, path_j, old_child_pre_replace, regions0,
                            );
                            OwnerSubtree::map_implies_and(subtree, path_j, f_sound, f_neq_old, g_sound);
                        }
                    };
                };
            } else {
                // Old child is absent or frame: metaregion_sound_preserved.
                final_cont.map_children_lift_skip_idx(cont0, idx as int, f_sound, g_sound);
            }

            assert(owner.path_metaregion_sound(*regions)) by {
                // Hoist loop-invariant setup: establish old child's metaregion_sound
                // and path length when the old child is a node.
                if old_child_pre_replace.is_node() {
                    owner0.inv_continuation(owner0.level - 1);
                    cont0.inv_children_unroll(cont0.idx as int);
                    assert(cont0.map_children(
                        |e: EntryOwner<C>, p: TreePath<NR_ENTRIES>| e.metaregion_sound(regions0)));
                    assert(cont0.children[cont0.idx as int].unwrap().tree_predicate_map(
                        cont0.path().push_tail(cont0.idx as usize),
                        |e: EntryOwner<C>, p: TreePath<NR_ENTRIES>| e.metaregion_sound(regions0)));
                    cont0.inv_children_rel_unroll(cont0.idx as int);
                    cont0.path().push_tail_property_len(cont0.idx as usize);
                }

                assert forall|i: int| #![trigger owner.continuations[i]]
                    owner.level - 1 <= i < NR_LEVELS implies
                        owner.continuations[i].entry_own.metaregion_sound(*regions) by {
                    if i >= owner.level as int {
                        assert(owner.continuations[i] == owner0.continuations[i]);
                    }
                    owner0.inv_continuation(i);
                    let eo = owner0.continuations[i].entry_own;
                    assert(eo.inv() && eo.is_node() && !eo.in_scope);
                    assert(eo.metaregion_sound(regions0));

                    if old_child_pre_replace.is_node() {
                        // Path lengths differ: eo at tree_level, child at tree_level + 1.
                        assert(eo.path.len() as nat == owner0.continuations[i].tree_level);
                        assert(old_child_pre_replace.path.len() == cont0.tree_level + 1);
                        eo.nodes_different_path_lengths_neq_slot(
                            old_child_pre_replace, regions0);
                        assert(g_sound(eo, owner0.continuations[i].path()));
                    }
                    // Old child absent/frame: regions unchanged at eo's slot.
                };
            };

            assert(owner.metaregion_sound(*regions));

            assert forall|j: int|
                #![trigger final_cont.children[j]]
                0 <= j < NR_ENTRIES && final_cont.children[j] is Some implies {
                &&& final_cont.children[j].unwrap().value.path == final_cont.path().push_tail(j as usize)
                &&& final_cont.children[j].unwrap().value.parent_level == final_cont.level()
                &&& final_cont.children[j].unwrap().inv()
                &&& final_cont.children[j].unwrap().level == final_cont.tree_level + 1
            } by { 
                if j != idx {
                    final_cont.inv_children_unroll(j);
                    assert(final_cont.children[j] == cont0.children[j]);
                }
            };
        }

        let ghost owner_after_replace = *owner;
        let ghost regions_after_replace = *regions;

        let result = match old {
            Child::None => None,
            Child::Frame(pa, ch_level, prop) => {
                proof {
                    let ghost entry_owner_snap = old_child_owner.value;
                    assert(old_child_snap.invariants(entry_owner_snap, regions_after_replace));
                    assert(entry_owner_snap.is_frame());
                    assert(entry_owner_snap.metaregion_sound(regions_after_replace));

                    // No slot_perm extraction/insertion — regions unchanged in Frame path.
                    assert(*regions == regions_after_replace);
                }
                // SAFETY:
                // This is part of (if `split_huge` happens) a page table item mapped
                // with a previous call to `C::item_into_raw`, where:
                //  - The physical address and the paging level match it;
                //  - The item part is now unmapped so we can take its ownership.
                //
                // For page table configs that require the `AVAIL1` flag to be kept
                // (currently, only kernel page tables), the callers of the unsafe
                // `protect_next` method uphold this invariant.
                let item = C::item_from_raw(pa, level, prop);
                proof { C::item_roundtrip(item, pa, level, prop); }
                Some(PageTableFrag::Mapped { va, item })
            },
            Child::PageTable(pt) => {
                // debug_assert_eq!(pt.level(), level - 1);
                if !C::TOP_LEVEL_CAN_UNMAP() && level as usize == NR_LEVELS {
                    let _ = ManuallyDrop::new(pt, Tracked(regions));  // leak it to make shared PTs stay `'static`.
                    // Runtime panic. Discharges the conditional postcondition
                    // `res matches Some(StrayPageTable) && !TOP_LEVEL_CAN_UNMAP
                    // ==> old.level < NR_LEVELS` via `panic_diverge`'s `-> !`.
                    vstd_extra::panic::panic_diverge();
                }
                // SAFETY: We must have locked this node.

                let ghost owner2 = *owner;
                let ghost child_entry = old_child_owner.value;

                let tracked mut old_node_owner = old_child_owner.value.node.tracked_take();

                let ghost regions_before_borrow = *regions;

                #[verus_spec(with Tracked(regions), Tracked(& old_node_owner.meta_perm))]
                let borrow_pt = pt.borrow();

                let ghost regions_after_borrow = *regions;

                let ghost guards0 = *guards;

                #[verus_spec(with Tracked(&old_node_owner), Tracked(guards))]
                let locked_pt = borrow_pt.make_guard_unchecked(rcu_guard);

                proof {
                    owner.map_children_implies(
                        CursorOwner::node_unlocked(guards0),
                        CursorOwner::node_unlocked_except(*guards, old_node_owner.meta_perm.addr()),
                    );
                }

                let ghost guards1 = *guards;
                let ghost locked_addr = old_node_owner.meta_perm.addr();
                let ghost owner_before_dfs = *owner;

                // SAFETY:
                //  - We checked that we are not unmapping shared kernel page table nodes.
                //  - We must have locked the entire sub-tree since the range is locked.
                let ghost subtree_count = PageTableOwner::<C>(owner0.cur_subtree())@.mappings.len();
                #[verus_spec(with Tracked(owner), Tracked(guards), Ghost(locked_addr), Ghost(subtree_count))]
                let num_frames = locking::dfs_mark_stray_and_unlock(rcu_guard, &locked_pt);

                proof {
                    owner.map_children_implies(
                        CursorOwner::node_unlocked_except(guards1, locked_addr),
                        CursorOwner::node_unlocked(*guards),
                    );

                    // Pre-establish cont_entries_metaregion for all continuations.
                    owner0.cont_entries_metaregion(regions0);

                    // dfs_mark_stray_and_unlock preserves continuations[i].guard for
                    // i >= owner.level - 1 (postcondition lines 450-463 of locking.rs).
                    // For each such continuation:
                    //   - cont.guard.addr was already locked in guards0 (from nodes_locked(guards0)),
                    //   - locked_addr was UNLOCKED in guards0 (precondition of make_guard_unchecked),
                    //   - so cont.guard.addr != locked_addr,
                    //   - dfs preserves locks for addresses != locked_addr.
                    assert forall|i: int|
                        owner.level - 1 <= i < NR_LEVELS implies
                        #[trigger] owner.continuations[i].node_locked(*guards) by {
                        let cont = owner.continuations[i];
                        let cont_addr = cont.guard.inner.inner@.ptr.addr();
                        assert(owner.continuations[i].guard == owner_before_dfs.continuations[i].guard);
                        assert(owner_before_dfs.nodes_locked(guards1));
                        assert(guards1.lock_held(cont_addr));
                        assert(guards0.lock_held(cont_addr));
                        assert(guards0.unlocked(locked_addr));
                        assert(guards.lock_held(cont_addr));
                    };

                    let ghost pt_idx = pt.index();
                    assert(regions_before_borrow =~= regions_after_replace);

                    owner_after_replace.metaregion_borrow_slot(
                        regions_after_replace,
                        regions_after_borrow,
                        pt_idx,
                    );
                    assert(owner_before_dfs.metaregion_sound(*regions));

                    let f = PageTableOwner::<C>::metaregion_sound_pred(*regions);

                    owner_before_dfs.cont_entries_metaregion(*regions);
                    assert forall|i: int| #![auto] owner.level - 1 <= i < NR_LEVELS implies {
                        &&& f(owner.continuations[i].entry_own, owner.continuations[i].path())
                        &&& owner.continuations[i].map_children(f)
                    } by {
                        if i >= owner.level as int {
                            assert(owner.continuations[i] == owner_before_dfs.continuations[i]);
                        } else {
                            assert(owner.continuations[i].entry_own
                                == owner_before_dfs.continuations[i].entry_own);
                            assert(forall|j: int|
                                0 <= j < NR_ENTRIES ==>
                                #[trigger] owner.continuations[owner.level - 1].children[j] ==
                                owner_before_dfs.continuations[owner.level - 1].children[j]);
                        }
                    };

                    assert forall|i: int|
                        #![auto]
                        owner.level - 1 <= i < NR_LEVELS
                            implies owner.continuations[i].view_mappings()
                        == owner_before_dfs.continuations[i].view_mappings() by {
                            assert(owner.continuations[i].children
                                =~= owner_before_dfs.continuations[i].children);
                    };

                    assert(forall|m: Mapping|
                        owner.view_mappings().contains(m) <==> #[trigger] owner_before_dfs.view_mappings().contains(m));
                }

                // num_frames == subtree mappings count: from dfs_mark_stray_and_unlock postcondition.
                assert(num_frames as nat ==
                    PageTableOwner::<C>(owner0.cur_subtree())@.mappings.len());

                Some(
                    PageTableFrag::StrayPageTable {
                        pt: pt.into(),
                        va,
                        len: page_size(self.0.level),
                        num_frames,
                    },
                )
            },
        };

        assert(forall|idx: usize| #![trigger regions.slot_owners[idx].paths_in_pt]
            (new_owner.value.is_absent() || idx != frame_to_index(new_owner.value.meta_slot_paddr().unwrap()))
                ==> regions.slot_owners[idx].paths_in_pt == regions0.slot_owners[idx].paths_in_pt
        ) by {
            assert(forall|i: usize| #![trigger regions.slot_owners[i].paths_in_pt]
                regions.slot_owners[i].paths_in_pt == regions_after_replace.slot_owners[i].paths_in_pt);
        };

        // Hoist popped_too_high preservation: replace_cur_entry only modifies the
        // current entry's continuation, not the owner's pop state. The body's
        // tracked_remove/insert pattern doesn't touch this field, so it inherits
        // from the precondition `!old(owner).popped_too_high`.
        assert(!owner.popped_too_high);

        result
    }
}

} // verus!
 
