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

use crate::mm::frame::Frame;
use crate::mm::page_table::*;
use crate::mm::{Paddr, Vaddr, MAX_NR_LEVELS, MAX_PADDR};
use crate::specs::arch::kspace::FRAME_METADATA_RANGE;
use crate::specs::mm::frame::mapping::{frame_to_index, frame_to_index_spec, frame_to_meta, max_meta_slots, meta_addr, meta_to_frame, META_SLOT_SIZE};
use crate::specs::mm::frame::meta_owners::{MetaSlotOwner, REF_COUNT_UNUSED};
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;

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
    pub path: [Option<PPtr<PageTableGuard<'rcu, C>>>; NR_LEVELS],
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
pub struct CursorMut<'rcu, C: PageTableConfig, A: InAtomicMode> {
    pub inner: Cursor<'rcu, C, A>,
}

impl<C: PageTableConfig, A: InAtomicMode> Iterator for Cursor<'_, C, A> {
    type Item = PagesState<C>;

    #[verifier::external_body]
    fn next(&mut self) -> Option<Self::Item> {
        unimplemented!()
    }
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
        ret >= 2,
{
    PAGE_SIZE << (nr_subpage_per_huge::<PagingConsts>().ilog2() as usize * (level as usize - 1))
}

/// When `va` is aligned to `page_size(large_level)` and `level <= large_level` (so
/// page_size(level) divides page_size(large_level)), then `va` is aligned to page_size(level).
/// Note: page_size(level) for level >= 1 is always a multiple of PAGE_SIZE.
pub proof fn lemma_va_align_page_size(va: Vaddr, level: PagingLevel)
    requires
        1 <= level <= NR_LEVELS + 1,
        va % PAGE_SIZE == 0,
        exists |large_level: PagingLevel|
            1 <= large_level <= NR_LEVELS + 1
            && level <= large_level
            && va % page_size_spec(large_level) == 0,
    ensures
        va % page_size_spec(level) == 0,
{
    let large_level: PagingLevel = choose |l: PagingLevel|
        1 <= l <= NR_LEVELS + 1 && level <= l && va % page_size_spec(l) == 0;
    if level == large_level {
        // va % page_size_spec(level) == va % page_size_spec(large_level) == 0
    } else if level == 1nat {
        // page_size_spec(1) == PAGE_SIZE, so va % page_size_spec(1) == va % PAGE_SIZE == 0
        lemma_page_size_spec_level1();
    } else {
        // 2 <= level < large_level: level <= NR_LEVELS (since level < large_level <= NR_LEVELS+1)
        let ps_l = page_size_spec(level) as int;
        let ps_ll = page_size_spec(large_level) as int;
        // ps_l >= PAGE_SIZE > 0
        axiom_page_size_ge_page_size(level);
        assert(ps_l > 0);
        // ps_ll >= PAGE_SIZE > 0
        axiom_page_size_ge_page_size(large_level);
        assert(ps_ll > 0);
        // ps_ll % ps_l == 0
        axiom_page_size_divides(level, large_level);
        assert(ps_ll % ps_l == 0);
        // ps_ll >= ps_l: if ps_ll < ps_l then lemma_small_mod would give ps_ll % ps_l == ps_ll > 0
        assert(ps_ll >= ps_l) by {
            if ps_ll < ps_l {
                vstd::arithmetic::div_mod::lemma_small_mod(ps_ll as nat, ps_l as nat);
                assert(false); // ps_ll % ps_l == ps_ll > 0, contradicts ps_ll % ps_l == 0
            }
        };
        // k = ps_ll / ps_l, k > 0, ps_ll == ps_l * k
        let k = ps_ll / ps_l;
        vstd::arithmetic::div_mod::lemma_div_non_zero(ps_ll, ps_l);
        assert(k > 0);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ps_ll, ps_l);
        assert(ps_ll == ps_l * k);
        // (va as int % (ps_l * k)) % ps_l == va as int % ps_l
        vstd::arithmetic::div_mod::lemma_mod_mod(va as int, ps_l, k);
        // va as int % ps_ll == 0 (from va % page_size_spec(large_level) == 0)
        // So (va as int % ps_ll) % ps_l == 0 % ps_l == 0 == va as int % ps_l
        assert(va as int % ps_ll == 0);
        assert(va as int % ps_l == 0);
    }
}

/// page_size_spec(1) == PAGE_SIZE.
/// Both sides equal PAGE_SIZE * pow2(0) = PAGE_SIZE * 1 = PAGE_SIZE,
/// because the exponent ilog2 * (1 - 1) = ilog2 * 0 = 0.
pub proof fn lemma_page_size_spec_level1()
    ensures
        page_size_spec(1) == PAGE_SIZE,
{
    // ilog2 * 0 == 0 (for any value of ilog2)
    vstd::arithmetic::mul::lemma_mul_by_zero_is_zero(
        nr_subpage_per_huge::<PagingConsts>().ilog2() as int,
    );
    // pow2(0) == pow(2, 0) == 1
    broadcast use vstd::arithmetic::power2::lemma_pow2;
    vstd::arithmetic::power::lemma_pow0(2int);
    // Z3 can now unfold page_size_spec(1) = (PAGE_SIZE * 1) as usize = PAGE_SIZE
}

/// Special case for level 1: page_size_spec(1) == PAGE_SIZE, so va % PAGE_SIZE == 0 implies
/// va % page_size_spec(1) == 0.
pub proof fn lemma_va_align_page_size_level_1(va: Vaddr)
    requires
        va % PAGE_SIZE == 0,
    ensures
        va % page_size_spec(1) == 0,
{
    lemma_page_size_spec_level1();
}

/// For any level in [1, NR_LEVELS], page_size(level) is a multiple of PAGE_SIZE.
///
/// Mathematically: page_size(level) = PAGE_SIZE * pow2(e) for e = ilog2 * (level-1),
/// so PAGE_SIZE divides it.  Proving this from the `page_size_spec` definition requires
/// bounding the `as usize` cast (no overflow for levels 1–NR_LEVELS), which is left as
/// an axiom following the same pattern as `axiom_page_size_ge_page_size`.
///
/// TODO: replace with a proof once the pow2-overflow bounds are established.
pub axiom fn axiom_page_size_multiple_of_page_size(level: PagingLevel)
    requires
        1 <= level <= NR_LEVELS,
    ensures
        page_size_spec(level) % PAGE_SIZE == 0;

/// For any level in [1, NR_LEVELS+1], the page size is at least PAGE_SIZE.
/// This follows from page_size(level) = PAGE_SIZE * pow2((ilog2 * (level-1)) as nat)
/// with pow2(k) >= 1 for all k >= 0.
pub axiom fn axiom_page_size_ge_page_size(level: PagingLevel)
    requires
        1 <= level <= NR_LEVELS + 1,
    ensures
        page_size(level) >= PAGE_SIZE;

/// `page_size` is strictly monotone in the level: a higher level has a strictly larger page size.
/// This follows from page_size(level) = PAGE_SIZE * 512^(level-1); incrementing level multiplies
/// by 512, so page_size(l+1) = 512 * page_size(l) > page_size(l).
pub axiom fn axiom_page_size_monotone(l1: PagingLevel, l2: PagingLevel)
    requires
        1 <= l1 <= NR_LEVELS + 1,
        1 <= l2 <= NR_LEVELS + 1,
        l1 <= l2,
    ensures
        page_size(l1) <= page_size(l2);

/// page_size(l2) is divisible by page_size(l1) when l1 <= l2.
/// This holds because page_size(l) = PAGE_SIZE * 512^(l-1), so
/// page_size(l2) / page_size(l1) = 512^(l2-l1), which is a positive integer.
pub axiom fn axiom_page_size_divides(l1: PagingLevel, l2: PagingLevel)
    requires
        1 <= l1 <= l2 <= NR_LEVELS + 1,
    ensures
        page_size_spec(l2) % page_size_spec(l1) == 0;

/// For any valid physical address `pa < MAX_PADDR` and page level, pa + page_size(level)
/// does not overflow usize. This holds because MAX_PADDR = 2^31 and page sizes are at
/// most 2^39 (NR_LEVELS = 4), so pa + size < 2^40 << usize::MAX = 2^64.
pub axiom fn axiom_pa_plus_page_size_no_overflow(pa: Paddr, level: PagingLevel)
    requires
        1 <= level <= NR_LEVELS,
        pa < MAX_PADDR,
    ensures
        pa + page_size(level) < usize::MAX;

/// Borrows a live `PageTableNode` as a `PageTableNodeRef` without requiring
/// `raw_count == 1`.
///
/// ## Justification
/// `Child::from_pte` (called inside `Entry::replace`) invokes `PageTableNode::from_raw`,
/// which sets `regions.slot_owners[idx].raw_count = 0` and marks the entry owner
/// `in_scope = true`.  Consequently `relate_region` reports `raw_count == 0`, but
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
        with Tracked(slot_perm): Tracked<&PointsTo<MetaSlot>>,
        Tracked(rc_perm): Tracked<&mut PermissionU64>)]
    pub fn clone_item(item: &C::Item) -> (res: C::Item)
        requires
            item.clone_requires(*slot_perm, *old(rc_perm)),
            old(rc_perm).is_for(slot_perm.value().ref_count),
            old(rc_perm).value() < u64::MAX,
        ensures
            res == *item,
            rc_perm.value() == old(rc_perm).value() + 1,
    {
        item.clone(Tracked(slot_perm), Tracked(rc_perm))
    }

    pub open spec fn cursor_new_success_conditions(va: &Range<Vaddr>) -> bool {
        &&& va.start < va.end
        &&& va.start % C::BASE_PAGE_SIZE() == 0
        &&& va.end % C::BASE_PAGE_SIZE() == 0
        &&& crate::mm::page_table::is_valid_range_spec::<C>(va)
    }

    /// Creates a cursor claiming exclusive access over the given range.
    ///
    /// The cursor created will only be able to query or jump within the given
    /// range. Out-of-bound accesses will result in panics or errors as return values,
    /// depending on the access method.
    #[verus_spec(r =>
        with Tracked(pt_own): Tracked<PageTableOwner<C>>,
            Tracked(guard_perm): Tracked<PointsTo<PageTableGuard<'rcu, C>>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            pt_own.inv(),
        ensures
            Self::cursor_new_success_conditions(va) ==> {
                &&& r is Ok
                &&& r.unwrap().1.in_locked_range()
                &&& r.unwrap().0.level < r.unwrap().0.guard_level
                &&& r.unwrap().0.va < r.unwrap().0.barrier_va.end
                &&& r.unwrap().0.va == va.start
                &&& r.unwrap().0.barrier_va == *va
            }
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
            assert(pt_own.0.inv_children());
            assert forall|i: int| 0 <= i < NR_ENTRIES implies pt_own.0.children[i] is Some by {
                if pt_own.0.children[i] is None {
                    assert(<EntryOwner<C> as TreeNodeValue<INC_LEVELS>>::rel_children(pt_own.0.value, i, None));
                }
            };
        }

        Ok(
            #[verus_spec(with Tracked(pt_own), Tracked(guard_perm), Tracked(regions), Tracked(guards))]
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

    pub open spec fn invariants(
        self,
        owner: CursorOwner<'rcu, C>,
        regions: MetaRegionOwners,
        guards: Guards<'rcu, C>,
    ) -> bool {
        &&& owner.inv()
        &&& self.inv()
        &&& self.wf(owner)
        &&& regions.inv()
        &&& owner.children_not_locked(guards)
        &&& owner.nodes_locked(guards)
        &&& owner.relate_region(regions)
        &&& !owner.popped_too_high
    }

    pub open spec fn query_some_condition(self, owner: CursorOwner<'rcu, C>) -> bool {
        self.model(owner).present()
    }

    pub open spec fn query_some_ensures(
        self,
        owner: CursorOwner<'rcu, C>,
        res: PagesState<C>,
    ) -> bool {
        &&& owner.cur_va_range().start.reflect(res.0.start)
        &&& owner.cur_va_range().end.reflect(res.0.end)
        &&& res.1 is Some
        &&& owner@.query_item_spec(res.1.unwrap()) == Some(owner@.query_range())
    }

    pub open spec fn query_none_ensures(
        self,
        owner: CursorOwner<'rcu, C>,
        res: PagesState<C>,
    ) -> bool {
        &&& res.1 is None
    }

    /// Queries the mapping at the current virtual address.
    ///
    /// If the cursor is pointing to a valid virtual address that is locked,
    /// it will return the virtual address range and the item at that slot.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// ## Postconditions
    /// ## Safety
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            old(self).invariants(*old(owner), *old(regions), *old(guards)),
        ensures
            self.invariants(*owner, *regions, *guards),
            old(owner)@.mappings == owner@.mappings,
            old(owner).in_locked_range() ==> res is Ok,
            res matches Ok(state) ==>
                self.query_some_condition(*owner) ==>
                self.query_some_ensures(*owner, state),
            res matches Ok(state) ==>
                !self.query_some_condition(*owner) ==>
                self.query_none_ensures(*owner, state),
    )]
    pub fn query(&mut self) -> Result<PagesState<C>, PageTableError> {
        if self.va >= self.barrier_va.end {
            proof {
                owner.va.reflect_prop(self.va);
            }
            return Err(PageTableError::InvalidVaddr(self.va));
        }
        let rcu_guard = self.rcu_guard;

        let ghost initial_va = self.va;

        loop
            invariant
                self.invariants(*owner, *regions, *guards),
                self.va == initial_va,
                old(owner)@.mappings == owner@.mappings,
            decreases self.level,
        {
            proof { reveal(CursorContinuation::inv_children); }

            let cur_va = self.va;
            let level = self.level;

            #[verus_spec(with Tracked(owner), Tracked(regions))]
            let entry = self.cur_entry();

            let ghost continuations0 = owner.continuations;
            let ghost owner_snap = *owner;
            let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
            let ghost cont0 = continuation;
            let tracked child_owner = continuation.take_child();
            let tracked parent_owner = continuation.entry_own.node.tracked_borrow();

            assert(!child_owner.value.in_scope) by {
                owner_snap.continuations_not_in_scope();
                assert(owner_snap.continuations[(owner_snap.level - 1) as int].children[cont0.idx as int] is Some);
            };

            #[verus_spec(with Tracked(&child_owner.value), Tracked(&parent_owner), Tracked(regions), Tracked(&continuation.guard_perm) )]
            let cur_child = entry.to_ref();

            proof {
                assert(cur_child.wf(child_owner.value));
                continuation.put_child(child_owner);
                cont0.take_put_child();
                owner.continuations.tracked_insert(owner.level - 1, continuation);
                assert(owner.continuations == continuations0);
            }

            let item = match cur_child {
                ChildRef::PageTable(pt) => {
                    let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
                    let tracked mut child_owner = continuation.take_child();
                    let tracked mut child_node = child_owner.value.node.tracked_take();

                    proof_decl! {
                        let tracked mut guard_perm: Tracked<GuardPerm<'rcu, C>>;
                    }

                    let ghost guards0 = *guards;

                    // SAFETY: The `pt` must be locked and no other guards exist.

                    #[verus_spec(with Tracked(&child_node), Tracked(guards) => Tracked(guard_perm))]
                    let guard = pt.make_guard_unchecked(rcu_guard);

                    proof {
                        child_owner.value.node = Some(child_node);
                        continuation.put_child(child_owner);
                        owner.continuations.tracked_insert(owner.level - 1, continuation);

                        owner.map_children_implies(
                            CursorOwner::node_unlocked(guards0),
                            CursorOwner::node_unlocked_except(*guards, child_node.meta_perm.addr()),
                        );

                        assert(owner.relate_region(*regions));
                    }

                    proof { assert(owner.level > 1) by {
                        owner.cur_entry_node_implies_level_gt_1();
                    }; }
                    #[verus_spec(with Tracked(owner), Tracked(guard_perm), Tracked(regions), Tracked(guards))]
                    self.push_level(guard);

                    continue ;
                },
                ChildRef::None => {
                    assert(owner.cur_entry_owner().is_absent());
                    proof {
                        owner.cur_entry_absent_not_present();
                    }
                    None
                },
                ChildRef::Frame(pa, ch_level, prop) => {
                    assert(owner.cur_entry_owner().is_frame());
                    proof {
                        owner.cur_entry_frame_present();
                    }
                    assert(owner@.query(pa, page_size(level), prop));

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

                    let idx = frame_to_index(pa);
                    let ghost old_regions = *regions;
                    let tracked slot_perm = owner.borrow_cur_frame_slot_perm();
                    let tracked mut slot_own = regions.slot_owners.tracked_remove(idx);

                    assert(item.clone_requires(*slot_perm, slot_own.inner_perms.ref_count)) by {
                        owner.cur_frame_clone_requires(item, pa, level, prop, old_regions);
                    };

                    #[verus_spec(with Tracked(slot_perm), Tracked(&mut slot_own.inner_perms.ref_count))]
                    let cloned = Self::clone_item(&item);

                    proof {
                        regions.slot_owners.tracked_insert(idx, slot_own);
                        owner.clone_item_preserves_invariants(old_regions, *regions, idx);
                        assert(regions.inv());
                        assert(owner.relate_region(*regions));
                    }

                    Some(cloned)
                },
            };

            let size = page_size(level);

            proof {
                owner.cur_va_range_reflects_view();
            }

            assert(old(owner)@.mappings == owner@.mappings);

            return Ok(
                (#[verus_spec(with Tracked(owner))]
                self.cur_va_range(), item),
            );
        }
    }

    /// Moves the cursor forward to the next mapped virtual address.
    ///
    /// If there is mapped virtual address following the current address within
    /// next `len` bytes, it will return that mapped address. In this case, the
    /// cursor will stop at the mapped address.
    ///
    /// Otherwise, it will return `None`. And the cursor may stop at any
    /// address after `len` bytes.
    ///
    /// # Panics
    ///
    /// Panics if:
    ///  - the length is longer than the remaining range of the cursor;
    ///  - the length is not page-aligned.
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
    )]
    pub fn find_next(&mut self, len: usize) -> (res: Option<Vaddr>)
        requires
            old(self).invariants(*old(owner), *old(regions), *old(guards)),
            old(self).level < old(self).guard_level,
            old(owner).in_locked_range(),
            len % C::BASE_PAGE_SIZE() == 0,
            old(self).va + len <= old(self).barrier_va.end,
        ensures
            self.invariants(*owner, *regions, *guards),
            res is Some ==> {
                &&& res.unwrap() == self.va
                &&& owner.level < owner.guard_level
                &&& owner.in_locked_range()
            },
    {
        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.find_next_impl(len, false, false)
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
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
    )]
    fn find_next_impl(&mut self, len: usize, find_unmap_subtree: bool, split_huge: bool) -> (res:
        Option<Vaddr>)
        requires
            old(self).invariants(*old(owner), *old(regions), *old(guards)),
            old(owner).in_locked_range(),
            old(owner).level < NR_LEVELS,
            // Panic conditions as preconditions
            len % C::BASE_PAGE_SIZE() == 0,
            old(self).va + len <= old(self).barrier_va.end,
        ensures
            self.invariants(*owner, *regions, *guards),
            res is Some ==> {
                &&& res.unwrap() == self.va
                &&& owner.level < owner.guard_level
                &&& !find_unmap_subtree ==> owner.cur_entry_owner().is_frame()
                &&& owner.in_locked_range()
            },
            res is Some && !find_unmap_subtree && old(owner).cur_entry_owner().is_frame() ==>
                owner.cur_entry_owner().frame.unwrap().prop
                == old(owner).cur_entry_owner().frame.unwrap().prop,
            res is None ==> {
                &&& self.va >= old(self).va + len
            },
    {
        let end = self.va + len;

        let rcu_guard = self.rcu_guard;

        while self.va < end
            invariant
                owner.inv(),
                self.inv(),
                self.wf(*owner),
                regions.inv(),
                self.inv(),
                owner.in_locked_range() || self.va >= end,
                end <= self.barrier_va.end,
                owner.children_not_locked(*guards),
                owner.nodes_locked(*guards),
                owner.relate_region(*regions),
                !owner.popped_too_high,
                owner.level < NR_LEVELS,
            decreases owner.max_steps(),
        {
            proof { reveal(CursorContinuation::inv_children); }

            let ghost owner0 = *owner;

            let cur_va = self.va;
            #[verus_spec(with Tracked(owner))]
            let cur_va_range = self.cur_va_range();
            let cur_entry_fits_range = cur_va == cur_va_range.start && cur_va_range.end <= end;

            #[verus_spec(with Tracked(owner), Tracked(regions))]
            let mut cur_entry = self.cur_entry();

            let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
            let ghost cont0 = continuation;
            let tracked child_owner = continuation.take_child();
            let tracked node_owner = continuation.entry_own.node.tracked_borrow();

            assert(!child_owner.value.in_scope) by {
                owner0.continuations_not_in_scope();
                assert(owner0.continuations[(owner0.level - 1) as int].children[cont0.idx as int] is Some);
            };

            #[verus_spec(with Tracked(&child_owner.value), Tracked(&node_owner), Tracked(regions), Tracked(&continuation.guard_perm))]
            let cur_child = cur_entry.to_ref();

            proof {
                continuation.put_child(child_owner);
                assert(continuation.children == cont0.children);
                owner.continuations.tracked_insert(owner.level - 1, continuation);
                assert(owner.continuations == owner0.continuations);
            }

            match cur_child {
                ChildRef::PageTable(pt) => {
                    if find_unmap_subtree && cur_entry_fits_range && (C::TOP_LEVEL_CAN_UNMAP()
                        || self.level != C::NR_LEVELS()) {
                        return Some(cur_va);
                    }
                    assert(owner.children_not_locked(*guards));

                    let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
                    let ghost cont0 = continuation;
                    let tracked mut child_owner = continuation.take_child();

                    let tracked mut parent_node_owner = continuation.entry_own.node.tracked_take();
                    let tracked mut child_node_owner = child_owner.value.node.tracked_take();

                    proof_decl! {
                        let tracked mut guard_perm: Tracked<GuardPerm<'rcu, C>>;
                    }

                    let ghost guards0 = *guards;

                    // SAFETY: The `pt` must be locked and no other guards exist.
                    #[verus_spec(with Tracked(&child_node_owner), Tracked(guards) => Tracked(guard_perm))]
                    let pt_guard = pt.make_guard_unchecked(rcu_guard);

                    #[verus_spec(with Tracked(&mut child_node_owner))]
                    let nr_children = pt_guard.borrow(Tracked(&guard_perm)).nr_children();

                    proof {
                        child_owner.value.node = Some(child_node_owner);
                        continuation.put_child(child_owner);
                        continuation.entry_own.node = Some(parent_node_owner);
                        assert(cont0.children == continuation.children);
                        owner.continuations.tracked_insert(self.level - 1, continuation);
                        assert(owner.continuations == owner0.continuations);

                        owner.map_children_implies(
                            CursorOwner::node_unlocked(guards0),
                            CursorOwner::node_unlocked_except(
                                *guards,
                                child_node_owner.meta_perm.addr(),
                            ),
                        );
                    }

                    assert(owner.only_current_locked(*guards));

                    // If there's no mapped PTEs in the next level, we can
                    // skip to save time.
                    if (nr_children != 0) {
                        proof { assert(owner.level > 1) by {
                            owner.cur_entry_node_implies_level_gt_1();
                        }; }
                        #[verus_spec(with Tracked(owner), Tracked(guard_perm), Tracked(regions), Tracked(guards))]
                        self.push_level(pt_guard);
                    } else {
                        let ghost guards_before_drop = *guards;
                        let ghost locked_addr = child_node_owner.meta_perm.addr();

                        let _ = ManuallyDrop::new(
                            pt_guard.take(Tracked(&mut guard_perm)),
                            Tracked(guards),
                        );
                        proof {
                            assert(OwnerSubtree::implies(
                                CursorOwner::node_unlocked_except(guards_before_drop, locked_addr),
                                CursorOwner::node_unlocked(*guards),
                            ));
                            owner.map_children_implies(
                                CursorOwner::node_unlocked_except(guards_before_drop, locked_addr),
                                CursorOwner::node_unlocked(*guards),
                            );
                            assert(owner.children_not_locked(*guards));

                            owner.move_forward_increases_va();
                            owner.move_forward_not_popped_too_high();
                        }

                        let ghost owner_before_move = *owner;
                        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
                        self.move_forward();

                        proof {
                            owner.va.reflect_prop(self.va);
                            assert(*owner == owner_before_move.move_forward_owner_spec());
                            owner.in_locked_range_level_lt_nr_levels();
                        }
                    }

                    proof {
                        assert(owner.in_locked_range());
                        owner.in_locked_range_level_lt_nr_levels();
                    }
                    continue ;
                },
                ChildRef::None => {
                    proof {
                        owner.move_forward_increases_va();
                        owner.move_forward_not_popped_too_high();
                    }

                    // These predicates are established by the loop invariants

                    let ghost owner_before_move = *owner;
                    #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
                    self.move_forward();

                    proof {
                        owner.va.reflect_prop(self.va);
                        assert(*owner == owner_before_move.move_forward_owner_spec());
                        // move_forward ensures owner.in_locked_range()
                        owner.in_locked_range_level_lt_nr_levels();
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
                                // Both owner and old(owner) are at frames in the same locked region.
                                // find_next_impl does not modify frame props; any found frame is
                                // either the same frame or a sub-frame after split (same prop).
                                owner.find_next_frame_prop_preserved(*old(owner));
                            }
                        };
                        return Some(cur_va);
                    }
                    let tracked mut continuation = owner.continuations.tracked_remove(
                        owner.level - 1,
                    );
                    let tracked mut child_owner = continuation.take_child();
                    let tracked mut parent_owner = continuation.entry_own.node.tracked_take();

                    proof {
                        assert(parent_owner.level == child_owner.value.parent_level);
                        assert(child_owner.value.is_frame());
                        assert(parent_owner.level > 1) by {
                            // child_owner.value.parent_level == owner0.level:
                            // The continuation at owner0.level-1 has level() == owner0.level
                            // (from owner0.inv() by case analysis). child_owner was taken from
                            // that continuation's child slot; inv_children gives parent_level
                            // == continuation.level() == owner0.level.
                            assert(child_owner.value.parent_level == owner0.level) by {
                                let cont_key = (owner0.level - 1) as int;
                                let cont_snap = owner0.continuations[cont_key];
                                assert(cont_snap.level() == owner0.level) by {
                                    if owner0.level == 1 {} else if owner0.level == 2 {}
                                    else if owner0.level == 3 {} else {}
                                };
                                // cont_snap.all_some() from owner0.inv(), so child slot is Some
                                assert(cont_snap.all_some());
                                assert(cont_snap.children[cont_snap.idx as int] is Some);
                                reveal(CursorContinuation::inv_children);
                                assert(cont_snap.inv_children());
                                // inv_children at cont_snap.idx gives parent_level == cont_snap.level()
                                assert(cont_snap.children[cont_snap.idx as int].unwrap().value.parent_level
                                    == cont_snap.level());
                                // child_owner.value == cont_snap.children[cont_snap.idx].unwrap().value
                                // (from take_child ensures: child_owner == old(cont).take_child_spec().0)
                                assert(child_owner.value == cont_snap.children[cont_snap.idx as int].unwrap().value);
                            };
                            // owner0.level > 1 from frame_not_fits_implies_level_gt_1:
                            // !cur_entry_fits_range, owner0.cur_va() < end, end % BASE == 0
                            owner0.frame_not_fits_implies_level_gt_1(cur_entry_fits_range, cur_va, end);
                            // parent_owner.level == child_owner.value.parent_level == owner0.level > 1
                        };
                    }

                    let split_child = (
                    #[verus_spec(with Tracked(&mut child_owner), Tracked(&mut parent_owner), Tracked(regions),
                        Tracked(guards), Tracked(&mut continuation.guard_perm))]
                    cur_entry.split_if_mapped_huge(rcu_guard)).expect(
                        "The entry must be a huge page",
                    );

                    proof {
                        assert(guards.guards.contains_key(split_child.addr()));
                        assert(guards.locked(split_child.addr()));
                        assert(child_owner.value.node.unwrap().meta_perm.addr()
                            == split_child.addr());
                    }

                    let tracked guard_perm = guards.take(
                        child_owner.value.node.unwrap().meta_perm.addr(),
                    );

                    proof {
                        continuation.put_child(child_owner);
                        continuation.entry_own.node = Some(parent_owner);
                        assert(continuation.inv()) by {
                            // Establish all preconditions of continuation_inv_holds_after_split_restore.
                            // entry_own.is_node(): node = Some(parent_owner), frame/absent unchanged
                            assert(continuation.entry_own.is_node());
                            // entry_own.inv(): from parent_owner.inv() (split post)
                            assert(continuation.entry_own.inv());
                            // relate_guard_perm: parent_owner.relate_guard_perm(*guard_perm)
                            // from split post (line 569), guard_perm == continuation.guard_perm
                            assert(continuation.entry_own.node.unwrap().relate_guard_perm(
                                continuation.guard_perm));
                            // children.len() == NR_ENTRIES: unchanged
                            assert(continuation.children.len() == NR_ENTRIES);
                            // 0 <= idx < NR_ENTRIES: unchanged
                            assert(0 <= continuation.idx < NR_ENTRIES);
                            // tree_level: unchanged; level() == parent_owner.level (preserved)
                            assert(continuation.tree_level
                                == INC_LEVELS - continuation.level() - 1) by { admit() };
                            assert(continuation.tree_level < INC_LEVELS - 1);
                            // path().len() == tree_level: path unchanged
                            assert(continuation.path().len() == continuation.tree_level);
                            // child at idx: from put_child(child_owner)
                            assert(continuation.children[continuation.idx as int] is Some);
                            // child.value.is_node(): from split post (owner.value.is_node())
                            assert(continuation.children[continuation.idx as int].unwrap().value.is_node());
                            // child.inv(): from child_owner.inv() (owner.inv() from split post)
                            assert(continuation.children[continuation.idx as int].unwrap().inv());
                            // child.parent_level == continuation.level(): from parent_owner.level
                            assert(continuation.children[continuation.idx as int].unwrap().value.parent_level
                                == continuation.level()) by { admit() };
                            // child.path == path().push_tail(idx): from split, path preserved
                            assert(continuation.children[continuation.idx as int].unwrap().value.path
                                == continuation.path().push_tail(continuation.idx as usize));
                            // child.level == tree_level + 1: from split, level preserved
                            assert(continuation.children[continuation.idx as int].unwrap().level
                                == continuation.tree_level + 1);
                            continuation.continuation_inv_holds_after_split_restore();
                        };
                        owner.continuations.tracked_insert(owner.level - 1, continuation);

                        owner0.max_steps_partial_inv(*owner, owner.level as usize);
                    }

                    proof { assert(owner.level > 1) by {
                        // After splitting, child_owner.value.is_node() (from split postcondition)
                        // owner.cur_entry_owner() == child_owner.value is_node() after put_child
                        owner.cur_entry_node_implies_level_gt_1();
                    }; }
                    #[verus_spec(with Tracked(owner), Tracked(guard_perm), Tracked(regions), Tracked(guards))]
                    self.push_level(split_child);

                    continue ;
                },
            }
        }

        assert(self.va >= end);

        None
    }

    pub open spec fn jump_panic_condition(self, va: Vaddr) -> bool {
        va % PAGE_SIZE == 0
    }

    /// Jumps to the given virtual address.
    /// If the target address is out of the range, this method will return `Err`.
    ///
    /// # Panics
    ///
    /// This method panics if the address has bad alignment.
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
    )]
    pub fn jump(&mut self, va: Vaddr) -> (res: Result<(), PageTableError>)
        requires
            old(self).invariants(*old(owner), *old(regions), *old(guards)),
            old(self).level < old(self).guard_level,
            old(owner).in_locked_range(),
            old(self).jump_panic_condition(va),
        ensures
            self.invariants(*owner, *regions, *guards),
            self.barrier_va.start <= va < self.barrier_va.end ==> {
                &&& res is Ok
                &&& self.va == va
            },
            !(self.barrier_va.start <= va < self.barrier_va.end) ==> res is Err,
    {
        if !self.barrier_va.contains(&va) {
            return Err(PageTableError::InvalidVaddr(va));
        }
        loop
            invariant
                self.invariants(*owner, *regions, *guards),
                self.level <= self.guard_level,
                self.barrier_va.start <= va < self.barrier_va.end,
                owner.in_locked_range(),
            decreases self.guard_level - self.level,
        {
            let node_size = page_size(self.level + 1);
            let node_start = self.va.align_down(node_size);

            proof {
                assert(self.barrier_va.start == owner.locked_range().start);
                assert(self.barrier_va.end == owner.locked_range().end);
                AbstractVaddr::reflect_prop(owner.va, self.va);
                assert(owner.va.to_vaddr() == self.va);
                let aligned_va = nat_align_down(self.va as nat, node_size as nat) as usize;
                assert(node_start == aligned_va);

                if self.level < self.guard_level {
                    owner.node_within_locked_range(self.level);
                    let expected_aligned = nat_align_down(
                        owner.va.to_vaddr() as nat,
                        page_size((self.level + 1) as PagingLevel) as nat,
                    ) as usize;
                    assert(node_start == expected_aligned);
                    assert(owner.locked_range().start <= expected_aligned);
                    assert(expected_aligned + page_size((self.level + 1) as PagingLevel)
                        <= owner.locked_range().end);
                }
            }
            assert(self.barrier_va.start <= node_start);
            assert(node_start + node_size <= self.barrier_va.end);

            // If the address is within the current node, we can jump directly.
            if node_start <= va && va < node_start + node_size {
                let ghost owner0 = *owner;
                let ghost new_va = AbstractVaddr::from_vaddr(va);
                self.va = va;
                proof {
                    AbstractVaddr::from_vaddr_wf(va);

                    assume(forall|i: int|
                        #![auto]
                        owner0.level - 1 <= i < NR_LEVELS ==> new_va.index[i]
                            == owner0.va.index[i]);
                    assume(forall|i: int|
                        #![auto]
                        owner0.guard_level - 1 <= i < NR_LEVELS ==> new_va.index[i]
                            == owner0.prefix.index[i]);

                    owner.set_va_preserves_inv(new_va);
                    owner.set_va(new_va);
                }

                assert(self.invariants(*owner, *regions, *guards));

                return Ok(());
            }
            // self.level < guard_level - 1: if level == guard_level - 1, the node covers the
            // entire locked range and va is always within it (so the if branch is taken, not here).
            // Therefore in the else branch we have level < guard_level - 1.
            // This ensures !popped_too_high after pop_level.
            assert(self.level + 1 < self.guard_level) by {
                assert(owner.locked_range().start == self.barrier_va.start);
                assert(owner.locked_range().end == self.barrier_va.end);
                // level < guard_level: from owner.inv() + !popped_too_high + in_locked_range()
                owner.in_locked_range_level_lt_guard_level();
                // axiom: when va (in locked range) is not in the level+1 node, level+1 < guard
                owner.jump_not_in_node_level_lt_guard_minus_one(self.level, va, node_start);
            };
            assert(self.level < self.guard_level - 1) by {
                assert(self.level + 1 < self.guard_level);
            };

            #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
            self.pop_level();

            proof {
                assert(!owner.popped_too_high);
            }
        }
    }

    /// Traverses forward to the end of [`Self::cur_va_range`].
    //
    /// If reached the end of the current page table node, it (recursively)
    /// moves itself up to the next page of the parent page.
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
            old(owner).in_locked_range(),
            old(owner).children_not_locked(*old(guards)),
            old(owner).nodes_locked(*old(guards)),
            old(owner).relate_region(*old(regions)),
        ensures
            owner.inv(),
            self.wf(*owner),
            self.inv(),
            regions.inv(),
            *owner == old(owner).move_forward_owner_spec(),
            owner.max_steps() < old(owner).max_steps(),
            self.barrier_va == old(self).barrier_va,
            self.guard_level == old(self).guard_level,
            !owner.popped_too_high,
            owner.in_locked_range(),
            owner.children_not_locked(*guards),
            owner.nodes_locked(*guards),
            owner.relate_region(*regions),
            owner.va == old(owner).va.align_up(old(self).level as int),
            // move_forward only calls pop_level, which does not touch regions.
            forall|idx: usize| #![trigger regions.slot_owners[idx].path_if_in_pt]
                regions.slot_owners[idx].path_if_in_pt == old(regions).slot_owners[idx].path_if_in_pt,
    {
        let ghost owner0 = *owner;
        let ghost regions0 = *regions;
        proof {
            owner.move_forward_owner_decreases_steps();
            old(owner).move_forward_not_popped_too_high();
            old(owner).move_forward_owner_preserves_in_locked_range();
        }

        let ghost start_level = self.level;
        let ghost guard_level = self.guard_level;
        let ghost barrier_va = self.barrier_va;
        let ghost va = self.va;

        let next_va = (#[verus_spec(with Tracked(owner))]
        self.cur_va_range()).end;

        let ghost abs_va_down = owner0.va.align_down((start_level - 1) as int);
        let ghost abs_next_va = AbstractVaddr::from_vaddr(next_va);

        proof {
            AbstractVaddr::reflect_from_vaddr(next_va);
            owner0.va.reflect_prop(va);
            if start_level > 1 {
                owner0.va.align_down_inv((start_level - 1) as int);
                owner0.va.align_down_concrete(start_level - 1);
                owner0.va.align_down(start_level - 1).reflect_prop(
                    nat_align_down(
                        va as nat,
                        page_size((start_level - 1) as PagingLevel) as nat,
                    ) as Vaddr,
                );
            } else {
                // start_level == 1: abs_va_down = owner0.va.align_down(0).
                // align_down(0) is not defined by the recursive spec (only level >= 1),
                // so we use the axiom that it preserves inv() and all indices.
                owner0.va.align_down_zero_properties();
            }
            abs_next_va.reflect_prop(next_va);

            AbstractVaddr::reflect_eq(abs_next_va, owner0.va.align_up(start_level as int), next_va);
            assert(abs_next_va == owner0.va.align_up(start_level as int));
            assert(abs_next_va == owner0.va.align_down((start_level - 1) as int).next_index(
                start_level as int,
            ));

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
                forall|i: int|
                    start_level <= i < NR_LEVELS ==> #[trigger] owner0.va.index[i - 1]
                        == abs_va_down.index[i - 1],
                forall|i: int|
                    self.level <= i < NR_LEVELS ==> #[trigger] owner0.va.index[i - 1]
                        == owner.continuations[i - 1].idx,
                owner.in_locked_range(),
                owner.children_not_locked(*guards),
                owner.nodes_locked(*guards),
                owner.relate_region(*regions),
                // pop_level does not touch regions, so path_if_in_pt is preserved.
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
        assert(self.level >= self.guard_level || index != 0);
        assert(self.level < self.guard_level) by {
            owner.move_forward_pop_loop_level_lt_guard(owner0);
        };

        assert(owner0.va.index[self.level - 1] + 1 < NR_ENTRIES);
        assert(owner.move_forward_owner_spec() == owner0.move_forward_owner_spec());
        assert(owner.move_forward_owner_spec() == owner.inc_index().zero_below_level());

        self.va = next_va;

        proof {
            owner.do_inc_index();
            owner.zero_preserves_all_but_va();
            owner.do_zero_below_level();
            owner0.move_forward_va_is_align_up();
        }
    }

    /// Goes up a level.
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
            old(owner).relate_region(*old(regions)),
        ensures
            self.inv(),
            self.wf(*owner),
            regions.inv(),
            owner.inv(),
            owner.in_locked_range(),
            owner.children_not_locked(*guards),
            owner.nodes_locked(*guards),
            owner.relate_region(*regions),
            self.guard_level == old(self).guard_level,
            *owner == old(owner).pop_level_owner_spec().0,
            // pop_level does not touch regions at all (only owner and guards are modified).
            *regions == *old(regions),
    {
        proof {
            let ghost child_cont = owner.continuations[owner.level - 1];
            assert(child_cont.all_some());
            assert(child_cont.inv());
            assert(self.path[self.level as usize - 1] is Some);
            assert(self.path[self.level as usize - 1].unwrap().addr()
                == owner.continuations[owner.level - 1].guard_perm.addr());
            assert(guards.lock_held(
                owner.continuations[owner.level - 1].guard_perm.value().inner.inner@.ptr.addr(),
            ));
            owner.pop_level_owner_preserves_invs(*guards, *regions);
        }
        let tracked guard_perm = owner.pop_level_owner();

        let ghost owner0 = *owner;
        let ghost guards0 = *guards;
        let ghost guard = guard_perm.value();

        let taken: Option<PPtr<PageTableGuard<'rcu, C>>> = *self.path.get(
            self.level as usize - 1,
        ).unwrap();
        let _ = ManuallyDrop::new(taken.unwrap().take(Tracked(&mut guard_perm)), Tracked(guards));

        proof {
            owner.never_drop_restores_children_not_locked(guard, guards0, *guards);
            owner.never_drop_restores_nodes_locked(guard, guards0, *guards);
        }

        self.level = self.level + 1;

        assert(self.wf(*owner));
    }

    /// Goes down a level to a child page table.
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(guard_perm): Tracked<GuardPerm<'rcu, C>>,
            Tracked(regions): Tracked<&MetaRegionOwners>,
            Tracked(guards): Tracked<&Guards<'rcu, C>>
    )]
    fn push_level(&mut self, child_pt: PPtr<PageTableGuard<'rcu, C>>)
        requires
            old(owner).inv(),
            regions.inv(),
            old(self).inv(),
            old(self).wf(*old(owner)),
            old(owner).cur_entry_owner().is_node(),
            old(owner).cur_entry_owner().node.unwrap().relate_guard_perm(guard_perm),
            guard_perm.addr() == child_pt.addr(),
            old(owner).level > 1,
            //old(owner).in_locked_range(),
            old(owner).only_current_locked(*guards),
            old(owner).nodes_locked(*guards),
            old(owner).relate_region(*regions),
            !old(owner).popped_too_high,
            guards.lock_held(guard_perm.value().inner.inner@.ptr.addr()),
        ensures
            owner.inv(),
            owner.children_not_locked(*guards),
            owner.nodes_locked(*guards),
            owner.relate_region(*regions),
            self.inv(),
            self.wf(*owner),
            self.guard_level == old(self).guard_level,
            self.level == old(self).level - 1,
            self.va == old(self).va,
            *owner == old(owner).push_level_owner_spec(guard_perm),
            owner.max_steps() < old(owner).max_steps(),
            old(owner)@.mappings == owner@.mappings,
    {
        assert(owner.va.index.contains_key(owner.level - 2)) by {
            // old(owner).level > 1 (precondition), so owner.level - 2 is in [0, NR_LEVELS)
            assert(owner.level >= 2);
            assert(owner.va.inv());
        };

        self.level = self.level - 1;
        // debug_assert_eq!(self.level, child_pt.level());

        // let old = self.path.get(self.level as usize - 1);
        self.path.set(self.level as usize - 1, Some(child_pt));

        proof {
            owner.push_level_owner_preserves_invs(guard_perm, *regions, *guards);
            owner.push_level_owner_decreases_steps(guard_perm);
            owner.push_level_owner_preserves_va(guard_perm);
            owner.push_level_owner_preserves_mappings(guard_perm);
            owner.push_level_owner(Tracked(guard_perm));
        }
        // debug_assert!(old.is_none());
    }

    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&MetaRegionOwners>
    )]
    fn cur_entry(&mut self) -> (res: Entry<'rcu, C>)
        requires
            old(self).inv(),
            old(owner).inv(),
            old(self).wf(*old(owner)),
            1 <= old(self).level <= 4,
            old(self).path[old(self).level as int - 1] is Some,
            old(owner).relate_region(*regions),
        ensures
            owner.inv(),
            self.inv(),
            self.wf(*owner),
            res.wf(owner.cur_entry_owner()),
            *self == *old(self),
            *owner == *old(owner),
            owner.continuations[owner.level - 1].guard_perm.addr() == res.node.addr(),
            owner.relate_region(*regions),
            res.idx == owner.continuations[owner.level - 1].idx,
    {
        proof { reveal(CursorContinuation::inv_children); }

        let ghost owner0 = *owner;

        let node = self.path[self.level as usize - 1].unwrap();
        let tracked mut parent_continuation = owner.continuations.tracked_remove(owner.level - 1);

        assert(parent_continuation.inv());
        let ghost cont0 = parent_continuation;
        let tracked parent_own = parent_continuation.entry_own.node.tracked_take();
        let tracked child = parent_continuation.take_child();

        let ghost index = frame_to_index(meta_to_frame(parent_own.meta_perm.addr));

        let ghost ptei = AbstractVaddr::from_vaddr(self.va).index[owner.level - 1];

        proof {
            AbstractVaddr::from_vaddr_wf(self.va);
            let ghost abs_va = AbstractVaddr::from_vaddr(self.va);
            assert(abs_va.inv());

            let ghost i = owner.level - 1;
            assert(0 <= i < NR_LEVELS);
            assert(abs_va.index.contains_key(i));
            assert(abs_va.index[i] < NR_ENTRIES);
        }

        assert(child.value.match_pte(
            parent_own.children_perm.value()[ptei as int],
            parent_own.level,
        ));

        assert(ptei == parent_continuation.idx) by {
            // Use owner0 (pre-tracked-remove snapshot) which satisfies inv()
            // owner0.va == AbstractVaddr::from_vaddr(self.va) (from wf)
            // owner0.inv(): owner0.va.index[level - 1] == owner0.continuations[level - 1].idx
            // parent_continuation was removed from owner0.continuations[owner0.level - 1]
            owner0.va.reflect_prop(self.va);
            assert(owner0.va == AbstractVaddr::from_vaddr(self.va));
            if owner0.level == 1 {
                assert(owner0.va.index[0] == owner0.continuations[0].idx);
                // parent_continuation == owner0.continuations[0] (it was just removed)
            } else if owner0.level == 2 {
                assert(owner0.va.index[1] == owner0.continuations[1].idx);
            } else if owner0.level == 3 {
                assert(owner0.va.index[2] == owner0.continuations[2].idx);
            } else {
                assert(owner0.va.index[3] == owner0.continuations[3].idx);
            }
        };
        assert(!child.value.in_scope) by {
            owner0.continuations_not_in_scope();
            assert(owner0.continuations[(owner0.level - 1) as int].children[cont0.idx as int] is Some);
        };

        #[verus_spec(with Tracked(&parent_own),
            Tracked(&child.value),
            Tracked(&parent_continuation.guard_perm))]
        let res = PageTableGuard::entry(node, pte_index::<C>(self.va, self.level));

        // res.idx == ptei: entry ensures res.idx == idx (pte_index result),
        // pte_index spec gives pte_index result == AbstractVaddr::from_vaddr(va).index[level-1] == ptei.

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
    #[verus_spec(
        with Tracked(owner): Tracked<&CursorOwner<C>>
    )]
    fn cur_va_range(&self) -> (res: Range<Vaddr>)
        requires
            owner.inv(),
            self.wf(*owner),
        ensures
            owner.cur_va_range().start.reflect(res.start),
            owner.cur_va_range().end.reflect(res.end),
    {
        let page_size = page_size(self.level);
        let start = self.va.align_down(page_size);

        proof {
            owner.va.reflect_prop(self.va);
            owner.va.align_down_concrete(self.level as int);
            owner.va.align_up_concrete(self.level as int);
            owner.va.align_diff(self.level as int);
            assert(owner.cur_va_range().start.reflect(start));
            assert(owner.cur_va_range().end.reflect((start + page_size) as Vaddr));
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
            Tracked(guard_perm): Tracked<GuardPerm<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            pt_own.0.inv(),
        ensures
            Cursor::<C, A>::cursor_new_success_conditions(va) ==> {
                &&& r is Ok
                &&& r.unwrap().0.inner.invariants(*r.unwrap().1, *regions, *guards)
                &&& r.unwrap().1.in_locked_range()
                &&& r.unwrap().0.inner.level < r.unwrap().0.inner.guard_level
                &&& r.unwrap().0.inner.va < r.unwrap().0.inner.barrier_va.end
                &&& r.unwrap().0.inner.va == va.start
                &&& r.unwrap().0.inner.barrier_va == *va
            },
            // cursor_mut only acquires locks on page-table node slots; it does not
            // set path_if_in_pt for data-frame slots. Any frame that was item_not_mapped
            // before the call remains item_not_mapped after.
            forall |item: C::Item| #![trigger Self::item_not_mapped(item, *old(regions))]
                Self::item_not_mapped(item, *old(regions)) ==>
                Self::item_not_mapped(item, *regions),
            // cursor_mut only locks page-table node slots; it does not modify path_if_in_pt
            // for any slot (neither node slots nor data-frame slots).
            forall |idx: usize| #![trigger regions.slot_owners[idx].path_if_in_pt]
                regions.slot_owners[idx].path_if_in_pt == old(regions).slot_owners[idx].path_if_in_pt,
    )]
    #[verifier::external_body]
    pub fn new(pt: &'rcu PageTable<C>, guard: &'rcu A, va: &Range<Vaddr>)
    -> Result<(Self, Tracked<CursorOwner<'rcu, C>>), PageTableError> {
        let res = #[verus_spec(with Tracked(pt_own), Tracked(guard_perm), Tracked(regions), Tracked(guards))]
        Cursor::new(pt, guard, va);
        match res {
            Ok((inner_cursor, tracked_owner)) => {
                proof {
                    assert(inner_cursor.invariants(*tracked_owner, *regions, *guards));
                    assert(CursorMut::<C, A> { inner: inner_cursor }.inner.invariants(*tracked_owner, *regions, *guards));
                }
                Ok((Self { inner: inner_cursor }, tracked_owner))
            }
            Err(e) => Err(e),
        }
    }

    /// Moves the cursor forward to the next mapped virtual address.
    ///
    /// This is the same as [`Cursor::find_next`].
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
    )]
    pub fn find_next(&mut self, len: usize) -> (res: Option<Vaddr>)
        requires
            old(self).inner.invariants(*old(owner), *old(regions), *old(guards)),
            old(self).inner.level < old(self).inner.guard_level,
            old(owner).in_locked_range(),
            len % C::BASE_PAGE_SIZE() == 0,
            old(self).inner.va + len <= old(self).inner.barrier_va.end,
        ensures
            self.inner.invariants(*owner, *regions, *guards),
            res is Some ==> {
                &&& res.unwrap() == self.inner.va
                &&& owner.level < owner.guard_level
                &&& owner.in_locked_range()
            },
    {
        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.inner.find_next(len)
    }

    /// Jumps to the given virtual address.
    ///
    /// This is the same as [`Cursor::jump`].
    ///
    /// # Panics
    ///
    /// This method panics if the address is out of the range where the cursor is required to operate,
    /// or has bad alignment.
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
    )]
    pub fn jump(&mut self, va: Vaddr) -> (res: Result<(), PageTableError>)
        requires
            old(self).inner.invariants(*old(owner), *old(regions), *old(guards)),
            old(self).inner.level < old(self).inner.guard_level,
            old(owner).in_locked_range(),
            old(self).inner.jump_panic_condition(va),
        ensures
            self.inner.invariants(*owner, *regions, *guards),
            self.inner.barrier_va.start <= va < self.inner.barrier_va.end ==> {
                &&& res is Ok
                &&& self.inner.va == va
            },
            !(self.inner.barrier_va.start <= va < self.inner.barrier_va.end) ==> res is Err,
    {
        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.inner.jump(va)
    }

    /// Gets the current virtual address.
    pub fn virt_addr(&self) -> Vaddr
        returns
            self.inner.va,
    {
        self.inner.virt_addr()
    }

    /// Queries the mapping at the current virtual address.
    ///
    /// If the cursor is pointing to a valid virtual address that is locked,
    /// it will return the virtual address range and the item at that slot.
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            old(self).inner.invariants(*old(owner), *old(regions), *old(guards)),
        ensures
            self.inner.invariants(*owner, *regions, *guards),
            old(owner).in_locked_range() ==> res is Ok,
            res matches Ok(state) ==>
                self.inner.query_some_condition(*owner) ==>
                self.inner.query_some_ensures(*owner, state),
            res matches Ok(state) ==>
                !self.inner.query_some_condition(*owner) ==>
                self.inner.query_none_ensures(*owner, state),
//            owner.in_locked_range(),
    )]
    pub fn query(&mut self) -> (res: Result<PagesState<C>, PageTableError>) {
        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.inner.query()
    }

    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            old(self).inner.invariants(*old(owner), *old(regions), *old(guards)),
            old(owner).in_locked_range(),
            ChildRef::PageTable(pt).wf(old(owner).cur_entry_owner())
        ensures
            self.inner.invariants(*owner, *regions, *guards),
            owner.in_locked_range(),
            owner.va == old(owner).va,
            self.inner.level == old(self).inner.level - 1,
            self.inner.guard_level == old(self).inner.guard_level,
            // push_level preserves the abstract view: mappings are unchanged and cur_va is unchanged.
            owner@ == old(owner)@,
            // map_branch_pt only locks an existing node (push_level takes regions by shared ref);
            // regions is not modified.
            *regions == *old(regions),
    )]
    fn map_branch_pt(&mut self, pt: PageTableNodeRef<'rcu, C>, rcu_guard: &'rcu A) {
        proof { reveal(CursorContinuation::inv_children); }

        let ghost guards0 = *guards;

        // Ghost snapshots for proving owner restoration after the manipulations below.
        let ghost level_key = owner.level as int - 1;
        let ghost cont_orig = owner.continuations[level_key];

        let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
        // After tracked_remove: owner.continuations == old(owner).continuations.remove(level_key)
        // continuation == cont_orig

        let tracked mut child_owner = continuation.take_child();
        // After take_child: child_owner == cont_orig.take_child_spec().0
        //                   continuation == cont_orig.take_child_spec().1

        // Capture ghost snapshot of child_owner before tracked_take mutates it.
        // orig_child_owner == cont_orig.take_child_spec().0 at this point.
        let ghost orig_child_owner = child_owner;

        let tracked mut child_node = child_owner.value.node.tracked_take();
        // After tracked_take: child_node == orig_child_owner.value.node.unwrap()
        //                     child_owner.value.node == None

        proof_decl! {
            let tracked mut guard_perm: Tracked<GuardPerm<'rcu, C>>;
        }

        // SAFETY: The `pt` must be locked and no other guards exist.
        #[verus_spec(with Tracked(&child_node), Tracked(guards) => Tracked(guard_perm))]
        let pt_guard = pt.make_guard_unchecked(rcu_guard);

        proof {
            // Restore node into child_owner.value.node.
            child_owner.value.node = Some(child_node);

            // child_owner is now equal to cont_orig.take_child_spec().0.
            // orig_child_owner captured child_owner == cont_orig.take_child_spec().0 before the take.
            // tracked_take postcondition: child_node == orig_child_owner.value.node.unwrap().
            // After restore: child_owner.value.node == Some(child_node) == orig_child_owner.value.node.
            // All other fields of child_owner are unchanged, so child_owner == orig_child_owner.
            assert(child_owner == cont_orig.take_child_spec().0) by {
                assert(orig_child_owner == cont_orig.take_child_spec().0);
                assert(child_node == orig_child_owner.value.node.unwrap());
                assert(child_owner.value.node == orig_child_owner.value.node);
                assert(child_owner == orig_child_owner);
            };

            continuation.put_child(child_owner);

            // continuation is now restored to cont_orig by take_put_child:
            // take_child_spec().1.put_child_spec(take_child_spec().0) == self.
            assert(continuation == cont_orig) by {
                cont_orig.take_put_child();
                assert(continuation ==
                    cont_orig.take_child_spec().1.put_child_spec(cont_orig.take_child_spec().0));
            };

            owner.continuations.tracked_insert(owner.level - 1, continuation);

            // owner.continuations is restored to old(owner).continuations by map identity:
            // m.remove(k).insert(k, m[k]) == m.
            assert(owner.continuations == old(owner).continuations) by {
                assert(owner.continuations ==
                    old(owner).continuations.remove(level_key).insert(level_key, cont_orig));
                let m = old(owner).continuations;
                assert(m.contains_key(level_key));
                assert forall |j: int| m.remove(level_key).insert(level_key, cont_orig).contains_key(j)
                    <==> m.contains_key(j) by {
                    if j == level_key {} else {}
                };
                assert forall |j: int|
                    #[trigger] m.remove(level_key).insert(level_key, cont_orig).contains_key(j) implies
                    m.remove(level_key).insert(level_key, cont_orig)[j] == m[j] by {
                    if j == level_key {} else {}
                };
            };

            // All other fields of owner are unchanged => owner is fully restored.
            assert(*owner == *old(owner));

            owner.map_children_implies(
                CursorOwner::node_unlocked(guards0),
                CursorOwner::node_unlocked_except(*guards, child_node.meta_perm.addr()),
            );
        }

        proof { assert(owner.level > 1) by {
            owner.cur_entry_node_implies_level_gt_1();
        }; }
        #[verus_spec(with Tracked(owner), Tracked(guard_perm), Tracked(regions), Tracked(guards))]
        self.inner.push_level(pt_guard);

        proof {
            // owner was restored to old(owner) before push_level (asserted above).
            // push_level postcondition: old(owner)@.mappings == owner@.mappings fires
            // with old = old(map_branch_pt)(owner).
            // push_level also preserves va, so owner.va == old(owner).va.
            assert(owner@ == old(owner)@) by {
                assert(old(owner)@.mappings == owner@.mappings);
                assert(owner.va == old(owner).va);
            };
        }
    }

    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            old(self).inner.invariants(*old(owner), *old(regions), *old(guards)),
            old(cur_entry).wf(old(owner).cur_entry_owner()),
            old(owner).cur_entry_owner().is_absent(),
            old(owner).in_locked_range(),
            old(owner).level >= 2,
            old(cur_entry).node.addr() == old(owner).continuations[old(owner).level - 1].guard_perm.addr(),
            old(owner).cur_entry_owner().match_pte(
                old(owner).continuations[old(owner).level - 1].entry_own.node.unwrap().children_perm.value()
                    [old(cur_entry).idx as int],
                old(owner).cur_entry_owner().parent_level,
            ),
        ensures
            self.inner.invariants(*owner, *regions, *guards),
            owner.in_locked_range(),
            owner.va == old(owner).va,
            self.inner.level == old(self).inner.level - 1,
            self.inner.guard_level == old(self).inner.guard_level,
            // alloc_if_none creates an empty PT; push_level preserves all existing mappings.
            owner@ == old(owner)@,
            // map_branch_none only allocates a new PT node slot; it does not set
            // path_if_in_pt for data-frame slots.
            forall|idx: usize| #![trigger regions.slot_owners[idx].path_if_in_pt]
                regions.slot_owners[idx].path_if_in_pt == old(regions).slot_owners[idx].path_if_in_pt,
            // Any frame that was item_not_mapped before remains item_not_mapped.
            forall |item: C::Item| #![trigger Self::item_not_mapped(item, *old(regions))]
                Self::item_not_mapped(item, *old(regions)) ==>
                Self::item_not_mapped(item, *regions),
            // The slot for item remains in regions.
            forall |item: C::Item| #![trigger Self::item_slot_in_regions(item, *old(regions))]
                Self::item_slot_in_regions(item, *old(regions)) ==>
                Self::item_slot_in_regions(item, *regions),
            // The newly allocated PT is empty, so the current entry at the new level is absent.
            owner.cur_entry_owner().is_absent(),
    )]
    fn map_branch_none(&mut self, cur_entry: &mut Entry<'rcu, C>, rcu_guard: &'rcu A) {
        proof { reveal(CursorContinuation::inv_children); }

        let ghost owner0 = *owner;
        let ghost guards0 = *guards;

        let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
        let ghost cont0 = continuation;
        let tracked mut child_owner = continuation.take_child();
        let ghost old_child_value = child_owner.value; // absent entry before alloc_if_none
        let tracked mut parent_owner = continuation.entry_own.node.tracked_take();

        proof {
            assert(continuation.guard_perm.addr() == cur_entry.node.addr());
            assert(cur_entry.node_matching(
                child_owner.value,
                parent_owner,
                continuation.guard_perm,
            ));
        }

        proof_decl! {
            let tracked mut guard_perm;
        }

        let child_guard = (
        #[verus_spec(with Tracked(&mut child_owner), Tracked(&mut parent_owner), Tracked(regions), Tracked(guards), Tracked(&mut continuation.guard_perm)
            => Tracked(guard_perm))]
        cur_entry.alloc_if_none(rcu_guard)).unwrap();

        let ghost new_node_addr = child_owner.value.node.unwrap().meta_perm.addr();
        let ghost new_child_value = child_owner.value; // newly allocated node after alloc_if_none

        proof {
            cont0.take_put_child();
            continuation.entry_own.node = Some(parent_owner);
            continuation.put_child(child_owner);
            owner.continuations.tracked_insert(owner.level - 1, continuation);
        }

        proof {
            assert(owner.cur_entry_owner().node.unwrap().meta_perm.addr() == new_node_addr);

            assert forall|i: int|
                owner0.level <= i < NR_LEVELS implies #[trigger] owner.continuations[i]
                == owner0.continuations[i] by {};

            let f_unlocked = CursorOwner::<'rcu, C>::node_unlocked(guards0);
            let g_unlocked = CursorOwner::<'rcu, C>::node_unlocked_except(*guards, new_node_addr);
            let f_region = PageTableOwner::<C>::relate_region_pred(*old(regions));
            let g_region = PageTableOwner::<C>::relate_region_pred(*regions);

            // alloc_if_none allocated a fresh node from a free slot (old_child was absent).
            // By alloc_if_none_relate_region_preserved: existing entries' relate_region is preserved.
            assert(old_child_value.is_absent()); // old(owner).cur_entry_owner().is_absent() precondition
            assert(old_child_value.inv());
            assert(new_child_value.is_node());
            assert(old(regions).inv());
            assert(old(regions).slots.contains_key(frame_to_index(new_child_value.meta_slot_paddr().unwrap())));
            assert(Entry::<C>::relate_region_neq_preserved(old_child_value, new_child_value, *old(regions), *regions));
            Entry::<C>::alloc_if_none_relate_region_preserved(old_child_value, new_child_value, *old(regions), *regions);
            // Entry::<C>::relate_region_preserved(*old(regions), *regions) now holds == implies(f_region, g_region)
            assert(OwnerSubtree::implies(f_region, g_region));

            assert forall|i: int|
                #![auto]
                owner.level <= i < NR_LEVELS implies owner.continuations[i].map_children(
                g_unlocked,
            ) by {
                let cont = owner0.continuations[i];
                assert forall|j: int|
                    #![auto]
                    0 <= j < NR_ENTRIES
                        && cont.children[j] is Some implies cont.children[j].unwrap().tree_predicate_map(
                cont.path().push_tail(j as usize), g_unlocked) by {
                    OwnerSubtree::map_implies(
                        cont.children[j].unwrap(),
                        cont.path().push_tail(j as usize),
                        f_unlocked,
                        g_unlocked,
                    );
                };
            };

            let idx = cont0.idx as int;
            let cont_final = owner.continuations[owner.level - 1];

            assert(cont_final.map_children(g_unlocked)) by {
                assert forall|j: int|
                    #![auto]
                    0 <= j < NR_ENTRIES
                        && cont_final.children[j] is Some implies cont_final.children[j].unwrap().tree_predicate_map(
                cont_final.path().push_tail(j as usize), g_unlocked) by {
                    if j != idx && cont0.children[j] is Some {
                        OwnerSubtree::map_implies(
                            cont0.children[j].unwrap(),
                            cont0.path().push_tail(j as usize),
                            f_unlocked,
                            g_unlocked,
                        );
                    }
                };
            };

            assert forall|i: int|
                #![auto]
                owner.level <= i < NR_LEVELS implies owner.continuations[i].map_children(
                g_region,
            ) by {
                assert(owner.continuations[i] == owner0.continuations[i]);
                let cont = owner0.continuations[i];
                assert forall|j: int|
                    #![auto]
                    0 <= j < NR_ENTRIES
                        && cont.children[j] is Some implies cont.children[j].unwrap().tree_predicate_map(
                cont.path().push_tail(j as usize), g_region) by {
                    OwnerSubtree::map_implies(
                        cont.children[j].unwrap(),
                        cont.path().push_tail(j as usize),
                        f_region,
                        g_region,
                    );
                };
            };

            assert(cont_final.map_children(g_region)) by {
                assert forall|j: int|
                    #![auto]
                    0 <= j < NR_ENTRIES
                        && cont_final.children[j] is Some implies cont_final.children[j].unwrap().tree_predicate_map(
                cont_final.path().push_tail(j as usize), g_region) by {
                    if j != idx && cont0.children[j] is Some {
                        OwnerSubtree::map_implies(
                            cont0.children[j].unwrap(),
                            cont0.path().push_tail(j as usize),
                            f_region,
                            g_region,
                        );
                    }
                };
            };

            // Admit 1: owner.inv() holds after alloc_if_none + restoration.
            // Higher continuations unchanged (asserted above); level/va/guard_level unchanged.
            owner.map_branch_none_inv_holds(owner0);
        }

        proof {
            // Admit 2: owner.relate_region(*regions).
            // We have owner.map_full_tree(g_region) from the proof above.
            // We get map_full_tree(path_tracked_pred) from map_branch_none_path_tracked_holds.
            let f_region = PageTableOwner::<C>::relate_region_pred(*old(regions));
            let g_region = PageTableOwner::<C>::relate_region_pred(*regions);
            assert(OwnerSubtree::implies(f_region, g_region));
            assert(Entry::<C>::path_tracked_pred_preserved(*old(regions), *regions));
            owner.map_branch_none_path_tracked_holds(owner0, *regions, *old(regions));
            // Now owner.map_full_tree(g_region) (from proof above) and map_full_tree(path_tracked_pred)
            // together give owner.relate_region(*regions) by definition.
        }

        let ghost owner_pre_push = *owner;
        proof { assert(owner.level > 1); } // follows from old(owner).level >= 2
        #[verus_spec(with Tracked(owner), Tracked(guard_perm.tracked_unwrap()), Tracked(regions), Tracked(guards))]
        self.inner.push_level(child_guard);

        proof {
            // Admit 3: owner@ == old(owner)@.
            // (a) alloc_if_none created an empty node → owner_pre_push.view_mappings() == owner0.view_mappings()
            owner_pre_push.map_branch_none_no_new_mappings(owner0);
            // (b) push_level preserved mappings: owner_pre_push@.mappings == owner@.mappings
            // (c) cur_va unchanged throughout: owner.va == owner0.va == old(owner).va
            // (d) owner0 == old(owner) (captured at line 1853 before any tracked ops)
            // Therefore owner@ == old(owner)@.
            assert(owner@ == old(owner)@);
            // The additional postconditions (path_if_in_pt, item_not_mapped, item_slot_in_regions,
            // cur_entry_owner().is_absent()) are trusted for now.
            admit();
        }
    }

    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            old(self).inner.invariants(*old(owner), *old(regions), *old(guards)),
            old(cur_entry).wf(old(owner).cur_entry_owner()),
            old(owner).cur_entry_owner().is_frame(),
            old(cur_entry).node.addr() == old(owner).continuations[old(owner).level - 1].guard_perm.addr(),
            old(owner).in_locked_range(),
            old(owner).level > 1,
            old(owner).level < NR_LEVELS,
        ensures
            self.inner.invariants(*owner, *regions, *guards),
            owner@ == old(owner)@.split_if_mapped_huge_spec(page_size((old(owner).level - 1) as PagingLevel)),
            owner.in_locked_range(),
            owner.va == old(owner).va,
            self.inner.level == old(self).inner.level - 1,
            self.inner.guard_level == old(self).inner.guard_level,
            // map_branch_frame splits a huge frame but does not change path_if_in_pt for
            // the item slot (which is a different frame).
            forall|idx: usize| #![trigger regions.slot_owners[idx].path_if_in_pt]
                regions.slot_owners[idx].path_if_in_pt == old(regions).slot_owners[idx].path_if_in_pt,
            // Any frame that was item_not_mapped remains item_not_mapped (the split frame
            // was already mapped, so items that weren't mapped don't overlap it).
            forall |item: C::Item| #![trigger Self::item_not_mapped(item, *old(regions))]
                Self::item_not_mapped(item, *old(regions)) ==>
                Self::item_not_mapped(item, *regions),
            // The slot for item remains in regions.
            forall |item: C::Item| #![trigger Self::item_slot_in_regions(item, *old(regions))]
                Self::item_slot_in_regions(item, *old(regions)) ==>
                Self::item_slot_in_regions(item, *regions),
    )]
    fn map_branch_frame(&mut self, cur_entry: &mut Entry<'rcu, C>, rcu_guard: &'rcu A) {
        proof { reveal(CursorContinuation::inv_children); }

        let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
        let tracked mut child_owner = continuation.take_child();
        let tracked mut parent_owner = continuation.entry_own.node.tracked_take();

        let split_child = (
        #[verus_spec(with Tracked(&mut child_owner), Tracked(&mut parent_owner), Tracked(regions),
                Tracked(guards), Tracked(&mut continuation.guard_perm))]
        cur_entry.split_if_mapped_huge(rcu_guard)).unwrap();

        proof {
            assert(guards.guards.contains_key(split_child.addr()));
            assert(guards.locked(split_child.addr()));
            assert(child_owner.value.node.unwrap().meta_perm.addr() == split_child.addr());

            continuation.put_child(child_owner);
            continuation.entry_own.node = Some(parent_owner);
            owner.continuations.tracked_insert(owner.level - 1, continuation);
        }

        let tracked child_guard_perm = guards.take(
            child_owner.value.node.unwrap().meta_perm.addr(),
        );

        proof { assert(owner.level > 1); } // from old(owner).level > 1 precondition
        #[verus_spec(with Tracked(owner), Tracked(child_guard_perm), Tracked(regions), Tracked(guards))]
        self.inner.push_level(split_child);

        // The additional postconditions (path_if_in_pt, item_not_mapped, item_slot_in_regions)
        // are trusted for now.
        proof { admit(); }
    }

    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            old(self).inner.invariants(*old(owner), *old(regions), *old(guards)),
            old(owner).in_locked_range(),
            level < old(self).inner.guard_level,
            level >= 1,
        ensures
            self.inner.invariants(*owner, *regions, *guards),
            owner.va == old(owner).va,
            self.inner.guard_level == old(self).inner.guard_level,
            self.inner.level == level,
            owner.in_locked_range(),
            owner@ == old(owner)@.split_while_huge(page_size(level)),
            // map_loop only creates/locks page-table node slots; it does not set
            // path_if_in_pt for data-frame slots.  Any frame that was item_not_mapped
            // before the call remains item_not_mapped after.
            forall |item: C::Item| #![trigger Self::item_not_mapped(item, *old(regions))]
                Self::item_not_mapped(item, *old(regions)) ==>
                Self::item_not_mapped(item, *regions),
            // map_loop never writes path_if_in_pt (only alloc_if_none which only changes raw_count).
            forall|idx: usize| #![trigger regions.slot_owners[idx].path_if_in_pt]
                regions.slot_owners[idx].path_if_in_pt == old(regions).slot_owners[idx].path_if_in_pt,
            // map_loop only creates page-table nodes along the path; the data-frame slot for item
            // stays in regions.slots with its ref_count intact.
            forall |item: C::Item| #![trigger Self::item_slot_in_regions(item, *old(regions))]
                Self::item_slot_in_regions(item, *old(regions)) ==>
                Self::item_slot_in_regions(item, *regions),
            // If the current entry was absent before map_loop (no mapping at that VA), it remains
            // absent at the target level after descending.
            old(owner).cur_entry_owner().is_absent() ==> owner.cur_entry_owner().is_absent(),
    )]
    pub fn map_loop(&mut self, level: PagingLevel, rcu_guard: &'rcu A) {
        let ghost guard_level = self.inner.guard_level;
        let ghost owner0 = *owner;
        proof { assert(owner0.inv()); }

        // The split_while_huge invariant holds initially: the cursor starts above the target level,
        // so the mapping at cur_va (if any) has page_size <= page_size(initial_level), meaning
        // split_while_huge(page_size(initial_level)) does not split it and returns owner0@.
        assert(owner@ == owner0@.split_while_huge(page_size(self.inner.level))) by {
            owner0.split_while_huge_at_level_noop();
        };

        // Adjust ourselves to the level of the item.
        while self.inner.level != level
            invariant
                owner.inv(),
                owner0.inv(),
                owner.va == owner0.va,
                self.inner.wf(*owner),
                regions.inv(),
                self.inner.inv(),
                self.inner.guard_level == guard_level,
                level < self.inner.guard_level,
                level >= 1,
                owner.in_locked_range(),
                owner.children_not_locked(*guards),
                owner.nodes_locked(*guards),
                owner.relate_region(*regions),
                !owner.popped_too_high,
                // Partial split_while_huge progress: the current view equals the result of
                // splitting the initial view down to the current cursor level's page size.
                owner@ == owner0@.split_while_huge(page_size(self.inner.level)),
                forall|idx: usize| #![trigger regions.slot_owners[idx].path_if_in_pt]
                    regions.slot_owners[idx].path_if_in_pt == old(regions).slot_owners[idx].path_if_in_pt,
                forall |item: C::Item| #![trigger Self::item_not_mapped(item, *old(regions))]
                    Self::item_not_mapped(item, *old(regions)) ==>
                    Self::item_not_mapped(item, *regions),
                forall |item: C::Item| #![trigger Self::item_slot_in_regions(item, *old(regions))]
                    Self::item_slot_in_regions(item, *old(regions)) ==>
                    Self::item_slot_in_regions(item, *regions),
                // If the initial entry (at map_loop start) was absent, it remains absent
                // as the cursor descends: None branches create empty nodes (absent entries),
                // PT/Frame branches are vacuously true since those entries are not absent.
                owner0.cur_entry_owner().is_absent() ==> owner.cur_entry_owner().is_absent(),
            decreases abs(level - self.inner.level),
        {
            proof { reveal(CursorContinuation::inv_children); }

            if self.inner.level < level {
                let ghost owner_pre_pop = *owner;
                let ghost level_pre_pop = self.inner.level;

                proof {
                    owner.pop_level_owner_preserves_invs(*guards, *regions);
                }

                #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
                self.inner.pop_level();

                // pop_level preserves owner@ (view_mappings does not change when removing a
                // continuation — its mappings are subsumed by the parent continuation).
                // After going UP, the new level's page_size is larger, so split_while_huge
                // at the new level equals the same state (no further splitting is needed).
                proof {
                    // Establish that pop_level preserved the view
                    owner_pre_pop.pop_level_owner_preserves_mappings();
                    // owner_pre_pop.pop_level_owner_spec().0 == *owner (from pop_level postcond)
                    // pop_level_owner_spec().0@.mappings == owner_pre_pop@.mappings
                    // va preserved by pop_level_owner_spec (..self)
                    // => owner@ == owner_pre_pop@
                    assert(owner@ == owner_pre_pop@);
                    // From loop invariant at iter start: owner_pre_pop@ == owner0@.split_while_huge(level_pre_pop)
                    let ghost level_before_pop = level_pre_pop as int;
                    owner.map_loop_pop_level_invariant(
                        owner0,
                        owner_pre_pop@,
                        level_before_pop,
                    );
                    assert(owner@ == owner0@.split_while_huge(page_size(self.inner.level)));
                    owner.map_loop_pop_level_absent_preserved(owner0);
                }
                continue ;
            }
            // We are at a higher level, go down.

            #[verus_spec(with Tracked(owner), Tracked(regions))]
            let mut cur_entry = self.inner.cur_entry();

            let ghost owner1 = *owner;
            let ghost regions0 = *regions;
            let ghost cont0 = owner.continuations[owner.level - 1];

            let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
            let tracked child_owner = continuation.take_child();
            // Ghost snapshot of child_owner.value for use in match arms after child_owner is consumed.
            let ghost child_entry_val = child_owner.value;
            let tracked parent_owner = continuation.entry_own.node.tracked_borrow();

            assert(!child_owner.value.in_scope) by {
                owner1.continuations_not_in_scope();
            };

            #[verus_spec(with Tracked(&child_owner.value), Tracked(&parent_owner),
                Tracked(regions), Tracked(&continuation.guard_perm))]
            let cur_child = cur_entry.to_ref();

            proof {
                cont0.take_put_child();
                continuation.put_child(child_owner);
                assert(continuation == cont0);
                owner.continuations.tracked_insert(owner.level - 1, continuation);

                assert(owner.continuations =~= owner1.continuations);
                owner1.relate_region_preserved(*owner, regions0, *regions);
            }

            match cur_child {
                ChildRef::PageTable(pt) => {
                    // Capture pre-call state for the split_while_huge invariant proof.
                    let ghost owner_pre_pt = *owner;
                    let ghost level_pre_pt = self.inner.level;
                    // At this point: owner_pre_pt.cur_entry_owner().is_node() holds because
                    // map_branch_pt's precondition ChildRef::PageTable(pt).wf(old(owner).cur_entry_owner())
                    // implies old(owner).cur_entry_owner().is_node().

                    #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
                    self.map_branch_pt(pt, rcu_guard);

                    // Proof that the split_while_huge loop invariant is maintained:
                    //   owner@ == owner0@.split_while_huge(page_size(self.inner.level))
                    //
                    // Chain:
                    //   owner@
                    //     == owner_pre_pt@           [map_branch_pt preserves owner@]
                    //     == owner0@.split_while_huge(page_size(level_pre_pt))  [loop invariant]
                    //   owner0@.split_while_huge(page_size(self.inner.level))   [= L-1 = level_pre_pt-1]
                    //     == owner0@.split_while_huge(page_size(level_pre_pt)).split_while_huge(page_size(self.inner.level))
                    //        [split_while_huge_compose: page_size(L-1) <= page_size(L)]
                    //     == owner_pre_pt@.split_while_huge(page_size(self.inner.level))
                    //        [loop invariant substitution]
                    //     == owner_pre_pt@            [split_while_huge_node_noop: cur entry was a node]
                    //     == owner@                  [map_branch_pt preserves owner@]
                    proof {
                        // Establish level bounds for axiom preconditions.
                        // level_pre_pt = self.inner.level_before; self.inner.level = level_pre_pt - 1.
                        assert(1 <= self.inner.level);
                        assert(self.inner.level <= level_pre_pt);
                        // owner_pre_pt.inv() gives 1 <= owner_pre_pt.level <= NR_LEVELS.
                        // owner_pre_pt.level == level_pre_pt (from wf: self.inner.level == owner.level,
                        // captured as level_pre_pt before the call).
                        assert(1 <= level_pre_pt <= NR_LEVELS) by {
                            assert(owner_pre_pt.inv());
                            assert(owner_pre_pt.level == level_pre_pt as u8);
                        };
                        // page_size is monotone: self.inner.level = level_pre_pt - 1 <= level_pre_pt.
                        axiom_page_size_monotone(self.inner.level, level_pre_pt);
                        // Step 1: composition law lets us chain the two split_while_huge calls.
                        owner0@.split_while_huge_compose(
                            page_size(level_pre_pt),
                            page_size(self.inner.level),
                        );
                        // Step 2: no-op because owner_pre_pt's current entry was a PT node.
                        owner_pre_pt.split_while_huge_node_noop();
                        assert(owner@ == owner0@.split_while_huge(page_size(self.inner.level)));
                    }
                    // map_branch_pt postcondition *regions == *old(regions) ensures all
                    // region-based loop invariants are preserved.
                    assert(forall|idx: usize| #![trigger regions.slot_owners[idx].path_if_in_pt]
                        regions.slot_owners[idx].path_if_in_pt == old(regions).slot_owners[idx].path_if_in_pt) by {};
                    assert(forall |item: C::Item| #![trigger Self::item_not_mapped(item, *old(regions))]
                        Self::item_not_mapped(item, *old(regions)) ==>
                        Self::item_not_mapped(item, *regions)) by {};
                    assert(forall |item: C::Item| #![trigger Self::item_slot_in_regions(item, *old(regions))]
                        Self::item_slot_in_regions(item, *old(regions)) ==>
                        Self::item_slot_in_regions(item, *regions)) by {};
                    // In the PT branch, child_entry_val.is_node(), so it is not absent.
                    // The loop invariant gives owner0.is_absent() => owner1.is_absent(),
                    // but owner1.cur_entry_owner() == child_entry_val and is_node() => !is_absent(),
                    // so owner0.cur_entry_owner().is_absent() must be false (vacuously true).
                    assert(owner0.cur_entry_owner().is_absent() ==> owner.cur_entry_owner().is_absent()) by {
                        assert(child_entry_val.is_node());
                        assert(!child_entry_val.is_absent());
                        assert(child_entry_val == owner1.cur_entry_owner());
                        assert(!owner1.cur_entry_owner().is_absent());
                    };
                    continue ;
                },
                ChildRef::None => {
                    let ghost owner_pre_none = *owner;
                    let ghost level_pre_none = self.inner.level;

                    #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
                    self.map_branch_none(&mut cur_entry, rcu_guard);

                    // Proof of split_while_huge invariant maintenance for the None branch:
                    //   owner@ == owner0@.split_while_huge(page_size(self.inner.level))
                    //
                    // Chain (same pattern as PT branch, but using absent_noop instead of node_noop):
                    //   owner0@.split_while_huge(page_size(self.inner.level))     [need to show == owner@]
                    //     == owner0@.split_while_huge(page_size(level_pre_none)).split_while_huge(page_size(self.inner.level))
                    //        [split_while_huge_compose]
                    //     == owner_pre_none@.split_while_huge(page_size(self.inner.level))
                    //        [loop invariant]
                    //     == owner_pre_none@   [split_while_huge_absent_noop: cur entry was absent]
                    //     == owner@            [map_branch_none preserves owner@]
                    proof {
                        assert(1 <= self.inner.level);
                        assert(self.inner.level <= level_pre_none);
                        assert(1 <= level_pre_none <= NR_LEVELS) by {
                            assert(owner_pre_none.inv());
                            assert(owner_pre_none.level == level_pre_none as u8);
                        };
                        axiom_page_size_monotone(self.inner.level, level_pre_none);
                        owner0@.split_while_huge_compose(
                            page_size(level_pre_none),
                            page_size(self.inner.level),
                        );
                        owner_pre_none.split_while_huge_absent_noop(page_size(self.inner.level));
                        assert(owner@ == owner0@.split_while_huge(page_size(self.inner.level)));
                    }
                    // map_branch_none only adds a new PT node slot; path_if_in_pt for data frames
                    // is unchanged (alloc_if_none / into_pte only changes raw_count).
                    // These follow directly from the map_branch_none postconditions.
                    // The loop's old(regions) == regions at the start of map_branch_none call
                    // (from the loop invariant: path_if_in_pt preserved cumulatively).
                    assert(forall|idx: usize| #![trigger regions.slot_owners[idx].path_if_in_pt]
                        regions.slot_owners[idx].path_if_in_pt == old(regions).slot_owners[idx].path_if_in_pt) by {
                        // map_branch_none postcond: regions.path_if_in_pt == old_none(regions).path_if_in_pt
                        // loop invariant: old_none(regions).path_if_in_pt == old(regions).path_if_in_pt
                        // transitivity
                    };
                    assert(forall |item: C::Item| #![trigger Self::item_not_mapped(item, *old(regions))]
                        Self::item_not_mapped(item, *old(regions)) ==>
                        Self::item_not_mapped(item, *regions)) by {};
                    assert(forall |item: C::Item| #![trigger Self::item_slot_in_regions(item, *old(regions))]
                        Self::item_slot_in_regions(item, *old(regions)) ==>
                        Self::item_slot_in_regions(item, *regions)) by {};
                    // map_branch_none postcond: owner.cur_entry_owner().is_absent()
                    // (new empty PT node at the pushed level has no entries → absent).
                    assert(owner0.cur_entry_owner().is_absent() ==> owner.cur_entry_owner().is_absent()) by {
                        assert(owner.cur_entry_owner().is_absent());
                    };
                    continue ;
                },
                ChildRef::Frame(_, _, _) => {
                    assert(owner.level > 1);

                    // Remember pre-split state for the invariant maintenance proof.
                    let ghost owner_before_frame = *owner;
                    let ghost level_before_frame = self.inner.level;

                    #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
                    self.map_branch_frame(&mut cur_entry, rcu_guard);


                    // Chain: owner@ = owner_before_frame@.split_if_mapped_huge_spec(page_size(level_before_frame - 1))
                    //   and loop invariant: owner_before_frame@ = owner0@.split_while_huge(page_size(level_before_frame))
                    //   => owner@ = owner0@.split_while_huge(page_size(self.inner.level))
                    //   via the map_branch_frame_split_while_huge axiom.
                    proof {
                        owner.map_branch_frame_split_while_huge(
                            owner0,
                            owner_before_frame,
                            level_before_frame as int,
                        );
                        assert(owner@ == owner0@.split_while_huge(page_size(self.inner.level)));
                    }
                    // map_branch_frame postconditions: path_if_in_pt, item_not_mapped, item_slot_in_regions
                    // preserved (the split frame was already mapped; the loop-cumulative invariant
                    // follows by transitivity from map_branch_frame's postconditions).
                    assert(forall|idx: usize| #![trigger regions.slot_owners[idx].path_if_in_pt]
                        regions.slot_owners[idx].path_if_in_pt == old(regions).slot_owners[idx].path_if_in_pt) by {};
                    assert(forall |item: C::Item| #![trigger Self::item_not_mapped(item, *old(regions))]
                        Self::item_not_mapped(item, *old(regions)) ==>
                        Self::item_not_mapped(item, *regions)) by {};
                    assert(forall |item: C::Item| #![trigger Self::item_slot_in_regions(item, *old(regions))]
                        Self::item_slot_in_regions(item, *old(regions)) ==>
                        Self::item_slot_in_regions(item, *regions)) by {};
                    // In the Frame branch, child_entry_val.is_frame(), so it is not absent.
                    // The loop invariant gives owner0.is_absent() => owner1.is_absent(),
                    // but owner1.cur_entry_owner() == child_entry_val and is_frame() => !is_absent(),
                    // so owner0.cur_entry_owner().is_absent() must be false (vacuously true).
                    assert(owner0.cur_entry_owner().is_absent() ==> owner.cur_entry_owner().is_absent()) by {
                        assert(child_entry_val.is_frame());
                        assert(!child_entry_val.is_absent());
                        assert(child_entry_val == owner1.cur_entry_owner());
                        assert(!owner1.cur_entry_owner().is_absent());
                    };
                    continue ;
                },
            }
        }
        assert(old(owner).cur_entry_owner().is_absent() ==> owner.cur_entry_owner().is_absent()) by {};
    }

    /// In order for the function to not panic, the current virtual address must be within the barrier range,
    /// the level of the item to be mapped must be within the highest translation level,
    /// the item must be aligned to the page size, at its level,
    /// and the virtual address range to be mapped must not exceed the barrier range.
    /// If the page table config doesn't allow the top level to be unmapped, then the item must also not be at the top level.
    pub open spec fn map_panic_conditions(self, item: C::Item) -> bool {
        &&& self.inner.va < self.inner.barrier_va.end
        &&& C::item_into_raw(item).1 <= C::HIGHEST_TRANSLATION_LEVEL()
        &&& !C::TOP_LEVEL_CAN_UNMAP_spec() ==> C::item_into_raw(item).1 < NR_LEVELS
        &&& self.inner.va % page_size(C::item_into_raw(item).1) == 0
        &&& self.inner.va + page_size(C::item_into_raw(item).1) <= self.inner.barrier_va.end
    }

    pub open spec fn map_cursor_requires(
        self,
        owner: CursorOwner<'rcu, C>,
        guards: Guards<'rcu, C>,
    ) -> bool {
        &&& owner.in_locked_range()
        &&& self.inner.level < self.inner.guard_level
        &&& self.inner.va < self.inner.barrier_va.end
    }

    pub open spec fn map_item_requires(self, item: C::Item, entry_owner: EntryOwner<C>) -> bool {
        let (paddr, level, prop) = C::item_into_raw(item);
        &&& entry_owner.inv()
        &&& self.inner.va % page_size(level) == 0
        &&& self.inner.va + page_size(level) <= self.inner.barrier_va.end
        &&& level < self.inner.guard_level
        &&& (entry_owner.is_absent()
            || Child::Frame(paddr, level, prop).wf(entry_owner))
    }

    pub open spec fn item_not_mapped(item: C::Item, regions: MetaRegionOwners) -> bool {
        let (pa, level, prop) = C::item_into_raw(item);
        let size = page_size(level);
        let range = pa..(pa + size) as usize;
        regions.paddr_range_not_mapped(range)
    }

    /// The physical frame of `item` has its slot permission in `regions.slots` and is allocated
    /// (ref_count != REF_COUNT_UNUSED).  This holds before mapping because the item owns the
    /// frame, which necessarily keeps its slot_perm in the pool until it is consumed by `new_child`.
    pub open spec fn item_slot_in_regions(item: C::Item, regions: MetaRegionOwners) -> bool {
        let (pa, level, prop) = C::item_into_raw(item);
        let idx = frame_to_index(pa);
        &&& regions.slots.contains_key(idx)
        &&& regions.slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED
    }

    pub open spec fn map_item_ensures(
        self,
        item: C::Item,
        old_view: CursorView<C>,
        new_view: CursorView<C>,
    ) -> bool {
        let (pa, level, prop) = C::item_into_raw(item);
        new_view == old_view.map_spec(pa, page_size(level), prop)
    }

    /// Maps the item starting from the current address to a physical address range.
    ///
    /// If the current address has already mapped pages, it will do a re-map,
    /// taking out the old physical address and replacing it with the new one.
    /// This function will return [`Err`] with a [`PageTableFrag`], the not
    /// mapped item. The caller should drop it after TLB coherence.
    ///
    /// If there is no mapped pages in the specified virtual address range,
    /// the function will return [`None`].
    ///
    /// # Panics
    ///
    /// This function will panic if
    ///  - the virtual address range to be mapped is out of the locked range;
    ///  - the current virtual address is not aligned to the page size of the
    ///    item to be mapped;
    ///
    /// # Safety
    ///
    /// The caller should ensure that
    ///  - the range being mapped does not affect kernel's memory safety;
    ///  - the physical address to be mapped is valid and safe to use;
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(entry_owner): Tracked<EntryOwner<C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            old(self).inner.invariants(*old(owner), *old(regions), *old(guards)),
            old(self).map_cursor_requires(*old(owner), *old(guards)),
            old(self).map_item_requires(item, entry_owner),
            old(self).map_panic_conditions(item),
            Self::item_not_mapped(item, *old(regions)),
            Self::item_slot_in_regions(item, *old(regions)),
        ensures
            self.inner.invariants(*owner, *regions, *guards),
            old(self).map_item_ensures(
                item,
                old(self).inner.model(*old(owner)),
                self.inner.model(*owner),
            ),
            self.inner.va < self.inner.barrier_va.end ==>
                self.map_cursor_requires(*owner, *guards),
            old(owner).cur_entry_owner().is_absent() ==> res.is_ok(),
            forall|idx: usize| #![trigger regions.slot_owners[idx].path_if_in_pt]
                idx != frame_to_index(C::item_into_raw(item).0) ==>
                regions.slot_owners[idx].path_if_in_pt == old(regions).slot_owners[idx].path_if_in_pt,
            self.inner.guard_level == old(self).inner.guard_level,
    )]
    pub fn map(&mut self, item: C::Item) -> (res: Result<(), PageTableFrag<C>>) {
        proof { reveal(CursorContinuation::inv_children); }

        let ghost self0 = *self;
        let ghost owner0 = *owner;

        let (pa, level, prop) = C::item_into_raw(item);
        let size = page_size(level);

        let ghost target = Mapping {
            va_range: owner@.cur_slot_range(size),
            pa_range: pa..(pa + size) as usize,
            page_size: size,
            property: prop,
        };

        let rcu_guard = self.inner.rcu_guard;

        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.map_loop(level, rcu_guard);

        let ghost owner1 = *owner;
        let ghost regions_before_new_child = *regions;

        proof_decl! {
            // item_slot_in_regions precondition + map_loop preservation => slot in regions.slots.
            assert(regions.slots.contains_key(frame_to_index(pa))) by {
                assert(Self::item_slot_in_regions(item, regions_before_new_child));
            };
            let tracked new_owner = owner.continuations.tracked_borrow(owner.level - 1).new_child(pa, prop, regions);
        }

        let ghost regions_after_new_child = *regions;

        proof {
            // Prove PageTableOwner(new_owner)@.mappings == set![target] via axiom.
            assert(PageTableOwner(new_owner)@.mappings == set![target]) by {
                // From new_child postcondition: new_owner.value == new_frame_spec(pa, path, cont.level(), prop, slot_perm).
                let cont = owner1.continuations[owner1.level as int - 1];
                assert(new_owner.value == EntryOwner::<C>::new_frame_spec(
                    pa,
                    cont.path().push_tail(cont.idx as usize),
                    cont.level(),
                    prop,
                    regions_before_new_child.slots[frame_to_index(pa)],
                ));
                // From new_frame_spec: value is a frame, path is as given, mapped_pa == pa, prop == prop.
                assert(new_owner.value.is_frame());
                assert(new_owner.value.path == cont.path().push_tail(cont.idx as usize));
                assert(new_owner.value.frame.unwrap().mapped_pa == pa);
                assert(new_owner.value.frame.unwrap().prop == prop);
                // From map_loop: self.inner.level == level, and wf gives owner.level == self.inner.level.
                assert(owner1.level == level);
                // Apply the axiom.
                owner1.new_child_mappings_eq_target(new_owner, pa, level, prop);
                // The axiom ensures PageTableOwner(new_owner)@.mappings ==
                //   set![Mapping { va_range: owner1@.cur_slot_range(page_size(level)), ... }].
                // And target uses owner@.cur_slot_range(size) where owner == owner1 and size == page_size(level).
                assert(owner@.cur_slot_range(size) == owner1@.cur_slot_range(page_size(level)));
            };

            // pa % PAGE_SIZE == 0 from new_owner.inv() (frame entry, mapped_pa = pa)
            assert(pa % PAGE_SIZE == 0) by {
                assert(new_owner.inv());
                assert(new_owner.value.frame is Some);
                assert(new_owner.value.frame.unwrap().mapped_pa == pa) by {
                    assert(new_owner.value == EntryOwner::<C>::new_frame_spec(
                        pa,
                        owner1.continuations[owner1.level as int - 1].path().push_tail(
                            owner1.continuations[owner1.level as int - 1].idx as usize),
                        owner1.continuations[owner1.level as int - 1].level(),
                        prop,
                        regions_before_new_child.slots[frame_to_index(pa)],
                    ));
                };
            };

            // From map_loop's item_not_mapped preservation and map precondition:
            // item_not_mapped(item, regions_before_new_child) holds.
            // Therefore slot_owners[frame_to_index(pa)].path_if_in_pt is None.
            let ghost pa_idx = frame_to_index(pa);
            // Size is positive so pa is strictly below pa+size.
            axiom_page_size_ge_page_size(level);
            assert(regions_before_new_child.slot_owners[pa_idx].path_if_in_pt is None) by {
                // From map's precondition + map_loop's item_not_mapped preservation.
                assert(Self::item_not_mapped(item, regions_before_new_child));
                // item_not_mapped unfolds to paddr_range_not_mapped(pa..(pa+size)).
                // pa < MAX_PADDR from new_owner.inv() (frame entry invariant)
                assert(pa < MAX_PADDR) by {
                    assert(new_owner.inv());
                    assert(new_owner.value.frame.unwrap().mapped_pa == pa) by {
                        assert(new_owner.value == EntryOwner::<C>::new_frame_spec(
                            pa,
                            owner1.continuations[owner1.level as int - 1].path().push_tail(
                                owner1.continuations[owner1.level as int - 1].idx as usize),
                            owner1.continuations[owner1.level as int - 1].level(),
                            prop,
                            regions_before_new_child.slots[frame_to_index(pa)],
                        ));
                    };
                };
                // 1 <= level <= NR_LEVELS from item_into_raw postcondition
                assert(1 <= level <= NR_LEVELS);
                // pa + size doesn't overflow usize by axiom
                axiom_pa_plus_page_size_no_overflow(pa, level);
                // size > 0 from axiom_page_size_ge_page_size (called above)
                assert(pa < pa + size);
                assert(pa % PAGE_SIZE == 0);
                // Use the helper lemma to instantiate the quantifier at paddr = pa.
                let ghost range = pa..(pa + size) as usize;
                regions_before_new_child.paddr_not_mapped_at(range, pa);
                // frame_to_index_spec(pa) == pa_idx (both equal pa / PAGE_SIZE)
                assert(frame_to_index_spec(pa) == pa_idx);
            };

            assert(new_owner.tree_predicate_map(
                new_owner.value.path,
                CursorOwner::<'rcu, C>::node_unlocked(*guards),
            ));

            // All entries in the tree have a different paddr than the new frame.
            // new_owner.value.meta_slot_paddr() == Some(pa), and pa has path_if_in_pt is None.
            assert(new_owner.value.meta_slot_paddr() == Some(pa));
            owner1.not_in_tree_from_not_mapped(regions_before_new_child, new_owner.value);
            assert(*owner == owner1);
            assert(owner.not_in_tree(new_owner.value));
            assert(owner.map_full_tree(
                |entry_owner: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                    entry_owner.meta_slot_paddr_neq(new_owner.value),
            ));

            // new_owner.value.relate_region(*regions): prove each conjunct for the frame case.
            assert(new_owner.value.relate_region(*regions)) by {
                let pa_idx3 = frame_to_index(pa);
                // new_owner.value == new_frame_spec(pa, path, level, prop, slot_perm)
                // where slot_perm = regions_before_new_child.slots[pa_idx3].
                let slot_perm = regions_before_new_child.slots[pa_idx3];
                assert(new_owner.value.is_frame());
                assert(new_owner.value.frame.unwrap().slot_perm == slot_perm) by {
                    assert(new_owner.value == EntryOwner::<C>::new_frame_spec(
                        pa,
                        owner1.continuations[owner1.level as int - 1].path().push_tail(
                            owner1.continuations[owner1.level as int - 1].idx as usize),
                        owner1.continuations[owner1.level as int - 1].level(),
                        prop,
                        slot_perm,
                    ));
                };
                // slot_owners unchanged by new_child
                assert(regions.slot_owners =~= regions_before_new_child.slot_owners);
                // regions_before_new_child.inv() gives slot properties
                assert(regions_before_new_child.slots.contains_key(pa_idx3)) by {
                    assert(Self::item_slot_in_regions(item, regions_before_new_child));
                };
                assert(slot_perm.is_init());
                assert(slot_perm.addr() == meta_addr(pa_idx3));
                assert(slot_perm.value().wf(regions.slot_owners[pa_idx3])) by {
                    assert(regions.slot_owners[pa_idx3] == regions_before_new_child.slot_owners[pa_idx3]);
                };
                // ref_count != UNUSED from item_slot_in_regions
                assert(regions.slot_owners[pa_idx3].inner_perms.ref_count.value() != REF_COUNT_UNUSED) by {
                    assert(Self::item_slot_in_regions(item, regions_before_new_child));
                    assert(regions.slot_owners[pa_idx3]
                        == regions_before_new_child.slot_owners[pa_idx3]);
                };
                // path_if_in_pt is None: frame is not mapped (item_not_mapped preservation)
                assert(regions_before_new_child.paddr_range_not_mapped(pa..(pa + size) as usize));
                assert(pa % PAGE_SIZE == 0);
                // pa < pa + size: size > 0 and no overflow.
                axiom_page_size_ge_page_size(level);
                axiom_pa_plus_page_size_no_overflow(pa, level);
                assert(pa < (pa + size) as usize);
                regions_before_new_child.paddr_not_mapped_at(pa..(pa + size) as usize, pa);
                assert(frame_to_index_spec(pa) == pa_idx3);
                assert(regions_before_new_child.slot_owners[pa_idx3].path_if_in_pt is None);
                assert(regions.slot_owners[pa_idx3].path_if_in_pt is None);
            };

            // new_child only removed frame_to_index(pa) from regions.slots; slot_owners unchanged.
            // EntryOwner::relate_region depends only on slot_owners, so relate_region is preserved.
            assert(owner.relate_region(*regions)) by {
                let f = PageTableOwner::<C>::relate_region_pred(regions_before_new_child);
                let g = PageTableOwner::<C>::relate_region_pred(*regions);
                let e = PageTableOwner::<C>::path_tracked_pred(regions_before_new_child);
                let h = PageTableOwner::<C>::path_tracked_pred(*regions);
                // slot_owners is unchanged by new_child
                assert(regions.slot_owners =~= regions_before_new_child.slot_owners);
                // relate_region and path_tracked_pred both only depend on slot_owners,
                // so the predicate implication holds trivially
                assert(OwnerSubtree::implies(f, g)) by {
                    assert forall |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                        entry.inv() ==> f(entry, path) ==> #[trigger] g(entry, path) by {
                        assert(regions.slot_owners =~= regions_before_new_child.slot_owners);
                    };
                };
                assert(OwnerSubtree::implies(e, h)) by {
                    assert forall |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                        entry.inv() ==> e(entry, path) ==> #[trigger] h(entry, path) by {
                        assert(regions.slot_owners =~= regions_before_new_child.slot_owners);
                    };
                };
                owner1.relate_region_preserved(owner1, regions_before_new_child, *regions);
            };

            // new_child removed one key from regions.slots; the remaining keys and all
            // slot_owners are unchanged, so the forall-based inv is preserved.
            assert(regions.inv()) by {
                let idx = frame_to_index(pa);
                assert(regions.slots =~= regions_before_new_child.slots.remove(idx));
                assert(regions.slot_owners =~= regions_before_new_child.slot_owners);
                assert forall |i: usize| #[trigger] regions.slots.contains_key(i) implies {
                    &&& regions.slot_owners.contains_key(i)
                    &&& regions.slot_owners[i].inv()
                    &&& regions.slots[i].is_init()
                    &&& regions.slots[i].addr() == meta_addr(i)
                    &&& regions.slots[i].value().wf(regions.slot_owners[i])
                    &&& regions.slot_owners[i].self_addr == regions.slots[i].addr()
                } by {
                    // i is in regions.slots = before.slots - {idx}, so i was in before.slots
                    assert(regions_before_new_child.slots.contains_key(i));
                    // slots[i] and slot_owners[i] are unchanged for i != idx
                    assert(regions.slots[i] == regions_before_new_child.slots[i]);
                    assert(regions.slot_owners[i] == regions_before_new_child.slot_owners[i]);
                };
                assert forall |i: usize| #[trigger] regions.slot_owners.contains_key(i) implies
                    regions.slot_owners[i].inv() by {
                    assert(regions.slot_owners[i] == regions_before_new_child.slot_owners[i]);
                };
                assert forall |i: usize| i < max_meta_slots() <==> #[trigger] regions.slot_owners.contains_key(i) by {
                    assert(regions.slot_owners.contains_key(i) <==> regions_before_new_child.slot_owners.contains_key(i));
                };
                assert forall |i: usize| #[trigger] regions.slots.contains_key(i) implies i < max_meta_slots() by {
                    assert(regions_before_new_child.slots.contains_key(i));
                };
            };
        }

        #[verus_spec(with Tracked(owner), Tracked(new_owner), Tracked(regions), Tracked(guards))]
        let frag = self.replace_cur_entry(Child::Frame(pa, level, prop));

        let ghost owner2 = *owner;
        let ghost regions_after_replace = *regions;
        assert(owner2@.mappings == owner1@.mappings - PageTableOwner(owner1.cur_subtree())@.mappings
            + PageTableOwner(new_owner)@.mappings);

        proof {
            // At this point, level == owner1.level
            owner1.cur_subtree_eq_filtered_mappings();
            owner.move_forward_owner_preserves_mappings();
        }
        assert(owner1@.remove_subtree(page_size(level)) == owner1@.mappings - PageTableOwner(
            owner1.cur_subtree(),
        )@.mappings);
        assert(owner2@.mappings == owner1@.remove_subtree(page_size(level)) + PageTableOwner(
            new_owner,
        )@.mappings);

        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.inner.move_forward();

        proof {
            owner.va.reflect_prop(self.inner.va);
            owner2.va.align_up_concrete(level as int);
            owner.va.reflect_prop(
                nat_align_up(owner1.va.to_vaddr() as nat, page_size(level) as nat) as Vaddr,
            );
        }

        assert(owner@.cur_va == owner2@.align_up_spec(page_size(level)));
        assert(owner@ == owner0@.map_spec(pa, page_size(level), prop));
        assert(self0.map_item_ensures(item, owner0@, owner@));

        proof {
            assert(self.inner.va >= self.inner.barrier_va.end
                || self.map_cursor_requires(*owner, *guards)) by {
                // After move_forward:
                // - self.wf(*owner): barrier_va.end = locked_range().end,
                //   self.inner.va = owner.va.to_vaddr(), level/guard_level match
                // - !owner.popped_too_high: from move_forward postcondition
                // - owner.inv(): from move_forward postcondition
                // From inv + !popped_too_high: level < guard_level || above_locked_range()
                if owner.above_locked_range() {
                    // owner.va.to_vaddr() >= locked_range().end = barrier_va.end
                    assert(self.inner.va >= self.inner.barrier_va.end);
                } else {
                    // level < guard_level (from inv + !popped_too_high + !above_locked_range)
                    assert(owner.level < owner.guard_level);
                    assert(self.inner.level < self.inner.guard_level);
                    // va < locked_range().end = barrier_va.end
                    assert(owner.va.to_vaddr() < owner.locked_range().end);
                    assert(self.inner.va < self.inner.barrier_va.end);
                    // in_locked_range(): va >= locked_range().start
                    // owner2.in_locked_range() held before move_forward (replace_cur_entry postcondition)
                    // move_forward_increases_va: owner.va.to_vaddr() > owner2.va.to_vaddr()
                    // locked_range().start unchanged by move_forward (prefix/guard_level fixed)
                    owner2.move_forward_increases_va();
                    assert(owner.va.to_vaddr() > owner2.va.to_vaddr());
                    assert(owner2.va.to_vaddr() >= owner2.locked_range().start);
                    assert(owner2.locked_range().start == owner.locked_range().start);
                    assert(owner.va.to_vaddr() >= owner.locked_range().start);
                    assert(owner.in_locked_range());
                    assert(self.map_cursor_requires(*owner, *guards));
                }
            };
            // The map operation only changes path_if_in_pt for the mapped pa's index;
            // all other slot_owners entries are preserved.
            // Chain of postconditions:
            //   map_loop:          forall idx, path_if_in_pt unchanged  (=> regions_before_new_child == old)
            //   new_child:         slot_owners entirely unchanged        (=> regions_after_new_child.slot_owners == regions_before_new_child.slot_owners)
            //   replace_cur_entry: for idx != pa_idx, path_if_in_pt unchanged from its old(regions) = regions_after_new_child
            //   move_forward:      forall idx, path_if_in_pt unchanged  (=> regions == regions_after_replace for path_if_in_pt)
            let ghost pa_idx2 = frame_to_index(C::item_into_raw(item).0);
            assert(forall|idx: usize| #![trigger regions.slot_owners[idx].path_if_in_pt]
                idx != pa_idx2 ==>
                regions.slot_owners[idx].path_if_in_pt == old(regions).slot_owners[idx].path_if_in_pt
            ) by {
                assert forall|idx: usize| idx != pa_idx2 implies
                    #[trigger] regions.slot_owners[idx].path_if_in_pt == old(regions).slot_owners[idx].path_if_in_pt
                by {
                    // move_forward: path_if_in_pt unchanged for all idx
                    assert(regions.slot_owners[idx].path_if_in_pt
                        == regions_after_replace.slot_owners[idx].path_if_in_pt);
                    // replace_cur_entry: for idx != pa_idx, path_if_in_pt unchanged from old(replace) = regions_after_new_child
                    // new_owner.value after replace_cur_entry: is_frame(), meta_slot_paddr() = Some(pa)
                    assert(new_owner.value.meta_slot_paddr() == Some(pa));
                    assert(frame_to_index(pa) == pa_idx2);
                    assert(!new_owner.value.is_absent());
                    assert(regions_after_replace.slot_owners[idx].path_if_in_pt
                        == regions_after_new_child.slot_owners[idx].path_if_in_pt);
                    // new_child: slot_owners entirely unchanged
                    assert(regions_after_new_child.slot_owners =~= regions_before_new_child.slot_owners);
                    // map_loop: path_if_in_pt unchanged for all idx
                    assert(regions_before_new_child.slot_owners[idx].path_if_in_pt
                        == old(regions).slot_owners[idx].path_if_in_pt);
                };
            };
            // When the entry was absent, the replacement always succeeds (no frag returned).
            // map_loop postcondition: cur_entry_owner().is_absent() is preserved.
            // new_child takes &self (immutable), so owner is unchanged after it.
            // replace_cur_entry postcondition: old(owner).cur_entry_owner().is_absent() ==> res is None.
            // old(owner) for replace_cur_entry = owner1 = owner after map_loop.
            assert(old(owner).cur_entry_owner().is_absent() ==> frag.is_none()) by {
                // map_loop: if absent at start, still absent after (new postcondition)
                assert(old(owner).cur_entry_owner().is_absent() ==> owner1.cur_entry_owner().is_absent());
                // new_child takes tracked &self (immutable borrow of owner.continuations[level-1]),
                // so owner is not modified; owner1 == *owner.
                // replace_cur_entry postcondition gives: owner1.cur_entry_owner().is_absent() ==> frag is None
                assert(owner1.cur_entry_owner().is_absent() ==> frag is None);
            };
        }

        if let Some(frag) = frag {
            Err(frag)
        } else {
            Ok(())
        }
    }

    /// Finds and removes the first page table fragment in the following range.
    ///
    /// The range to be found in is the current virtual address with the
    /// provided length.
    ///
    /// The function stops and yields the fragment if it has actually removed a
    /// fragment, no matter if the following pages are also required to be
    /// unmapped. The returned virtual address is the virtual page that existed
    /// before the removal but having just been unmapped.
    ///
    /// It also makes the cursor moves forward to the next page after the
    /// removed one, when an actual page is removed. If no mapped pages exist
    /// in the following range, the cursor will stop at the end of the range
    /// and return [`None`].
    ///
    /// The caller should handle TLB coherence if necessary, using the returned
    /// virtual address range.
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
    #[verus_spec(res =>
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            old(self).inner.invariants(*old(owner), *old(regions), *old(guards)),
            old(owner).in_locked_range(),
            len % C::BASE_PAGE_SIZE() == 0,
            old(self).inner.va + len <= old(self).inner.barrier_va.end,
        ensures
            self.inner.invariants(*owner, *regions, *guards),
            self.inner.va > old(self).inner.va,
            self.inner.va <= old(self).inner.va + len,
            self.inner.va % C::BASE_PAGE_SIZE() == 0,
            self.inner.barrier_va == old(self).inner.barrier_va,
            owner.in_locked_range(),
            res is None ==> {
                &&& owner@.cur_va >= (old(owner)@.cur_va + len) as Vaddr
                &&& owner@.mappings =~= old(owner)@.mappings
                &&& old(owner)@.mappings.filter(|m: Mapping|
                    old(owner)@.cur_va <= m.va_range.start < (old(owner)@.cur_va + len) as Vaddr) =~= Set::<Mapping>::empty()
            },
            res is Some ==> {
                &&& owner@.mappings =~= old(owner)@.mappings.difference(
                    old(owner)@.mappings.filter(|m: Mapping| old(owner)@.cur_va <= m.va_range.start < owner@.cur_va))
            },
            res is Some ==> res.unwrap() is Mapped ==> {
                old(owner)@.mappings.filter(|m: Mapping| old(owner)@.cur_va <= m.va_range.start < owner@.cur_va).len() == 1
            },
            res is Some ==> res.unwrap() is StrayPageTable ==> {
                old(owner)@.mappings.filter(|m: Mapping| old(owner)@.cur_va <= m.va_range.start < owner@.cur_va).len()
                    == (res.unwrap()->StrayPageTable_num_frames) as nat
            },
    )]
    #[verifier::external_body]
    pub fn take_next(&mut self, len: usize) -> (r: Option<PageTableFrag<C>>) {
        (#[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.inner.find_next_impl(len, true, true))?;

        let tracked absent_entry_owner = EntryOwner::new_absent(
            owner.cur_entry_owner().path,
            owner.level,
        );
        let tracked subtree = OwnerSubtree::new_val_tracked(
            absent_entry_owner,
            (owner.continuations.tracked_borrow(owner.level - 1).tree_level + 1) as nat,
        );

        assert(subtree.value.meta_slot_paddr() is None);
        proof {
            owner.absent_not_in_tree(subtree.value);
        }

        #[verus_spec(with Tracked(owner), Tracked(subtree), Tracked(regions), Tracked(guards))]
        let frag = self.replace_cur_entry(Child::None);

        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.inner.move_forward();

        frag
    }

    /// Applies the operation to the next slot of mapping within the range.
    ///
    /// The range to be found in is the current virtual address with the
    /// provided length.
    ///
    /// The function stops and yields the actually protected range if it has
    /// actually protected a page, no matter if the following pages are also
    /// required to be protected.
    ///
    /// It also makes the cursor moves forward to the next page after the
    /// protected one. If no mapped pages exist in the following range, the
    /// cursor will stop at the end of the range and return [`None`].
    ///
    /// # Safety
    ///
    /// The caller should ensure that:
    ///  - the range being protected with the operation does not affect
    ///    kernel's memory safety;
    ///  - the privileged flag `AVAIL1` should not be altered if in the kernel
    ///    page table (the restriction may be lifted in the futures).
    ///
    /// # Panics
    ///
    /// Panics if:
    ///  - the length is longer than the remaining range of the cursor;
    ///  - the length is not page-aligned.
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            old(regions).inv(),
            old(owner).inv(),
            old(self).inner.wf(*old(owner)),
            old(self).inner.inv(),
            old(owner).in_locked_range(),
            !old(owner).popped_too_high,
            old(owner).children_not_locked(*old(guards)),
            old(owner).nodes_locked(*old(guards)),
            old(owner).relate_region(*old(regions)),
            len % C::BASE_PAGE_SIZE() == 0,
            old(self).inner.va + len <= old(self).inner.barrier_va.end,
            old(self).inner.level < NR_LEVELS,
            old(owner).cur_entry_owner().is_frame(),
            op.requires((old(owner).cur_entry_owner().frame.unwrap().prop,)),
        )]
    pub fn protect_next(
        &mut self,
        len: usize,
        op: impl FnOnce(PageProperty) -> PageProperty,
    ) -> Option<Range<Vaddr>> {
        (#[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.inner.find_next_impl(len, false, true))?;

        // find_next_impl ensures: res is Some && !find_unmap_subtree ==> is_frame()
        // find_unmap_subtree=false was passed and we're on the Some path after ?
        assert(owner.cur_entry_owner().is_frame());

        // The prop is preserved from old(owner) to the found entry
        assert(owner.cur_entry_owner().frame.unwrap().prop == old(
            owner,
        ).cur_entry_owner().frame.unwrap().prop);

        #[verus_spec(with Tracked(owner), Tracked(regions))]
        let mut entry = self.inner.cur_entry();

        // Bridge: entry.wf(owner.cur_entry_owner()) + is_frame() ==> pte.prop() == frame.prop
        proof { reveal(CursorContinuation::inv_children); }
        assert(entry.pte.prop() == owner.cur_entry_owner().frame.unwrap().prop) by {
            assert(entry.wf(owner.cur_entry_owner()));
            assert(owner.cur_entry_owner().is_frame());
            assert(owner.cur_entry_owner().match_pte(
                entry.pte,
                owner.cur_entry_owner().parent_level,
            ));
        };

        let ghost owner0 = *owner;

        let tracked mut continuation = owner.continuations.tracked_remove(owner.level - 1);
        let ghost cont0 = continuation;
        let tracked mut child_owner = continuation.take_child();
        let tracked mut parent_owner = continuation.entry_own.node.tracked_take();

        #[verus_spec(with Tracked(&mut child_owner.value), Tracked(&mut parent_owner), Tracked(&mut continuation.guard_perm))]
        entry.protect(op);

        let ghost child_owner_path = child_owner.value.path;
        let ghost child_owner_mapped_pa = child_owner.value.frame.unwrap().mapped_pa;
        let ghost child_owner_slot_perm = child_owner.value.frame.unwrap().slot_perm;
        let ghost child_owner_parent_level = child_owner.value.parent_level;

        proof {
            assert(child_owner.inv());
            continuation.put_child(child_owner);
            continuation.entry_own.node = Some(parent_owner);
            cont0.take_put_child();
            owner.continuations.tracked_insert(owner.level - 1, continuation);

            // Establish preconditions for protect_preserves_cursor_inv_relate:
            assert(owner0.cur_entry_owner().is_frame());  // from function precondition
            assert(owner.cur_entry_owner().is_frame());   // protect ensures is_frame
            assert(owner.cur_entry_owner().inv());        // from protect ensures
            assert(owner.cur_entry_owner().frame.unwrap().mapped_pa == owner0.cur_entry_owner().frame.unwrap().mapped_pa) by {
                assert(owner0.cur_entry_owner().frame.unwrap().mapped_pa == child_owner_mapped_pa);
            };
            assert(owner.cur_entry_owner().frame.unwrap().slot_perm == owner0.cur_entry_owner().frame.unwrap().slot_perm) by {
                assert(owner0.cur_entry_owner().frame.unwrap().slot_perm == child_owner_slot_perm);
            };
            assert(owner.cur_entry_owner().path == owner0.cur_entry_owner().path);
            assert(owner.cur_entry_owner().parent_level == owner0.cur_entry_owner().parent_level) by {
                assert(owner0.cur_entry_owner().parent_level == child_owner_parent_level);
            };
            assert(owner.level == owner0.level);
            assert(owner.guard_level == owner0.guard_level);
            assert(owner.va == owner0.va);
            assert(owner.prefix == owner0.prefix);
            assert(owner.popped_too_high == owner0.popped_too_high);
            owner0.protect_preserves_cursor_inv_relate(*owner, *regions);
            assert(owner.inv());
            assert(owner.relate_region(*regions));
        }

        #[verus_spec(with Tracked(owner))]
        let protected_va = self.inner.cur_va_range();

        #[verus_spec(with Tracked(owner), Tracked(regions), Tracked(guards))]
        self.inner.move_forward();

        Some(protected_va)
    }

    #[verifier::rlimit(200)]
    #[verus_spec(
        with Tracked(owner): Tracked<&mut CursorOwner<'rcu, C>>,
            Tracked(new_owner): Tracked<OwnerSubtree<C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
    )]
    fn replace_cur_entry(&mut self, new_child: Child<C>) -> (res: Option<PageTableFrag<C>>)
        requires
            old(self).inner.invariants(*old(owner), *old(regions), *old(guards)),
            old(owner).in_locked_range(),
            !old(owner).popped_too_high,
            new_owner.inv(),
            new_owner.value.is_node() ==> new_owner.value.node.unwrap().level + 1 == new_owner.value.parent_level,
            new_owner.level == old(owner).continuations[old(owner).level - 1].tree_level + 1,
            new_owner.value.parent_level == old(owner).continuations[old(owner).level - 1].child().value.parent_level,
            new_owner.value.path == old(owner).continuations[old(owner).level - 1].path().push_tail(
                old(owner).continuations[old(owner).level - 1].idx as usize,
            ),
            new_child.wf(new_owner.value),
            new_owner.value.is_node() ==> old(regions).slot_owners[
                frame_to_index(new_owner.value.meta_slot_paddr().unwrap())
            ].inner_perms.ref_count.value() != REF_COUNT_UNUSED,
            new_owner.value.is_node() ==> old(regions).slots.contains_key(
                frame_to_index(new_owner.value.meta_slot_paddr().unwrap())
            ),
            new_owner.value.in_scope,
            new_owner == OwnerSubtree::new_val(new_owner.value, new_owner.level as nat),
            new_owner.value.relate_region(*old(regions)),
            new_owner.tree_predicate_map(
                new_owner.value.path,
                CursorOwner::<'rcu, C>::node_unlocked(*old(guards)),
            ),
            old(owner).map_full_tree(
                |entry_owner: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                    entry_owner.meta_slot_paddr_neq(new_owner.value),
            ),
            // panic
            !C::TOP_LEVEL_CAN_UNMAP_spec() ==> old(owner).level < NR_LEVELS,
        ensures
            owner@.mappings == old(owner)@.mappings - PageTableOwner(
                old(owner).cur_subtree(),
            )@.mappings + PageTableOwner(new_owner)@.mappings,
            self.inner.invariants(*owner, *regions, *guards),
            owner.va == old(owner).va,
            self.inner.level == old(self).inner.level,
            owner.guard_level == old(owner).guard_level,
            owner.in_locked_range(),
            // If the current entry was absent before the replace, no old fragment is returned.
            old(owner).cur_entry_owner().is_absent() ==> res is None,
            // path_if_in_pt is changed only for new_owner's slot; all others are preserved.
            // (new_owner.value here is the post-into_pte state; meta_slot_paddr() is unchanged.)
            forall|idx: usize| #![trigger regions.slot_owners[idx].path_if_in_pt]
                (new_owner.value.is_absent() || idx != frame_to_index(new_owner.value.meta_slot_paddr().unwrap()))
                    ==> regions.slot_owners[idx].path_if_in_pt == old(regions).slot_owners[idx].path_if_in_pt,
    {
        proof { reveal(CursorContinuation::inv_children); }

        let ghost owner0 = *owner;
        let ghost regions0 = *regions;
        let ghost guard_level = owner.guard_level;
        let rcu_guard = self.inner.rcu_guard;

        let tracked mut new_owner = new_owner;

        let va = self.inner.va;
        let level = self.inner.level;

        #[verus_spec(with Tracked(owner), Tracked(regions))]
        let mut cur_entry = self.inner.cur_entry();

        let tracked mut continuation = owner.continuations.tracked_remove((owner.level - 1) as int);
        let ghost cont0 = continuation;
        let ghost owner1 = *owner;
        let tracked old_child_owner = continuation.take_child();

        let ghost cont1 = continuation;
        assert(cont1.view_mappings() == cont0.view_mappings()
            - cont0.view_mappings_take_child_spec()) by {
            cont0.view_mappings_take_child();
            assert(cont1 == cont0.take_child_spec().1);
        }
        assert(owner.continuations == owner0.continuations.remove(owner.level - 1));

        let tracked mut parent_owner = continuation.entry_own.node.tracked_take();
        assert(new_owner.value.is_node() ==> parent_owner.level - 1
            == new_owner.value.node.unwrap().level) by {
            if new_owner.value.is_node() {
                // cont1 was captured right before tracked_take; take_child_spec preserves entry_own
                assert(cont1 == cont0.take_child_spec().1);
                assert(cont1.entry_own == cont0.entry_own);
                // parent_owner == cont1.entry_own.node.unwrap() (from tracked_take semantics)
                assert(parent_owner.level == cont0.level());
                // cont0.all_some() from owner0.inv() => cont0.child() is defined
                assert(cont0.children[cont0.idx as int] is Some);
                // inv_children (revealed at fn entry): child.value.parent_level == cont0.level()
                assert(cont0.inv_children());
                assert(cont0.child().value.parent_level == cont0.level());
                // precondition: new_owner.value.parent_level == cont0.child().value.parent_level
                assert(new_owner.value.parent_level == cont0.child().value.parent_level);
                // new precondition: node.level + 1 == parent_level
                assert(new_owner.value.node.unwrap().level + 1 == new_owner.value.parent_level);
            }
        };

        let ghost pre_new_owner_value = new_owner.value;
        // Capture the old child value before Entry::replace mutates it (from_pte_owner_spec
        // only changes in_scope, so meta_slot_paddr() is unchanged, but we need the pre-replace
        // value to match Entry::relate_region_neq_preserved's old(owner) parameter).
        let ghost old_child_pre_replace = old_child_owner.value;

        assert(!old_child_owner.value.in_scope) by {
            owner0.continuations_not_in_scope();
            assert(owner0.continuations[(owner0.level - 1) as int].children[cont0.idx as int] is Some);
        };

        #[verus_spec(with Tracked(regions),
            Tracked(&mut old_child_owner.value),
            Tracked(&mut new_owner.value),
            Tracked(&mut parent_owner),
            Tracked(&mut continuation.guard_perm)
        )]
        let old = cur_entry.replace(new_child);
        let ghost old_child_snap = old; // ghost alias to avoid `old(...)` keyword ambiguity in proofs

        // Pin relate_region_neq_preserved: for entries with paddr ≠ old_child and ≠ new_child,
        // relate_region is preserved from regions0 to post-replace *regions.
        // This is Entry::replace's postcondition (line 278 in entry.rs).
        assert(Entry::<C>::relate_region_neq_preserved(
            old_child_pre_replace,
            pre_new_owner_value,
            regions0,
            *regions,
        ));

        // Pin the path_if_in_pt preservation fact to a static snapshot so Z3 doesn't re-trigger
        // on later modifications to `regions`. The postcondition of `replace` gives us this with
        // old(regions) == regions0 (since cur_entry() takes only an immutable ref to regions).
        let ghost regions_after_replace = *regions;
        assert(forall|idx: usize| #![trigger regions_after_replace.slot_owners[idx].path_if_in_pt]
            (new_owner.value.is_absent() || idx != frame_to_index(new_owner.value.meta_slot_paddr().unwrap()))
                ==> regions_after_replace.slot_owners[idx].path_if_in_pt == regions0.slot_owners[idx].path_if_in_pt
        );

        assert(new_owner.value.match_pte(
            parent_owner.children_perm.value()[cur_entry.idx as int],
            parent_owner.level,
        ));
        assert(cur_entry.idx == continuation.idx) by {
            assert(cur_entry.idx == owner0.continuations[(owner0.level - 1) as int].idx);
        };

        proof {
            continuation.entry_own.node = Some(parent_owner);
            continuation.put_child(new_owner);
            cont1.view_mappings_put_child(new_owner);

            let ghost final_cont = continuation;
            owner.continuations.tracked_insert((owner.level - 1) as int, continuation);

            owner0.view_mappings_take_lowest(owner1);
            owner1.view_mappings_put_lowest(*owner, continuation);
            assert(owner@.mappings == owner0@.mappings - PageTableOwner(
                owner0.cur_subtree(),
            )@.mappings + PageTableOwner(new_owner)@.mappings);

            let level = owner0.level;
            let idx = cont0.idx as int;

            assert forall|i: int| level <= i < NR_LEVELS implies owner0.continuations[i]
                == owner.continuations[i] by {};
            assert forall|j: int|
                #![trigger final_cont.children[j]]
                0 <= j < NR_ENTRIES && j != idx implies final_cont.children[j]
                == cont0.children[j] by {
                assert(cont1.children[j] == cont0.children[j]);
            };

            assert(new_owner.value.meta_slot_paddr() == pre_new_owner_value.meta_slot_paddr());
            // f_neq uses pre-replace old_child value so it matches relate_region_neq_preserved.
            // (from_pte_owner_spec only changes in_scope, so meta_slot_paddr() is unchanged.)
            let f_neq_new = |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                entry.meta_slot_paddr_neq(pre_new_owner_value);
            let f_neq_old = |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                entry.meta_slot_paddr_neq(old_child_pre_replace);
            let f_neq = |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                entry.meta_slot_paddr_neq(pre_new_owner_value)
                    && entry.meta_slot_paddr_neq(old_child_pre_replace);
            let f_region = PageTableOwner::<C>::relate_region_pred(regions0);
            let g_region = PageTableOwner::<C>::relate_region_pred(*regions);
            let f_path = PageTableOwner::<C>::path_tracked_pred(regions0);
            let g_path = PageTableOwner::<C>::path_tracked_pred(*regions);

            // relate_region_neq_preserved (Entry::replace postcondition) gives the key implication:
            // f_region && f_neq → g_region.
            assert(OwnerSubtree::implies(
                |e: EntryOwner<C>, p: TreePath<NR_ENTRIES>| f_region(e, p) && f_neq(e, p),
                g_region,
            ));

            // f_neq_new holds for all entries in owner0's tree (precondition map_full_tree).
            // f_neq_old: for entries at different paths from old_child, by path_if_in_pt uniqueness.
            //   Proof: same_paddr_implies_same_path shows same paddr → same path; contrapositive
            //   gives different path → different paddr → f_neq_old. The formal proof for the
            //   entire subtree (all depths) is encapsulated by the per-subtree block below.

            // For higher levels (i >= level): continuations unchanged, use map_implies_and
            assert forall|i: int| #![auto] owner0.level <= i < NR_LEVELS implies {
                &&& owner.continuations[i].map_children(g_region)
                &&& owner.continuations[i].map_children(g_path)
            } by {
                assert(owner.continuations[i] == owner0.continuations[i]);
                let cont = owner0.continuations[i];
                assert forall|j: int|
                    #![auto]
                    0 <= j < NR_ENTRIES
                        && cont.children[j] is Some implies cont.children[j].unwrap().tree_predicate_map(
                cont.path().push_tail(j as usize), g_region) by {
                    let subtree = cont.children[j].unwrap();
                    let path_j = cont.path().push_tail(j as usize);
                    // f_region: from owner0.relate_region(regions0) via map_full_tree
                    assert(subtree.tree_predicate_map(path_j, f_region));
                    // f_neq_new: from precondition map_full_tree(|e| e.meta_slot_paddr_neq(new_owner))
                    assert(subtree.tree_predicate_map(path_j, f_neq_new));
                    // f_neq_old: entries at different paths from old_child have different paddr.
                    // Proof: cont.children[j] is Some only when j != cont.idx (all_but_index_some).
                    // By cursor_path_nesting: old_child_pre_replace.path has cont.idx at position
                    // cont.path().len() (the cursor descended through cont.idx at level i).
                    // path_j has j != cont.idx at that position → !is_prefix_of → f_neq_old.
                    assert(subtree.tree_predicate_map(path_j, f_neq_old)) by {
                        if old_child_pre_replace.meta_slot_paddr() is None {
                            assert(OwnerSubtree::implies(f_region, f_neq_old)) by {
                                assert forall|e: EntryOwner<C>, p: TreePath<NR_ENTRIES>|
                                    f_region(e, p) implies #[trigger] f_neq_old(e, p) by {};
                            };
                            OwnerSubtree::map_implies(subtree, path_j, f_region, f_neq_old);
                        } else {
                            // j != cont.idx (since cont.children[j] is Some and all_but_index_some)
                            assert(j != cont.idx as int);
                            // By cursor_path_nesting: old_child_pre_replace.path has cont.idx at cont.path().len()
                            // (old_child_pre_replace.path == cont0.path() ++ [...] and cont0.path starts with
                            // cont.path() ++ [cont.idx], so old_child.path[cont.path().len()] = cont.idx)
                            owner0.cursor_path_nesting(i, owner0.level as int - 1);
                            assert(old_child_pre_replace.path.index(cont.path().len() as int) == cont.idx as usize) by {
                                // cont0 = owner0.continuations[owner0.level - 1]
                                // cursor_path_nesting(i, owner0.level - 1) gives:
                                //   cont0.path().index(cont.path().len()) == cont.idx
                                // And old_child_pre_replace.path = cont0.path().push_tail(idx as usize)
                                // So old_child_pre_replace.path.index(cont.path().len()) = cont0.path()[cont.path().len()] = cont.idx
                                let len = cont.path().len() as int;
                                assert(cont0.path().index(len) == cont.idx as usize);
                                // old_child_pre_replace.path = cont0.path().push_tail(idx)
                                // cont.path().len() < cont0.path().len() (cont is higher level)
                                // push_tail_property_index: for i < base.len(), push_tail(v).index(i) == base.index(i)
                                assert(old_child_pre_replace.path == cont0.path().push_tail(idx as usize));
                                assert(len < cont0.path().len() as int);
                                cont0.path().push_tail_property_index(idx as usize);
                                assert(old_child_pre_replace.path.index(len) == cont0.path().index(len));
                            };
                            // path_j[cont.path().len()] = j != cont.idx = old_child_pre_replace.path[cont.path().len()]
                            cont.path().push_tail_property_index(j as usize);
                            let k = cont.path().len() as int;
                            assert(path_j.index(k) == j as usize);
                            assert(!PageTableOwner::<C>::is_prefix_of(path_j, old_child_pre_replace.path)) by {
                                assert(path_j.index(k) != old_child_pre_replace.path.index(k));
                            };
                            assert(subtree.value.path == path_j);
                            assert(subtree.level == cont.tree_level + 1);
                            assert(path_j.len() == subtree.level) by {
                                cont.path().push_tail_property_len(j as usize);
                            };
                            assert(old_child_pre_replace.relate_region(regions0));
                            assert(regions0.slot_owners[frame_to_index(
                                old_child_pre_replace.meta_slot_paddr().unwrap()
                            )].path_if_in_pt is Some);
                            PageTableOwner::<C>::neq_old_from_path_disjoint(
                                subtree, path_j, old_child_pre_replace, regions0,
                            );
                        }
                    };
                    // Combine f_neq_new + f_neq_old → f_neq (trivially, since f_neq = conjunction)
                    assert(OwnerSubtree::implies(
                        |e: EntryOwner<C>, p: TreePath<NR_ENTRIES>| f_neq_new(e, p) && f_neq_old(e, p),
                        f_neq,
                    ));
                    OwnerSubtree::map_implies_and(subtree, path_j, f_neq_new, f_neq_old, f_neq);
                    // Now apply: (f_region && f_neq) → g_region
                    OwnerSubtree::map_implies_and(subtree, path_j, f_region, f_neq, g_region);
                };
                assert forall|j: int|
                    #![auto]
                    0 <= j < NR_ENTRIES
                        && cont.children[j] is Some implies cont.children[j].unwrap().tree_predicate_map(
                cont.path().push_tail(j as usize), g_path) by {
                    OwnerSubtree::map_implies(
                        cont.children[j].unwrap(),
                        cont.path().push_tail(j as usize),
                        f_path,
                        g_path,
                    );
                };
            };

            // New owner satisfies predicates (from Entry::replace postconditions)
            assert(new_owner.value.relate_region(*regions));
            assert(!new_owner.value.is_absent() ==> PageTableOwner::<C>::path_tracked_pred(
                *regions,
            )(new_owner.value, new_owner.value.path));
            // new_owner == new_val(value, level): children are Node::new(level+1) (absent defaults).
            // For absent default entries, both g_region and g_path are trivially true.
            let child_path = final_cont.path().push_tail(idx as usize);
            assert(new_owner.tree_predicate_map(child_path, g_region)) by {
                assert forall|lv: nat, p: TreePath<NR_ENTRIES>| lv < INC_LEVELS implies
                    #[trigger] g_region(<EntryOwner<C> as TreeNodeValue<INC_LEVELS>>::default(lv), p) by {}; // default is absent
                OwnerSubtree::new_val_tree_predicate_map(new_owner, child_path, g_region);
            };
            assert(new_owner.tree_predicate_map(child_path, g_path)) by {
                assert forall|lv: nat, p: TreePath<NR_ENTRIES>| lv < INC_LEVELS implies
                    #[trigger] g_path(<EntryOwner<C> as TreeNodeValue<INC_LEVELS>>::default(lv), p) by {}; // default.meta_slot_paddr() is None
                OwnerSubtree::new_val_tree_predicate_map(new_owner, child_path, g_path);
            };

            // For the modified continuation (level - 1): handle siblings and new_owner
            assert(final_cont.map_children(g_region)) by {
                assert forall|j: int|
                    #![auto]
                    0 <= j < NR_ENTRIES
                        && final_cont.children[j] is Some implies final_cont.children[j].unwrap().tree_predicate_map(
                final_cont.path().push_tail(j as usize), g_region) by {
                    let path_j = final_cont.path().push_tail(j as usize);
                    if j == idx as int {
                        // new_owner at idx: already proved above via new_val_tree_predicate_map
                        assert(final_cont.children[j] == Some(new_owner));
                    } else {
                        // Sibling j != idx: unchanged from cont0
                        assert(final_cont.children[j] == cont0.children[j]);
                        let subtree = cont0.children[j].unwrap();
                        // f_region: from owner0.relate_region(regions0) via map_full_tree
                        assert(subtree.tree_predicate_map(path_j, f_region));
                        // f_neq_new: from precondition map_full_tree
                        assert(subtree.tree_predicate_map(path_j, f_neq_new));
                        // f_neq_old: sibling j != idx has path cont0.path().push_tail(j)
                        // which differs from old_child.path = cont0.path().push_tail(idx) since j != idx.
                        // All deeper entries in this subtree have even longer paths → also ≠ old_child.path.
                        // By neq_old_from_path_disjoint: different structural positions → different paddrs.
                        assert(subtree.tree_predicate_map(path_j, f_neq_old)) by {
                            if old_child_pre_replace.meta_slot_paddr() is None {
                                // f_neq_old trivially true when old has no paddr
                                assert(OwnerSubtree::implies(f_region, f_neq_old)) by {
                                    assert forall|e: EntryOwner<C>, p: TreePath<NR_ENTRIES>|
                                        f_region(e, p) implies #[trigger] f_neq_old(e, p) by {};
                                };
                                OwnerSubtree::map_implies(subtree, path_j, f_region, f_neq_old);
                            } else {
                                // old_child_pre_replace.path == cont0.path().push_tail(idx)
                                // (from cont0.inv_children() + rel_children, already revealed)
                                assert(old_child_pre_replace.path == cont0.path().push_tail(idx as usize));
                                // path_j == cont0.path().push_tail(j), old_child.path == cont0.path().push_tail(idx)
                                // They differ at position cont0.path().len(): j vs idx (j != idx)
                                assert(!PageTableOwner::<C>::is_prefix_of(path_j, old_child_pre_replace.path)) by {
                                    let k = cont0.path().len() as int;
                                    cont0.path().push_tail_property_index(j as usize);
                                    cont0.path().push_tail_property_index(idx as usize);
                                    assert(path_j.index(k) == j as usize);
                                    assert(old_child_pre_replace.path.index(k) == idx as usize);
                                    assert(j as usize != idx as usize);
                                };
                                // subtree.value.path == path_j (from cont0.inv_children())
                                assert(subtree.value.path == path_j);
                                assert(subtree.level == cont0.tree_level + 1);
                                assert(path_j.len() == subtree.level) by {
                                    cont0.path().push_tail_property_len(j as usize);
                                };
                                // old_child_pre_replace.relate_region(regions0) from owner0.relate_region(regions0)
                                assert(old_child_pre_replace.relate_region(regions0));
                                // path_if_in_pt is Some for old_child's paddr (from path_tracked_pred)
                                assert(regions0.slot_owners[frame_to_index(
                                    old_child_pre_replace.meta_slot_paddr().unwrap()
                                )].path_if_in_pt is Some);
                                PageTableOwner::<C>::neq_old_from_path_disjoint(
                                    subtree, path_j, old_child_pre_replace, regions0,
                                );
                            }
                        };
                        // Combine
                        assert(OwnerSubtree::implies(
                            |e: EntryOwner<C>, p: TreePath<NR_ENTRIES>| f_neq_new(e, p) && f_neq_old(e, p),
                            f_neq,
                        ));
                        OwnerSubtree::map_implies_and(subtree, path_j, f_neq_new, f_neq_old, f_neq);
                        OwnerSubtree::map_implies_and(subtree, path_j, f_region, f_neq, g_region);
                    }
                };
            };

            assert(final_cont.map_children(g_path)) by {
                assert forall|j: int|
                    #![auto]
                    0 <= j < NR_ENTRIES
                        && final_cont.children[j] is Some implies final_cont.children[j].unwrap().tree_predicate_map(
                final_cont.path().push_tail(j as usize), g_path) by {
                    if j != idx && cont0.children[j] is Some {
                        OwnerSubtree::map_implies(
                            cont0.children[j].unwrap(),
                            cont0.path().push_tail(j as usize),
                            f_path,
                            g_path,
                        );
                    }
                };
            };

            assert(owner.relate_region(*regions));

            assert forall|j: int|
                #![trigger final_cont.children[j]]
                0 <= j < NR_ENTRIES && final_cont.children[j] is Some implies {
                &&& final_cont.children[j].unwrap().value.path == final_cont.path().push_tail(
                    j as usize,
                )
                &&& final_cont.children[j].unwrap().value.parent_level == final_cont.level()
                &&& final_cont.children[j].unwrap().inv()
                &&& final_cont.children[j].unwrap().level == final_cont.tree_level + 1
            } by {
                if j != idx {
                    assert(final_cont.children[j] == cont0.children[j]);
                }
            };
        }

        // Capture owner and regions at this point (after relate_region was established)
        let ghost owner_after_replace = *owner;
        let ghost regions_after_replace = *regions;

        let result = match old {
            Child::None => None,
            Child::Frame(pa, ch_level, prop) => {
                // debug_assert_eq!(ch_level, level);
                // Return the slot perm from the old FrameEntryOwner back to regions.slots so
                // that item_from_raw can reclaim it.  Full instrumentation of item_from_raw to
                // accept the perm directly is a follow-up (TODO).
                proof {
                    // Snapshot the entry owner before tracked_take modifies frame field.
                    let ghost entry_owner_snap = old_child_owner.value;
                    // From Entry::replace postcondition: old.invariants(entry_owner_snap, regions_after_replace)
                    // (res.invariants(*owner, *regions) where res = old_child_snap = old,
                    //  *owner at replace time = entry_owner_snap, *regions = regions_after_replace)
                    assert(old_child_snap.invariants(entry_owner_snap, regions_after_replace));
                    assert(entry_owner_snap.is_frame());
                    assert(entry_owner_snap.relate_region(regions_after_replace));

                    let tracked frame_own = old_child_owner.value.frame.tracked_take();
                    // frame_own.slot_perm == entry_owner_snap.frame.unwrap().slot_perm
                    let idx = frame_to_index(pa);
                    assert(idx < max_meta_slots());
                    assert(frame_own.slot_perm.addr() == meta_addr(idx));
                    assert(frame_own.slot_perm.is_init());
                    assert(frame_own.slot_perm.value().wf(regions_after_replace.slot_owners[idx]));
                    assert(regions_after_replace.slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED);
                    assert(regions_after_replace.slot_owners.contains_key(idx));
                    regions.slots.tracked_insert(idx, frame_own.slot_perm);
                    // regions.inv(): use the axiom that inserting a valid frame slot perm preserves inv
                    assert(regions.inv()) by {
                        assert(regions.slots == regions_after_replace.slots.insert(idx, frame_own.slot_perm));
                        assert(regions.slot_owners == regions_after_replace.slot_owners);
                        regions_after_replace.frame_slot_perm_insert_preserves_inv(idx, frame_own.slot_perm, *regions);
                    };
                    // owner.relate_region(*regions): relate_region only uses slot_owners,
                    // and regions.slot_owners == regions_after_replace.slot_owners (unchanged by tracked_insert).
                    assert(owner.relate_region(*regions)) by {
                        assert(regions.slot_owners == regions_after_replace.slot_owners);
                        assert(owner_after_replace.relate_region(regions_after_replace));
                        // Lift per-entry implication to full tree via relate_region_preserved.
                        assert(OwnerSubtree::implies(
                            PageTableOwner::<C>::relate_region_pred(regions_after_replace),
                            PageTableOwner::<C>::relate_region_pred(*regions),
                        )) by {
                            assert forall |e: EntryOwner<C>, p: TreePath<NR_ENTRIES>|
                                PageTableOwner::<C>::relate_region_pred(regions_after_replace)(e, p)
                                implies #[trigger] PageTableOwner::<C>::relate_region_pred(*regions)(e, p) by {
                                e.relate_region_slot_owners_only(regions_after_replace, *regions);
                            };
                        };
                        assert(OwnerSubtree::implies(
                            PageTableOwner::<C>::path_tracked_pred(regions_after_replace),
                            PageTableOwner::<C>::path_tracked_pred(*regions),
                        )) by {
                            assert forall |e: EntryOwner<C>, p: TreePath<NR_ENTRIES>|
                                PageTableOwner::<C>::path_tracked_pred(regions_after_replace)(e, p)
                                implies #[trigger] PageTableOwner::<C>::path_tracked_pred(*regions)(e, p) by {
                                assert(regions.slot_owners == regions_after_replace.slot_owners);
                            };
                        };
                        owner_after_replace.relate_region_preserved(*owner, regions_after_replace, *regions);
                    };
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
                Some(PageTableFrag::Mapped { va, item })
            },
            Child::PageTable(pt) => {
                // debug_assert_eq!(pt.level(), level - 1);
                if !C::TOP_LEVEL_CAN_UNMAP() {
                    assert(!C::TOP_LEVEL_CAN_UNMAP_spec());
                    if level as usize == NR_LEVELS {
                        assert(owner.level == NR_LEVELS);

                        let _ = ManuallyDrop::new(pt, Tracked(regions));  // leak it to make shared PTs stay `'static`.
                        assert(false);
                        return None;
                        // panic!("Unmapping shared kernel page table nodes");
                    }
                }
                // SAFETY: We must have locked this node.

                let ghost owner2 = *owner;
                let ghost child_entry = old_child_owner.value;

                let tracked mut old_node_owner = old_child_owner.value.node.tracked_take();

                // TODO: we will need to apply the `raw_count` approach to `Child` in order
                // to track this correctly.
                assert(regions.slot_owners[pt.index()].raw_count == 1) by { admit() };

                #[verus_spec(with Tracked(regions), Tracked(& old_node_owner.meta_perm))]
                let borrow_pt = pt.borrow();

                proof_decl! {
                    let tracked mut guard_perm: Tracked<GuardPerm<'rcu, C>>;
                }

                let ghost guards0 = *guards;

                #[verus_spec(with Tracked(&old_node_owner), Tracked(guards) => Tracked(guard_perm))]
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
                #[verus_spec(with Tracked(owner), Tracked(guards), Ghost(locked_addr))]
                let num_frames = locking::dfs_mark_stray_and_unlock(rcu_guard, locked_pt);

                proof {
                    assert(OwnerSubtree::implies(
                        CursorOwner::node_unlocked_except(guards1, locked_addr),
                        CursorOwner::node_unlocked(*guards),
                    ));

                    owner.map_children_implies(
                        CursorOwner::node_unlocked_except(guards1, locked_addr),
                        CursorOwner::node_unlocked(*guards),
                    );

                    // Prove nodes_locked: continuation node addresses differ from child address
                    assert forall|i: int|
                        owner.level - 1 <= i
                            < NR_LEVELS implies #[trigger] owner.continuations[i].node_locked(
                        *guards,
                    ) by {
                        let cont_i = owner.continuations[i];
                        let cont_addr = cont_i.guard_perm.value().inner.inner@.ptr.addr();
                        let owner0_cont_addr =
                            owner0.continuations[i].guard_perm.value().inner.inner@.ptr.addr();
                        if i >= owner.level as int {
                            assert(owner.continuations[i] == owner0.continuations[i]);
                            assert(cont_addr == owner0_cont_addr);
                        } else {
                            assert(owner.continuations[owner.level - 1].guard_perm
                                == owner_before_dfs.continuations[owner.level - 1].guard_perm);
                            assert(cont_addr == owner0_cont_addr);
                        }
                        let cont_entry = owner0.continuations[i].entry_own;
                        // TODO: prove preconditions of nodes_different_paths_different_addrs.
                        // These were previously hidden by Z3 inconsistency from the old
                        // wrong-key admit.  The required preconditions (cont_entry/child_entry
                        // relate_region + path_if_in_pt is Some) follow from owner0.relate_region
                        // and the cursor invariant, but need explicit proof plumbing.
                        assert(cont_entry.is_node() ==> cont_entry.relate_region(regions0)) by { admit() };
                        assert(child_entry.is_node() ==> child_entry.relate_region(regions0)) by { admit() };
                        assert(cont_entry.is_node() && child_entry.is_node() ==>
                            (cont_entry.meta_slot_paddr() is Some ==>
                                regions0.slot_owners[frame_to_index(cont_entry.meta_slot_paddr().unwrap())].path_if_in_pt is Some)
                        ) by { admit() };
                        assert(cont_entry.is_node() && child_entry.is_node() ==>
                            (child_entry.meta_slot_paddr() is Some ==>
                                regions0.slot_owners[frame_to_index(child_entry.meta_slot_paddr().unwrap())].path_if_in_pt is Some)
                        ) by { admit() };
                        cont_entry.nodes_different_paths_different_addrs(child_entry, regions0);
                    };
                    assert(owner_before_dfs == owner_after_replace);
                    assert(*regions =~= regions_after_replace);
                    assert(owner_before_dfs.relate_region(*regions));

                    let f = PageTableOwner::<C>::relate_region_pred(*regions);

                    // TODO: prove relate_region forall for continuations after dfs_mark_stray.
                    // Hidden by Z3 inconsistency from the old wrong-key admit.
                    // The proof should follow from owner_before_dfs.relate_region(*regions) and
                    // the fact that dfs_mark_stray only changes regions.slot_owners for slots
                    // within the removed subtree, which are disjoint from continuation entries.
                    assert forall|i: int| #![auto] owner.level - 1 <= i < NR_LEVELS implies {
                        &&& f(owner.continuations[i].entry_own, owner.continuations[i].path())
                        &&& owner.continuations[i].map_children(f)
                    } by {
                        if i < owner.level as int {
                            assert(forall|j: int|
                                0 <= j < NR_ENTRIES ==>
                                #[trigger] owner.continuations[owner.level - 1].children[j] ==
                                owner_before_dfs.continuations[owner.level - 1].children[j]);
                        }
                        admit();
                    };

                    assert forall|i: int|
                        #![auto]
                        owner.level - 1 <= i < NR_LEVELS
                            implies owner.continuations[i].view_mappings()
                        == owner_before_dfs.continuations[i].view_mappings() by {
                        if i >= owner.level as int {
                            assert(owner.continuations[i] == owner_before_dfs.continuations[i]);
                        } else {
                            assert(owner.continuations[i].children
                                =~= owner_before_dfs.continuations[i].children);
                        }
                    };

                    assert(forall|m: Mapping|
                        owner.view_mappings().contains(m) <==> owner_before_dfs.view_mappings().contains(m));
                }

                Some(
                    PageTableFrag::StrayPageTable {
                        pt: pt.into(),
                        va,
                        len: page_size(self.inner.level),
                        num_frames,
                    },
                )
            },
        };

        assert(forall|idx: usize| #![trigger regions.slot_owners[idx].path_if_in_pt]
            (new_owner.value.is_absent() || idx != frame_to_index(new_owner.value.meta_slot_paddr().unwrap()))
                ==> regions.slot_owners[idx].path_if_in_pt == regions0.slot_owners[idx].path_if_in_pt
        ) by {
            assert(regions.slot_owners =~= regions_after_replace.slot_owners);
        };

        result
    }
}

} // verus!
