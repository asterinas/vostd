mod locking;
pub mod spec_helpers;

use std::{
    any::TypeId,
    borrow::{Borrow, BorrowMut},
    cell::Cell,
    char::MAX,
    marker::PhantomData,
    ops::Range,
};

use vstd::{
    invariant, layout::is_power_2, pervasive::VecAdditionalExecFns, prelude::*,
    raw_ptr::MemContents,
};
use vstd::bits::*;
use vstd::tokens::SetToken;

use crate::{
    helpers::align_ext::align_down,
    mm::{
        child::{self, Child},
        entry::Entry,
        frame::{self, allocator::AllocatorModel},
        meta::AnyFrameMeta,
        node::PageTableNode,
        nr_subpage_per_huge,
        page_prop::PageProperty,
        page_size,
        vm_space::Token,
        Frame, MapTrackingStatus, Paddr, PageTableGuard, Vaddr, MAX_USERSPACE_VADDR, PAGE_SIZE,
    },
    task::DisabledPreemptGuard,
    x86_64::VMALLOC_VADDR_RANGE,
};

use super::{
    pte_index, PageTable, PageTableConfig, PageTableEntryTrait, PageTableError, PagingConsts,
    PagingConstsTrait, PagingLevel,
};

use crate::spec::sub_page_table;
use crate::exec;
use spec_helpers::*;
use crate::mm::NR_ENTRIES;

verus! {

/// The cursor for traversal over the page table.
///
/// A slot is a PTE at any levels, which correspond to a certain virtual
/// memory range sized by the "page size" of the current level.
///
/// A cursor is able to move to the next slot, to read page properties,
/// and even to jump to a virtual address directly.
// #[derive(Debug)] // TODO: Implement `Debug` for `Cursor`.
pub struct Cursor<'a, C: PageTableConfig> {
    /// The current path of the cursor.
    ///
    /// The level 1 page table lock guard is at index 0, and the level N page
    /// table lock guard is at index N - 1.
    // path: [Option<PageTableLock<C, T>>; MAX_NR_LEVELS],
    pub path: Vec<Option<PageTableGuard<C>>>,
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
    /// This also make all the operation in the `Cursor::new` performed in a
    /// RCU read-side critical section.
    // #[expect(dead_code)]
    pub preempt_guard: DisabledPreemptGuard,
    // _phantom: PhantomData<&'a PageTable<C>>,
    pub _phantom: PhantomData<&'a PageTable<C>>,
}

/// The maximum value of `PagingConstsTrait::NR_LEVELS`.
pub const MAX_NR_LEVELS: usize = 4;

// #[derive(Clone, Debug)] // TODO: Implement Debug and Clone for PageTableItem
pub enum PageTableItem {
    NotMapped { va: Vaddr, len: usize },
    Mapped { va: Vaddr, page: Frame, prop: PageProperty },
    MappedUntracked { va: Vaddr, pa: Paddr, len: usize, prop: PageProperty },
    StrayPageTable { pt: Frame, va: Vaddr, len: usize },
    /// The current slot is marked to be reserved.
    Marked {
        /// The virtual address of the slot.
        va: Vaddr,
        /// The length of the slot.
        len: usize,
        /// A user-provided token.
        token: Token,
    },
}

impl<'a, C: PageTableConfig> Cursor<'a, C> {
    pub open spec fn sub_page_table_valid_before_map(
        &self,
        sub_page_table: &exec::SubPageTable,
    ) -> bool {
        &&& sub_page_table.wf()
        &&& sub_page_table.frames@.value().contains_key(
            self.path[path_index_at_level(self.level)].unwrap().paddr() as int,
        )
    }

    pub open spec fn sub_page_table_valid_after_map(
        &self,
        sub_page_table: &exec::SubPageTable,
        frame: &Frame,
        level: u8,
        root: int,
        last_level: u8,
    ) -> bool
        decreases level,
    {
        &&& sub_page_table.wf()
        &&& sub_page_table.frames@.value().contains_key(root)
        &&& level > last_level ==> {
            &&& sub_page_table.ptes@.value().contains_key(
                root + pte_index::<C>(self.va, level) * exec::SIZEOF_PAGETABLEENTRY as int,
            )
            &&& self.sub_page_table_valid_after_map(
                sub_page_table,
                frame,
                (level - 1) as u8,
                sub_page_table.ptes@.value()[root + pte_index::<C>(self.va, level)
                    * exec::SIZEOF_PAGETABLEENTRY as int].frame_pa,
                last_level,
            )
        }
        &&& level == last_level ==> {
            &&& last_level == frame.map_level() ==> {
                &&& sub_page_table.ptes@.value().contains_key(
                    root + pte_index::<C>(self.va, level) * exec::SIZEOF_PAGETABLEENTRY as int,
                )
                &&& sub_page_table.ptes@.value()[root + pte_index::<C>(self.va, level)
                    * exec::SIZEOF_PAGETABLEENTRY as int].frame_pa == frame.start_paddr() as int
            }
        }
    }

    pub open spec fn sub_page_table_valid_before_map_level(
        &self,
        sub_page_table: &exec::SubPageTable,
        frame: &Frame,
        level: u8,
        root: int,
        last_level: u8,
    ) -> bool
        decreases level,
    {
        &&& sub_page_table.wf()
        &&& sub_page_table.frames@.value().contains_key(root)
        &&& level > last_level ==> {
            &&& sub_page_table.ptes@.value().contains_key(
                root + pte_index::<C>(self.va, level) * exec::SIZEOF_PAGETABLEENTRY as int,
            )
            &&& self.sub_page_table_valid_before_map_level(
                sub_page_table,
                frame,
                (level - 1) as u8,
                sub_page_table.ptes@.value()[root + pte_index::<C>(self.va, level)
                    * exec::SIZEOF_PAGETABLEENTRY as int].frame_pa,
                last_level,
            )
        }
    }

    // TODO: do we need a path model?
    pub open spec fn path_matchs_page_table(
        &self,
        sub_page_table: &exec::SubPageTable,
        level: u8,
        root: int,
        last_level: u8,
    ) -> bool
        decreases level,
    {
        &&& self.path[path_index_at_level(level)].is_some()
        &&& self.path[path_index_at_level(level)].unwrap().paddr() as int == root
        &&& level > last_level ==> {
            &&& sub_page_table.ptes@.value().contains_key(
                root + pte_index::<C>(self.va, level) * exec::SIZEOF_PAGETABLEENTRY as int,
            )
            &&& self.path_matchs_page_table(
                sub_page_table,
                (level - 1) as u8,
                sub_page_table.ptes@.value()[root + pte_index::<C>(self.va, level)
                    * exec::SIZEOF_PAGETABLEENTRY as int].frame_pa,
                last_level,
            )
        }
    }

    pub open spec fn path_item_points_to(
        &self,
        level: u8,
        spt: &exec::SubPageTable,
        a: PageTableGuard<C>,
        b: PageTableGuard<C>,
    ) -> bool {
        &&& 1 <= self.level <= PagingConsts::NR_LEVELS_SPEC() as u8
        &&& 1 <= level <= PagingConsts::NR_LEVELS_SPEC() as u8
        &&& exec::get_pte_from_addr(
            (a.paddr() + pte_index::<C>(self.va, level) * exec::SIZEOF_PAGETABLEENTRY) as usize,
            spt,
        ).frame_paddr() == b.paddr()
    }

    // Path is well-formed if:
    ///  - if self.level - 1 <= i < NR_LEVELS, path[i] is some
    ///  - if 0 <= i < self.level - 1, path[i] is None
    ///  - path[i + 1] points_to path[i]
    pub open spec fn path_wf(&self, spt: &exec::SubPageTable) -> bool {
        &&& self.path.len() == PagingConsts::NR_LEVELS_SPEC()
        &&& forall|i: int| 0 <= i < self.level - 1 ==> self.path[i].is_none()
        &&& forall|i: int|
            self.level - 1 <= i < PagingConsts::NR_LEVELS_SPEC() ==> {
                &&& (#[trigger] self.path[i]).is_some()
                &&& self.path[i].unwrap().wf()
            }
        &&& forall|i: int, j: int|
            0 <= i < j < self.path.len() && self.path[i].is_some() && i + 1 == j
                ==> self.path_item_points_to(
                level_at_path_index(j),
                spt,
                #[trigger] self.path[j].unwrap(),
                #[trigger] self.path[i].unwrap(),
            )
        &&& forall|i: int|
            1 <= i < self.path.len() && self.path[i].is_some() ==> spt.frames@.value().contains_key(
                ((#[trigger] self.path[i].unwrap().paddr()) as int),
            )
    }

    /// Creates a cursor claiming exclusive access over the given range.
    ///
    /// The cursor created will only be able to query or jump within the given
    /// range. Out-of-bound accesses will result in panics or errors as return values,
    /// depending on the access method.
    pub fn new(pt: &'a PageTable<C>, va: &Range<Vaddr>) -> Result<Self, PageTableError> {
        if   /* Check range covers || */
        !(va.start < va.end) {
            return Err(PageTableError::InvalidVaddrRange(va.start, va.end));
        }
        if va.start % C::BASE_PAGE_SIZE() != 0 || va.end % C::BASE_PAGE_SIZE() != 0 {
            return Err(PageTableError::UnalignedVaddr);
        }
        // TODO
        // const { assert!(C::NR_LEVELS() as usize <= MAX_NR_LEVELS) };

        Ok(locking::lock_range(pt, va))
    }

    /// Traverses forward in the current level to the next PTE.
    ///
    /// If reached the end of a page table node, it leads itself up to the next page of the parent
    /// page if possible.
    pub(in crate::mm) fn move_forward(&mut self, spt: &exec::SubPageTable)
        requires
            old(self).path_wf(spt),
            old(self).level > 0,
            old(self).level <= C::NR_LEVELS(),
            old(self).level <= PagingConsts::NR_LEVELS(),
        ensures
            self.path == old(self).path,
            self.level >= old(self).level,
            self.level <= C::NR_LEVELS(),
            self.level <= PagingConsts::NR_LEVELS(),
            self.va > old(self).va,
            self.va < MAX_USERSPACE_VADDR,
            // forall|i: u8|
            //     self.level <= i <= PagingConsts::NR_LEVELS() ==> pte_index::<C>(self.va, i)
            //         == pte_index::<C>(old(self).va, i),
            self.path_wf(spt),
    {
        assume(self.va + page_size::<C>(self.level) < MAX_USERSPACE_VADDR);
        let page_size = page_size::<C>(self.level);
        let next_va = align_down(self.va, page_size) + page_size;
        // while self.level < self.guard_level && pte_index::<C>(next_va, self.level) == 0
        // decreases self.guard_level - self.level
        // {
        //     self.pop_level();
        // }
        self.va = next_va;
        // TODO: P0 self.va changed, but the higher bits of va does not change.
        assume(forall|i: u8|
            self.level <= i <= PagingConsts::NR_LEVELS() ==> pte_index::<C>(self.va, i)
                == pte_index::<C>(old(self).va, i));
    }

    pub fn virt_addr(&self) -> Vaddr {
        self.va
    }

    /// Goes up a level.
    fn pop_level(&mut self)
        requires
            old(self).level <= PagingConsts::NR_LEVELS_SPEC() as usize,
            old(self).level > 1,
            old(self).path.len() > old(self).level as usize,
        ensures
            self.level == old(self).level + 1,
    {
        // let Some(taken) = self.path[self.level as usize - 1].take() else {
        //     panic!("Popping a level without a lock");
        // };
        let taken = &self.path[self.level as usize - 1];
        if (taken.is_none()) {
            // panic!("Popping a level without a lock");
            // assert(false); // TODO
        }
        // TODO
        // let _taken = taken.unwrap().into_raw_paddr();

        self.level = self.level + 1;
    }

    /// Goes down a level to a child page table.
    fn push_level(
        &mut self,
        child_pt: PageTableGuard<C>,
        old_level: Tracked<PagingLevel>,
        // ghost
        spt: &exec::SubPageTable,
    )
        requires
            old(self).level > 1,
            old(self).level <= PagingConsts::NR_LEVELS_SPEC(),
            old(self).path_wf(spt),
            child_pt.wf(),
            spt.frames@.value().contains_key(child_pt.paddr() as int),
            spt.wf(),
            old(self).path_item_points_to(
                old(self).level,
                spt,
                old(self).path[old(self).level as usize - 1].unwrap(),
                child_pt,
            ),
        ensures
            self.level == old(self).level - 1,
            old(self).va == self.va,
            old(self).barrier_va == self.barrier_va,
            forall|i: int|
                0 <= i < old(self).path.len() && i != old(self).level as usize
                    - 2
                // path remains unchanged except the one being set
                 ==> self.path[i] == old(self).path[i],
            self.path[self.level as usize - 1].unwrap().paddr() as int == child_pt.paddr() as int,
            self.path[path_index_at_level(self.level)].unwrap().paddr() as int
                == child_pt.paddr() as int,
            self.path_wf(spt),
    {
        self.level = self.level - 1;

        // let old = self.path[self.level as usize - 1].replace(child_pt);
        let _ = self.path.set(self.level as usize - 1, Some(child_pt));
    }

    // fn cur_entry(&mut self) -> Entry<'_, C> {
    fn cur_entry(&self, spt: &exec::SubPageTable) -> (res: Entry<'_, C>)
        requires
            self.level > 0,
            self.level <= PagingConsts::NR_LEVELS_SPEC() as usize,
            self.path.len() >= self.level as usize,
            self.path[self.level as usize - 1].is_some(),
            spt.wf(),
            self.path_wf(spt),
        ensures
            res.node.wf(),
            res.pte.pte_paddr() == self.path[self.level as usize - 1].unwrap().paddr() as usize
                + pte_index::<C>(self.va, self.level) * exec::SIZEOF_PAGETABLEENTRY,
            res.pte.pte_paddr() == exec::get_pte_from_addr(res.pte.pte_paddr(), spt).pte_addr,
            res.pte.frame_paddr() == exec::get_pte_from_addr(res.pte.pte_paddr(), spt).frame_pa,
            res.idx == pte_index::<C>(self.va, self.level),
            res.idx < nr_subpage_per_huge::<C>(),
            res.pte.frame_paddr() == 0 ==> !spt.ptes@.value().contains_key(
                res.pte.pte_paddr() as int,
            ),
            res.pte.frame_paddr() != 0 ==> {
                &&& spt.ptes@.value().contains_key(res.pte.pte_paddr() as int)
                &&& spt.ptes@.value()[res.pte.pte_paddr() as int].frame_pa
                    == res.pte.frame_paddr() as int
                &&& spt.frames@.value().contains_key(res.pte.frame_paddr() as int)
            },
            res.pte.pte_paddr() == res.node.paddr() as int + pte_index::<C>(self.va, self.level)
                * exec::SIZEOF_PAGETABLEENTRY,
            self.path_wf(spt),
    {
        let cur_node = self.path[self.level as usize - 1].as_ref().unwrap();
        let res = Entry::new_at(cur_node, pte_index::<C>(self.va, self.level), spt);
        res
    }
}

/// The cursor of a page table that is capable of map, unmap or protect pages.
///
/// It has all the capabilities of a [`Cursor`], which can navigate over the
/// page table corresponding to the address range. A virtual address range
/// in a page table can only be accessed by one cursor, regardless of the
/// mutability of the cursor.
// #[derive(Debug)] // TODO: Implement `Debug` for `CursorMut`.
pub struct CursorMut<'a, C: PageTableConfig>(pub Cursor<'a, C>);

impl<'a, C: PageTableConfig> CursorMut<'a, C> {
    /// Creates a cursor claiming exclusive access over the given range.
    ///
    /// The cursor created will only be able to map, query or jump within the given
    /// range. Out-of-bound accesses will result in panics or errors as return values,
    /// depending on the access method.
    pub(super) fn new(pt: &'a PageTable<C>, va: &Range<Vaddr>) -> Result<Self, PageTableError> {
        Cursor::new(pt, va).map(|inner| Self(inner))
    }

    /// Gets the current virtual address.
    pub fn virt_addr(&self) -> Vaddr {
        self.0.virt_addr()
    }

    pub open spec fn path_valid_after_map(&self, old: &CursorMut<'a, C>) -> bool {
        &&& self.0.path.len() == old.0.path.len()
        &&& self.0.path.len() == PagingConsts::NR_LEVELS_SPEC()
        &&& self.0.path[0].is_some()  // frame.map_level?
        &&& self.0.path[old.0.level - 1] == old.0.path[old.0.level - 1]
        &&& forall|i: int| 1 < i <= old.0.level ==> #[trigger] self.0.path[i - 1].is_some()
    }

    pub open spec fn va_valid(&self, old: Option<&CursorMut<'a, C>>) -> bool {
        &&& self.0.va < MAX_USERSPACE_VADDR
        &&& self.0.va >= self.0.barrier_va.start
        &&& self.0.va + PAGE_SIZE() <= self.0.barrier_va.end
        &&& !old.is_none() ==> self.0.va == old.unwrap().0.va
    }

    /// Maps the range starting from the current address to a [`Frame<dyn AnyFrameMeta>`].
    ///
    /// It returns the previously mapped [`Frame<dyn AnyFrameMeta>`] if that exists.
    ///
    /// # Panics
    ///
    /// This function will panic if
    ///  - the virtual address range to be mapped is out of the range;
    ///  - the alignment of the page is not satisfied by the virtual address;
    ///  - it is already mapped to a huge page while the caller wants to map a smaller one.
    ///
    /// # Safety
    ///
    /// The caller should ensure that the virtual range being mapped does
    /// not affect kernel's memory safety.
    pub fn map(
        &mut self,
        frame: Frame,
        prop: PageProperty,
        // non ghost
        spt: &mut exec::SubPageTable,
        Tracked(alloc_model): Tracked<&mut AllocatorModel>,
    ) -> (res: Option<Frame>)
        requires
            old(spt).wf(),
            old(alloc_model).invariants(),
            old(self).va_valid(None),
            level_is_greater_than_one(old(self).0.level),
            old(self).0.path_wf(old(spt)),
            // page table validation
            old(self).0.sub_page_table_valid_before_map(old(spt)),
            spt_contains_no_unallocated_frames(old(spt), old(alloc_model)),
            // path
            old(self).0.path_matchs_page_table(
                old(spt),
                old(self).0.level,
                old(self).0.path[old(self).0.level as usize - 1].unwrap().paddr() as int,
                old(self).0.level,
            ),
        ensures
            self.path_valid_after_map(old(self)),
            spt.wf(),
            alloc_model.invariants(),
            // the post condition
            self.0.sub_page_table_valid_after_map(
                spt,
                &frame,
                old(self).0.level,
                old(self).0.path[old(self).0.level as usize - 1].unwrap().paddr() as int,
                frame.map_level(),
            ),
            spt_contains_no_unallocated_frames(spt, alloc_model),
    {
        let end = self.0.va + frame.size();
        let root_level = Tracked(self.0.level);
        let root_addr = self.0.path[self.0.level as usize - 1].as_ref().unwrap().paddr();

        #[verifier::loop_isolation(false)]
        // Go down if not applicable.
        while self.0.level
            > frame.map_level()
        // TODO || self.0.va % page_size::<C>(self.0.level) != 0 || self.0.va + page_size::<C>(self.0.level) > end

            invariant
        // self.0.va + page_size::<C>(self.0.level) <= end,

                self.0.level >= frame.map_level(),
                self.0.path.len() == old(self).0.path.len(),
                self.va_valid(Some(old(self))),
                forall|i: int|
                    path_index_at_level(self.0.level) <= i <= path_index_at_level(old(self).0.level)
                        ==> self.0.path[i].is_some(),
                self.0.path[path_index_at_level(root_level@)] == old(
                    self,
                ).0.path[path_index_at_level(root_level@)],
                root_level@ >= self.0.level,
                spt.wf(),
                alloc_model.invariants(),
                spt_contains_no_unallocated_frames(spt, alloc_model),
                forall|i: int|
                    path_index_at_level(self.0.level) <= i <= path_index_at_level(old(self).0.level)
                        ==> #[trigger] spt.frames@.value().contains_key(
                        self.0.path[i].unwrap().paddr() as int,
                    ),
                // the post condition
                self.0.sub_page_table_valid_before_map_level(
                    spt,
                    &frame,
                    root_level@,
                    /* root */
                    root_addr as int,
                    /* last level */
                    self.0.level,
                ),
                self.0.path_matchs_page_table(
                    spt,
                    root_level@,
                    /* root */
                    root_addr as int,
                    /* last level */
                    self.0.level,
                ),
                self.0.path_wf(spt),
            decreases self.0.level - frame.map_level(),
        {
            let cur_level = self.0.level;
            let cur_entry = self.0.cur_entry(spt);
            match cur_entry.to_ref(spt) {
                Child::PageTableRef(pt) => {
                    reveal_with_fuel(Cursor::sub_page_table_valid_before_map_level, 4);
                    reveal_with_fuel(Cursor::path_matchs_page_table, 4);
                    let child_pt = PageTableGuard::<C>::from_raw_paddr(pt, cur_level);
                    // SAFETY: `pt` points to a PT that is attached to a node
                    // in the locked sub-tree, so that it is locked and alive.
                    self.0.push_level(child_pt, root_level, spt);
                },
                Child::PageTable(_) => {
                    // unreachable!();
                    assert(false);
                },
                Child::None => {
                    assert(!spt.ptes@.value().contains_key(cur_entry.pte.pte_paddr() as int));

                    let pt = cur_entry.alloc_if_none(
                        self.0.level,
                        MapTrackingStatus::Tracked,
                        spt,
                        Tracked(alloc_model),
                    ).unwrap();

                    assert(spt.frames@.value().contains_key(pt as int));

                    let child_pt = PageTableGuard::<C>::from_raw_paddr(pt, cur_level);

                    assume(self.0.path_item_points_to(
                        self.0.level,
                        spt,
                        self.0.path[self.0.level as usize - 1].unwrap(),
                        child_pt,
                    ));
                    assume(self.0.path_wf(spt));

                    self.0.push_level(child_pt, root_level, spt);

                    // the post condition
                    assume(self.0.sub_page_table_valid_before_map_level(
                        spt,
                        &frame,
                        root_level@,
                        /* root */
                        root_addr as int,
                        /* last level */
                        self.0.level,
                    ));
                    assume(self.0.path_matchs_page_table(
                        spt,
                        root_level@,
                        /* root */
                        root_addr as int,
                        /* last level */
                        self.0.level,
                    ));
                },
                Child::Frame(_, _) => {
                    // panic!("Mapping a smaller frame in an already mapped huge page");
                    assert(false);
                },
                Child::Untracked(_, _, _) => {
                    // panic!("Mapping a tracked page in an untracked range");
                    assert(false);
                },
                Child::Token(_, _) => {
                    // let split_child = cur_entry.split_if_huge_token().unwrap();
                    // self.0.push_level(split_child);
                    assert(false);  // TODO: Token
                },
            }
            continue ;
        }
        assert(forall|i: int|
            1 < i <= old(self).0.level ==> #[trigger] self.0.path[i - 1].is_some());
        assert(self.0.level == frame.map_level());

        let cur_entry = self.0.cur_entry(spt);
        assume(cur_entry.idx < nr_subpage_per_huge::<C>() as usize);  // TODO
        assume(!spt.ptes@.value().contains_key(cur_entry.pte.pte_paddr() as int));  // TODO
        assume(cur_entry.pte.pte_paddr() == cur_entry.node.paddr() as int + pte_index::<C>(
            self.0.va,
            self.0.level,
        ) * exec::SIZEOF_PAGETABLEENTRY);

        // TODO: P0 Fix the last level frame in SubPageTableStateMachine and SubPageTable.
        // Map the current page.
        let old_entry = cur_entry.replace(
            Child::Frame(frame, prop),
            self.0.level,
            spt,
            Tracked(alloc_model),
        );
        assume(self.0.path_wf(spt));  // TODO: P0
        assume(self.0.level <= C::NR_LEVELS());
        self.0.move_forward(spt);

        // TODO: P0
        assume(self.0.sub_page_table_valid_after_map(
            spt,
            &frame,
            old(self).0.level,
            self.0.path[old(self).0.level as usize - 1].unwrap().paddr() as int,
            frame.map_level(),
        ));

        // TODO: P0
        assume(forall|i: int|
            path_index_at_level(self.0.level) <= i <= path_index_at_level(old(self).0.level)
                ==> #[trigger] spt.frames@.value().contains_key(
                self.0.path[i].unwrap().paddr() as int,
            ));

        match old_entry {
            Child::Frame(old_page, _) => Some(old_page),
            Child::None | Child::Token(_, _) => None,
            Child::PageTable(_) => {
                // todo!("Dropping page table nodes while mapping requires TLB flush")
                // assert(false); // TODO
                None
            },
            Child::Untracked(_, _, _) => {
                // panic!("Mapping a tracked page in an untracked range"),
                // assert(false); // TODO
                None
            }
            // Child::PageTableRef(_) => unreachable!(),
            ,
            Child::PageTableRef(_) => {
                // panic!("Mapping a page in a page table reference")
                // assert(false); // TODO
                None
            },
        }
    }

    /// Find and remove the first page in the cursor's following range.
    ///
    /// The range to be found in is the current virtual address with the
    /// provided length.
    ///
    /// The function stops and yields the page if it has actually removed a
    /// page, no matter if the following pages are also required to be unmapped.
    /// The returned page is the virtual page that existed before the removal
    /// but having just been unmapped.
    ///
    /// It also makes the cursor moves forward to the next page after the
    /// removed one, when an actual page is removed. If no mapped pages exist
    /// in the following range, the cursor will stop at the end of the range
    /// and return [`PageTableItem::NotMapped`].
    ///
    /// # Safety
    ///
    /// The caller should ensure that the range being unmapped does not affect
    /// kernel's memory safety.
    ///
    /// # Panics
    ///
    /// This function will panic if the end range covers a part of a huge page
    /// and the next page is that huge page.
    pub unsafe fn take_next(
        &mut self,
        len: usize,
        spt: &mut exec::SubPageTable,
        Tracked(alloc_model): Tracked<&mut AllocatorModel>,
    ) -> PageTableItem
        requires
            old(spt).wf(),
            old(self).va_valid(None),
            level_is_greater_than_one(old(self).0.level),
            old(self).0.va + len < MAX_USERSPACE_VADDR,
            old(self).0.level <= C::NR_LEVELS(),
            len % page_size::<C>(1) == 0,
            len > page_size::<C>(old(self).0.level),
            old(alloc_model).invariants(),
            spt_contains_no_unallocated_frames(old(spt), old(alloc_model)),
            old(self).0.path_wf(old(spt)),
    {
        let start = self.0.va;
        assert(len % page_size::<C>(1) == 0);
        let end = start + len;
        // assert!(end <= self.0.barrier_va.end); // TODO

        while self.0.va < end && self.0.level > 1
            invariant
                spt.wf(),
                self.0.level >= 1,
                self.0.level <= C::NR_LEVELS(),
                self.0.level <= PagingConsts::NR_LEVELS(),
                self.0.va + page_size::<C>(self.0.level) < end,
                self.0.va + len < MAX_USERSPACE_VADDR,
                alloc_model.invariants(),
                spt_contains_no_unallocated_frames(spt, alloc_model),
                self.0.path_wf(spt),
            decreases
                    end - self.0.va,
                    self.0.level,  // for push_level, only level decreases

        {
            let cur_va = self.0.va;
            let cur_level = self.0.level;
            let cur_entry = self.0.cur_entry(spt);

            // Skip if it is already absent.
            // if cur_entry.is_none(spt) {
            if !cur_entry.pte.is_present(spt) {
                if self.0.va + page_size::<C>(self.0.level) > end {
                    self.0.va = end;
                    break ;
                }
                self.0.move_forward(spt);
                assert(self.0.path_wf(spt));

                assume(self.0.va + page_size::<C>(self.0.level) < end);
                assume(self.0.va + len < MAX_USERSPACE_VADDR);
                continue ;
            }
            // Go down if not applicable.

            if cur_va % page_size::<C>(cur_level) != 0 || cur_va + page_size::<C>(cur_level) > end {
                assume(self.0.level > 1);  // TODO
                let child = cur_entry.to_ref(spt);
                match child {
                    Child::PageTableRef(pt) => {
                        // SAFETY: `pt` points to a PT that is attached to a node
                        // in the locked sub-tree, so that it is locked and alive.
                        let pt = PageTableGuard::<C>::from_raw_paddr(pt, cur_level);
                        // If there's no mapped PTEs in the next level, we can
                        // skip to save time.
                        if pt.nr_children() != 0 {
                            self.0.push_level(
                                pt,
                                Tracked(cur_level),
                                // ghost
                                spt,
                            );
                        } else {
                            let _ = pt.into_raw_paddr();
                            if self.0.va + page_size::<C>(self.0.level) > end {
                                self.0.va = end;
                                break ;
                            }
                            self.0.move_forward(spt);
                        }
                    },
                    Child::PageTable(_) => {
                        // unreachable!();
                        assert(false);
                    },
                    Child::None => {
                        // unreachable!("Already checked");
                        assert(false);
                    },
                    Child::Frame(_, _) => {
                        // panic!("Removing part of a huge page");
                        assert(false);
                    },
                    Child::Untracked(_, _, _) => {
                        // let split_child = cur_entry.split_if_untracked_huge().unwrap();
                        // self.0.push_level(split_child, cur_level, spt);
                        assert(false);
                    },
                    Child::Token(_, _) => {
                        // let split_child = cur_entry.split_if_huge_status().unwrap();
                        // self.0.push_level(split_child, cur_level, spt);
                        assert(false);
                    },
                }

                assume(self.0.va + page_size::<C>(self.0.level) < end);
                assume(self.0.va + len < MAX_USERSPACE_VADDR);
                continue ;
            }
            // Unmap the current page and return it.

            let old = cur_entry.replace(Child::None, cur_level, spt, Tracked(alloc_model));
            let item = match old {
                Child::Frame(page, prop) => PageTableItem::Mapped { va: self.0.va, page, prop },
                Child::Untracked(pa, level, prop) => {
                    // debug_assert_eq!(level, self.0.level); // TODO
                    assume(level == self.0.level);
                    PageTableItem::MappedUntracked {
                        va: self.0.va,
                        pa,
                        len: page_size::<C>(level),
                        prop,
                    }
                },
                Child::Token(status, _) => PageTableItem::Marked {
                    va: self.0.va,
                    len: page_size::<C>(self.0.level),
                    token: status,
                },
                Child::PageTable(pt) => {
                    let paddr = pt.into_raw();
                    // SAFETY: We must have locked this node.
                    let locked_pt = PageTableGuard::<C>::from_raw_paddr(paddr, cur_level);
                    // assert!(
                    //     !(TypeId::of::<M>() == TypeId::of::<KernelMode>()
                    //         && self.0.level == C::NR_LEVELS()),
                    //     "Unmapping shared kernel page table nodes"
                    // ); // TODO
                    // SAFETY:
                    //  - We checked that we are not unmapping shared kernel page table nodes.
                    //  - We must have locked the entire sub-tree since the range is locked.
                    let unlocked_pt = locking::dfs_mark_astray(locked_pt);
                    // See `locking.rs` for why we need this. // TODO: I don't have time to see, so if you see this, please see.
                    // let drop_after_grace = unlocked_pt.clone();
                    // crate::sync::after_grace_period(|| {
                    //     drop(drop_after_grace);
                    // });
                    PageTableItem::StrayPageTable {
                        // pt: unlocked_pt.into(),
                        pt: Frame { ptr: unlocked_pt.paddr() },
                        va: self.0.va,
                        len: page_size::<C>(self.0.level),
                    }
                },
                Child::None | Child::PageTableRef(_) => { PageTableItem::NotMapped { va: 0, len: 0 }
                },
            };

            assume(self.0.va + page_size::<C>(self.0.level) < MAX_USERSPACE_VADDR);
            assume(self.0.path_wf(spt));  // TODO: P0
            self.0.move_forward(spt);

            return item;
        }

        // If the loop exits, we did not find any mapped pages in the range.
        PageTableItem::NotMapped { va: start, len }
    }
}

} // verus!
