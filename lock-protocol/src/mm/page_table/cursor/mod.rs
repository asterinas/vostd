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
        child::Child, entry::Entry, frame, meta::AnyFrameMeta, node::PageTableNode,
        nr_subpage_per_huge, page_prop::PageProperty, page_size, vm_space::Token, Frame,
        MapTrackingStatus, Paddr, PageTableLockTrait, Vaddr, MAX_USERSPACE_VADDR, PAGE_SIZE,
    },
    task::DisabledPreemptGuard,
    x86_64::VMALLOC_VADDR_RANGE,
};

use super::{
    pte_index, KernelMode, PageTable, PageTableEntryTrait, PageTableError, PageTableMode,
    PagingConsts, PagingConstsTrait, PagingLevel, UserMode,
};

use crate::spec::simple_page_table;
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
pub struct Cursor<
    'a,
    M: PageTableMode,
    E: PageTableEntryTrait,
    C: PagingConstsTrait,
    PTL: PageTableLockTrait<E, C>,
> {
    /// The current path of the cursor.
    ///
    /// The level 1 page table lock guard is at index 0, and the level N page
    /// table lock guard is at index N - 1.
    // path: [Option<PageTableLock<E, C, T>>; MAX_NR_LEVELS],
    pub path: Vec<Option<PTL>>,
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
    // _phantom: PhantomData<&'a PageTable<M, E, C>>,
    pub _phantom: PhantomData<&'a PageTable<M, E, C>>,
}

/// The maximum value of `PagingConstsTrait::NR_LEVELS`.
const MAX_NR_LEVELS: usize = 4;

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

impl<
    'a,
    M: PageTableMode,
    E: PageTableEntryTrait,
    C: PagingConstsTrait,
    PTL: PageTableLockTrait<E, C>,
> Cursor<'a, M, E, C, PTL> {
    pub open spec fn mock_page_table_valid_before_map(
        &self,
        mock_page_table: &exec::MockPageTable,
    ) -> bool {
        &&& mock_page_table.wf()
        &&& mock_page_table.frames@.value().contains_key(
            self.path[path_index_at_level(self.level)].unwrap().paddr() as int,
        )
    }

    pub open spec fn mock_page_table_valid_after_map(
        &self,
        mock_page_table: &exec::MockPageTable,
        frame: &Frame,
        level: u8,
        root: int,
        last_level: u8,
    ) -> bool
        decreases level,
    {
        &&& mock_page_table.wf()
        &&& mock_page_table.frames@.value().contains_key(root)
        &&& level > last_level ==> {
            &&& mock_page_table.ptes@.value().contains_key(
                root + pte_index(self.va, level) * exec::SIZEOF_PAGETABLEENTRY as int,
            )
            &&& self.mock_page_table_valid_after_map(
                mock_page_table,
                frame,
                (level - 1) as u8,
                mock_page_table.ptes@.value()[root + pte_index(self.va, level)
                    * exec::SIZEOF_PAGETABLEENTRY as int].frame_pa,
                last_level,
            )
        }
        &&& level == last_level ==> {
            &&& last_level == frame.map_level() ==> {
                &&& mock_page_table.ptes@.value().contains_key(
                    root + pte_index(self.va, level) * exec::SIZEOF_PAGETABLEENTRY as int,
                )
                &&& mock_page_table.ptes@.value()[root + pte_index(self.va, level)
                    * exec::SIZEOF_PAGETABLEENTRY as int].frame_pa == frame.start_paddr() as int
            }
        }
    }

    pub open spec fn mock_page_table_valid_before_map_level(
        &self,
        mock_page_table: &exec::MockPageTable,
        frame: &Frame,
        level: u8,
        root: int,
        last_level: u8,
    ) -> bool
        decreases level,
    {
        &&& mock_page_table.wf()
        &&& mock_page_table.frames@.value().contains_key(root)
        &&& level > last_level ==> {
            &&& mock_page_table.ptes@.value().contains_key(
                root + pte_index(self.va, level) * exec::SIZEOF_PAGETABLEENTRY as int,
            )
            &&& self.mock_page_table_valid_before_map_level(
                mock_page_table,
                frame,
                (level - 1) as u8,
                mock_page_table.ptes@.value()[root + pte_index(self.va, level)
                    * exec::SIZEOF_PAGETABLEENTRY as int].frame_pa,
                last_level,
            )
        }
    }

    // TODO: do we need a path model?
    pub open spec fn path_matchs_page_table(
        &self,
        mock_page_table: &exec::MockPageTable,
        level: u8,
        root: int,
        last_level: u8,
    ) -> bool
        decreases level,
    {
        &&& self.path[path_index_at_level(level)].is_some()
        &&& self.path[path_index_at_level(level)].unwrap().paddr() as int == root
        &&& level > last_level ==> {
            &&& mock_page_table.ptes@.value().contains_key(
                root + pte_index(self.va, level) * exec::SIZEOF_PAGETABLEENTRY as int,
            )
            &&& self.path_matchs_page_table(
                mock_page_table,
                (level - 1) as u8,
                mock_page_table.ptes@.value()[root + pte_index(self.va, level)
                    * exec::SIZEOF_PAGETABLEENTRY as int].frame_pa,
                last_level,
            )
        }
    }

    /// Creates a cursor claiming exclusive access over the given range.
    ///
    /// The cursor created will only be able to query or jump within the given
    /// range. Out-of-bound accesses will result in panics or errors as return values,
    /// depending on the access method.
    pub fn new(pt: &'a PageTable<M, E, C>, va: &Range<Vaddr>) -> Result<Self, PageTableError> {
        if !M::covers(va)
        // || va.is_empty()
         || !(va.start < va.end) {
            return Err(PageTableError::InvalidVaddrRange(va.start, va.end));
        }
        if va.start % C::BASE_PAGE_SIZE() != 0 || va.end % C::BASE_PAGE_SIZE() != 0 {
            return Err(PageTableError::UnalignedVaddr);
        }  // const { assert!(C::NR_LEVELS() as usize <= MAX_NR_LEVELS) };
        // TODO

        let new_pt_is_tracked = if should_map_as_tracked::<M>(va.start) {
            MapTrackingStatus::Tracked
        } else {
            MapTrackingStatus::Untracked
        };
        Ok(locking::lock_range(pt, va, new_pt_is_tracked))
    }

    /// Traverses forward in the current level to the next PTE.
    ///
    /// If reached the end of a page table node, it leads itself up to the next page of the parent
    /// page if possible.
    pub(in crate::mm) fn move_forward(&mut self)
        requires
            old(self).va < MAX_USERSPACE_VADDR,
        ensures
            self.path == old(self).path,
            self.path.len() == old(self).path.len(),
            self.level == old(self).level,
            self.va == old(self).va,
    {
        // let page_size = page_size::<C>(self.level);
        // // let next_va = self.va.align_down(page_size) + page_size;
        // let next_va = align_down(self.va, page_size) + page_size;
        // while self.level < self.guard_level && pte_index(next_va, self.level) == 0 {
        //     self.pop_level();
        // }
        // self.va = next_va;
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
    {
        // let Some(taken) = self.path[self.level as usize - 1].take() else {
        //     panic!("Popping a level without a lock");
        // };
        let taken = &self.path[self.level as usize - 1];
        if (taken.is_none()) {
            // panic!("Popping a level without a lock");
            // assert(false); // TODO
        }  // let _taken = taken.unwrap().into_raw_paddr();
        // TODO

        self.level = self.level + 1;
    }

    /// Goes down a level to a child page table.
    fn push_level(
        &mut self,
        child_pt: PTL,
        old_level: Tracked<PagingLevel>,
        // ghost
        mpt: &exec::MockPageTable,
    )
        requires
            old(self).level > 1,
            old(self).path.len() >= old(self).level as usize,
            old(self).path[old(self).level as usize - 1].is_some(),
            old_level@ >= old(self).level,
        ensures
            self.level == old(self).level - 1,
            self.path.len() == old(self).path.len(),
            self.path[old(self).level as usize - 1].is_some(),
            self.path[old(self).level as usize - 2].is_some(),
            old(self).va == self.va,
            old(self).barrier_va == self.barrier_va,
            old(self).path.len() == self.path.len(),
            old(self).path@.len() == self.path@.len(),
            old(self).path[old(self).level as usize - 1] == self.path[old(self).level as usize - 1],
            forall|i: int|
                0 <= i < old(self).path.len() && i != old(self).level as usize
                    - 2
                // path remains unchanged except the one being set
                 ==> self.path[i] == old(self).path[i],
            self.path[old(self).level as usize - 1] == old(self).path[old(self).level as usize - 1],
            self.path@[old(self).level as usize - 1] == old(self).path@[old(self).level as usize
                - 1],
            self.path[old(self).level as usize - 2] == Some(child_pt),
            self.path.len() >= old_level@ ==> self.path[old_level@ as usize - 1] == old(
                self,
            ).path[old_level@ as usize - 1],
            self.path[self.level as usize - 1] == Some(child_pt),
            self.path[self.level as usize - 1].unwrap().paddr() as int == child_pt.paddr() as int,
            self.path[path_index_at_level(self.level)].unwrap().paddr() as int
                == child_pt.paddr() as int,
    {
        self.level = self.level - 1;
        // debug_assert_eq!(self.level, child_pt.level()); // TODO: assert

        // let old = self.path[self.level as usize - 1].replace(child_pt);
        let old = self.path.set(self.level as usize - 1, Some(child_pt));
    }

    // fn cur_entry(&mut self) -> Entry<'_, E, C> {
    fn cur_entry(&self, mpt: &exec::MockPageTable) -> (res: Entry<'_, E, C, PTL>)
        requires
            self.level > 0,
            self.level <= PagingConsts::NR_LEVELS_SPEC() as usize,
            self.path.len() >= self.level as usize,
            self.path[self.level as usize - 1].is_some(),
            mpt.wf(),
    // mock_page_table.frames@.value().contains_key(self.path[self.level as usize - 1].unwrap().paddr() as int),

        ensures
            res.pte.pte_paddr() == self.path[self.level as usize - 1].unwrap().paddr() as usize
                + pte_index(self.va, self.level) * exec::SIZEOF_PAGETABLEENTRY,
            res.pte.pte_paddr() == exec::get_pte_from_addr(res.pte.pte_paddr(), mpt).pte_addr,
            res.pte.frame_paddr() == exec::get_pte_from_addr(res.pte.pte_paddr(), mpt).frame_pa,
            res.idx == pte_index(self.va, self.level),
            res.idx < nr_subpage_per_huge(),
            res.pte.frame_paddr() == 0 ==> !mpt.ptes@.value().contains_key(
                res.pte.pte_paddr() as int,
            ),
            res.pte.frame_paddr() != 0 ==> {
                &&& mpt.ptes@.value().contains_key(res.pte.pte_paddr() as int)
                &&& mpt.ptes@.value()[res.pte.pte_paddr() as int].frame_pa
                    == res.pte.frame_paddr() as int
                &&& mpt.frames@.value().contains_key(res.pte.frame_paddr() as int)
            },
    {
        // let node = self.path[self.level as usize - 1].as_mut().unwrap();
        // node.entry(pte_index::<C>(self.va, self.level))
        let cur_node = self.path[self.level as usize - 1].as_ref().unwrap();  // current node
        // node.entry(pte_index(self.va, self.level))
        let res = Entry::new_at(cur_node, pte_index(self.va, self.level), mpt);
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
pub struct CursorMut<
    'a,
    M: PageTableMode,
    E: PageTableEntryTrait,
    C: PagingConstsTrait,
    PTL: PageTableLockTrait<E, C>,
>(pub Cursor<'a, M, E, C, PTL>);

impl<
    'a,
    M: PageTableMode,
    E: PageTableEntryTrait,
    C: PagingConstsTrait,
    PTL: PageTableLockTrait<E, C>,
> CursorMut<'a, M, E, C, PTL> {
    /// Creates a cursor claiming exclusive access over the given range.
    ///
    /// The cursor created will only be able to map, query or jump within the given
    /// range. Out-of-bound accesses will result in panics or errors as return values,
    /// depending on the access method.
    pub(super) fn new(pt: &'a PageTable<M, E, C>, va: &Range<Vaddr>) -> Result<
        Self,
        PageTableError,
    > {
        Cursor::new(pt, va).map(|inner| Self(inner))
    }

    /// Gets the current virtual address.
    pub fn virt_addr(&self) -> Vaddr {
        self.0.virt_addr()
    }

    pub open spec fn path_valid_before_map(&self) -> bool {
        &&& self.0.path.len() >= self.0.level
        &&& self.0.path.len() == PagingConsts::NR_LEVELS_SPEC()
        &&& self.0.path[self.0.level - 1].is_some()
    }

    pub open spec fn path_valid_after_map(&self, old: &CursorMut<'a, M, E, C, PTL>) -> bool {
        &&& self.0.path.len() == old.0.path.len()
        &&& self.0.path.len() == PagingConsts::NR_LEVELS_SPEC()
        &&& self.0.path[self.0.level - 1].is_some()
        &&& self.0.path[old.0.level - 1] == old.0.path[old.0.level - 1]
        &&& forall|i: int| 1 < i <= old.0.level ==> #[trigger] self.0.path[i - 1].is_some()
    }

    pub open spec fn va_valid(
        &self,
        frame: Frame,
        old: Option<&CursorMut<'a, M, E, C, PTL>>,
    ) -> bool {
        &&& self.0.va < MAX_USERSPACE_VADDR
        &&& self.0.va >= self.0.barrier_va.start
        &&& self.0.va + frame.size() <= self.0.barrier_va.end
        &&& !old.is_none() ==> self.0.va == old.unwrap().0.va
    }

    pub open spec fn path_wf(&self, mock_page_table: &exec::MockPageTable) -> bool {
        &&& forall|i: int, j: int|
            1 <= i < j < self.0.path.len() ==> 0 < (j - 1) < PagingConsts::NR_LEVELS_SPEC()
                && #[trigger] self.0.path[i].is_some() ==> self.0.path[j].is_some()
                && exec::get_pte_from_addr(
                (#[trigger] self.0.path[j].unwrap().paddr() + pte_index(self.0.va, (j + 1) as u8)
                    * exec::SIZEOF_PAGETABLEENTRY) as usize,
                mock_page_table,
            ).frame_paddr() == self.0.path[i].unwrap().paddr()
        &&& forall|i: int|
            1 <= i < self.0.path.len() && self.0.path[i].is_some()
                ==> mock_page_table.frames@.value().contains_key(
                (#[trigger] self.0.path[i].unwrap().paddr() as int),
            )
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
        // ghost
        tokens: Tracked<exec::Tokens>,
        // non ghost
        mpt: &mut exec::MockPageTable,
        cur_alloc_index: &mut usize,
    ) -> (res: Option<Frame>)
        requires
            instance_match(old(mpt), tokens@),
            // cursor validation
            old(self).va_valid(frame, None),
            level_is_greate_than_one(old(self).0.level),
            old(self).path_valid_before_map(),
            old(self).path_wf(old(mpt)),
            *old(cur_alloc_index) < exec::MAX_FRAME_NUM - 4,  // we have enough frames
            // page table validation
            old(self).0.mock_page_table_valid_before_map(old(mpt)),
            mpt_and_tokens_wf(old(mpt), tokens@),
            mpt_not_contains_not_allocated_frames(old(mpt), *old(cur_alloc_index)),
            unallocated_frames_are_unused(
                tokens@.unused_addrs,
                tokens@.unused_pte_addrs,
                *old(cur_alloc_index),
            ),
            tokens_wf(tokens@.unused_addrs, tokens@.unused_pte_addrs),
            // path
            old(self).0.path_matchs_page_table(
                old(mpt),
                old(self).0.level,
                old(self).0.path[old(self).0.level as usize - 1].unwrap().paddr() as int,
                old(self).0.level,
            ),
        ensures
            self.path_valid_after_map(old(self)),
            instance_match(old(mpt), tokens@),
            mpt.wf(),
            *cur_alloc_index < exec::MAX_FRAME_NUM,
            // the post condition
            self.0.mock_page_table_valid_after_map(
                mpt,
                &frame,
                old(self).0.level,
                old(self).0.path[old(self).0.level as usize - 1].unwrap().paddr() as int,
                frame.map_level(),
            ),
    {
        let end = self.0.va + frame.size();
        let root_level = Tracked(self.0.level);
        let root_addr = self.0.path[self.0.level as usize - 1].as_ref().unwrap().paddr();

        let tracked exec::Tokens {
            unused_addrs: mut unused_addrs,
            unused_pte_addrs: mut unused_pte_addrs,
        } = tokens.get();  // TODO: can we just use the tokens inside the loop?

        #[verifier::loop_isolation(false)]
        // Go down if not applicable.
        while self.0.level
            > frame.map_level()   // || self.0.va % page_size::<C>(self.0.level) != 0
        // TODO?
        // || self.0.va + page_size::<C>(self.0.level) > end // TODO?

            invariant
        // self.0.va + page_size::<C>(self.0.level) <= end,

                self.0.level >= frame.map_level(),
                self.0.path.len() == old(self).0.path.len(),
                self.va_valid(frame, Some(old(self))),
                forall|i: int|
                    path_index_at_level(self.0.level) <= i <= path_index_at_level(old(self).0.level)
                        ==> self.0.path[i].is_some(),
                self.0.path[path_index_at_level(root_level@)] == old(
                    self,
                ).0.path[path_index_at_level(root_level@)],
                root_level@ >= self.0.level,
                mpt.wf(),
                *cur_alloc_index < exec::MAX_FRAME_NUM - 4,  // we have enough frames
                instance_match_addrs(mpt, unused_addrs, unused_pte_addrs),
                forall|i: int|
                    path_index_at_level(self.0.level) <= i <= path_index_at_level(old(self).0.level)
                        ==> #[trigger] mpt.frames@.value().contains_key(
                        self.0.path[i].unwrap().paddr() as int,
                    ),
                mpt_not_contains_not_allocated_frames(mpt, *cur_alloc_index),
                unallocated_frames_are_unused(unused_addrs, unused_pte_addrs, *cur_alloc_index),
                tokens_wf(unused_addrs, unused_pte_addrs),
                // the post condition
                self.0.mock_page_table_valid_before_map_level(
                    mpt,
                    &frame,
                    root_level@,
                    /* root */
                    root_addr as int,
                    /* last level */
                    self.0.level,
                ),
                self.0.path_matchs_page_table(
                    mpt,
                    root_level@,
                    /* root */
                    root_addr as int,
                    /* last level */
                    self.0.level,
                ),
            decreases self.0.level - frame.map_level(),
        {
            // debug_assert!(should_map_as_tracked::<M>(self.0.va)); // TODO
            let cur_level = self.0.level;
            let cur_entry = self.0.cur_entry(mpt);
            match cur_entry.to_ref(mpt) {
                Child::PageTableRef(pt) => {
                    assert(mpt.frames@.value().contains_key(pt as int));
                    assert(cur_entry.pte.frame_paddr() == pt);
                    assert(cur_entry.pte.frame_paddr() != 0);
                    reveal_with_fuel(Cursor::mock_page_table_valid_before_map_level, 4);
                    reveal_with_fuel(Cursor::path_matchs_page_table, 4);
                    assert(self.0.mock_page_table_valid_before_map_level(
                        mpt,
                        &frame,
                        root_level@,
                        root_addr as int,
                        self.0.level,
                    ));
                    assert(self.0.mock_page_table_valid_before_map_level(
                        mpt,
                        &frame,
                        root_level@,
                        root_addr as int,
                        (self.0.level - 1) as u8,
                    ));
                    // SAFETY: `pt` points to a PT that is attached to a node
                    // in the locked sub-tree, so that it is locked and alive.
                    self.0.push_level(
                    // unsafe { PageTableLock::from_raw_paddr(pt) }

                        PTL::from_raw_paddr(pt),
                        root_level,
                        // ghost
                        mpt,
                    );
                    assert(self.0.va == old(self).0.va);
                    assert(self.0.path@.len() == old(self).0.path@.len());
                    assert(self.0.path[cur_level - 2].is_some());
                    assert(self.0.path[old(self).0.level - 1].is_some());
                    assert(self.0.path[root_level@ - 1] == old(self).0.path[root_level@ - 1]);

                    assert(mpt_not_contains_not_allocated_frames(mpt, *cur_alloc_index));
                    assert(forall|i: int|
                        path_index_at_level(self.0.level) <= i <= path_index_at_level(root_level@)
                            ==> #[trigger] mpt.frames@.value().contains_key(
                            self.0.path[i].unwrap().paddr() as int,
                        ));
                    assert(self.0.mock_page_table_valid_before_map_level(
                        mpt,
                        &frame,
                        old(self).0.level,
                        self.0.path[path_index_at_level(old(self).0.level)].unwrap().paddr() as int,
                        self.0.level,
                    ));
                    assert(self.0.path_matchs_page_table(
                        mpt,
                        old(self).0.level,
                        /* root */
                        self.0.path[old(self).0.level as usize - 1].unwrap().paddr() as int,
                        /* last level */
                        self.0.level,
                    ));
                },
                Child::PageTable(_) => {
                    // unreachable!();
                    assert(false);
                },
                Child::None => {
                    assert(!mpt.ptes@.value().contains_key(cur_entry.pte.pte_paddr() as int));
                    assert(cur_entry.pte.frame_paddr() == 0);
                    assert(mpt_not_contains_not_allocated_frames(mpt, *cur_alloc_index));

                    let preempt_guard = crate::task::disable_preempt();  // currently nothing happen

                    let used_addr = exec::frame_index_to_addr(*cur_alloc_index);
                    let tracked used_addr_token = unused_addrs.tracked_remove(used_addr as int);
                    assert(used_addr_token.instance_id() == mpt.instance@.id());
                    // before_alloc
                    {
                        assert(used_addr_token.element() == used_addr as int);  // ensured by token_wf
                        assert(!mpt.frames@.value().contains_key(used_addr as int));  // ensured by unallocated_frames_are_unused
                        assert(mpt.mem@[*cur_alloc_index].1@.mem_contents() == MemContents::<
                            exec::SimpleFrame,
                        >::Uninit);
                        assert(forall|i: int|
                            0 <= i < NR_ENTRIES ==> !(#[trigger] mpt.ptes@.value().dom().contains(
                                used_addr + i * exec::SIZEOF_PAGETABLEENTRY,
                            )));
                        assert(forall|i: int|
                            0 <= i < NR_ENTRIES ==> !#[trigger] mpt.ptes@.value().contains_key(
                                used_addr + i * exec::SIZEOF_PAGETABLEENTRY as int,
                            ));
                        assert(forall|i: int| #[trigger]
                            mpt.ptes@.value().contains_key(i) ==> (mpt.ptes@.value()[i]).frame_pa
                                != used_addr);
                    }
                    let pt = PTL::alloc(
                        cur_level - 1,
                        MapTrackingStatus::Tracked,
                        mpt,
                        *cur_alloc_index,
                        used_addr,
                        Tracked(used_addr_token),  // TODO: can we pass all the tokens directly?
                    );  // alloc frame here
                    let ghost_index = *cur_alloc_index + 1;
                    assert(unallocated_frames_are_unused(
                        unused_addrs,
                        unused_pte_addrs,
                        ghost_index,
                    ));  // TODO: P0

                    let paddr = pt.into_raw_paddr();

                    assert(!mpt.ptes@.value().contains_key(cur_entry.pte.pte_paddr() as int));
                    assert(mpt.wf());
                    assume(cur_entry.pte.pte_paddr() == cur_entry.node.paddr() as int + pte_index(
                        self.0.va,
                        cur_level,
                    ) * exec::SIZEOF_PAGETABLEENTRY);
                    reveal(spec_helpers::frame_keys_do_not_change);
                    assume(unused_pte_addrs.contains_key(cur_entry.pte.pte_paddr() as int));  // TODO: P0 need more wf
                    let tracked used_pte_addr_token = unused_pte_addrs.tracked_remove(
                        cur_entry.pte.pte_paddr() as int,
                    );
                    // SAFETY: It was forgotten at the above line.
                    let _ = cur_entry.replace(
                        Child::<E, C>::PageTable(
                        // unsafe { PageTableNode::from_raw(paddr) }
                        PageTableNode::from_raw(paddr)),
                        mpt,
                        self.0.level,
                        ghost_index,
                        Tracked(used_pte_addr_token),
                    );  // alloc pte here
                    // SAFETY: `pt` points to a PT that is attached to a node
                    // in the locked sub-tree, so that it is locked and alive.
                    self.0.push_level(
                    // unsafe { PageTableLock::from_raw_paddr(paddr) }
                    PTL::from_raw_paddr(paddr), root_level, mpt);

                    *cur_alloc_index += 1;  // TODO: do it inside the alloc function
                    assume(unallocated_frames_are_unused(
                        unused_addrs,
                        unused_pte_addrs,
                        *cur_alloc_index,
                    ));  // TODO: P0
                    assume(*cur_alloc_index < exec::MAX_FRAME_NUM - 4);  // TODO

                    // TODO: P0 see @path_matchs_page_table
                    assume(self.0.mock_page_table_valid_before_map_level(
                        mpt,
                        &frame,
                        old(self).0.level,
                        self.0.path[old(self).0.level as usize - 1].unwrap().paddr() as int,
                        self.0.level,
                    ));
                    assume(self.0.path_matchs_page_table(
                        mpt,
                        old(self).0.level,
                        /* root */
                        self.0.path[old(self).0.level as usize - 1].unwrap().paddr() as int,
                        /* last level */
                        self.0.level,
                    ));
                    // TODO: P0: mpt wf here
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
            assert(self.0.level == cur_level - 1);
            assert(self.0.path[cur_level - 1].is_some());
            assert(self.0.path[self.0.level as usize - 1].is_some());
            continue ;
        }
        assert(forall|i: int|
            1 < i <= old(self).0.level ==> #[trigger] self.0.path[i - 1].is_some());
        assert(self.0.level == frame.map_level());

        let cur_entry = self.0.cur_entry(mpt);
        assume(cur_entry.idx < nr_subpage_per_huge() as usize);  // TODO
        assume(!mpt.ptes@.value().contains_key(cur_entry.pte.pte_paddr() as int));  // TODO
        assume(unused_pte_addrs.contains_key(cur_entry.pte.pte_paddr() as int));  // TODO: P0 need more wf
        assume(cur_entry.pte.pte_paddr() == cur_entry.node.paddr() as int + pte_index(
            self.0.va,
            self.0.level,
        ) * exec::SIZEOF_PAGETABLEENTRY);
        let tracked used_pte_addr_token = unused_pte_addrs.tracked_remove(
            cur_entry.pte.pte_paddr() as int,
        );

        // TODO: P0 Fix the last level frame in SimplePageTable and MockPageTable.
        // Map the current page.
        let old_entry = cur_entry.replace(
            Child::Frame(frame, prop),
            mpt,
            self.0.level,
            *cur_alloc_index,
            Tracked(used_pte_addr_token),
        );
        self.0.move_forward();

        // TODO: P0
        assume(self.0.mock_page_table_valid_after_map(
            mpt,
            &frame,
            old(self).0.level,
            self.0.path[old(self).0.level as usize - 1].unwrap().paddr() as int,
            frame.map_level(),
        ));

        // TODO: P0
        assume(forall|i: int|
            path_index_at_level(self.0.level) <= i <= path_index_at_level(old(self).0.level)
                ==> #[trigger] mpt.frames@.value().contains_key(
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
    #[verifier::external_body]
    pub unsafe fn take_next(
        &mut self,
        len: usize,
        // ghost
        tokens: Tracked<exec::Tokens>,
        // non ghost, but it should be
        mpt: &mut exec::MockPageTable,
    ) -> PageTableItem {
        let start = self.0.va;
        // assert!(len % page_size::<C>(1) == 0); // TODO
        let end = start + len;
        // assert!(end <= self.0.barrier_va.end); // TODO

        let tracked exec::Tokens {
            unused_addrs: mut unused_addrs,
            unused_pte_addrs: mut unused_pte_addrs,
        } = tokens.get();  // TODO: can we just use the tokens inside the loop?

        while self.0.va < end {
            let cur_va = self.0.va;
            let cur_level = self.0.level;
            let cur_entry = self.0.cur_entry(mpt);

            // Skip if it is already absent.
            // if cur_entry.is_none(mpt) { // TODO: is_none
            if !cur_entry.pte.is_present(mpt) {
                if self.0.va + page_size::<C>(self.0.level) > end {
                    self.0.va = end;
                    break ;
                }
                self.0.move_forward();
                continue ;
            }
            // Go down if not applicable.

            if cur_va % page_size::<C>(cur_level) != 0 || cur_va + page_size::<C>(cur_level) > end {
                let child = cur_entry.to_ref(mpt);
                match child {
                    Child::PageTableRef(pt) => {
                        // SAFETY: `pt` points to a PT that is attached to a node
                        // in the locked sub-tree, so that it is locked and alive.
                        // let pt = unsafe { PageTableLock::<E, C>::from_raw_paddr(pt) };
                        let pt = unsafe { PTL::from_raw_paddr(pt) };
                        // If there's no mapped PTEs in the next level, we can
                        // skip to save time.
                        if pt.nr_children() != 0 {
                            self.0.push_level(
                                pt,
                                Tracked(cur_level),
                                // ghost
                                mpt,
                            );
                        } else {
                            let _ = pt.into_raw_paddr();
                            if self.0.va + page_size::<C>(self.0.level) > end {
                                self.0.va = end;
                                break ;
                            }
                            self.0.move_forward();
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
                        // self.0.push_level(split_child, cur_level, mpt);
                        assert(false);
                    }
                    // Child::Status(_) => {
                    ,
                    Child::Token(_, _) => {
                        // let split_child = cur_entry.split_if_huge_status().unwrap();
                        // self.0.push_level(split_child, cur_level, mpt);
                        assert(false);
                    },
                }
                continue ;
            }
            let tracked used_pte_addr_token: simple_page_table::SimplePageTable::unused_pte_addrs;
            proof {
                used_pte_addr_token =
                unused_pte_addrs.tracked_remove(unused_pte_addrs.dom().choose());
            }
            // Unmap the current page and return it.
            let old = cur_entry.replace(
                Child::None,
                mpt,
                cur_level,
                exec::MAX_FRAME_NUM,
                Tracked(used_pte_addr_token),
            );
            let item = match old {
                Child::Frame(page, prop) => PageTableItem::Mapped { va: self.0.va, page, prop },
                Child::Untracked(pa, level, prop) => {
                    // debug_assert_eq!(level, self.0.level); // TODO
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
                    let locked_pt = PTL::from_raw_paddr(paddr);
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
                Child::None | Child::PageTableRef(_) => {
                    // unreachable!();
                    assert(false);
                    PageTableItem::NotMapped { va: 0, len: 0 }
                },
            };

            self.0.move_forward();

            return item;
        }

        // If the loop exits, we did not find any mapped pages in the range.
        PageTableItem::NotMapped { va: start, len }
    }
}

fn should_map_as_tracked<M: PageTableMode>(va: Vaddr) -> bool {
    // TODO: Check if the type is `KernelMode` or `UserMode`.
    // (TypeId::of::<M>() == TypeId::of::<KernelMode>()
    //     || TypeId::of::<M>() == TypeId::of::<UserMode>())
    //     &&
    crate::x86_64::kspace::should_map_as_tracked(va)
}

} // verus!
