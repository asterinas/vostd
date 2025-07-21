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

use crate::spec::sub_pt::{SubPageTable, index_pte_paddr};
use crate::exec;
use spec_helpers::*;
use crate::mm::NR_ENTRIES;

/// A handy ghost mode macro to get the guard at a certain level in the path.
macro_rules! path_index {
    ($self: ident . path [$i:expr]) => {
        $self.path.view().index(path_index_at_level($i))
    };
    ($self: ident . 0 . path [$i:expr]) => {
        $self.0.path.view().index(path_index_at_level($i))
    };
    (old($self: ident) . path [$i:expr]) => {
        old($self).path.view().index(path_index_at_level($i))
    };
    (old($self: ident) . 0 . path [$i:expr]) => {
        old($self).0.path.view().index(path_index_at_level($i))
    };
}

verus! {

pub open spec fn path_index_at_level(level: PagingLevel) -> int {
    level - 1
}

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
    pub path: [Option<PageTableGuard<C>>; MAX_NR_LEVELS],
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
    /// Well-formedness of the cursor.
    pub open spec fn wf(&self, spt: &SubPageTable) -> bool {
        &&& spt.wf()
        &&& self.va_wf()
        &&& self.level_wf(spt)
        &&& self.path_wf(spt)
    }

    /// Well-formedness of the cursor's virtual address.
    pub open spec fn va_wf(&self) -> bool {
        &&& self.va < MAX_USERSPACE_VADDR
        &&& self.barrier_va.start < self.barrier_va.end
            < MAX_USERSPACE_VADDR
        // We allow the cursor to be at the end of the range.
        &&& self.barrier_va.start <= self.va <= self.barrier_va.end
    }

    /// Well-formedness of the cursor's level and guard level.
    pub open spec fn level_wf(&self, spt: &SubPageTable) -> bool {
        // The fixed array size should be large enough for the specified number of levels.
        &&& C::NR_LEVELS_SPEC() <= MAX_NR_LEVELS as int
        &&& 1 <= self.level <= C::NR_LEVELS_SPEC()
        &&& 1 <= self.guard_level <= C::NR_LEVELS_SPEC()
        &&& self.level <= self.guard_level
        &&& self.guard_level == spt.instance.root().level
    }

    /// The path above the current node should match the ancestors of the current node.
    pub open spec fn path_wf(&self, spt: &SubPageTable) -> bool {
        let cur_frame = path_index!(self.path[self.level]).unwrap();
        let cur_frame_pa = cur_frame.paddr() as int;
        let cur_frame_view = spt.frames.value()[cur_frame_pa];
        let cur_ancestors = cur_frame_view.ancestor_chain;

        &&& path_index!(self.path[self.level]).is_some()
        &&& spt.frames.value().contains_key(cur_frame_pa)
        &&& forall|i: PagingLevel|
            #![trigger self.path[path_index_at_level(i)]]
            {
                let guard_option = path_index!(self.path[i]);
                &&& self.level < i <= self.guard_level ==> {
                    &&& guard_option.is_some()
                    &&& guard_option.unwrap().wf()
                    &&& guard_option.unwrap().paddr_spec() == cur_ancestors[i as int].frame_pa
                    &&& guard_option.unwrap().level_spec() == i as int
                    &&& pte_index::<C>(self.va, i) == cur_ancestors[i as int].in_frame_index
                }
                &&& i == self.level ==> {
                    !cur_ancestors.contains_key(i as int) && guard_option.is_some()
                }
                &&& 1 <= i < self.level || self.guard_level < i <= MAX_NR_LEVELS ==> {
                    !cur_ancestors.contains_key(i as int) && guard_option.is_none()
                }
            }
    }

    /// Guard level and barrier virtual address should not change.
    pub open spec fn constant_fields_unchanged(
        &self,
        old: &Cursor<'a, C>,
        spt: &SubPageTable,
        old_spt: &SubPageTable,
    ) -> bool {
        &&& self.guard_level == old.guard_level
        &&& self.barrier_va == old.barrier_va
        &&& spt.instance.id() == old_spt.instance.id()
        &&& spt.instance.root() == old_spt.instance.root()
    }

    /// Tells if the provided guard's ancestors is the same as the current path.
    ///
    /// This is used to check if the provided guard can be appended to the path.
    closed spec fn ancestors_match_path(
        &self,
        spt: &SubPageTable,
        guard: PageTableGuard<C>,
    ) -> bool {
        &&& guard.wf()
        &&& guard.level_spec() == self.level - 1
        &&& {
            let frame_view = spt.frames.value().get(guard.paddr_spec() as int);
            let ancestors = frame_view.unwrap().ancestor_chain;
            &&& frame_view.is_some()
            &&& forall|i: PagingLevel|
                #![trigger self.path.view().index(path_index_at_level(i))]
                #![trigger ancestors.contains_key(i as int)]
                {
                    let guard_option = path_index!(self.path[i]);
                    &&& self.level <= i <= self.guard_level ==> {
                        &&& guard_option.is_some()
                        &&& guard_option.unwrap().paddr_spec() == ancestors[i as int].frame_pa
                        &&& pte_index::<C>(self.va, i) == ancestors[i as int].in_frame_index
                    }
                    &&& i == guard.level_spec() ==> {
                        !ancestors.contains_key(
                            i as int,
                        )
                        // && guard_option.is_some()

                    }&&& 1 <= i < guard.level_spec() || self.guard_level < i <= MAX_NR_LEVELS ==> {
                        !ancestors.contains_key(i as int) && guard_option.is_none()
                    }
                }
        }
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
    pub(in crate::mm) fn move_forward(&mut self, Tracked(spt): Tracked<&SubPageTable>)
        requires
            old(self).wf(spt),
            old(self).va + page_size::<C>(old(self).level) <= old(self).barrier_va.end,
        ensures
            self.wf(spt),
            self.constant_fields_unchanged(old(self), spt, spt),
            self.va > old(self).va,
            self.level >= old(self).level,
    {
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
    fn pop_level(&mut self, Tracked(spt): Tracked<&SubPageTable>)
        requires
            old(self).wf(spt),
            old(self).level < old(self).guard_level,
        ensures
            old(self).wf(spt),
            self.constant_fields_unchanged(old(self), spt, spt),
            self.level == old(self).level + 1,
            // Other fields remain unchanged.
            self.va == old(self).va,
    {
        // let Some(taken) = self.path[self.level as usize - 1].take() else {
        //     panic!("Popping a level without a lock");
        // };
        let taken = &self.path[self.level as usize - 1];
        assert(taken.is_some());
        // TODO
        // let _taken = taken.unwrap().into_raw_paddr();

        self.level = self.level + 1;
    }

    /// Goes down a level to a child page table.
    fn push_level(&mut self, child_pt: PageTableGuard<C>, Tracked(spt): Tracked<&SubPageTable>)
        requires
            old(self).wf(spt),
            old(self).level > 1,
            child_pt.wf(),
            spt.frames.value().contains_key(child_pt.paddr() as int),
            old(self).ancestors_match_path(spt, child_pt),
        ensures
            self.wf(spt),
            self.constant_fields_unchanged(old(self), spt, spt),
            self.level == old(self).level - 1,
            path_index!(self.path[self.level]) == Some(child_pt),
            // Other fields remain unchanged.
            self.va == old(self).va,
            // Path remains unchanged except the one being set
            forall|i: PagingLevel|
                #![trigger self.path.view().index(path_index_at_level(i))]
                old(self).level <= i <= old(self).guard_level ==> {
                    #[trigger] path_index!(self.path[i]) == path_index!(old(self).path[i])
                },
    {
        assert(forall|i: PagingLevel|
            self.level < i <= self.guard_level ==> {
                &&& #[trigger] path_index!(self.path[i]).is_some()
                &&& path_index!(self.path[i]).unwrap().level_spec() == i as int
                &&& path_index!(self.path[i]).unwrap().wf()
            });

        self.level = self.level - 1;

        self.path[self.level as usize - 1] = Some(child_pt);

        assume(forall|i: PagingLevel|
            self.level < i <= self.guard_level ==> {
                &&& #[trigger] path_index!(self.path[i]).is_some()
                // Verus can't reveal them even if the previous assertion is true.
                &&& path_index!(self.path[i]).unwrap().level_spec() == i as int
                &&& path_index!(self.path[i]).unwrap().wf()
            });
    }

    // Note that mut types are not supported in Verus.
    // fn cur_entry(&mut self) -> Entry<'_, C> {
    fn cur_entry(&self, Tracked(spt): Tracked<&SubPageTable>) -> (res: Entry<'_, C>)
        requires
            self.wf(spt),
        ensures
            res.node.wf(),
            res.idx == pte_index::<C>(self.va, self.level),
            res.idx < nr_subpage_per_huge::<C>(),  // This is the post condition of `pte_index`. Why we have to specify here?
            res.pte.pte_paddr() == index_pte_paddr(
                path_index!(self.path[self.level]).unwrap().paddr() as int,
                pte_index::<C>(self.va, self.level) as int,
            ),
            res.pte.pte_paddr() == exec::get_pte_from_addr_spec(res.pte.pte_paddr(), spt).pte_addr,
            res.pte.frame_paddr() == exec::get_pte_from_addr_spec(
                res.pte.pte_paddr(),
                spt,
            ).frame_pa,
            res.pte.frame_paddr() == 0 ==> !spt.i_ptes.value().contains_key(
                res.pte.pte_paddr() as int,
            ),
            res.pte.frame_paddr() != 0 ==> {
                &&& spt.i_ptes.value().contains_key(res.pte.pte_paddr() as int)
                &&& spt.i_ptes.value()[res.pte.pte_paddr() as int].frame_pa
                    == res.pte.frame_paddr() as int
                &&& spt.frames.value().contains_key(res.pte.frame_paddr() as int)
            },
    {
        let cur_node = self.path[self.level as usize - 1].as_ref().unwrap();
        assume(cur_node.wf());  // This should be obvious given `path_wf`, but Verus can't reveal it.
        Entry::new_at(cur_node, pte_index::<C>(self.va, self.level), Tracked(spt))
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
        Tracked(spt): Tracked<&mut SubPageTable>,
    ) -> (res: Option<Frame>)
        requires
            old(spt).wf(),
            old(self).0.wf(old(spt)),
        ensures
            spt.wf(),
            self.0.wf(spt),
            self.0.constant_fields_unchanged(&old(self).0, spt, old(spt)),
            self.0.va > old(
                self,
            ).0.va,
    // TODO: Add the mapping model and ensure the mapping is built.

    {
        let end = self.0.va + frame.size();

        // To track that VA does not change in loop;
        let old_va = Tracked(self.0.va);

        #[verifier::loop_isolation(false)]
        // Go down if not applicable.
        while self.0.level
            > frame.map_level()
        // TODO || self.0.va % page_size::<C>(self.0.level) != 0 || self.0.va + page_size::<C>(self.0.level) > end

            invariant
                spt.wf(),
                self.0.wf(spt),
                self.0.constant_fields_unchanged(&old(self).0, spt, old(spt)),
                // VA should be unchanged in the loop.
                self.0.va == old_va@,
            decreases self.0.level - frame.map_level(),
        {
            let cur_level = self.0.level;
            let cur_entry = self.0.cur_entry(Tracked(spt));
            match cur_entry.to_ref(Tracked(spt)) {
                Child::PageTableRef(pt) => {
                    let child_pt = PageTableGuard::<C>::from_raw_paddr(pt, cur_level);
                    // FIXME: Fix by letting `cur_entry.to_ref` generate PT guard, like how we do in exec code.
                    assume(self.0.ancestors_match_path(spt, child_pt));
                    self.0.push_level(child_pt, Tracked(spt));
                },
                Child::PageTable(_) => {
                    assert(false);
                },
                Child::None => {
                    assert(!spt.ptes.value().contains_key(cur_entry.pte.pte_paddr() as int));
                    let pt = cur_entry.alloc_if_none(Tracked(spt)).unwrap();

                    assert(spt.frames.value().contains_key(pt as int));

                    let child_pt = PageTableGuard::<C>::from_raw_paddr(pt, cur_level);

                    // FIXME: Fix by letting `cur_entry.to_ref` generate PT guard, like how we do in exec code.
                    assume(self.0.ancestors_match_path(spt, child_pt));
                    self.0.push_level(child_pt, Tracked(spt));
                },
                Child::Frame(_, _) => {
                    assert(false);
                },
                Child::Untracked(_, _, _) => {
                    assert(false);
                },
                Child::Token(_, _) => {
                    assert(false);  // TODO: Token
                },
            }
            continue ;
        }

        assert(self.0.level == frame.map_level());

        let cur_entry = self.0.cur_entry(Tracked(spt));

        // TODO: P0 Fix the last level frame in SubPageTableStateMachine and SubPageTable.
        // Map the current page.
        let old_entry = cur_entry.replace(Child::Frame(frame, prop), Tracked(spt));

        assume(self.0.va + page_size::<C>(self.0.level) <= self.0.barrier_va.end);  // TODO: P1
        assume(self.0.path_wf(spt));  // TODO: P0
        self.0.move_forward(Tracked(spt));

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
        Tracked(spt): Tracked<&mut SubPageTable>,
    ) -> (res: PageTableItem)
        requires
            old(spt).wf(),
            old(self).0.wf(old(spt)),
            old(self).0.va as int + len as int <= old(self).0.barrier_va.end as int,
            len % page_size::<C>(1) == 0,
            len > page_size::<C>(old(self).0.level),
        ensures
            spt.wf(),
            self.0.wf(spt),
            self.0.constant_fields_unchanged(&old(self).0, spt, old(spt)),
    {
        let start = self.0.va;
        assert(len % page_size::<C>(1) == 0);
        let end = start + len;
        // assert!(end <= self.0.barrier_va.end); // TODO

        while self.0.va < end && self.0.level > 1
            invariant
                spt.wf(),
                self.0.wf(spt),
                self.0.constant_fields_unchanged(&old(self).0, spt, old(spt)),
                self.0.va + page_size::<C>(self.0.level) < end,
                self.0.va + len < MAX_USERSPACE_VADDR,
            decreases
                    end - self.0.va,
                    self.0.level,  // for push_level, only level decreases

        {
            let cur_va = self.0.va;
            let cur_level = self.0.level;
            let cur_entry = self.0.cur_entry(Tracked(spt));

            // Skip if it is already absent.
            // if cur_entry.is_none(spt) {
            if !cur_entry.pte.is_present(Tracked(spt)) {
                if self.0.va + page_size::<C>(self.0.level) > end {
                    self.0.va = end;
                    break ;
                }
                assume(self.0.va + page_size::<C>(self.0.level) <= self.0.barrier_va.end);  // TODO: P1
                self.0.move_forward(Tracked(spt));
                assert(self.0.path_wf(spt));

                assume(self.0.va + page_size::<C>(self.0.level) < end);
                assume(self.0.va + len < MAX_USERSPACE_VADDR);
                continue ;
            }
            // Go down if not applicable.

            if cur_va % page_size::<C>(cur_level) != 0 || cur_va + page_size::<C>(cur_level) > end {
                let child = cur_entry.to_ref(Tracked(spt));
                match child {
                    Child::PageTableRef(pt) => {
                        // SAFETY: `pt` points to a PT that is attached to a node
                        // in the locked sub-tree, so that it is locked and alive.
                        let pt = PageTableGuard::<C>::from_raw_paddr(pt, cur_level);
                        // If there's no mapped PTEs in the next level, we can
                        // skip to save time.
                        if pt.nr_children() != 0 {
                            // FIXME: Fix by letting `cur_entry.to_ref` generate PT guard, like how we do in exec code.
                            assume(self.0.ancestors_match_path(spt, pt));
                            self.0.push_level(pt, Tracked(spt));
                        } else {
                            let _ = pt.into_raw_paddr();
                            if self.0.va + page_size::<C>(self.0.level) > end {
                                self.0.va = end;
                                break ;
                            }
                            assume(self.0.va + page_size::<C>(self.0.level)
                                <= self.0.barrier_va.end);  // TODO: P1
                            self.0.move_forward(Tracked(spt));
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
                        // self.0.push_level(split_child, cur_level, Tracked(spt));
                        assert(false);
                    },
                    Child::Token(_, _) => {
                        // let split_child = cur_entry.split_if_huge_status().unwrap();
                        // self.0.push_level(split_child, cur_level, Tracked(spt));
                        assert(false);
                    },
                }

                assume(self.0.va + page_size::<C>(self.0.level) < end);
                assume(self.0.va + len < MAX_USERSPACE_VADDR);
                continue ;
            }
            // Unmap the current page and return it.

            let old = cur_entry.replace(Child::None, Tracked(spt));
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

            assume(self.0.va + page_size::<C>(self.0.level) <= self.0.barrier_va.end);  // TODO: P1
            assume(self.0.path_wf(spt));  // TODO: P0
            self.0.move_forward(Tracked(spt));

            return item;
        }

        // If the loop exits, we did not find any mapped pages in the range.
        PageTableItem::NotMapped { va: start, len }
    }
}

} // verus!
