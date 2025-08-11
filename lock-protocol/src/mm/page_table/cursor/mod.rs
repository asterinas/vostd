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
    arithmetic::{div_mod::*, power::*, power2::*},
    calc, invariant,
    pervasive::VecAdditionalExecFns,
    prelude::*,
    raw_ptr::MemContents,
};
use vstd::bits::*;
use vstd::tokens::SetToken;
use core::ops::Deref;

use crate::{
    helpers::{align_ext::align_down, math::lemma_usize_mod_0_maintain_after_add},
    mm::{
        child::{self, Child, ChildRef},
        entry::Entry,
        frame::{self, allocator::AllocatorModel},
        meta::AnyFrameMeta,
        node::PageTableNode,
        nr_subpage_per_huge,
        page_prop::PageProperty,
        page_size, page_size_spec, lemma_page_size_spec_properties, lemma_page_size_increases,
        lemma_page_size_geometric,
        vm_space::Token,
        Frame, Paddr, PageTableGuard, Vaddr, MAX_USERSPACE_VADDR, PAGE_SIZE,
    },
    task::DisabledPreemptGuard,
    sync::rcu::RcuDrop,
};

use super::{
    lemma_aligned_pte_index_unchanged, lemma_addr_aligned_propagate,
    lemma_carry_ends_at_nonzero_result_bits, lemma_pte_index_alternative_spec, pte_index,
    pte_index_mask, PageTable, PageTableConfig, PageTableEntryTrait, PageTableError, PagingConsts,
    PagingConstsTrait, PagingLevel,
};

use crate::spec::sub_pt::{SubPageTable, index_pte_paddr};
use crate::exec;
use spec_helpers::*;
use crate::mm::NR_ENTRIES;

/// A handy ghost mode macro to get the guard at a certain level in the path.
macro_rules! path_index {
    ($self: ident . path [$i:expr]) => {
        $self.path.view().index(path_index_at_level_spec($i))
    };
    ($self: ident . 0 . path [$i:expr]) => {
        $self.0.path.view().index(path_index_at_level_spec($i))
    };
    (old($self: ident) . path [$i:expr]) => {
        old($self).path.view().index(path_index_at_level_spec($i))
    };
    (old($self: ident) . 0 . path [$i:expr]) => {
        old($self).0.path.view().index(path_index_at_level_spec($i))
    };
}

verus! {

pub open spec fn path_index_at_level_spec(level: PagingLevel) -> int {
    level - 1
}

fn path_index_at_level(level: PagingLevel) -> (res: usize)
    requires
        1 <= level <= MAX_NR_LEVELS as int,
    ensures
        res as int == path_index_at_level_spec(level),
{
    (level - 1) as usize
}

/// The cursor for traversal over the page table.
///
/// A slot is a PTE at any levels, which correspond to a certain virtual
/// memory range sized by the "page size" of the current level.
///
/// A cursor is able to move to the next slot, to read page properties,
/// and even to jump to a virtual address directly.
// #[derive(Debug)] // TODO: Implement `Debug` for `Cursor`.
pub struct Cursor<'rcu, C: PageTableConfig> {
    /// The current path of the cursor.
    ///
    /// The level 1 page table lock guard is at index 0, and the level N page
    /// table lock guard is at index N - 1.
    pub path: [Option<PageTableGuard<'rcu, C>>; MAX_NR_LEVELS],
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
    pub preempt_guard: &'rcu DisabledPreemptGuard,
    pub _phantom: PhantomData<&'rcu PageTable<C>>,
}

/// The maximum value of `PagingConstsTrait::NR_LEVELS`.
pub const MAX_NR_LEVELS: usize = 4;

// #[derive(Clone, Debug)] // TODO: Implement Debug and Clone for PageTableItem
pub enum PageTableItem<C: PageTableConfig> {
    NotMapped { va: Vaddr, len: usize },
    Mapped { va: Vaddr, page: Paddr, prop: PageProperty },
    StrayPageTable { pt: RcuDrop<PageTableNode<C>>, va: Vaddr, len: usize },
}

impl<'a, C: PageTableConfig> Cursor<'a, C> {
    /// Well-formedness of the cursor.
    pub open spec fn wf(&self, spt: &SubPageTable<C>) -> bool {
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
    pub open spec fn level_wf(&self, spt: &SubPageTable<C>) -> bool {
        // The fixed array size should be large enough for the specified number of levels.
        &&& C::NR_LEVELS_SPEC() <= MAX_NR_LEVELS as int
        &&& 1 <= self.level <= C::NR_LEVELS_SPEC()
        &&& 1 <= self.guard_level <= C::NR_LEVELS_SPEC()
        &&& 1 <= self.guard_level <= PagingConsts::NR_LEVELS_SPEC()
        &&& self.level <= self.guard_level
        &&& self.guard_level == spt.instance.root().level
    }

    pub open spec fn path_item_wf(
        &self,
        level: PagingLevel,
        cur_frame: PageTableGuard<C>,
        spt: &SubPageTable<C>,
    ) -> bool {
        let cur_frame_pa = cur_frame.paddr() as int;
        let cur_frame_view = spt.frames.value()[cur_frame_pa];
        let cur_ancestors = cur_frame_view.ancestor_chain;

        &&& cur_frame.wf(&spt.alloc_model)
        &&& cur_frame.level_spec(&spt.alloc_model) == level
        &&& cur_frame == self.path[path_index_at_level_spec(level)].unwrap()
        &&& spt.frames.value().contains_key(cur_frame_pa)
        &&& forall|j: PagingLevel|
            #![trigger self.path[path_index_at_level_spec(j)]]
            #![trigger cur_ancestors.contains_key(j as int)]
            {
                let guard_option_ = path_index!(self.path[j]);
                &&& level < j <= self.guard_level ==> {
                    &&& guard_option_.is_some()
                    &&& guard_option_.unwrap().wf(&spt.alloc_model)
                    &&& guard_option_.unwrap().paddr() == cur_ancestors[j as int].frame_pa
                    &&& guard_option_.unwrap().level_spec(&spt.alloc_model) == j as int
                    &&& pte_index::<C>(self.va, j) == cur_ancestors[j as int].in_frame_index
                }
                &&& j == level ==> {
                    &&& !cur_ancestors.contains_key(j as int)
                    &&& guard_option_.is_some()
                    &&& guard_option_.unwrap().level_spec(&spt.alloc_model) == j as int
                }
                &&& 1 <= j < level || self.guard_level < j <= MAX_NR_LEVELS ==> {
                    !cur_ancestors.contains_key(j as int)
                }
            }
    }

    /// The path above the current node should match the ancestors of the current node.
    pub open spec fn path_wf(&self, spt: &SubPageTable<C>) -> bool {
        forall|i: PagingLevel|
            #![trigger self.path[path_index_at_level_spec(i)]]
            {
                let guard_option = path_index!(self.path[i]);
                &&& self.level <= i <= self.guard_level ==> {
                    &&& guard_option.is_some()
                    &&& self.path_item_wf(i, guard_option.unwrap(), spt)
                }
                &&& 1 <= i < self.level || self.guard_level < i <= MAX_NR_LEVELS ==> {
                    guard_option.is_none()
                }
            }
    }

    /// Guard level and barrier virtual address should not change.
    pub open spec fn constant_fields_unchanged(
        &self,
        old: &Cursor<'a, C>,
        spt: &SubPageTable<C>,
        old_spt: &SubPageTable<C>,
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
        spt: &SubPageTable<C>,
        guard: PageTableGuard<C>,
    ) -> bool {
        &&& guard.wf(&spt.alloc_model)
        &&& guard.level_spec(&spt.alloc_model) == self.level - 1
        &&& {
            let frame_view = spt.frames.value().get(guard.paddr() as int);
            let ancestors = frame_view.unwrap().ancestor_chain;
            &&& frame_view.is_some()
            &&& forall|i: PagingLevel|
                #![trigger self.path.view().index(path_index_at_level_spec(i))]
                #![trigger ancestors.contains_key(i as int)]
                {
                    let guard_option = path_index!(self.path[i]);
                    &&& self.level <= i <= self.guard_level ==> {
                        &&& guard_option.is_some()
                        &&& guard_option.unwrap().level_spec(&spt.alloc_model) == i as int
                        &&& guard_option.unwrap().paddr() == ancestors[i as int].frame_pa
                        &&& pte_index::<C>(self.va, i) == ancestors[i as int].in_frame_index
                    }
                    &&& 1 <= i < self.level || self.guard_level < i <= MAX_NR_LEVELS ==> {
                        &&& !ancestors.contains_key(i as int)
                        &&& guard_option.is_none()
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
    pub(in crate::mm) fn move_forward(&mut self, Tracked(spt): Tracked<&SubPageTable<C>>)
        requires
            old(self).wf(spt),
            old(self).va + page_size::<C>(old(self).level) <= old(self).barrier_va.end,
        ensures
            self.wf(spt),
            self.constant_fields_unchanged(old(self), spt, spt),
            self.va > old(self).va,
            self.level >= old(self).level,
    {
        let cur_page_size = page_size::<C>(self.level);
        let next_va = align_down(self.va, cur_page_size) + cur_page_size;
        assert(next_va % page_size::<C>(self.level) == 0) by (nonlinear_arith)
            requires
                next_va == align_down(self.va, cur_page_size) + cur_page_size,
                cur_page_size == page_size::<C>(self.level),
                align_down(self.va, cur_page_size) % cur_page_size == 0,
        ;
        while self.level < self.guard_level && pte_index::<C>(next_va, self.level) == 0
            invariant
                old(self).wf(spt),
                self.wf(spt),
                self.constant_fields_unchanged(old(self), spt, spt),
                self.level >= old(self).level,
                self.va == old(self).va,
                next_va % page_size::<C>(self.level) == 0,
            decreases self.guard_level - self.level,
        {
            self.pop_level(Tracked(&spt));
            proof {
                // Only thing we need to prove is next_va % page_size(self.level) == 0
                assert(next_va % page_size::<C>((self.level - 1) as u8) == 0);
                assert(pte_index::<C>(next_va, (self.level - 1) as u8) == 0);
                lemma_addr_aligned_propagate::<C>(next_va, self.level);
            }
        }
        self.va = next_va;
        proof {
            if (self.level == self.guard_level) {
                // The proof automatically goes through in this case.
            } else {
                let old_level = old(self).level;
                let old_page_size = cur_page_size;
                let aligned_va = align_down(old(self).va, old_page_size);
                // Information from the loop termination
                assert(old_level <= self.level < self.guard_level);
                assert(pte_index::<C>(next_va, self.level) != 0);

                // No overflow.
                assert(aligned_va + old_page_size < usize::MAX) by {
                    assert(aligned_va + old_page_size <= old(self).barrier_va.end);
                    assert(old(self).barrier_va.end < usize::MAX);
                }
                assert(self.va == next_va == aligned_va + old_page_size);

                assert forall|i: u8| self.level < i <= self.guard_level implies pte_index::<C>(
                    self.va,
                    i,
                ) == pte_index::<C>(old(self).va, i) by {
                    assert(self.level + 1 <= i);
                    // The page size of the "next" level, i.e., self.level + 1.
                    let next_pg_size = page_size::<C>((self.level + 1) as u8) as nat;
                    assert(next_pg_size > 0) by {
                        lemma_page_size_spec_properties::<C>((self.level + 1) as u8);
                    }
                    // Ratio of page_size::<C>(i) / next_pg_size
                    let ratio = pow(
                        nr_subpage_per_huge::<C>() as int,
                        (i - (self.level + 1)) as nat,
                    ) as nat;
                    assert(page_size::<C>(i) as nat == next_pg_size * ratio) by {
                        lemma_page_size_geometric::<C>((self.level + 1) as u8, i);
                    }
                    assert(ratio > 0) by {
                        C::lemma_consts_properties();
                        assert(nr_subpage_per_huge::<C>() > 0);
                        lemma_pow_positive(
                            nr_subpage_per_huge::<C>() as int,
                            (i - (self.level + 1)) as nat,
                        );
                    }

                    calc! {
                        (==)
                        pte_index::<C>(self.va, i) as nat; {
                            assert(self.va == next_va);
                        }
                        pte_index::<C>(next_va, i) as nat; {
                            lemma_pte_index_alternative_spec::<C>(next_va, i);
                        }
                        next_va as nat / page_size_spec::<C>(i) as nat % nr_subpage_per_huge::<
                            C,
                        >() as nat; {
                            // Already proven: page_size(i) == next_pg_size * ratio
                        }
                        next_va as nat / (next_pg_size * ratio) % nr_subpage_per_huge::<
                            C,
                        >() as nat; {
                            lemma_div_denominator(
                                next_va as int,
                                next_pg_size as int,
                                ratio as int,
                            );
                        }
                        next_va as nat / next_pg_size / ratio % nr_subpage_per_huge::<C>() as nat; {
                            assert(next_va == aligned_va + old_page_size);
                            // These are the arguments to lemma_carry_ends_at_nonzero_result_bits
                            let p = (C::BASE_PAGE_SIZE().ilog2() + (C::BASE_PAGE_SIZE().ilog2()
                                - C::PTE_SIZE().ilog2()) * self.level) as nat;
                            assert(pow2(p) == next_pg_size) by {
                                lemma_page_size_spec_properties::<C>(
                                    (self.level + 1) as PagingLevel,
                                );
                            }
                            let q = (C::BASE_PAGE_SIZE().ilog2() + (C::BASE_PAGE_SIZE().ilog2()
                                - C::PTE_SIZE().ilog2()) * (self.level - 1)) as nat;
                            assert(pow2(q) == page_size::<C>(self.level) as nat) by {
                                lemma_page_size_spec_properties::<C>(self.level);
                            }
                            // Preconditions
                            C::lemma_consts_properties();
                            // q <= p
                            assert(q <= p) by (nonlinear_arith)
                                requires
                                    p == (C::BASE_PAGE_SIZE().ilog2() + (C::BASE_PAGE_SIZE().ilog2()
                                        - C::PTE_SIZE().ilog2()) * self.level) as nat,
                                    q == (C::BASE_PAGE_SIZE().ilog2() + (C::BASE_PAGE_SIZE().ilog2()
                                        - C::PTE_SIZE().ilog2()) * (self.level - 1)) as nat,
                                    C::BASE_PAGE_SIZE().ilog2() - C::PTE_SIZE().ilog2() >= 0,
                            ;
                            // old_page_size is not too large
                            assert(old_page_size <= pow2(q)) by {
                                lemma_page_size_increases::<C>(old(self).level, self.level);
                            }
                            // The middle part of the result is not zero
                            assert(next_va as nat % pow2(p) / pow2(q) != 0) by {
                                lemma_pte_index_alternative_spec::<C>(next_va, self.level);
                                // Use this to activate the second alternative spec
                                assert(self.level < self.guard_level <= C::NR_LEVELS());
                                // Then, use this to help the verifier know where the !=0 came from
                                assert(pte_index::<C>(next_va, self.level) != 0);
                            }
                            // Now we are finally ready to apply the main lemma
                            lemma_carry_ends_at_nonzero_result_bits(
                                next_va as nat,
                                aligned_va as nat,
                                p,
                                q,
                            );
                            // Let's restate the result of the lemma here.
                            assert(next_va as nat / pow2(p) == aligned_va as nat / pow2(p));
                        }
                        aligned_va as nat / next_pg_size / ratio % nr_subpage_per_huge::<
                            C,
                        >() as nat; {
                            lemma_div_denominator(
                                aligned_va as int,
                                next_pg_size as int,
                                ratio as int,
                            );
                        }
                        aligned_va as nat / (next_pg_size * ratio) % nr_subpage_per_huge::<
                            C,
                        >() as nat; {
                            // Already proven: page_size(i) == next_pg_size * ratio
                        }
                        aligned_va as nat / page_size_spec::<C>(i) as nat % nr_subpage_per_huge::<
                            C,
                        >() as nat; {
                            lemma_pte_index_alternative_spec::<C>(aligned_va, i);
                        }
                        pte_index::<C>(aligned_va, i) as nat; {
                            lemma_aligned_pte_index_unchanged::<C>(old(self).va, old_level);
                        }
                        pte_index::<C>(old(self).va, i) as nat;
                    }
                }
                assert(self.wf(spt));
            }
        }
    }

    pub fn virt_addr(&self) -> Vaddr {
        self.va
    }

    /// Goes up a level.
    fn pop_level(&mut self, Tracked(spt): Tracked<&SubPageTable<C>>)
        requires
            old(self).wf(spt),
            old(self).level < old(self).guard_level,
        ensures
            self.wf(spt),
            self.constant_fields_unchanged(old(self), spt, spt),
            self.level == old(self).level + 1,
            // Other fields remain unchanged.
            self.va == old(self).va,
    {
        proof {
            let taken = &path_index!(self.path[self.level]);
            // self.path[path_index_at_level(self.level)].take() // Verus does not support this currently
            assert(taken == path_index!(self.path[self.level]));
            assert(taken.is_some());
        }
        self.path[path_index_at_level(self.level)] = None;

        self.level = self.level + 1;
    }

    /// Goes down a level to a child page table.
    fn push_level(
        &mut self,
        child_pt: PageTableGuard<'a, C>,
        Tracked(spt): Tracked<&SubPageTable<C>>,
    )
        requires
            old(self).wf(spt),
            old(self).level > 1,
            child_pt.wf(&spt.alloc_model),
            child_pt.level_spec(&spt.alloc_model) == old(self).level - 1,
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
                #![trigger self.path.view().index(path_index_at_level_spec(i))]
                old(self).level <= i <= old(self).guard_level ==> {
                    #[trigger] path_index!(self.path[i]) == path_index!(old(self).path[i])
                },
    {
        self.level = self.level - 1;

        self.path[path_index_at_level(self.level)] = Some(child_pt);
    }

    // Note that mut types are not supported in Verus.
    // fn cur_entry(&mut self) -> Entry<'_, C> {
    fn cur_entry(&self, Tracked(spt): Tracked<&SubPageTable<C>>) -> (res: Entry<'_, 'a, C>)
        requires
            self.wf(spt),
        ensures
            res.wf(spt),
            res.node == path_index!(self.path[self.level]).unwrap(),
            res.node.level_spec(&spt.alloc_model) == self.level,
            res.idx == pte_index::<C>(self.va, self.level),
            res.va == align_down(self.va, page_size::<C>(self.level)),
    {
        let cur_node = self.path[path_index_at_level(self.level)].as_ref().unwrap();
        let idx = pte_index::<C>(self.va, self.level);
        assert(self.level == cur_node.level_spec(&spt.alloc_model));
        assume(cur_node.va@ + idx * page_size::<C>(self.level) == align_down(
            self.va,
            page_size::<C>(self.level),
        ));
        Entry::new_at(cur_node, idx, Tracked(spt))
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

    /// Maps the range starting from the current address to an item.
    ///
    /// It returns the previously mapped item if that exists.
    ///
    /// Note that the item `C::Item`, when converted to a raw item, if the page property
    /// indicate that it is marked metadata, the function is essentially `mark`.
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
    pub fn map(&mut self, item: C::Item, Tracked(spt): Tracked<&mut SubPageTable<C>>) -> (res:
        PageTableItem<C>)
        requires
            old(spt).wf(),
            old(self).0.wf(old(spt)),
            old(self).0.va % page_size::<C>(1) == 0,
            1 <= C::item_into_raw_spec(item).1 <= old(self).0.guard_level,
            old(self).0.va + page_size::<C>(C::item_into_raw_spec(item).1) <= old(
                self,
            ).0.barrier_va.end,
        ensures
            spt.wf(),
            self.0.wf(spt),
            self.0.constant_fields_unchanged(&old(self).0, spt, old(spt)),
            self.0.va > old(self).0.va,
            // The map succeeds.
            exists|pte_pa: Paddr|
                {
                    &&& #[trigger] spt.ptes.value().contains_key(
                        pte_pa as int,
                    )
                    // &&& #[trigger] spt.ptes.value()[pte_pa as int].map_va == old(self).0.va
                    &&& #[trigger] spt.ptes.value()[pte_pa as int].map_to_pa
                        == C::item_into_raw_spec(item).0
                },
    {
        let preempt_guard = self.0.preempt_guard;

        let (pa, level, prop) = C::item_into_raw(item);
        assert(1 <= level <= self.0.guard_level);

        let end = self.0.va + page_size::<C>(level);

        #[verifier::loop_isolation(false)]
        // Go up if not applicable.
        while self.0.level < level
            invariant
                spt.wf(),
                self.0.wf(spt),
                self.0.constant_fields_unchanged(&old(self).0, spt, old(spt)),
                // VA should be unchanged in the loop.
                self.0.va == old(self).0.va,
            decreases level - self.0.level,
        {
            self.0.pop_level(Tracked(spt));
        }

        assert(self.0.level >= level);

        #[verifier::loop_isolation(false)]
        // Go down if not applicable.
        while self.0.level != level
            invariant
                spt.wf(),
                self.0.wf(spt),
                self.0.constant_fields_unchanged(&old(self).0, spt, old(spt)),
                // VA should be unchanged in the loop.
                self.0.va == old(self).0.va,
            decreases self.0.level,
        {
            let cur_level = self.0.level;
            let ghost cur_va = self.0.va;
            let mut cur_entry = self.0.cur_entry(Tracked(spt));
            match cur_entry.to_ref(Tracked(spt)) {
                ChildRef::PageTable(pt) => {
                    assert(spt.i_ptes.value().contains_key(cur_entry.pte.pte_paddr() as int));
                    assert(cur_level == cur_entry.node.level_spec(&spt.alloc_model));
                    assert(cur_level - 1 == pt.level_spec(&spt.alloc_model));
                    let child_pt = pt.make_guard_unchecked(
                        preempt_guard,
                        Ghost(align_down(cur_va, page_size::<C>(cur_level))),
                    );
                    assert(self.0.ancestors_match_path(spt, child_pt));
                    self.0.push_level(child_pt, Tracked(spt));
                },
                ChildRef::None => {
                    assert(!spt.ptes.value().contains_key(cur_entry.pte.pte_paddr() as int));
                    assert(cur_entry.node.level_spec(&spt.alloc_model) == cur_level);
                    let child_pt = cur_entry.alloc_if_none(preempt_guard, Tracked(spt)).unwrap();
                    self.0.push_level(child_pt, Tracked(spt));
                },
                ChildRef::Frame(_, _, _) => {
                    assume(false);  // FIXME: implement split if huge page
                },
            }
            continue ;
        }
        assert(self.0.level == level);

        let mut cur_entry = self.0.cur_entry(Tracked(spt));

        let old_entry = cur_entry.replace(Child::Frame(pa, level, prop), Tracked(spt));

        assume(self.0.va + page_size::<C>(self.0.level) <= self.0.barrier_va.end);  // TODO: P1
        assert(self.0.path_wf(spt));

        let old_va = self.0.va;
        let old_len = page_size::<C>(self.0.level);

        self.0.move_forward(Tracked(spt));

        match old_entry {
            Child::Frame(pa, level, prop) => PageTableItem::Mapped {
                va: old_va,
                page: pa,
                prop: prop,
            },
            Child::None => PageTableItem::NotMapped { va: old_va, len: old_len },
            Child::PageTable(pt) => PageTableItem::StrayPageTable { pt, va: old_va, len: old_len },
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
    #[verifier::spinoff_prover]
    pub unsafe fn take_next(
        &mut self,
        len: usize,
        Tracked(spt): Tracked<&mut SubPageTable<C>>,
    ) -> (res: PageTableItem<C>)
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
        let preempt_guard = self.0.preempt_guard;

        let start = self.0.va;
        assert(len % page_size::<C>(1) == 0);
        let end = start + len;
        assert(end <= self.0.barrier_va.end);

        while self.0.va < end && self.0.level > 1
            invariant
                spt.wf(),
                self.0.wf(spt),
                self.0.constant_fields_unchanged(&old(self).0, spt, old(spt)),
                self.0.va + page_size::<C>(self.0.level) < end,
                self.0.va + len < MAX_USERSPACE_VADDR,
                end <= self.0.barrier_va.end,
            decreases
                    end - self.0.va,
                    self.0.level,  // for push_level, only level decreases

        {
            let cur_va = self.0.va;
            let cur_level = self.0.level;
            let mut cur_entry = self.0.cur_entry(Tracked(spt));

            // Skip if it is already absent.
            if cur_entry.is_none(Tracked(spt)) {
                if self.0.va + page_size::<C>(self.0.level) > end {
                    self.0.va = end;
                    break ;
                }
                assert(self.0.va + page_size::<C>(self.0.level) <= self.0.barrier_va.end);
                self.0.move_forward(Tracked(spt));
                assert(self.0.path_wf(spt));

                assume(self.0.va + page_size::<C>(self.0.level) < end);
                assume(self.0.va + len < MAX_USERSPACE_VADDR);
                continue ;
            }
            // Go down if not applicable.

            if cur_va % page_size::<C>(cur_level) != 0 || cur_va + page_size::<C>(cur_level) > end {
                assert(!cur_entry.is_none_spec(spt));
                let child = cur_entry.to_ref(Tracked(spt));
                match child {
                    ChildRef::PageTable(pt) => {
                        let pt = pt.make_guard_unchecked(
                            preempt_guard,
                            Ghost(align_down(cur_va, page_size::<C>(cur_level))),
                        );
                        // If there's no mapped PTEs in the next level, we can
                        // skip to save time.
                        if pt.nr_children() != 0 {
                            self.0.push_level(pt, Tracked(spt));
                        } else {
                            let _ = pt.into_raw_paddr();
                            if self.0.va + page_size::<C>(self.0.level) > end {
                                self.0.va = end;
                                break ;
                            }
                            assert(self.0.va + page_size::<C>(self.0.level)
                                <= self.0.barrier_va.end);
                            self.0.move_forward(Tracked(spt));
                        }
                    },
                    ChildRef::None => {
                        // unreachable!("Already checked");
                        assert(false);
                    },
                    ChildRef::Frame(_, _, _) => {
                        // panic!("Removing part of a huge page");
                        assume(false);  // FIXME: implement split if huge page
                    },
                }

                assume(self.0.va + page_size::<C>(self.0.level) < end);
                assume(self.0.va + len < MAX_USERSPACE_VADDR);
                continue ;
            }
            // Unmap the current page and return it.

            assert(!cur_entry.is_none_spec(spt));
            let old_pte_paddr = cur_entry.pte.pte_paddr();
            assert(old_pte_paddr == cur_entry.pte.pte_paddr());

            assume(spt.i_ptes.value().contains_key(cur_entry.pte.pte_paddr() as int));
            proof {
                let child_frame_addr = spt.i_ptes.value()[index_pte_paddr(
                    cur_entry.node.paddr() as int,
                    cur_entry.idx as int,
                ) as int].map_to_pa;
                let child_frame_level = spt.frames.value()[child_frame_addr].level as int;
                // TODO: enhance path_wf or spt_wf
                assume(forall|i: int| #[trigger]
                    self.0.path[i].is_some() ==> #[trigger] self.0.path[i].unwrap().paddr()
                        != child_frame_addr);
            }
            // TODO: prove the last level entry...
            let old = cur_entry.replace_with_none(Child::None, Tracked(spt));

            // the post condition
            assert(!spt.i_ptes.value().contains_key(old_pte_paddr as int));

            let item = match old {
                Child::Frame(page, level, prop) => PageTableItem::Mapped {
                    va: self.0.va,
                    page,
                    prop,
                },
                Child::PageTable(pt) => {
                    // SAFETY: We must have locked this node.
                    let locked_pt = pt.deref().borrow(
                        Tracked(&spt.alloc_model),
                    ).make_guard_unchecked(
                        preempt_guard,
                        Ghost(align_down(self.0.va, page_size::<C>(self.0.level))),
                    );
                    // assert!(
                    //     !(TypeId::of::<M>() == TypeId::of::<KernelMode>()
                    //         && self.0.level == C::NR_LEVELS()),
                    //     "Unmapping shared kernel page table nodes"
                    // ); // TODO
                    // SAFETY:
                    //  - We checked that we are not unmapping shared kernel page table nodes.
                    //  - We must have locked the entire sub-tree since the range is locked.
                    let unlocked_pt = locking::dfs_mark_astray(locked_pt);
                    // See `locking.rs` for why we need this. // TODO
                    // let drop_after_grace = unlocked_pt.clone();
                    // crate::sync::after_grace_period(|| {
                    //     drop(drop_after_grace);
                    // });
                    PageTableItem::StrayPageTable {
                        pt,
                        va: self.0.va,
                        len: page_size::<C>(self.0.level),
                    }
                },
                Child::None => { PageTableItem::NotMapped { va: 0, len: 0 } },
            };

            assume(self.0.va + page_size::<C>(self.0.level) <= self.0.barrier_va.end);  // TODO
            assert(self.0.path_wf(spt));
            self.0.move_forward(Tracked(spt));

            return item;
        }

        // If the loop exits, we did not find any mapped pages in the range.
        PageTableItem::NotMapped { va: start, len }
    }
}

} // verus!
