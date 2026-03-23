use vstd::prelude::*;

use vstd::set_lib::*;

use vstd_extra::ownership::*;
use vstd_extra::prelude::TreePath;

use crate::mm::page_prop::PageProperty;
use crate::mm::page_table::*;
use crate::mm::{Paddr, PagingConstsTrait, PagingLevel, Vaddr};
use crate::specs::arch::mm::{NR_ENTRIES, NR_LEVELS, PAGE_SIZE};
use crate::specs::arch::paging_consts::PagingConsts;
use crate::specs::mm::page_table::cursor::owners::*;
use crate::specs::mm::page_table::*;
use vstd_extra::arithmetic::*;

use core::ops::Range;

verus! {

impl<C: PageTableConfig> PageTableOwner<C> {
    pub uninterp spec fn new_cursor_owner_spec<'rcu>(self) -> (Self, CursorOwner<'rcu, C>);
}

/// A `CursorView` is not aware that the underlying structure of the page table is a tree.
/// It treats the page table as an array of mappings of various sizes, and the cursor itself as the
/// current virtual address, moving from low to high addresses. These functions specify its behavior
/// and provide a simple interface for reasoning about its behavior.
impl<C: PageTableConfig> CursorView<C> {

    pub open spec fn item_into_mapping(va: Vaddr, item: C::Item) -> Mapping {
        let (paddr, level, prop) = C::item_into_raw_spec(item);
        let size = page_size(level);
        Mapping {
            va_range: va..(va + size) as usize,
            pa_range: paddr..(paddr + size) as Paddr,
            page_size: size,
            property: prop,
        }
    }

    /// This function checks if the current virtual address is mapped. It does not correspond
    /// to a cursor method itself, but defines what it means for an entry to present:
    /// there is a mapping whose virtual address range contains the current virtual address.
    pub open spec fn present(self) -> bool {
        self.mappings.filter(|m: Mapping| m.va_range.start <= self.cur_va < m.va_range.end).len() > 0
    }

    pub open spec fn query_mapping(self) -> Mapping
        recommends
            self.present(),
    {
        self.mappings.filter(|m: Mapping| m.va_range.start <= self.cur_va < m.va_range.end).choose()
    }

    pub open spec fn query(self, paddr: Paddr, size: usize, prop: PageProperty) -> bool {
        let m = self.query_mapping();
        m.pa_range.start == paddr && m.page_size == size && m.property == prop
    }

    pub open spec fn query_range(self) -> Range<Vaddr> {
        self.query_mapping().va_range
    }

    /// The VA range of the current slot when mapping a page of the given size.
    /// Works for both present and absent mappings: when present, equals query_range() for
    /// a mapping of that size; when absent, returns the aligned range that would be mapped.
    pub open spec fn cur_slot_range(self, size: usize) -> Range<Vaddr> {
        let start = nat_align_down(self.cur_va as nat, size as nat) as Vaddr;
        start..(start as nat + size as nat) as Vaddr
    }

    /// This predicate specifies the behavior of the `query` method. It states that the current item
    /// in the page table matches the given item, mapped at the resulting virtual address range.
    pub open spec fn query_item_spec(self, item: C::Item) -> Option<Range<Vaddr>>
        recommends
            self.present(),
    {
        let (paddr, level, prop) = C::item_into_raw_spec(item);
        let size = page_size(level);
        if self.query(paddr, size, prop) {
            Some(self.query_range())
        } else {
            None
        }
    }

    /// The specification for the internal function, `find_next_impl`. It finds the next mapped virtual address
    /// that is at most `len` bytes away from the current virtual address. TODO: add the specifications for
    /// `find_unmap_subtree` and `split_huge`, which are used by other functions that call this one.
    /// This returns a mapping rather than the address because that is useful when it's called as a subroutine.
    pub open spec fn find_next_impl_spec(self, len: usize, find_unmap_subtree: bool, split_huge: bool) -> (Self, Option<Mapping>) {
        let mappings_in_range = self.mappings.filter(|m: Mapping| self.cur_va <= m.va_range.start < self.cur_va + len);

        if mappings_in_range.len() > 0 {
            let mapping = mappings_in_range.find_unique_minimal(|m: Mapping, n: Mapping| m.va_range.start < n.va_range.start);
            let view = CursorView {
                cur_va: mapping.va_range.end,
                ..self
            };
            (view, Some(mapping))
        } else {
            let view = CursorView {
                cur_va: (self.cur_va + len) as Vaddr,
                ..self
            };
            (view, None)
        }
    }

    /// Actual specification for `find_next`. The cursor finds the next mapped virtual address
    /// that is at most `len` bytes away from the current virtual address, returns it, and then
    /// moves the cursor forward to the next end of its range.
    pub open spec fn find_next_spec(self, len: usize) -> (Self, Option<Vaddr>) {
        let (cursor, mapping) = self.find_next_impl_spec(len, false, false);
        if mapping is Some {
            (cursor, Some(mapping.unwrap().va_range.start))
        } else {
            (cursor, None)
        }
    }

    /// Jump just sets the current virtual address to the given address.
    pub open spec fn jump_spec(self, va: usize) -> Self {
        CursorView {
            cur_va: va as Vaddr,
            ..self
        }
    }

    pub open spec fn align_up_spec(self, size: usize) -> Vaddr {
        nat_align_up(self.cur_va as nat, size as nat) as Vaddr
    }

    pub open spec fn split_index(m: Mapping, new_size: usize, n: usize) -> Mapping {
        Mapping {
            va_range: (m.va_range.start + n * new_size) as usize..(m.va_range.start + (n + 1) * new_size) as usize,
            pa_range: (m.pa_range.start + n * new_size) as usize..(m.pa_range.start + (n + 1) * new_size) as usize,
            page_size: new_size,
            property: m.property,
        }
    }

    pub open spec fn split_if_mapped_huge_spec(self, new_size: usize) -> Self {
        let m = self.query_mapping();
        let size = m.page_size;
        let new_mappings = Set::<int>::new(|n:int| 0 <= n < size / new_size).map(|n:int| Self::split_index(m, new_size, n as usize));
        CursorView {
            cur_va: self.cur_va,
            mappings: self.mappings - set![m] + new_mappings,
            ..self
        }
    }

    pub open spec fn split_while_huge(self, size: usize) -> Self
        decreases self.query_mapping().page_size
    {
        if self.present() {
            let m = self.query_mapping();
            if m.page_size > size {
                let new_size = m.page_size / NR_ENTRIES;
                let new_self = self.split_if_mapped_huge_spec(new_size);
                proof {
                    assert(new_self.present()) by { admit() };
                    assert(new_self.query_mapping().page_size < m.page_size) by { admit() };
                }
                new_self.split_while_huge(size)
            } else {
                self
            }
        } else {
            self
        }
    }

    /// `split_while_huge` only modifies `mappings`, not `cur_va`.
    pub broadcast proof fn lemma_split_while_huge_preserves_cur_va(self, size: usize)
        ensures #[trigger] self.split_while_huge(size).cur_va == self.cur_va
        decreases self.query_mapping().page_size
    {
        if self.present() {
            let m = self.query_mapping();
            if m.page_size > size {
                let new_size = m.page_size / NR_ENTRIES;
                let new_self = self.split_if_mapped_huge_spec(new_size);
                // split_if_mapped_huge_spec preserves cur_va (it's in the struct literal)
                assert(new_self.cur_va == self.cur_va);
                // Use the same admits as in split_while_huge itself
                assert(new_self.present()) by { admit() };
                assert(new_self.query_mapping().page_size < m.page_size) by { admit() };
                Self::lemma_split_while_huge_preserves_cur_va(new_self, size);
            }
        }
    }

    pub open spec fn remove_subtree(self, size: usize) -> Set<Mapping> {
        let subtree = self.mappings.filter(|m: Mapping|
            self.cur_va <= m.va_range.start < self.cur_va + size);
        self.mappings - subtree
    }

    /// Inserts a mapping into the cursor. If there were previously mappings there,
    /// they are removed. Note that multiple mappings might be removed if they overlap with
    /// a new large mapping.
    pub open spec fn map_spec(self, paddr: Paddr, size: usize, prop: PageProperty) -> Self {
        let new = Mapping {
            va_range: self.cur_slot_range(size),
            pa_range: paddr..(paddr + size) as usize,
            page_size: size,
            property: prop,
        };
        let split_self = self.split_while_huge(size);
        CursorView {
            cur_va: split_self.align_up_spec(size),
            mappings: split_self.remove_subtree(size) + set![new],
            ..split_self
        }
    }

    ///
    pub open spec fn map_simple(self, paddr: Paddr, size: usize, prop: PageProperty) -> Self {
        let new = Mapping {
            va_range: self.cur_slot_range(size),
            pa_range: paddr..(paddr + size) as usize,
            page_size: size,
            property: prop,
        };
        CursorView {
            cur_va: self.cur_va,
            mappings: self.mappings + set![new],
            ..self
        }
    }

    /// Unmaps a range of virtual addresses from the current address up to `len` bytes.
    /// It returns the number of mappings that were removed.
    ///
    /// Because the implementation may split huge pages that straddle the range
    /// boundaries, the spec first applies `split_while_huge` at both `cur_va`
    /// and `cur_va + len` to obtain a "base" set of mappings where all boundary
    /// entries are at the finest granularity.  Mappings whose `va_range.start`
    /// falls in `[cur_va, cur_va + len)` are then removed from this base.
    pub open spec fn unmap_spec(self, len: usize, new_view: Self, num_unmapped: usize) -> bool {
        // Split the mapping at the start boundary
        let after_start_split = self.split_while_huge(PAGE_SIZE);
        // Split the mapping at the end boundary
        let at_end = CursorView { cur_va: (self.cur_va + len) as Vaddr, ..after_start_split };
        let after_both_splits = at_end.split_while_huge(PAGE_SIZE);
        let base = CursorView { cur_va: self.cur_va, ..after_both_splits };
        let taken = base.mappings.filter(|m: Mapping|
            self.cur_va <= m.va_range.start < self.cur_va + len);
            &&& new_view.cur_va >= (self.cur_va + len) as Vaddr
            &&& new_view.mappings == base.mappings - taken
            &&& num_unmapped == taken.len() as usize
    }

    /// Composition law for `split_while_huge`:
    /// splitting to a finer target `s2 <= s1` is the same as first splitting to `s1` and then
    /// further splitting to `s2`.  This holds because `split_while_huge(s1)` leaves the current
    /// mapping with `page_size <= s1`, so a subsequent `split_while_huge(s2)` (with `s2 <= s1`)
    /// produces the same result as applying `split_while_huge(s2)` directly.
    pub proof fn split_while_huge_compose(self, s1: usize, s2: usize)
        requires
            s2 <= s1,
        ensures
            self.split_while_huge(s2) == self.split_while_huge(s1).split_while_huge(s2),
    { admit() }

    /// When the current entry is absent or maps at `page_size <= size`, `split_while_huge(size)`
    /// is a no-op.  Applying a second call with the same `size` therefore returns the same value.
    pub proof fn split_while_huge_idempotent(self, size: usize)
        ensures
            self.split_while_huge(size).split_while_huge(size) == self.split_while_huge(size),
    {
        // Follows from split_while_huge_compose with s1 = s2 = size.
        self.split_while_huge_compose(size, size);
    }

    /// Models `protect_next`: find the next mapping in range, split it to
    /// `target_page_size` if it is a huge page, then update its property via `op`.
    ///
    /// `target_page_size` corresponds to the cursor level after `find_next_impl`
    /// with `split_huge = true` — this is determined by the page table structure
    /// and cannot be derived from the abstract view alone.
    pub open spec fn protect_spec(self, len: usize, op: spec_fn(PageProperty) -> PageProperty, target_page_size: usize) -> (Self, Option<Range<Vaddr>>) {
        let (find_cursor, next) = self.find_next_impl_spec(len, false, true);
        if next is Some {
            let found = next.unwrap();
            // Position cursor at the found mapping and split to target size
            let at_found = CursorView {
                cur_va: found.va_range.start as Vaddr,
                ..self
            };
            let split_view = at_found.split_while_huge(target_page_size);
            // The mapping at cur_va in the split view is the one to protect
            let split_mapping = split_view.query_mapping();
            let new_mapping = Mapping {
                property: op(split_mapping.property),
                ..split_mapping
            };
            let new_cursor = CursorView {
                cur_va: split_mapping.va_range.end,
                mappings: split_view.mappings - set![split_mapping] + set![new_mapping],
                ..self
            };
            (new_cursor, Some(split_mapping.va_range))
        } else {
            (find_cursor, None)
        }
    }
}

} // verus!
