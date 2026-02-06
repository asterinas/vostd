use vstd::prelude::*;

use vstd::set_lib::*;

use vstd_extra::ownership::*;
use vstd_extra::prelude::TreePath;

use crate::mm::page_table::*;
use crate::mm::{Paddr, PagingConstsTrait, PagingLevel, Vaddr};
use crate::specs::arch::mm::{NR_ENTRIES, NR_LEVELS, PAGE_SIZE};
use crate::specs::arch::paging_consts::PagingConsts;
use crate::specs::mm::page_table::cursor::owners::*;
use crate::specs::mm::page_table::*;
use crate::mm::page_prop::PageProperty;

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

    /// This function checks if the current virtual address is mapped. It does not correspond
    /// to a cursor method itself, but defines what it means for an entry to present:
    /// there is a mapping whose virtual address range contains the current virtual address.
    pub open spec fn present(self) -> bool {
        self.mappings.filter(|m: Mapping| m.va_range.start <= self.cur_va < m.va_range.end).len() > 0
    }

    /// This function specifies the behavior of the `query` method. It returns the mapping containing
    /// the current virtual address.
    pub open spec fn query_item_spec(self) -> Mapping
        recommends
            self.present(),
    {
        self.mappings.filter(|m: Mapping| m.va_range.start <= self.cur_va < m.va_range.end).choose()
    }

    /// The specification for the internal function, `find_next_impl`. It finds the next mapped virtual address
    /// that is at most `len` bytes away from the current virtual address. TODO: add the specifications for
    /// `find_unmap_subtree` and `split_huge`, which are used by other functions that call thie one.
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

    /// Inserts a mapping into the cursor. If there were previously mappings there,
    /// they are removed. Note that multiple mappings might be removed if they overlap with
    /// a new large mapping.
    pub open spec fn map_spec(self, paddr: Paddr, size: usize, prop: PageProperty) -> Self {
        let existing = self.mappings.filter(|m: Mapping|
            self.cur_va <= m.va_range.start < m.va_range.end <= self.cur_va + size);
        let new = Mapping {
            va_range: self.cur_va..(self.cur_va + size) as usize,
            pa_range: paddr..(paddr + size) as usize,
            page_size: size,
            property: prop,
        };
        CursorView {
            cur_va: self.align_up_spec(size),
            mappings: self.mappings - existing + set![new],
            ..self
        }
    }

    /// Unmaps a range of virtual addresses from the current address up to `len` bytes.
    /// It returns the number of mappings that were removed.
    pub open spec fn unmap_spec(self, len: usize) -> (Self, usize) {
        let taken = self.mappings.filter(|m: Mapping|
            self.cur_va <= m.va_range.start < self.cur_va + len);
        (CursorView {
            cur_va: (self.cur_va + len) as Vaddr,
            mappings: self.mappings.difference(taken),
            ..self
        }, taken.len() as usize)
    }

    pub open spec fn protect_spec(self, len: usize, op: impl Fn(PageProperty) -> PageProperty) -> (Self, Option<Range<Vaddr>>) {
        let (cursor, next) = self.find_next_impl_spec(len, false, true);
        if next is Some {
            // TODO: Model props in here
            (cursor, Some(next.unwrap().va_range))
        } else {
            (cursor, None)
        }
    }
}

} // verus!
