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

    /// This function specifies the behavior of the `query` method. It returns the mapping
    pub open spec fn query_item_spec(self) -> Mapping
        recommends
            self.present(),
    {
        self.mappings.filter(|m: Mapping| m.va_range.start <= self.cur_va < m.va_range.end).choose()
    }

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

    pub open spec fn find_next_spec(self, len: usize) -> (Self, Option<Vaddr>) {
        let (cursor, mapping) = self.find_next_impl_spec(len, false, false);
        if mapping is Some {
            (cursor, Some(mapping.unwrap().va_range.start))
        } else {
            (cursor, None)
        }
    }

    pub open spec fn jump_spec(self, va: usize) -> Self {
        CursorView {
            cur_va: va as Vaddr,
            ..self
        }
    }

    pub open spec fn map_spec(self, item: Mapping) -> Self {
        CursorView {
            cur_va: item.va_range.end,
            mappings: self.mappings.insert(item),
            ..self
        }
    }

    pub open spec fn unmap_spec(self, len: usize) -> (Self, usize) {
        let taken = self.mappings.filter(|m: Mapping| self.cur_va <= m.va_range.start < self.cur_va + len);
        let remaining = self.mappings.difference(taken);
        (CursorView {
            cur_va: (self.cur_va + len) as Vaddr,
            mappings: remaining,
            ..self
        }, taken.len() as usize)
    }

    pub open spec fn protect_spec(self, len: usize, op: impl Fn(PageProperty) -> PageProperty) -> (Self, Option<Range<Vaddr>>) {
        let (cursor, next) = self.find_next_impl_spec(len, false, true);
        if next is Some {
            // TODO: Protect the page
            (cursor, Some(next.unwrap().va_range))
        } else {
            (cursor, None)
        }
    }
}

} // verus!
