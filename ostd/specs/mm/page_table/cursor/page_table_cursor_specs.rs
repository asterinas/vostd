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

impl<C: PageTableConfig> CursorView<C> {
    /* A `CursorView` is not aware that the underlying structure of the page table is a tree.
       It is concerned with the elements that can be reached by moving forward (the `rear` of the structure)
       and, to a lesser degree, those that have already been traversed (the `fore`).

       It also tracks a `cur_va` and a `step`. Even in an "empty" view (one in which none of the subtree is mapped)
       `move_forward` can update `cur_va` by adding `step` to it. `push_level` and `pop_level` decrease and increase
       `step`, respectively. If the new virtual address would be aligned to `step`, `move_forward` additionally increases
       `step` until it is no longer aligned, if possible. Functions that remove entries from the page table entirely
       remove them in `step`-sized chunks.
    */

    pub open spec fn present(self) -> bool {
        self.mappings.filter(|m: Mapping| m.va_range.start <= self.cur_va < m.va_range.end).len() > 0
    }

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
