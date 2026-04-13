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
        decreases self.query_mapping().page_size when self.inv()
    {
        if self.present() {
            let m = self.query_mapping();
            if m.page_size > size {
                let new_size = m.page_size / NR_ENTRIES;
                let new_self = self.split_if_mapped_huge_spec(new_size);
                proof {
                    let f = self.mappings.filter(|m2: Mapping| m2.va_range.start <= self.cur_va < m2.va_range.end);
                    vstd::set::axiom_set_intersect_finite::<Mapping>(
                        self.mappings, Set::new(|m2: Mapping| m2.va_range.start <= self.cur_va < m2.va_range.end));
                    vstd::set::axiom_set_choose_len(f);
                    assert(self.mappings.contains(m));
                    assert(m.inv());
                    assert(NR_ENTRIES == 512);
                    assert(m.page_size % (m.page_size / 512usize) == 0) by {
                        if m.page_size == 4096 { assert(4096usize % (4096usize / 512usize) == 0); }
                        else if m.page_size == 2097152 { assert(2097152usize % (2097152usize / 512usize) == 0); }
                        else { assert(1073741824usize % (1073741824usize / 512usize) == 0); }
                    };
                    Self::split_if_mapped_huge_spec_preserves_present(self, new_size);
                    Self::split_if_mapped_huge_spec_decreases_page_size(self, new_size);
                }
                new_self.split_while_huge(size)
            } else {
                self
            }
        } else {
            self
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
        let start = self.cur_va;
        let end = (self.cur_va + len) as Vaddr;
        // Cursor advanced past the range.
        &&& new_view.cur_va >= end
        // Mappings fully outside [start, end) are preserved.
        // (A mapping that straddles a boundary may be split, but its sub-mappings
        // outside the range are present — see refinement clause.)
        &&& forall |m: Mapping| #[trigger] self.mappings.contains(m)
            && (m.va_range.end <= start || m.va_range.start >= end)
            ==> new_view.mappings.contains(m)
        // No mapping in the new view starts inside [start, end), UNLESS it is
        // a sub-mapping of an old entry that straddled the start boundary.
        // (When a huge page straddles `start`, splitting it produces sub-mappings
        // whose `start` may fall inside [start, end) but before the cursor.)
        &&& forall |m: Mapping| new_view.mappings.contains(m)
            && start <= m.va_range.start < end
            ==> exists |parent: Mapping| #[trigger] self.mappings.contains(parent)
                && parent.va_range.start < start
                && parent.va_range.start <= m.va_range.start
                && m.va_range.end <= parent.va_range.end
                && m.pa_range.start == (parent.pa_range.start + (m.va_range.start - parent.va_range.start)) as Paddr
                && m.property == parent.property
        // New mappings are either from the old view or are sub-mappings of
        // old entries that straddled a boundary (refinement).
        &&& forall |m: Mapping| new_view.mappings.contains(m)
            ==> self.mappings.contains(m)
            || exists |parent: Mapping| #[trigger] self.mappings.contains(parent)
                && parent.va_range.start <= m.va_range.start
                && m.va_range.end <= parent.va_range.end
                && m.pa_range.start == (parent.pa_range.start + (m.va_range.start - parent.va_range.start)) as Paddr
                && m.property == parent.property
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
