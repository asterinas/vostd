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

    /// After `split_if_mapped_huge_spec(new_size)`, a sub-mapping at `cur_va`
    /// still exists.  The witness is `split_index(m, new_size, k)` where
    /// `k = (cur_va - m.va_range.start) / new_size`.
    pub proof fn split_if_mapped_huge_spec_preserves_present(v: Self, new_size: usize)
        requires
            v.inv(),
            v.present(),
            new_size > 0,
            v.query_mapping().page_size > 0,
            v.query_mapping().page_size % new_size == 0,
        ensures
            v.split_if_mapped_huge_spec(new_size).present(),
    {
        let cur_va = v.cur_va;
        let m = v.query_mapping();
        let ps = m.page_size;

        // Step 1: m covers cur_va.
        // present() = filter.len() > 0 where filter = mappings.filter(pred).
        // query_mapping() = filter.choose().
        // From inv(): mappings.finite() ⇒ filter.finite().
        // axiom_set_choose_len: finite ∧ len ≠ 0 ⇒ contains(choose()).
        // So filter.contains(m), meaning m satisfies the predicate.
        //
        // Rather than reconstructing the filter, assert the consequence directly:
        // query_mapping() ∈ mappings and covers cur_va.
        assert(v.mappings.contains(m) && m.va_range.start <= cur_va && cur_va < m.va_range.end) by {
            // The filter set used by present()/query_mapping()
            let f = v.mappings.filter(|m2: Mapping| m2.va_range.start <= v.cur_va < m2.va_range.end);
            assert(f.finite()) by {
                vstd::set::axiom_set_intersect_finite::<Mapping>(
                    v.mappings,
                    Set::new(|m2: Mapping| m2.va_range.start <= v.cur_va < m2.va_range.end));
            };
            vstd::set::axiom_set_choose_len(f);
        };
        assert(m.inv());
        assert(m.va_range.start + ps == m.va_range.end);

        // Step 2: compute witness index k = (cur_va - m.va_range.start) / new_size.
        let diff: int = cur_va as int - m.va_range.start as int;
        let ki: int = diff / new_size as int;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(diff, new_size as int);
        vstd::arithmetic::div_mod::lemma_mod_division_less_than_divisor(diff, new_size as int);
        vstd::arithmetic::div_mod::lemma_div_pos_is_pos(diff, new_size as int);
        // diff == ki * new_size + diff % new_size, 0 <= diff % new_size < new_size, ki >= 0.

        // Step 3: ki < ps / new_size (witness is in range).
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ps as int, new_size as int);
        assert(ki < ps as int / new_size as int) by {
            if ki >= ps as int / new_size as int {
                vstd::arithmetic::mul::lemma_mul_inequality(
                    ps as int / new_size as int, ki, new_size as int);
            }
        };

        // Step 4: the sub-mapping covers cur_va.
        let sub = Self::split_index(m, new_size, ki as usize);
        // From fundamental_div_mod: ki * new_size <= diff < (ki + 1) * new_size.
        // sub.va_range = [m.start + ki*new_size, m.start + (ki+1)*new_size)
        // cur_va = m.start + diff, so sub covers cur_va.
        // Help the solver with the usize ↔ int connection:
        assert(ki * (new_size as int) >= 0) by {
            vstd::arithmetic::mul::lemma_mul_nonnegative(ki, new_size as int);
        };
        assert((ki + 1) * (new_size as int) <= ps as int) by {
            vstd::arithmetic::mul::lemma_mul_inequality(
                ki + 1, ps as int / new_size as int, new_size as int);
        };
        // Values stay within [0, m.va_range.end) ⊂ [0, MAX_USERSPACE_VADDR), so no usize overflow.
        // Connect sub's range to int arithmetic (no usize overflow since values < MAX_USERSPACE_VADDR).
        assert(m.va_range.start as int + (ki + 1) * (new_size as int)
            <= (m.va_range.end as int)) by {
            vstd::arithmetic::mul::lemma_mul_is_commutative(ki + 1, new_size as int);
            vstd::arithmetic::mul::lemma_mul_is_commutative(
                ps as int / new_size as int, new_size as int);
        };
        // The as-usize cast is a no-op: all values are in [0, MAX_USERSPACE_VADDR).
        assert(ki as usize as int == ki);
        vstd::arithmetic::mul::lemma_mul_is_distributive_add(new_size as int, ki, 1 as int);
        assert((cur_va as int) >= (m.va_range.start as int) + ki * (new_size as int));
        assert((cur_va as int) < (m.va_range.start as int) + (ki + 1) * (new_size as int));
        assert(sub.va_range.start <= cur_va);
        assert(cur_va < sub.va_range.end);

        // Step 5: sub ∈ new_self.mappings.
        // ki is in the domain of the map, so sub = split_index(m, new_size, ki) is in new_mappings.
        let new_self = v.split_if_mapped_huge_spec(new_size);
        let domain = Set::<int>::new(|n:int| 0 <= n < ps as int / new_size as int);
        assert(domain.contains(ki));
        assert(new_self.mappings.contains(sub));

        // Step 6: new_self.present().
        // sub is in new_self.mappings and covers cur_va, so it's in the filter.
        // The filter is finite (subset of new_self.mappings which is finite due to
        // finite original mappings + finite new_mappings).
        // finite + non-empty → len > 0 → present().
        let new_filter = new_self.mappings.filter(
            |m2: Mapping| m2.va_range.start <= new_self.cur_va < m2.va_range.end);
        assert(new_filter.contains(sub));
        assert(new_self.mappings.finite()) by {
            // v.mappings - {m} is finite (remove from finite).
            vstd::set::axiom_set_remove_finite(v.mappings, m);
            // new_mappings = domain.map(f) where domain = int::range_set(0, ps/new_size) is finite.
            let domain = Set::<int>::new(|n:int| 0 <= n < ps as int / new_size as int);
            assert(domain =~= int::range_set(0int, ps as int / new_size as int));
            vstd::set_lib::range_set_properties::<int>(0int, ps as int / new_size as int);
            domain.lemma_map_finite(|n:int| Self::split_index(m, new_size, n as usize));
            // (v.mappings - {m}) ∪ new_mappings: union of two finite sets.
            vstd::set::axiom_set_union_finite(
                v.mappings.remove(m),
                domain.map(|n:int| Self::split_index(m, new_size, n as usize)));
        };
        assert(new_filter.finite()) by {
            vstd::set::axiom_set_intersect_finite::<Mapping>(
                new_self.mappings,
                Set::new(|m2: Mapping| m2.va_range.start <= new_self.cur_va < m2.va_range.end));
        };
        vstd::set::axiom_set_contains_len(new_filter, sub);
    }

    /// After `split_if_mapped_huge_spec(new_size)` on a valid view, the
    /// mapping at `cur_va` has `page_size == new_size < m.page_size`.
    ///
    /// The sub-mapping `split_index(m, new_size, k)` has `page_size = new_size`.
    /// No other mapping from the original view covers `cur_va` (non-overlapping),
    /// so `query_mapping()` must return a sub-mapping with `page_size = new_size`.
    pub proof fn split_if_mapped_huge_spec_decreases_page_size(v: Self, new_size: usize)
        requires
            v.inv(),
            v.present(),
            new_size > 0,
            v.query_mapping().page_size > new_size,
            v.query_mapping().page_size % new_size == 0,
        ensures
            v.split_if_mapped_huge_spec(new_size).present(),
            v.split_if_mapped_huge_spec(new_size).query_mapping().page_size < v.query_mapping().page_size,
    {
        Self::split_if_mapped_huge_spec_preserves_present(v, new_size);

        let cur_va = v.cur_va;
        let m = v.query_mapping();
        let new_self = v.split_if_mapped_huge_spec(new_size);
        let m2 = new_self.query_mapping();
        let ps = m.page_size;

        // m covers cur_va (same chain as in preserves_present)
        assert(v.mappings.contains(m) && m.va_range.start <= cur_va && cur_va < m.va_range.end) by {
            let f = v.mappings.filter(
                |m2: Mapping| m2.va_range.start <= v.cur_va < m2.va_range.end);
            assert(f.finite()) by {
                vstd::set::axiom_set_intersect_finite::<Mapping>(
                    v.mappings,
                    Set::new(|m2: Mapping| m2.va_range.start <= v.cur_va < m2.va_range.end));
            };
            vstd::set::axiom_set_choose_len(f);
        };

        // m2 covers cur_va (from new_self.present() + choose)
        assert(new_self.mappings.contains(m2)
            && m2.va_range.start <= cur_va && cur_va < m2.va_range.end) by {
            let f = new_self.mappings.filter(
                |m3: Mapping| m3.va_range.start <= new_self.cur_va < m3.va_range.end);
            assert(new_self.mappings.finite()) by {
                vstd::set::axiom_set_remove_finite(v.mappings, m);
                let domain = Set::<int>::new(|n:int| 0 <= n < ps as int / new_size as int);
                assert(domain =~= int::range_set(0int, ps as int / new_size as int));
                vstd::set_lib::range_set_properties::<int>(0int, ps as int / new_size as int);
                domain.lemma_map_finite(|n:int| Self::split_index(m, new_size, n as usize));
                vstd::set::axiom_set_union_finite(
                    v.mappings.remove(m),
                    domain.map(|n:int| Self::split_index(m, new_size, n as usize)));
            };
            assert(f.finite()) by {
                vstd::set::axiom_set_intersect_finite::<Mapping>(
                    new_self.mappings,
                    Set::new(|m3: Mapping| m3.va_range.start <= new_self.cur_va < m3.va_range.end));
            };
            vstd::set::axiom_set_choose_len(f);
        };

        // m2 ∈ new_self.mappings = (v.mappings - {m}) ∪ new_mappings.
        // If m2 ∈ v.mappings - {m}: m2 ≠ m, m2 ∈ v.mappings, m2 covers cur_va.
        //   But m also covers cur_va and m ∈ v.mappings. From inv (non-overlapping): m == m2.
        //   Contradiction with m2 ≠ m.
        // So m2 ∈ new_mappings, hence m2.page_size == new_size < m.page_size.
        if v.mappings.contains(m2) && m2 != m {
            // Both m and m2 are in v.mappings and both cover cur_va. Non-overlapping ⇒ m == m2.
            assert(m.va_range.end <= m2.va_range.start || m2.va_range.end <= m.va_range.start);
            // But both cover cur_va: m.start <= cur_va < m.end AND m2.start <= cur_va < m2.end.
            // Contradiction with disjointness.
            assert(false);
        }
        // So m2 ∉ v.mappings or m2 == m.
        // m2 ∈ new_self.mappings = (v.mappings - {m}) ∪ new_mappings.
        // If m2 == m: m ∉ (v.mappings - {m}), so m2 ∈ new_mappings. m2.page_size = new_size. ✓
        // If m2 ∉ v.mappings: m2 ∉ (v.mappings - {m}), so m2 ∈ new_mappings. m2.page_size = new_size. ✓
        // Either way: m2.page_size == new_size < m.page_size.
        // m2 ∉ (v.mappings - {m}), so m2 ∈ new_mappings.
        // All elements of new_mappings have page_size == new_size.
        assert(!v.mappings.remove(m).contains(m2));
        let new_mappings = Set::<int>::new(
            |n:int| 0 <= n < ps as int / new_size as int
        ).map(|n:int| Self::split_index(m, new_size, n as usize));
        assert(new_mappings.contains(m2));
        let k = choose|k: int| 0 <= k < ps as int / new_size as int
            && #[trigger] Self::split_index(m, new_size, k as usize) == m2;
        assert(m2.page_size == new_size);
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

    /// `split_while_huge` only modifies `mappings`, not `cur_va`.
    pub broadcast proof fn lemma_split_while_huge_preserves_cur_va(self, size: usize)
        requires self.inv(),
        ensures #[trigger] self.split_while_huge(size).cur_va == self.cur_va
        decreases self.query_mapping().page_size
    {
        if self.present() {
            let m = self.query_mapping();
            if m.page_size > size {
                let new_size = m.page_size / NR_ENTRIES;
                let new_self = self.split_if_mapped_huge_spec(new_size);
                assert(new_self.inv()) by { admit() }; // split_if_mapped_huge_spec preserves inv
                // Decreases: new_self.query_mapping().page_size < m.page_size
                let f = self.mappings.filter(|m2: Mapping| m2.va_range.start <= self.cur_va < m2.va_range.end);
                vstd::set::axiom_set_intersect_finite::<Mapping>(
                    self.mappings, Set::new(|m2: Mapping| m2.va_range.start <= self.cur_va < m2.va_range.end));
                vstd::set::axiom_set_choose_len(f);
                assert(m.inv());
                
                Self::split_if_mapped_huge_spec_decreases_page_size(self, new_size);
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
        &&& forall |m: Mapping| self.mappings.contains(m)
            && (m.va_range.end <= start || m.va_range.start >= end)
            ==> new_view.mappings.contains(m)
        // No mapping in the new view starts inside [start, end).
        &&& forall |m: Mapping| new_view.mappings.contains(m)
            ==> !(start <= m.va_range.start < end)
        // New mappings are either from the old view or are sub-mappings of
        // old entries that straddled a boundary (refinement).
        &&& forall |m: Mapping| new_view.mappings.contains(m)
            ==> self.mappings.contains(m)
            || exists |parent: Mapping| self.mappings.contains(parent)
                && parent.va_range.start <= m.va_range.start
                && m.va_range.end <= parent.va_range.end
                && m.pa_range.start == (parent.pa_range.start + (m.va_range.start - parent.va_range.start)) as Paddr
                && m.property == parent.property
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

    /// When `split_while_huge(size)` is a no-op and the view is `present()`,
    /// the mapping at `cur_va` already has `page_size <= size`.
    ///
    /// Follows from one step of unfolding: if `page_size > size`, the function
    /// would recurse and modify mappings, so it couldn't be a no-op.
    pub proof fn split_while_huge_noop_implies_page_size_le(self, size: usize)
        requires
            self.split_while_huge(size) == self,
            self.present(),
        ensures
            self.query_mapping().page_size <= size,
    {
        // From the definition: present() && page_size > size ⇒ recurse.
        // The recursion calls split_if_mapped_huge_spec which changes mappings
        // (removes the old mapping, adds sub-mappings).  So the result ≠ self.
        // Therefore page_size <= size.
        admit()
    }

    /// When the mapping at `cur_va` is exactly one split-step above `size`
    /// (i.e. `query_mapping().page_size / NR_ENTRIES == size`), one step of
    /// `split_while_huge` equals `split_if_mapped_huge_spec`:
    ///
    /// `self.split_while_huge(size) == self.split_if_mapped_huge_spec(size)`
    ///
    /// This is because `split_while_huge` takes one step
    /// `split_if_mapped_huge_spec(m.page_size / NR_ENTRIES)` = `split_if_mapped_huge_spec(size)`,
    /// then the sub-mapping at `cur_va` has `page_size == size <= size`, so it stops.
    pub proof fn split_while_huge_one_step(self, size: usize)
        requires
            self.present(),
            self.query_mapping().page_size > size,
            self.query_mapping().page_size / NR_ENTRIES == size,
        ensures
            self.split_while_huge(size).mappings
                =~= self.split_if_mapped_huge_spec(size).mappings,
    {
        // Unfold split_while_huge one step:
        // split_while_huge(size) = split_if_mapped_huge_spec(m.page_size / NR_ENTRIES).split_while_huge(size)
        //                        = split_if_mapped_huge_spec(size).split_while_huge(size)
        //
        // After split_if_mapped_huge_spec(size), the sub-mapping at cur_va has page_size == size.
        // split_while_huge(size) on this result: present, page_size <= size, returns self.
        // So: split_while_huge(size) == split_if_mapped_huge_spec(size).
        //
        // The admits in split_while_huge's decreases check prevent direct unfolding.
        admit()
    }

    /// Locality of `split_if_mapped_huge_spec`: a mapping `m2` whose VA range
    /// is disjoint from the mapping at `cur_va` is preserved.
    ///
    /// Proof: `split_if_mapped_huge_spec` does `self.mappings - {m} + new_mappings`
    /// where `m = query_mapping()` contains `cur_va`.
    /// - `m2 != m` because `m2.va_range` is disjoint from `m.va_range`.
    /// - `m2 ∉ new_mappings` because sub-mappings are within `m.va_range`.
    pub proof fn split_if_mapped_huge_spec_locality(self, new_size: usize, m2: Mapping)
        requires
            self.inv(),
            self.present(),
            Mapping::disjoint_vaddrs(m2, self.query_mapping()),
        ensures
            self.split_if_mapped_huge_spec(new_size).mappings.contains(m2)
                == self.mappings.contains(m2),
    {
        let m = self.query_mapping();
        let size = m.page_size;
        let new_mappings = Set::<int>::new(|n: int| 0 <= n < size / new_size)
            .map(|n: int| Self::split_index(m, new_size, n as usize));

        // Establish m covers cur_va (from present() + choose semantics).
        let f = self.mappings.filter(
            |m2: Mapping| m2.va_range.start <= self.cur_va < m2.va_range.end);
        assert(f.finite()) by {
            vstd::set::axiom_set_intersect_finite::<Mapping>(
                self.mappings,
                Set::new(|m2: Mapping| m2.va_range.start <= self.cur_va < m2.va_range.end));
        };
        vstd::set::axiom_set_choose_len(f);
        assert(self.mappings.contains(m));
        assert(m.va_range.start <= self.cur_va < m.va_range.end);

        // m2 != m: m contains cur_va but m2.va_range is disjoint from m.va_range.
        // If m2 == m, then their ranges are equal, contradicting disjointness
        // (since m.va_range is non-empty from m.inv()).
        assert(m.inv());
        assert(m.va_range.start < m.va_range.end);

        // m2 ∉ new_mappings: sub-mappings have va_range.start in [m.start, m.end),
        // so they overlap m. Since m2 is disjoint from m, m2 can't be a sub-mapping.
        assert(!new_mappings.contains(m2)) by {
            if new_mappings.contains(m2) {
                let k = choose|k: int| 0 <= k < size as int / new_size as int
                    && #[trigger] Self::split_index(m, new_size, k as usize) == m2;
                // Unfold split_index to get va_range bounds.
                let si = Self::split_index(m, new_size, k as usize);
                // si.va_range.start = m.va_range.start + k * new_size
                // k >= 0 and new_size >= 0, so si.va_range.start >= m.va_range.start.
                // si.va_range.end = m.va_range.start + (k+1) * new_size
                // k+1 <= size/new_size, so (k+1)*new_size <= size.
                // si.va_range.end <= m.va_range.start + size = m.va_range.end.
                // So si.va_range ⊂ m.va_range, meaning si overlaps m.
                // Since m2 == si, m2 overlaps m — contradicts disjoint_vaddrs.
                admit(); // sub-mapping va_range containment arithmetic
            }
        };
        // result.mappings = (self.mappings - {m}) + new_mappings
        // m2 != m (from disjoint_vaddrs + non-empty range) and m2 ∉ new_mappings.
        // So: m2 ∈ result ⟺ m2 ∈ self.mappings.
    }

    /// Locality of `split_while_huge`: a mapping `m2` that is in `self.mappings`
    /// and whose VA range does not contain `cur_va` is preserved.
    ///
    /// This is stronger than `split_if_mapped_huge_spec_locality` because it
    /// handles the recursive case: each step only splits the mapping at `cur_va`,
    /// and `m2` is disjoint from that mapping (by non-overlap invariant).
    #[verifier::rlimit(80)]
    pub proof fn split_while_huge_locality(self, size: usize, m2: Mapping)
        requires
            self.inv(),
            self.mappings.contains(m2),
            !(m2.va_range.start <= self.cur_va < m2.va_range.end),
        ensures
            self.split_while_huge(size).mappings.contains(m2),
        decreases self.query_mapping().page_size,
    {
        if self.present() {
            let m = self.query_mapping();
            if m.page_size > size {
                let new_size = m.page_size / NR_ENTRIES;
                // Establish m covers cur_va.
                let f = self.mappings.filter(
                    |m3: Mapping| m3.va_range.start <= self.cur_va < m3.va_range.end);
                assert(f.finite()) by {
                    vstd::set::axiom_set_intersect_finite::<Mapping>(
                        self.mappings,
                        Set::new(|m3: Mapping| m3.va_range.start <= self.cur_va < m3.va_range.end));
                };
                vstd::set::axiom_set_choose_len(f);
                assert(self.mappings.contains(m));
                assert(m.va_range.start <= self.cur_va < m.va_range.end);
                assert(m.inv());
                // m2 != m and disjoint va_ranges (non-overlap invariant).
                assert(Mapping::disjoint_vaddrs(m2, m));
                // page_size % new_size == 0
                assert(NR_ENTRIES == 512usize);
                assert(m.page_size % new_size == 0) by {
                    if m.page_size == 4096 { assert(4096usize % (4096usize / 512usize) == 0); }
                    else if m.page_size == 2097152 { assert(2097152usize % (2097152usize / 512usize) == 0); }
                    else { assert(1073741824usize % (1073741824usize / 512usize) == 0); }
                };
                self.split_if_mapped_huge_spec_locality(new_size, m2);
                let new_self = self.split_if_mapped_huge_spec(new_size);
                assert(new_self.inv()) by { admit() }; // split_if_mapped_huge_spec preserves inv
                Self::split_if_mapped_huge_spec_decreases_page_size(self, new_size);
                new_self.split_while_huge_locality(size, m2);
            }
        }
    }

    /// Converse locality: a mapping NOT in `self.mappings` and whose VA range
    /// does not overlap any mapping in `self.mappings` that contains `cur_va`
    /// is also NOT in `self.split_while_huge(size).mappings`.
    ///
    /// More precisely: if `m2 ∉ self.mappings` and `m2.va_range` is disjoint
    /// from the range `[start, end)` of the mapping at `cur_va` (if present),
    /// then `m2 ∉ self.split_while_huge(size).mappings`.
    #[verifier::rlimit(120)]
    pub proof fn split_while_huge_locality_absent(self, size: usize, m2: Mapping)
        requires
            self.inv(),
            !self.mappings.contains(m2),
            self.present() ==> Mapping::disjoint_vaddrs(m2, self.query_mapping()),
        ensures
            !self.split_while_huge(size).mappings.contains(m2),
        decreases self.query_mapping().page_size,
    {
        if self.present() {
            let m = self.query_mapping();
            if m.page_size > size {
                let new_size = m.page_size / NR_ENTRIES;
                // Establish m covers cur_va and m.inv().
                let f = self.mappings.filter(
                    |m3: Mapping| m3.va_range.start <= self.cur_va < m3.va_range.end);
                assert(f.finite()) by {
                    vstd::set::axiom_set_intersect_finite::<Mapping>(
                        self.mappings,
                        Set::new(|m3: Mapping| m3.va_range.start <= self.cur_va < m3.va_range.end));
                };
                vstd::set::axiom_set_choose_len(f);
                assert(self.mappings.contains(m));
                // page_size % new_size == 0
                assert(m.inv());
                assert(m.page_size % new_size == 0) by {
                    assert(set![4096usize, 2097152usize, 1073741824usize].contains(m.page_size));
                    assert(4096usize % (4096usize / 512usize) == 0) by (compute_only);
                    assert(2097152usize % (2097152usize / 512usize) == 0) by (compute_only);
                    assert(1073741824usize % (1073741824usize / 512usize) == 0) by (compute_only);
                };
                self.split_if_mapped_huge_spec_locality(new_size, m2);
                let new_self = self.split_if_mapped_huge_spec(new_size);
                assert(new_self.inv()) by { admit() }; // split_if_mapped_huge_spec preserves inv
                Self::split_if_mapped_huge_spec_preserves_present(self, new_size);
                Self::split_if_mapped_huge_spec_decreases_page_size(self, new_size);
                // new_self is present. The new mapping at cur_va is a sub-mapping of m,
                // so its va_range ⊂ m.va_range. Since m2 is disjoint from m,
                // m2 is also disjoint from the new mapping.
                // TODO: prove sub-mapping va_range containment (split_index bounds).
                assume(new_self.present() ==>
                    Mapping::disjoint_vaddrs(m2, new_self.query_mapping()));
                new_self.split_while_huge_locality_absent(size, m2);
            }
        }
    }

    /// After `split_while_huge(size)`, the mapping at `cur_va` (if present) has
    /// `page_size <= size` and is in the result's mappings.
    pub proof fn split_while_huge_contains_query(self, size: usize)
        requires
            self.inv(),
            self.present(),
        ensures
            self.split_while_huge(size).present(),
            self.split_while_huge(size).mappings.contains(
                self.split_while_huge(size).query_mapping()),
    {
        // split_while_huge preserves present (from split_if_mapped_huge_spec_preserves_present).
        // query_mapping() = filter.choose(), and present() = filter.len() > 0,
        // so choose() ∈ filter ⊆ mappings.
        admit()
    }

    /// Refinement: every mapping in `split_while_huge(size).mappings` is either
    /// from `self.mappings` or a sub-mapping of an entry in `self.mappings`.
    pub proof fn split_while_huge_refinement(self, size: usize, m: Mapping)
        requires
            self.inv(),
            self.split_while_huge(size).mappings.contains(m),
        ensures
            self.mappings.contains(m)
            || exists |parent: Mapping| self.mappings.contains(parent)
                && parent.va_range.start <= m.va_range.start
                && m.va_range.end <= parent.va_range.end
                && m.pa_range.start == (parent.pa_range.start + (m.va_range.start - parent.va_range.start)) as Paddr
                && m.property == parent.property,
    { admit() }

    /// `split_while_huge` produces a set disjoint from any set that was
    /// already disjoint from `self.mappings`.
    ///
    /// Proof sketch: `split_while_huge` only adds sub-mappings of the entry at
    /// `cur_va` and preserves all other entries from `self.mappings`.  If `other`
    /// is disjoint from `self.mappings`, then entries preserved from `self.mappings`
    /// aren't in `other`, and sub-mappings (with `va_range ⊂ query_mapping().va_range`)
    /// can't equal any entry in `other` because `other` has no entry overlapping
    /// the query mapping (which is in `self.mappings`).
    pub proof fn split_while_huge_disjoint(self, size: usize, other: Set<Mapping>)
        requires
            self.inv(),
            self.mappings.disjoint(other),
        ensures
            self.split_while_huge(size).mappings.disjoint(other),
    { admit() }

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
