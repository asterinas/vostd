use vstd::prelude::*;
use vstd::set::{axiom_set_choose_len, axiom_set_intersect_finite};
use vstd::set_lib::*;

use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;

use crate::mm::page_prop::PageProperty;
use crate::mm::page_table::*;
use crate::mm::{Paddr, PagingConstsTrait, PagingLevel, Vaddr};
use crate::specs::arch::mm::{NR_ENTRIES, NR_LEVELS, PAGE_SIZE};
use crate::specs::arch::MAX_PADDR;
use crate::specs::arch::paging_consts::PagingConsts;
use crate::specs::mm::page_table::cursor::owners::*;
use crate::specs::mm::page_table::owners::PageTableOwner;
use crate::specs::mm::page_table::Mapping;
use vstd_extra::arithmetic::*;

use crate::mm::page_table::page_size_spec as page_size;

verus! {

impl<C: PageTableConfig> CursorView<C> {

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

        assert(v.mappings.contains(m) && m.va_range.start <= cur_va && cur_va < m.va_range.end) by {
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

        let diff: int = cur_va as int - m.va_range.start as int;
        let ki: int = diff / new_size as int;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(diff, new_size as int);
        vstd::arithmetic::div_mod::lemma_mod_division_less_than_divisor(diff, new_size as int);
        vstd::arithmetic::div_mod::lemma_div_pos_is_pos(diff, new_size as int);

        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ps as int, new_size as int);
        assert(ki < ps as int / new_size as int) by {
            if ki >= ps as int / new_size as int {
                vstd::arithmetic::mul::lemma_mul_inequality(
                    ps as int / new_size as int, ki, new_size as int);
            }
        };

        let sub = Self::split_index(m, new_size, ki as usize);

        assert(ki * (new_size as int) >= 0) by {
            vstd::arithmetic::mul::lemma_mul_nonnegative(ki, new_size as int);
        };
        assert((ki + 1) * (new_size as int) <= ps as int) by {
            vstd::arithmetic::mul::lemma_mul_inequality(
                ki + 1, ps as int / new_size as int, new_size as int);
        };
        assert(m.va_range.start as int + (ki + 1) * (new_size as int)
            <= (m.va_range.end as int)) by {
            vstd::arithmetic::mul::lemma_mul_is_commutative(ki + 1, new_size as int);
            vstd::arithmetic::mul::lemma_mul_is_commutative(
                ps as int / new_size as int, new_size as int);
        };

        assert(ki as usize as int == ki);
        vstd::arithmetic::mul::lemma_mul_is_distributive_add(new_size as int, ki, 1 as int);
        assert((cur_va as int) >= (m.va_range.start as int) + ki * (new_size as int));
        assert((cur_va as int) < (m.va_range.start as int) + (ki + 1) * (new_size as int));
        assert(sub.va_range.start <= cur_va);
        assert(cur_va < sub.va_range.end);

        let new_self = v.split_if_mapped_huge_spec(new_size);
        let domain = Set::<int>::new(|n:int| 0 <= n < ps as int / new_size as int);
        assert(domain.contains(ki));
        assert(new_self.mappings.contains(sub));

        let new_filter = new_self.mappings.filter(
            |m2: Mapping| m2.va_range.start <= new_self.cur_va < m2.va_range.end);
        assert(new_filter.contains(sub));
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

        if v.mappings.contains(m2) && m2 != m {
            assert(m.va_range.end <= m2.va_range.start || m2.va_range.end <= m.va_range.start);
            assert(false);
        }

        assert(!v.mappings.remove(m).contains(m2));
        let new_mappings = Set::<int>::new(
            |n:int| 0 <= n < ps as int / new_size as int
        ).map(|n:int| Self::split_index(m, new_size, n as usize));
        assert(new_mappings.contains(m2));
        let k = choose|k: int| 0 <= k < ps as int / new_size as int
            && #[trigger] Self::split_index(m, new_size, k as usize) == m2;
        assert(m2.page_size == new_size);
    }

    /// `split_if_mapped_huge_spec` preserves `CursorView::inv()`.
    ///
    /// Requires: `v.inv()`, `v.present()`, the mapping at `cur_va` has
    /// `page_size > new_size`, `page_size % new_size == 0`, and `new_size`
    /// is itself a valid page size.
    pub proof fn split_if_mapped_huge_spec_preserves_inv(v: Self, new_size: usize)
        requires
            v.inv(),
            v.present(),
            new_size > 0,
            v.query_mapping().page_size > new_size,
            v.query_mapping().page_size % new_size == 0,
            set![4096usize, 2097152, 1073741824].contains(new_size),
        ensures
            v.split_if_mapped_huge_spec(new_size).inv(),
    {
        let cur_va = v.cur_va;
        let m = v.query_mapping();
        let ps = m.page_size;
        let ns: int = new_size as int;
        let new_self = v.split_if_mapped_huge_spec(new_size);
        let count: int = ps as int / ns;
        let domain = Set::<int>::new(|n: int| 0 <= n < count);
        let new_mappings = domain.map(|n: int| Self::split_index(m, new_size, n as usize));

        // --- Establish that m is in v.mappings and covers cur_va ---
        assert(v.mappings.contains(m) && m.va_range.start <= cur_va && cur_va < m.va_range.end) by {
            let f = v.mappings.filter(|m2: Mapping| m2.va_range.start <= v.cur_va < m2.va_range.end);
            assert(f.finite()) by {
                vstd::set::axiom_set_intersect_finite::<Mapping>(
                    v.mappings,
                    Set::new(|m2: Mapping| m2.va_range.start <= v.cur_va < m2.va_range.end));
            };
            vstd::set::axiom_set_choose_len(f);
        };
        assert(m.inv());

        // --- (1) cur_va preserved ---

        // --- (2) mappings.finite() ---
        assert(new_self.mappings.finite()) by {
            vstd::set::axiom_set_remove_finite(v.mappings, m);
            assert(domain =~= int::range_set(0int, count));
            vstd::set_lib::range_set_properties::<int>(0int, count);
            domain.lemma_map_finite(|n: int| Self::split_index(m, new_size, n as usize));
            vstd::set::axiom_set_union_finite(
                v.mappings.remove(m), new_mappings);
        };

        // --- Helper: ps == count * ns (no remainder) ---
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ps as int, ns);
        assert(ps as int == count * ns);

        assert(m.va_range.start % new_size as int == 0) by {
            vstd::arithmetic::mul::lemma_mul_is_commutative(count, ns);
            vstd::arithmetic::div_mod::lemma_mod_mod(
                m.va_range.start as int, ns, count);
        };
        assert(m.pa_range.start % new_size == 0) by {
            vstd::arithmetic::mul::lemma_mul_is_commutative(count, ns);
            vstd::arithmetic::div_mod::lemma_mod_mod(
                m.pa_range.start as int, ns, count);
        };

        // --- (3) All mappings satisfy Mapping::inv() ---
        assert forall|e: Mapping| new_self.mappings.contains(e) implies #[trigger] e.inv() by {
            if v.mappings.remove(m).contains(e) {
                assert(v.mappings.contains(e));
            } else {
                assert(new_mappings.contains(e));
                let k = choose|k: int| 0 <= k < count
                    && #[trigger] Self::split_index(m, new_size, k as usize) == e;
                let sub = Self::split_index(m, new_size, k as usize);

                // sub.page_size == new_size ∈ {4096, 2M, 1G}
                assert(set![4096usize, 2097152, 1073741824].contains(sub.page_size));

                // Alignment: (base + k * ns) % ns == base % ns == 0.
                // Use lemma_mod_multiples_vanish: (ns * a + b) % ns == b % ns.
                vstd::arithmetic::mul::lemma_mul_is_commutative(k, ns);
                vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(
                    k, m.va_range.start as int, ns);
                assert(sub.va_range.start % new_size as int == 0);
                vstd::arithmetic::mul::lemma_mul_is_commutative(k + 1, ns);
                vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(
                    k + 1, m.va_range.start as int, ns);
                assert(sub.va_range.end % new_size as int == 0);

                vstd::arithmetic::mul::lemma_mul_is_commutative(k, ns);
                vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(
                    k, m.pa_range.start as int, ns);
                assert(sub.pa_range.start % new_size == 0);
                vstd::arithmetic::mul::lemma_mul_is_commutative(k + 1, ns);
                vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(
                    k + 1, m.pa_range.start as int, ns);
                assert(sub.pa_range.end % new_size == 0);

                // Range spans exactly new_size.
                vstd::arithmetic::mul::lemma_mul_is_distributive_add(ns, k, 1int);
                assert(sub.va_range.start + new_size == sub.va_range.end);
                assert(sub.pa_range.start + new_size == sub.pa_range.end);

                // Bounds: sub is within m's range.
                vstd::arithmetic::mul::lemma_mul_nonnegative(k, ns);
                vstd::arithmetic::mul::lemma_mul_inequality(k + 1, count, ns);
                // (k+1)*ns <= count*ns = ps, so m.start + (k+1)*ns <= m.start + ps = m.end.
                assert(sub.va_range.start >= m.va_range.start);
                assert(sub.va_range.end <= m.va_range.end);
                assert(sub.va_range.start <= sub.va_range.end);

                assert(sub.pa_range.start >= m.pa_range.start);
                assert(sub.pa_range.end <= m.pa_range.end);
                assert(sub.pa_range.start <= sub.pa_range.end);
            }
        };

        // --- (4) Non-overlapping ---
        assert forall|e1: Mapping, e2: Mapping|
            #[trigger] new_self.mappings.contains(e1) &&
            #[trigger] new_self.mappings.contains(e2) &&
            e1 != e2
        implies
            e1.va_range.end <= e2.va_range.start || e2.va_range.end <= e1.va_range.start
        by {
            if v.mappings.remove(m).contains(e1) && v.mappings.remove(m).contains(e2) {
                // Both from original: inherit from v.inv().
                assert(v.mappings.contains(e1));
                assert(v.mappings.contains(e2));
            } else if v.mappings.remove(m).contains(e1) && new_mappings.contains(e2) {
                // e1 from original (disjoint from m), e2 sub-mapping within m.
                assert(v.mappings.contains(e1));
                assert(e1 != m);
                let k2 = choose|k: int| 0 <= k < count
                    && #[trigger] Self::split_index(m, new_size, k as usize) == e2;
                vstd::arithmetic::mul::lemma_mul_nonnegative(k2, ns);
                vstd::arithmetic::mul::lemma_mul_inequality(k2 + 1, count, ns);
                assert(e2.va_range.start >= m.va_range.start);
                assert(e2.va_range.end <= m.va_range.end);
            } else if new_mappings.contains(e1) && v.mappings.remove(m).contains(e2) {
                // Symmetric case.
                assert(v.mappings.contains(e2));
                assert(e2 != m);
                let k1 = choose|k: int| 0 <= k < count
                    && #[trigger] Self::split_index(m, new_size, k as usize) == e1;
                vstd::arithmetic::mul::lemma_mul_nonnegative(k1, ns);
                vstd::arithmetic::mul::lemma_mul_inequality(k1 + 1, count, ns);
                assert(e1.va_range.start >= m.va_range.start);
                assert(e1.va_range.end <= m.va_range.end);
            } else if new_mappings.contains(e1) && new_mappings.contains(e2) {
                // Both sub-mappings with different indices.
                let i = choose|k: int| 0 <= k < count
                    && #[trigger] Self::split_index(m, new_size, k as usize) == e1;
                let j = choose|k: int| 0 <= k < count
                    && #[trigger] Self::split_index(m, new_size, k as usize) == e2;
                vstd::arithmetic::mul::lemma_mul_nonnegative(i, ns);
                vstd::arithmetic::mul::lemma_mul_nonnegative(j, ns);
                if i < j {
                    vstd::arithmetic::mul::lemma_mul_inequality(i + 1, j, ns);
                    vstd::arithmetic::mul::lemma_mul_is_distributive_add(ns, i, 1int);
                } else {
                    vstd::arithmetic::mul::lemma_mul_inequality(j + 1, i, ns);
                    vstd::arithmetic::mul::lemma_mul_is_distributive_add(ns, j, 1int);
                }
            }
        };
    }

    /// `split_while_huge` only modifies `mappings`, not `cur_va`.
    pub broadcast proof fn lemma_split_while_huge_preserves_cur_va(self, size: usize)
        requires self.inv(), size >= PAGE_SIZE,
        ensures #[trigger] self.split_while_huge(size).cur_va == self.cur_va
        decreases if self.present() { self.query_mapping().page_size as int } else { 0 }
    {
        if self.present() {
            let m = self.query_mapping();
            if m.page_size > size {
                let new_size = m.page_size / NR_ENTRIES;
                let new_self = self.split_if_mapped_huge_spec(new_size);
                // Establish m.inv() first.
                let f = self.mappings.filter(|m2: Mapping| m2.va_range.start <= self.cur_va < m2.va_range.end);
                vstd::set::axiom_set_intersect_finite::<Mapping>(
                    self.mappings, Set::new(|m2: Mapping| m2.va_range.start <= self.cur_va < m2.va_range.end));
                vstd::set::axiom_set_choose_len(f);
                assert(m.inv());
                assert(NR_ENTRIES == 512usize) by (compute_only);
                // new_size is a valid page size (case split on m.page_size).
                assert(set![4096usize, 2097152, 1073741824].contains(new_size)) by {
                    if m.page_size == 2097152 { assert(2097152usize / 512 == 4096usize); }
                    else if m.page_size == 1073741824 { assert(1073741824usize / 512 == 2097152usize); }
                    else { assert(4096usize / 512 == 8usize); assert(false); } // 4096 case impossible: 8 not in set
                };
                assert(m.page_size % new_size == 0) by {
                    if m.page_size == 2097152 { assert(2097152usize % 4096 == 0); }
                    else { assert(1073741824usize % 2097152 == 0); }
                };
                Self::split_if_mapped_huge_spec_preserves_inv(self, new_size);

                Self::split_if_mapped_huge_spec_decreases_page_size(self, new_size);
                Self::lemma_split_while_huge_preserves_cur_va(new_self, size);
            }
        }
    }

    /// `split_while_huge` preserves `CursorView::inv()`.
    pub proof fn lemma_split_while_huge_preserves_inv(self, size: usize)
        requires self.inv(), size >= PAGE_SIZE,
        ensures self.split_while_huge(size).inv(),
        decreases if self.present() { self.query_mapping().page_size as int } else { 0 }
    {
        if self.present() {
            let m = self.query_mapping();
            if m.page_size > size {
                let new_size = m.page_size / NR_ENTRIES;
                let new_self = self.split_if_mapped_huge_spec(new_size);
                // Establish m.inv() and call preserves_inv.
                let f = self.mappings.filter(|m2: Mapping| m2.va_range.start <= self.cur_va < m2.va_range.end);
                vstd::set::axiom_set_intersect_finite::<Mapping>(
                    self.mappings, Set::new(|m2: Mapping| m2.va_range.start <= self.cur_va < m2.va_range.end));
                vstd::set::axiom_set_choose_len(f);
                assert(m.inv());
                assert(NR_ENTRIES == 512usize) by (compute_only);
                assert(set![4096usize, 2097152, 1073741824].contains(new_size)) by {
                    if m.page_size == 2097152 { assert(2097152usize / 512 == 4096usize); }
                    else if m.page_size == 1073741824 { assert(1073741824usize / 512 == 2097152usize); }
                    else { assert(4096usize / 512 == 8usize); assert(false); }
                };
                assert(m.page_size % new_size == 0) by {
                    if m.page_size == 2097152 { assert(2097152usize % 4096 == 0); }
                    else { assert(1073741824usize % 2097152 == 0); }
                };
                Self::split_if_mapped_huge_spec_preserves_inv(self, new_size);
                Self::split_if_mapped_huge_spec_decreases_page_size(self, new_size);
                new_self.lemma_split_while_huge_preserves_inv(size);
            }
        }
    }

    /// Composition law for `split_while_huge`:
    /// splitting to a finer target `s2 <= s1` is the same as first splitting to `s1` and then
    /// further splitting to `s2`.
    pub proof fn split_while_huge_compose(self, s1: usize, s2: usize)
        requires
            self.inv(),
            s1 >= PAGE_SIZE,
            s2 <= s1,
        ensures
            self.split_while_huge(s2) == self.split_while_huge(s1).split_while_huge(s2),
        decreases if self.present() { self.query_mapping().page_size as int } else { 0 },
    {
        if !self.present() {
            return;
        }
        let m = self.query_mapping();
        if m.page_size <= s1 {
            return;
        }
        let new_size = m.page_size / NR_ENTRIES;
        let f = self.mappings.filter(
            |m2: Mapping| m2.va_range.start <= self.cur_va < m2.va_range.end);
        vstd::set::axiom_set_intersect_finite::<Mapping>(
            self.mappings,
            Set::new(|m2: Mapping| m2.va_range.start <= self.cur_va < m2.va_range.end));
        vstd::set::axiom_set_choose_len(f);
        assert(m.inv());
        assert(NR_ENTRIES == 512usize) by (compute_only);
        assert(set![4096usize, 2097152, 1073741824].contains(new_size)) by {
            if m.page_size == 2097152 { assert(2097152usize / 512 == 4096usize); }
            else { assert(1073741824usize / 512 == 2097152usize); }
        };
        assert(m.page_size % new_size == 0) by {
            if m.page_size == 2097152 { assert(2097152usize % 4096 == 0); }
            else { assert(1073741824usize % 2097152 == 0); }
        };
        Self::split_if_mapped_huge_spec_preserves_inv(self, new_size);
        Self::split_if_mapped_huge_spec_decreases_page_size(self, new_size);
        self.split_if_mapped_huge_spec(new_size).split_while_huge_compose(s1, s2);
    }

    /// When the current entry is absent or maps at `page_size <= size`, `split_while_huge(size)`
    /// is a no-op.  Applying a second call with the same `size` therefore returns the same value.
    pub proof fn split_while_huge_idempotent(self, size: usize)
        requires
            self.inv(),
            size >= PAGE_SIZE,
        ensures
            self.split_while_huge(size).split_while_huge(size) == self.split_while_huge(size),
    {
        self.split_while_huge_compose(size, size);
    }

    /// When `split_while_huge(size)` is a no-op and the view is `present()`,
    /// the mapping at `cur_va` already has `page_size <= size`.
    pub proof fn split_while_huge_noop_implies_page_size_le(self, size: usize)
        requires
            self.inv(),
            size >= PAGE_SIZE,
            self.split_while_huge(size) == self,
            self.present(),
        ensures
            self.query_mapping().page_size <= size,
    {
        let m = self.query_mapping();
        if m.page_size > size {
            let new_size = m.page_size / NR_ENTRIES;
            let f = self.mappings.filter(
                |m2: Mapping| m2.va_range.start <= self.cur_va < m2.va_range.end);
            vstd::set::axiom_set_intersect_finite::<Mapping>(
                self.mappings,
                Set::new(|m2: Mapping| m2.va_range.start <= self.cur_va < m2.va_range.end));
            vstd::set::axiom_set_choose_len(f);
            assert(m.inv());
            assert(NR_ENTRIES == 512usize) by (compute_only);
            assert(set![4096usize, 2097152, 1073741824].contains(new_size)) by {
                if m.page_size == 2097152 { assert(2097152usize / 512 == 4096usize); }
                else if m.page_size == 1073741824 { assert(1073741824usize / 512 == 2097152usize); }
                else { assert(4096usize / 512 == 8usize); assert(false); }
            };
            assert(m.page_size % new_size == 0) by {
                if m.page_size == 2097152 { assert(2097152usize % 4096 == 0); }
                else { assert(1073741824usize % 2097152 == 0); }
            };
            Self::split_if_mapped_huge_spec_preserves_inv(self, new_size);
            Self::split_if_mapped_huge_spec_decreases_page_size(self, new_size);
            let new_self = self.split_if_mapped_huge_spec(new_size);
            new_self.split_while_huge_refinement(size, m);
            assert(!new_self.mappings.contains(m)) by {
                let new_mappings = Set::<int>::new(
                    |n: int| 0 <= n < m.page_size as int / new_size as int
                ).map(|n: int| Self::split_index(m, new_size, n as usize));
                if new_mappings.contains(m) {
                    let k = choose|k: int|
                        0 <= k < m.page_size as int / new_size as int
                        && #[trigger] Self::split_index(m, new_size, k as usize) == m;
                }
            };
            let p = choose |p: Mapping| #[trigger] new_self.mappings.contains(p)
                && p.va_range.start <= m.va_range.start
                && m.va_range.end <= p.va_range.end
                && m.pa_range.start == (p.pa_range.start + (m.va_range.start - p.va_range.start)) as Paddr
                && m.property == p.property;
            if self.mappings.contains(p) {
                assert(p.va_range.start <= self.cur_va < p.va_range.end);
            } else {
                let new_mappings = Set::<int>::new(
                    |n: int| 0 <= n < m.page_size as int / new_size as int
                ).map(|n: int| Self::split_index(m, new_size, n as usize));
                let k = choose|k: int|
                    0 <= k < m.page_size as int / new_size as int
                    && #[trigger] Self::split_index(m, new_size, k as usize) == p;
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
                    m.page_size as int, new_size as int);
                vstd::arithmetic::mul::lemma_mul_inequality(
                    (k + 1) as int, m.page_size as int / new_size as int, new_size as int);
                vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(
                    new_size as int, k, 1int);
            }
        }
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
            self.inv(),
            self.present(),
            self.query_mapping().page_size > size,
            self.query_mapping().page_size / NR_ENTRIES == size,
            self.query_mapping().page_size % size == 0,
            set![4096usize, 2097152, 1073741824].contains(size),
        ensures
            self.split_while_huge(size).mappings
                =~= self.split_if_mapped_huge_spec(size).mappings,
    {
        let m = self.query_mapping();
        let new_size = m.page_size / NR_ENTRIES;
        let f0 = self.mappings.filter(
            |m2: Mapping| m2.va_range.start <= self.cur_va < m2.va_range.end);
        vstd::set::axiom_set_intersect_finite::<Mapping>(
            self.mappings,
            Set::new(|m2: Mapping| m2.va_range.start <= self.cur_va < m2.va_range.end));
        vstd::set::axiom_set_choose_len(f0);
        assert(m.inv());
        assert(NR_ENTRIES == 512usize) by (compute_only);
        Self::split_if_mapped_huge_spec_preserves_present(self, new_size);
        Self::split_if_mapped_huge_spec_preserves_inv(self, new_size);
        Self::split_if_mapped_huge_spec_decreases_page_size(self, new_size);
        let new_self = self.split_if_mapped_huge_spec(new_size);

        assert(new_self.query_mapping().page_size == new_size) by {
            let new_m = new_self.query_mapping();
            let f = new_self.mappings.filter(
                |m2: Mapping| m2.va_range.start <= new_self.cur_va < m2.va_range.end);
            vstd::set::axiom_set_intersect_finite::<Mapping>(
                new_self.mappings,
                Set::new(|m2: Mapping| m2.va_range.start <= new_self.cur_va < m2.va_range.end));
            vstd::set::axiom_set_choose_len(f);
            if self.mappings.contains(new_m) && new_m != m {
                assert(false);
            }
            let new_mappings = Set::<int>::new(
                |n: int| 0 <= n < m.page_size as int / new_size as int
            ).map(|n: int| Self::split_index(m, new_size, n as usize));
            assert(new_mappings.contains(new_m));
        };
        assert(new_self.split_while_huge(size) == new_self);
    }

    /// Locality of `split_if_mapped_huge_spec`: a mapping `m2` whose VA range
    /// is disjoint from the mapping at `cur_va` is preserved.
    pub proof fn split_if_mapped_huge_spec_locality(self, new_size: usize, m2: Mapping)
        requires
            self.inv(),
            self.present(),
            new_size > 0,
            self.query_mapping().page_size % new_size == 0,
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
        assert(m.inv());

        assert(!new_mappings.contains(m2)) by {
            if new_mappings.contains(m2) {
                let k = choose|k: int| 0 <= k < size as int / new_size as int
                    && #[trigger] Self::split_index(m, new_size, k as usize) == m2;
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
                    size as int, new_size as int);
                vstd::arithmetic::mul::lemma_mul_inequality(
                    (k + 1) as int, size as int / new_size as int, new_size as int);
                vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(
                    new_size as int, k, 1int);
                vstd::arithmetic::mul::lemma_mul_nonnegative(k, new_size as int);
            }
        };
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
            size >= PAGE_SIZE,
            self.mappings.contains(m2),
            !(m2.va_range.start <= self.cur_va < m2.va_range.end),
        ensures
            self.split_while_huge(size).mappings.contains(m2),
        decreases if self.present() { self.query_mapping().page_size as int } else { 0 },
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
                assert(set![4096usize, 2097152, 1073741824].contains(new_size)) by {
                    if m.page_size == 2097152 { assert(2097152usize / 512 == 4096usize); }
                    else if m.page_size == 1073741824 { assert(1073741824usize / 512 == 2097152usize); }
                    else { assert(4096usize / 512 == 8usize); assert(false); }
                };
                self.split_if_mapped_huge_spec_locality(new_size, m2);
                let new_self = self.split_if_mapped_huge_spec(new_size);
                Self::split_if_mapped_huge_spec_preserves_inv(self, new_size);
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
            size >= PAGE_SIZE,
            !self.mappings.contains(m2),
            self.present() ==> Mapping::disjoint_vaddrs(m2, self.query_mapping()),
        ensures
            !self.split_while_huge(size).mappings.contains(m2),
        decreases if self.present() { self.query_mapping().page_size as int } else { 0 },
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
                assert(set![4096usize, 2097152, 1073741824].contains(new_size)) by {
                    if m.page_size == 2097152 { assert(2097152usize / 512 == 4096usize); }
                    else if m.page_size == 1073741824 { assert(1073741824usize / 512 == 2097152usize); }
                    else { assert(4096usize / 512 == 8usize); assert(false); }
                };
                self.split_if_mapped_huge_spec_locality(new_size, m2);
                let new_self = self.split_if_mapped_huge_spec(new_size);
                Self::split_if_mapped_huge_spec_preserves_inv(self, new_size);
                Self::split_if_mapped_huge_spec_preserves_present(self, new_size);
                Self::split_if_mapped_huge_spec_decreases_page_size(self, new_size);
                assert(new_self.present() ==>
                    Mapping::disjoint_vaddrs(m2, new_self.query_mapping())) by {
                    if new_self.present() {
                        let new_m = new_self.query_mapping();
                        let nf = new_self.mappings.filter(
                            |m3: Mapping| m3.va_range.start <= new_self.cur_va < m3.va_range.end);
                        vstd::set::axiom_set_intersect_finite::<Mapping>(
                            new_self.mappings,
                            Set::new(|m3: Mapping| m3.va_range.start <= new_self.cur_va < m3.va_range.end));
                        vstd::set::axiom_set_choose_len(nf);
                        if self.mappings.contains(new_m) && new_m != m {
                            assert(false);
                        }
                        let new_mappings = Set::<int>::new(
                            |n: int| 0 <= n < m.page_size as int / new_size as int
                        ).map(|n: int| Self::split_index(m, new_size, n as usize));
                        let k = choose|k: int|
                            0 <= k < m.page_size as int / new_size as int
                            && #[trigger] Self::split_index(m, new_size, k as usize) == new_m;
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
                            m.page_size as int, new_size as int);
                        vstd::arithmetic::mul::lemma_mul_inequality(
                            (k + 1) as int, m.page_size as int / new_size as int, new_size as int);
                        vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(
                            new_size as int, k, 1int);
                        vstd::arithmetic::mul::lemma_mul_nonnegative(k, new_size as int);
                    }
                };
                new_self.split_while_huge_locality_absent(size, m2);
            }
        }
    }

    /// Refinement: every mapping in `split_while_huge(size).mappings` is either
    /// from `self.mappings` or a sub-mapping of an entry in `self.mappings`.
    /// Base lemma: every mapping in `split_if_mapped_huge_spec(new_size).mappings`
    /// is either from the original mappings or a sub-mapping of `query_mapping()`.
    pub proof fn split_if_mapped_huge_spec_refinement(self, new_size: usize, e: Mapping)
        requires
            self.inv(),
            self.present(),
            new_size > 0,
            self.query_mapping().page_size > new_size,
            self.query_mapping().page_size % new_size == 0,
            self.split_if_mapped_huge_spec(new_size).mappings.contains(e),
        ensures
            self.mappings.contains(e)
            || {
                let parent = self.query_mapping();
                &&& self.mappings.contains(parent)
                &&& parent.va_range.start <= e.va_range.start
                &&& e.va_range.end <= parent.va_range.end
                &&& e.pa_range.start == (parent.pa_range.start + (e.va_range.start - parent.va_range.start)) as Paddr
                &&& e.property == parent.property
            },
    {
        let qm = self.query_mapping();
        let ps = qm.page_size;
        let ns: int = new_size as int;
        let count: int = ps as int / ns;
        let new_self = self.split_if_mapped_huge_spec(new_size);
        let domain = Set::<int>::new(|n: int| 0 <= n < count);
        let new_mappings = domain.map(|n: int| Self::split_index(qm, new_size, n as usize));

        // Establish qm ∈ self.mappings.
        let f = self.mappings.filter(|m2: Mapping| m2.va_range.start <= self.cur_va < m2.va_range.end);
        vstd::set::axiom_set_intersect_finite::<Mapping>(
            self.mappings,
            Set::new(|m2: Mapping| m2.va_range.start <= self.cur_va < m2.va_range.end));
        vstd::set::axiom_set_choose_len(f);
        assert(self.mappings.contains(qm));
        assert(qm.inv());

        if self.mappings.remove(qm).contains(e) {
            assert(self.mappings.contains(e));
        } else {
            assert(new_mappings.contains(e));
            let k = choose|k: int| 0 <= k < count
                && #[trigger] Self::split_index(qm, new_size, k as usize) == e;

            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ps as int, ns);
            assert(ps as int == count * ns);

            vstd::arithmetic::mul::lemma_mul_nonnegative(k, ns);
            vstd::arithmetic::mul::lemma_mul_inequality(k + 1, count, ns);

            assert(k as usize as int == k);
            let ku = k as usize;
            assert(e == Self::split_index(qm, new_size, ku));
            vstd::arithmetic::mul::lemma_mul_is_distributive_add(ns, k, 1int);

            assert(e.va_range.start as int == qm.va_range.start as int + k * ns);
            assert(e.va_range.start >= qm.va_range.start);
            assert(e.va_range.end as int == qm.va_range.start as int + (k + 1) * ns);
            assert(e.va_range.end <= qm.va_range.end);
            assert(e.pa_range.start as int == qm.pa_range.start as int + k * ns);
            assert(e.va_range.start - qm.va_range.start == k * ns);
            assert(e.pa_range.start == (qm.pa_range.start + (e.va_range.start - qm.va_range.start)) as Paddr);
            assert(e.property == qm.property);
        }
    }

    pub proof fn split_while_huge_refinement(self, size: usize, m: Mapping)
        requires
            self.inv(),
            size >= PAGE_SIZE,
            self.split_while_huge(size).mappings.contains(m),
        ensures
            self.mappings.contains(m)
            || exists |parent: Mapping| #[trigger] self.mappings.contains(parent)
                && parent.va_range.start <= m.va_range.start
                && m.va_range.end <= parent.va_range.end
                && m.pa_range.start == (parent.pa_range.start + (m.va_range.start - parent.va_range.start)) as Paddr
                && m.property == parent.property,
        decreases if self.present() { self.query_mapping().page_size as int } else { 0 }
    {
        if self.present() {
            let qm = self.query_mapping();
            if qm.page_size > size {
                let new_size = qm.page_size / NR_ENTRIES;
                let new_self = self.split_if_mapped_huge_spec(new_size);

                let f = self.mappings.filter(|m2: Mapping| m2.va_range.start <= self.cur_va < m2.va_range.end);
                vstd::set::axiom_set_intersect_finite::<Mapping>(
                    self.mappings,
                    Set::new(|m2: Mapping| m2.va_range.start <= self.cur_va < m2.va_range.end));
                vstd::set::axiom_set_choose_len(f);
                assert(qm.inv());
                assert(NR_ENTRIES == 512usize) by (compute_only);
                assert(set![4096usize, 2097152, 1073741824].contains(new_size)) by {
                    if qm.page_size == 2097152 { assert(2097152usize / 512 == 4096usize); }
                    else if qm.page_size == 1073741824 { assert(1073741824usize / 512 == 2097152usize); }
                    else { assert(4096usize / 512 == 8usize); assert(false); }
                };
                assert(qm.page_size % new_size == 0) by {
                    if qm.page_size == 2097152 { assert(2097152usize % 4096 == 0); }
                    else { assert(1073741824usize % 2097152 == 0); }
                };
                Self::split_if_mapped_huge_spec_preserves_inv(self, new_size);
                Self::split_if_mapped_huge_spec_decreases_page_size(self, new_size);

                new_self.split_while_huge_refinement(size, m);

                if new_self.mappings.contains(m) {
                    self.split_if_mapped_huge_spec_refinement(new_size, m);
                } else {
                    let p = choose|p: Mapping|
                        #[trigger] new_self.mappings.contains(p)
                        && p.va_range.start <= m.va_range.start
                        && m.va_range.end <= p.va_range.end
                        && m.pa_range.start == (p.pa_range.start + (m.va_range.start - p.va_range.start)) as Paddr
                        && m.property == p.property;
                    self.split_if_mapped_huge_spec_refinement(new_size, p);
                    if !self.mappings.contains(p) {
                        assert(qm.va_range.start <= m.va_range.start);
                        assert(m.va_range.end <= qm.va_range.end);
                        // Extract m.inv() and p.inv() via inv preservation of
                        // split_while_huge / split_if_mapped_huge_spec.
                        new_self.lemma_split_while_huge_preserves_inv(size);
                        assert(new_self.split_while_huge(size).inv());
                        assert(m.inv());
                        assert(new_self.inv());
                        assert(p.inv());
                        // Mapping::inv gives `start + page_size == end`.
                        assert(m.va_range.start + m.page_size == m.va_range.end);
                        assert(qm.va_range.start + qm.page_size == qm.va_range.end);
                        // m's va offset within qm: at most qm.page_size - m.page_size <= qm.page_size.
                        assert(m.va_range.start - qm.va_range.start
                            <= qm.page_size - m.page_size);
                        // pa-side chain in int arithmetic.
                        assert(qm.pa_range.start + qm.page_size == qm.pa_range.end);
                        assert(qm.pa_range.end <= MAX_PADDR);
                        assert(p.pa_range.start as int
                            == qm.pa_range.start as int
                                + (p.va_range.start - qm.va_range.start));
                        assert(m.pa_range.start as int
                            == p.pa_range.start as int
                                + (m.va_range.start - p.va_range.start));
                        assert(m.pa_range.start as int
                            == qm.pa_range.start as int
                                + (m.va_range.start - qm.va_range.start));
                        // No-overflow: sum <= qm.pa_range.end <= MAX_PADDR <= usize::MAX.
                        assert(qm.pa_range.start as int
                            + (m.va_range.start - qm.va_range.start)
                            <= qm.pa_range.end as int);
                        assert(m.pa_range.start
                            == (qm.pa_range.start + (m.va_range.start - qm.va_range.start)) as Paddr);
                        assert(m.property == qm.property);
                    }
                }
            }
        }
    }

    /// `split_while_huge` produces a set disjoint from any set that is
    /// pairwise VA-disjoint from `self.mappings`.
    ///
    /// Set-disjointness of `other` from `self.mappings` is **not** sufficient
    /// (counterexample: `other = {split_index(m, k, 0)}` collides with the
    /// first sub-mapping after one split step). We need VA-disjointness so
    /// that sub-mappings — which lie strictly inside the parent's va_range
    /// and hence have distinct va_ranges from anything in `other` — cannot
    /// equal any element of `other`.
    pub proof fn split_while_huge_disjoint(self, size: usize, other: Set<Mapping>)
        requires
            self.inv(),
            size >= PAGE_SIZE,
            forall|m: Mapping, x: Mapping|
                #[trigger] self.mappings.contains(m) && #[trigger] other.contains(x) ==>
                    Mapping::disjoint_vaddrs(m, x),
        ensures
            self.split_while_huge(size).mappings.disjoint(other),
        decreases if self.present() { self.query_mapping().page_size as int } else { 0 }
    {
        if !self.present() {
            // split_while_huge is a no-op; disjointness is by va-disjoint hypothesis.
            assert forall |x: Mapping| #![trigger other.contains(x)] other.contains(x)
                implies !self.split_while_huge(size).mappings.contains(x) by {
                if self.mappings.contains(x) {
                    assert(Mapping::disjoint_vaddrs(x, x));
                    assert(x.inv());
                }
            };
            return;
        }
        let m = self.query_mapping();
        if m.page_size <= size {
            assert forall |x: Mapping| #![trigger other.contains(x)] other.contains(x)
                implies !self.split_while_huge(size).mappings.contains(x) by {
                if self.mappings.contains(x) {
                    assert(Mapping::disjoint_vaddrs(x, x));
                    assert(x.inv());
                }
            };
            return;
        }
        let new_size = m.page_size / NR_ENTRIES;

        // Standard scaffolding: m ∈ self.mappings, m covers cur_va, m.inv().
        let f = self.mappings.filter(
            |m2: Mapping| m2.va_range.start <= self.cur_va < m2.va_range.end);
        vstd::set::axiom_set_intersect_finite::<Mapping>(
            self.mappings,
            Set::new(|m2: Mapping| m2.va_range.start <= self.cur_va < m2.va_range.end));
        vstd::set::axiom_set_choose_len(f);
        assert(self.mappings.contains(m));
        assert(m.inv());

        assert(NR_ENTRIES == 512usize) by (compute_only);
        assert(set![4096usize, 2097152, 1073741824].contains(new_size)) by {
            if m.page_size == 2097152 { assert(2097152usize / 512 == 4096usize); }
            else if m.page_size == 1073741824 { assert(1073741824usize / 512 == 2097152usize); }
            else { assert(4096usize / 512 == 8usize); assert(false); }
        };
        assert(m.page_size % new_size == 0) by {
            if m.page_size == 2097152 { assert(2097152usize % 4096 == 0); }
            else { assert(1073741824usize % 2097152 == 0); }
        };
        Self::split_if_mapped_huge_spec_preserves_inv(self, new_size);
        Self::split_if_mapped_huge_spec_decreases_page_size(self, new_size);
        let new_self = self.split_if_mapped_huge_spec(new_size);

        // Recursive call: establish va-disjoint hypothesis for new_self.
        assert forall |m2: Mapping, x: Mapping|
            #[trigger] new_self.mappings.contains(m2) && #[trigger] other.contains(x) implies
            Mapping::disjoint_vaddrs(m2, x) by {
            if self.mappings.contains(m2) {
                // Existing mapping preserved by split: va-disjoint by hypothesis.
            } else {
                // m2 is a sub-mapping of m, with va_range ⊆ m.va_range.
                let new_mappings = Set::<int>::new(
                    |n: int| 0 <= n < m.page_size as int / new_size as int
                ).map(|n: int| Self::split_index(m, new_size, n as usize));
                assert(new_mappings.contains(m2));
                let k = choose|k: int|
                    0 <= k < m.page_size as int / new_size as int
                    && #[trigger] Self::split_index(m, new_size, k as usize) == m2;
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
                    m.page_size as int, new_size as int);
                vstd::arithmetic::mul::lemma_mul_inequality(
                    (k + 1) as int, m.page_size as int / new_size as int, new_size as int);
                vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(
                    new_size as int, k, 1int);
                vstd::arithmetic::mul::lemma_mul_nonnegative(k, new_size as int);
                // m2.va_range ⊆ m.va_range; m.va_range va-disjoint from x.va_range.
                assert(Mapping::disjoint_vaddrs(m, x));
            }
        };

        new_self.split_while_huge_disjoint(size, other);
    }
}


impl<'rcu, C: PageTableConfig> CursorOwner<'rcu, C> {

    /// When the current entry is a PT node at level `self.level`, any mapping at `cur_va` has
    /// `page_size <= page_size(self.level - 1)`.  Therefore `split_while_huge` at
    /// `page_size(self.level - 1)` does not split anything and is a no-op on the abstract view.
    /// When present, the query_mapping is from the current subtree's view_rec.
    proof fn query_mapping_from_subtree(self, qm: Mapping)
        requires
            self.inv(),
            self.in_locked_range(),
            self@.inv(),
            self@.present(),
            qm == self@.query_mapping(),
        ensures
            PageTableOwner(self.cur_subtree()).view_rec(self.cur_subtree().value.path).contains(qm),
    {
        let f = self@.mappings.filter(|m2: Mapping| m2.va_range.start <= self@.cur_va < m2.va_range.end);
        axiom_set_intersect_finite::<Mapping>(
            self@.mappings, Set::new(|m2: Mapping| m2.va_range.start <= self@.cur_va < m2.va_range.end));
        axiom_set_choose_len(f);
        self.mapping_covering_cur_va_from_cur_subtree(qm);
    }

    pub proof fn split_while_huge_node_noop(self)
        requires
            self.inv(),
            self.in_locked_range(),
            self.cur_entry_owner().is_node(),
            self.level > 1,
        ensures
            self@.split_while_huge(page_size((self.level - 1) as PagingLevel)) == self@
    {
        self.view_preserves_inv();
        if self@.present() {
            self.cur_subtree_inv();
            let subtree = self.cur_subtree();
            let path = subtree.value.path;
            let qm = self@.query_mapping();
            self.query_mapping_from_subtree(qm);
            let cont = self.continuations[self.level - 1];
            cont.path().push_tail_property_len(cont.idx as usize);
            PageTableOwner(subtree).view_rec_node_page_size_bound(path, qm);
        }
    }

    /// When the current entry is absent, there is no mapping at `cur_va` in the abstract view,
    /// so `split_while_huge` finds nothing to split and is a no-op for any target size.
    pub proof fn split_while_huge_absent_noop(self, size: usize)
        requires
            self.inv(),
            self.in_locked_range(),
            self.cur_entry_owner().is_absent(),
        ensures
            self@.split_while_huge(size) == self@,
    {
        self.view_preserves_inv();
        self.cur_entry_absent_not_present();
    }

    pub proof fn split_while_huge_at_level_noop(self)
        requires
            self.inv(),
            self.in_locked_range(),
        ensures
            self@.split_while_huge(page_size(self.level as PagingLevel)) == self@
    {
        self.view_preserves_inv();
        if self@.present() {
            self.cur_subtree_inv();
            let subtree = self.cur_subtree();
            let path = subtree.value.path;
            let qm = self@.query_mapping();
            self.query_mapping_from_subtree(qm);
            let cont = self.continuations[self.level - 1];
            cont.path().push_tail_property_len(cont.idx as usize);
            PageTableOwner(subtree).view_rec_page_size_bound(path, qm);
        }
    }

    /// After `map_branch_none` splits a huge frame at level `level_before_frame` and descends,
    /// the cursor view equals `owner0@.split_while_huge(page_size(level_before_frame - 1))`.
    ///
    /// Chain:
    ///   owner@ = owner_before_frame@.split_if_mapped_huge_spec(page_size(level_before_frame - 1))
    ///          = owner0@.split_while_huge(page_size(level_before_frame)).split_if_mapped_huge_spec(...)
    ///          = owner0@.split_while_huge(page_size(level_before_frame - 1))
    /// The last equality uses the fact that split_while_huge(L) on a frame of size page_size(L)
    /// takes exactly one split step to page_size(L-1), matching split_if_mapped_huge_spec.
    pub proof fn map_branch_frame_split_while_huge(
        self,
        owner0: Self,
        owner_before_frame: Self,
        level_before_frame: int,
    )
        requires
            self.inv(),
            owner0.inv(),
            owner_before_frame.inv(),
            1 <= level_before_frame - 1,
            level_before_frame <= NR_LEVELS,
            self.level == (level_before_frame - 1) as u8,
            owner_before_frame@ == owner0@.split_while_huge(
                page_size(level_before_frame as PagingLevel)),
            self@ == owner_before_frame@.split_if_mapped_huge_spec(
                page_size((level_before_frame - 1) as PagingLevel)),
            // The mapping at cur_va in owner_before_frame is exactly the
            // frame at the level being split: present, with page_size equal
            // to page_size(level_before_frame). Both follow from being in
            // the ChildRef::Frame branch at level `level_before_frame`.
            owner_before_frame@.present(),
            owner_before_frame@.query_mapping().page_size
                == page_size(level_before_frame as PagingLevel),
    {
        owner0.view_preserves_inv();
        owner_before_frame.view_preserves_inv();
        let s_top = page_size(level_before_frame as PagingLevel);
        let s_low = page_size((level_before_frame - 1) as PagingLevel);

        // page_size(L) >= PAGE_SIZE; page_size(L) > page_size(L-1);
        // page_size(L) / NR_ENTRIES == page_size(L-1); page_size(L) % page_size(L-1) == 0;
        // page_size(L-1) ∈ {4K, 2M, 1G}.
        crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_spec_values();
        crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_ge_page_size(
            level_before_frame as PagingLevel);
        assert(NR_ENTRIES == 512usize) by (compute_only);

        // Compose: owner0.split_while_huge(s_low)
        //         == owner0.split_while_huge(s_top).split_while_huge(s_low)
        //         == owner_before_frame.split_while_huge(s_low)
        owner0@.split_while_huge_compose(s_top, s_low);

        // One step: owner_before_frame.split_while_huge(s_low)
        //         == owner_before_frame.split_if_mapped_huge_spec(s_low)
        owner_before_frame@.split_while_huge_one_step(s_low);
    }

    /// After split_if_mapped_huge + push_level, the mappings equal
    /// `old_view.split_while_huge(page_size(current_level))`.
    pub proof fn find_next_split_push_equals_split_while_huge(
        self,
        old_view: CursorView<C>,
    )
        requires
            self.inv(),
            old_view.inv(),
            self.cur_entry_owner().is_frame(),
            self@.cur_va == old_view.cur_va,
            old_view.present(),
            old_view.query_mapping().page_size > page_size(self.level as PagingLevel),
            old_view.query_mapping().page_size / NR_ENTRIES
                == page_size(self.level as PagingLevel),
            old_view.query_mapping().page_size
                % page_size(self.level as PagingLevel) == 0,
            self@.mappings =~= old_view.split_if_mapped_huge_spec(
                page_size(self.level as PagingLevel)).mappings,
        ensures
            self@.mappings =~= old_view.split_while_huge(
                page_size(self.level as PagingLevel)).mappings,
    {
        let ps = page_size(self.level as PagingLevel);
        let m = old_view.query_mapping();
        let f = old_view.mappings.filter(
            |m2: Mapping| m2.va_range.start <= old_view.cur_va < m2.va_range.end);
        vstd::set::axiom_set_intersect_finite::<Mapping>(
            old_view.mappings,
            Set::new(|m2: Mapping| m2.va_range.start <= old_view.cur_va < m2.va_range.end));
        vstd::set::axiom_set_choose_len(f);
        assert(m.inv());
        assert(NR_ENTRIES == 512usize) by (compute_only);
        crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_spec_values();
        assert(set![4096usize, 2097152, 1073741824].contains(ps)) by {
            if m.page_size == 2097152 { assert(2097152usize / 512 == 4096usize); }
            else { assert(1073741824usize / 512 == 2097152usize); }
        };
        old_view.split_while_huge_one_step(ps);
    }

    /// `split_while_huge` gives the same mappings for two `cur_va` values
    /// when no mapping starts between them and the `!present` case is a no-op.
    ///
    /// The `v1.cur_va < v2.cur_va ==> !v1.present()` precondition rules out
    /// the genuinely hard case where v1's query mapping spans v2.cur_va but
    /// gets split inconsistently — at the call site this is supplied by
    /// `find_next_impl`'s ensures (`final.va > old.va ==> !old(owner)@.present()`).
    pub proof fn split_while_huge_cur_va_independent(
        v1: CursorView<C>,
        v2: CursorView<C>,
        size: usize,
    )
        requires
            v1.inv(),
            v2.inv(),
            v1.mappings =~= v2.mappings,
            v1.cur_va <= v2.cur_va,
            // No mapping starts in [v1.cur_va, v2.cur_va).
            v1.mappings.filter(|m: Mapping|
                v1.cur_va <= m.va_range.start && m.va_range.start < v2.cur_va)
                =~= Set::<Mapping>::empty(),
            // When v1 has no mapping at cur_va, any mapping at v2.cur_va is
            // already small enough that split_while_huge is a no-op on it too.
            // (At the call site this follows from: split_while_huge(v1) was a
            // no-op, so find_next found the mapping without splitting, meaning
            // its page_size <= size.)
            !v1.present() && v2.present() ==> v2.query_mapping().page_size <= size,
            // When the cursor advances strictly forward, the original cur_va
            // had no mapping. Supplied by `find_next_impl`'s ensures.
            v1.cur_va < v2.cur_va ==> !v1.present(),
        ensures
            v1.split_while_huge(size).mappings =~= v2.split_while_huge(size).mappings,
    {
        if v1.cur_va == v2.cur_va {
            assert(v1 =~= v2);
        }
    }
}

} // verus!
