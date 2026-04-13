use vstd::prelude::*;
use vstd::set_lib::*;

use crate::mm::Vaddr;
use crate::specs::arch::mm::{MAX_USERSPACE_VADDR, PAGE_SIZE};
use crate::specs::arch::MAX_PADDR;

use super::view::Mapping;

verus! {

/// Well-formed mapping set: finite, all inv(), pairwise VA-disjoint.
pub open spec fn wf_mapping_set(s: Set<Mapping>) -> bool {
    &&& s.finite()
    &&& forall|m: Mapping| #![auto] s.contains(m) ==> m.inv()
    &&& forall|m: Mapping, n: Mapping| #![auto]
        s.contains(m) && s.contains(n) && m != n ==>
            m.va_range.end <= n.va_range.start || n.va_range.end <= m.va_range.start
}

/// A well-formed mapping set whose VA ranges all lie within `[lo, hi)` has
/// cardinality at most `(hi - lo) / PAGE_SIZE`.
///
/// Proof by induction on `|s|`: pick any element `m`, partition the rest into
/// mappings below `m` and mappings above `m`, recurse on each half.
pub proof fn lemma_mapping_set_cardinality_in_range(s: Set<Mapping>, lo: Vaddr, hi: Vaddr)
    requires
        wf_mapping_set(s),
        forall|m: Mapping| #[trigger] s.contains(m) ==> lo <= m.va_range.start && m.va_range.end <= hi,
        lo <= hi,
        hi <= MAX_USERSPACE_VADDR,
    ensures
        s.len() * PAGE_SIZE <= hi - lo,
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        let m = s.choose();
        let rest = s.remove(m);
        vstd::set::axiom_set_remove_len(s, m);
        vstd::set::axiom_set_remove_finite(s, m);
        assert(m.inv());

        let below = rest.filter(|n: Mapping| n.va_range.end <= m.va_range.start);
        let above = rest.filter(|n: Mapping| n.va_range.start >= m.va_range.end);

        // Every element of rest is either below or above m (VA-disjoint).
        assert(rest =~= below.union(above)) by {
            assert forall|n: Mapping| rest.contains(n)
                implies below.contains(n) || above.contains(n) by {
                assert(s.contains(n) && n != m);
            };
        };

        // Finiteness of below and above.
        vstd::set::axiom_set_intersect_finite::<Mapping>(
            rest, Set::new(|n: Mapping| n.va_range.end <= m.va_range.start));
        vstd::set::axiom_set_intersect_finite::<Mapping>(
            rest, Set::new(|n: Mapping| n.va_range.start >= m.va_range.end));

        // below and above are disjoint (below.end <= m.start <= m.end <= above.start).
        assert(below.disjoint(above)) by {
            assert forall|n: Mapping| below.contains(n) implies !above.contains(n) by {
                if above.contains(n) {
                    assert(n.inv());
                    // n.end <= m.start (from below) and n.start >= m.end (from above).
                    // n.inv() gives n.start < n.end. So m.end <= n.start < n.end <= m.start.
                    // But m.inv() gives m.start < m.end. Contradiction.
                }
            };
        };

        // |below| + |above| == |rest| == |s| - 1.
        vstd::set_lib::lemma_set_disjoint_lens(below, above);
        assert(rest.len() == below.len() + above.len());

        // Decreases check: |below| < |s| and |above| < |s|.
        // (|below| <= |rest| = |s| - 1 < |s|, similarly for |above|.)

        // below is a wf_mapping_set within [lo, m.va_range.start).
        assert(wf_mapping_set(below)) by {
            assert forall|a: Mapping, b: Mapping|
                #[trigger] below.contains(a) && #[trigger] below.contains(b) && a != b implies
                a.va_range.end <= b.va_range.start || b.va_range.end <= a.va_range.start by {
                assert(s.contains(a) && s.contains(b));
            };
        };
        // above is a wf_mapping_set within [m.va_range.end, hi).
        assert(wf_mapping_set(above)) by {
            assert forall|a: Mapping, b: Mapping|
                #[trigger] above.contains(a) && #[trigger] above.contains(b) && a != b implies
                a.va_range.end <= b.va_range.start || b.va_range.end <= a.va_range.start by {
                assert(s.contains(a) && s.contains(b));
            };
        };

        // Recurse.
        lemma_mapping_set_cardinality_in_range(below, lo, m.va_range.start);
        lemma_mapping_set_cardinality_in_range(above, m.va_range.end, hi);

        // |below| * PAGE <= m.start - lo
        // |above| * PAGE <= hi - m.end
        // m.page_size == m.end - m.start >= PAGE_SIZE
        // |s| * PAGE = (|below| + |above| + 1) * PAGE
        //            = |below|*PAGE + |above|*PAGE + PAGE
        //            <= (m.start - lo) + (hi - m.end) + PAGE
        //            <= (m.start - lo) + (hi - m.end) + (m.end - m.start)
        //            = hi - lo.
        assert(m.page_size >= PAGE_SIZE);
        assert(m.page_size == m.va_range.end - m.va_range.start);
        vstd::arithmetic::mul::lemma_mul_is_distributive_add(
            PAGE_SIZE as int, (below.len() + above.len()) as int, 1);
        vstd::arithmetic::mul::lemma_mul_is_distributive_add(
            PAGE_SIZE as int, below.len() as int, above.len() as int);
    }
}

/// **Main lemma**: A well-formed mapping set has cardinality at most
/// `MAX_USERSPACE_VADDR / PAGE_SIZE`.
pub proof fn lemma_mapping_set_cardinality_bound(s: Set<Mapping>)
    requires
        wf_mapping_set(s),
    ensures
        s.len() <= MAX_USERSPACE_VADDR / PAGE_SIZE,
{
    // All mappings have va_range in (0, MAX_USERSPACE_VADDR).
    // m.inv() gives 0 < m.va.start and m.va.end < MAX_USERSPACE_VADDR, so within [0, MAX_USERSPACE_VADDR].
    assert forall|m: Mapping| #[trigger] s.contains(m)
        implies 0 <= m.va_range.start && m.va_range.end <= MAX_USERSPACE_VADDR by {
        assert(m.inv());
    };
    lemma_mapping_set_cardinality_in_range(s, 0, MAX_USERSPACE_VADDR);
    // |s| * PAGE_SIZE <= MAX_USERSPACE_VADDR.
    // ⟹ |s| <= MAX_USERSPACE_VADDR / PAGE_SIZE.
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(MAX_USERSPACE_VADDR as int, PAGE_SIZE as int);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(MAX_USERSPACE_VADDR as int, PAGE_SIZE as int);
    if s.len() > MAX_USERSPACE_VADDR / PAGE_SIZE {
        vstd::arithmetic::mul::lemma_mul_inequality(
            MAX_USERSPACE_VADDR as int / PAGE_SIZE as int + 1,
            s.len() as int,
            PAGE_SIZE as int,
        );
        vstd::arithmetic::mul::lemma_mul_is_distributive_add(
            PAGE_SIZE as int,
            MAX_USERSPACE_VADDR as int / PAGE_SIZE as int,
            1,
        );
    }
}

/// Corollary: the cardinality fits in usize.
pub proof fn lemma_mapping_set_cardinality_fits_usize(s: Set<Mapping>)
    requires
        wf_mapping_set(s),
    ensures
        s.len() < usize::MAX,
{
    lemma_mapping_set_cardinality_bound(s);
    assert(MAX_USERSPACE_VADDR / PAGE_SIZE < usize::MAX) by (compute_only);
}

/// A subset of a wf_mapping_set is also wf.
pub proof fn lemma_wf_subset(s: Set<Mapping>, sub: Set<Mapping>)
    requires
        wf_mapping_set(s),
        sub.subset_of(s),
        sub.finite(),
    ensures
        wf_mapping_set(sub),
{
    assert forall|m: Mapping| #![auto] sub.contains(m) implies m.inv() by {};
    assert forall|m: Mapping, n: Mapping| #![auto]
        sub.contains(m) && sub.contains(n) && m != n implies
        m.va_range.end <= n.va_range.start || n.va_range.end <= m.va_range.start by {};
}

/// A union of two wf sets is wf if every element of one is VA-disjoint from every element of the other.
pub proof fn lemma_wf_union(a: Set<Mapping>, b: Set<Mapping>)
    requires
        wf_mapping_set(a),
        wf_mapping_set(b),
        forall|m: Mapping, n: Mapping|
            #[trigger] a.contains(m) && #[trigger] b.contains(n) ==>
                m.va_range.end <= n.va_range.start || n.va_range.end <= m.va_range.start,
    ensures
        wf_mapping_set(a.union(b)),
{
    vstd::set::axiom_set_union_finite(a, b);
    assert forall|m: Mapping| #![auto] a.union(b).contains(m) implies m.inv() by {};
    assert forall|m: Mapping, n: Mapping| #![auto]
        a.union(b).contains(m) && a.union(b).contains(n) && m != n implies
        m.va_range.end <= n.va_range.start || n.va_range.end <= m.va_range.start by {};
}

/// If `m` is a sub-mapping of `p` and `p` is a sub-mapping of `orig`,
/// then `m` is a sub-mapping of `orig` (PA arithmetic composes).
pub proof fn lemma_sub_mapping_pa_compose(m: Mapping, p: Mapping, orig: Mapping)
    requires
        m.inv(),
        orig.inv(),
        p.va_range.start >= orig.va_range.start,
        p.va_range.end <= orig.va_range.end,
        p.pa_range.start == (orig.pa_range.start + (p.va_range.start - orig.va_range.start)) as usize,
        p.property == orig.property,
        m.va_range.start >= p.va_range.start,
        m.va_range.end <= p.va_range.end,
        m.pa_range.start == (p.pa_range.start + (m.va_range.start - p.va_range.start)) as usize,
        m.property == p.property,
    ensures
        orig.va_range.start <= m.va_range.start,
        m.va_range.end <= orig.va_range.end,
        m.pa_range.start == (orig.pa_range.start + (m.va_range.start - orig.va_range.start)) as usize,
        m.property == orig.property,
{
    assert(MAX_PADDR < usize::MAX) by (compute_only);
    // All VA offsets fit within orig's page_size, so PA offsets don't overflow.
    assert(p.va_range.start - orig.va_range.start <= orig.page_size);
    assert(m.va_range.start - orig.va_range.start <= orig.page_size);
    assert(orig.pa_range.start + (p.va_range.start - orig.va_range.start) < usize::MAX);
    assert(p.pa_range.start as int == orig.pa_range.start as int + (p.va_range.start as int - orig.va_range.start as int));
    assert(orig.pa_range.start + (m.va_range.start - orig.va_range.start) < usize::MAX);
    assert(p.pa_range.start + (m.va_range.start - p.va_range.start) < usize::MAX);
    assert(m.pa_range.start as int == p.pa_range.start as int + (m.va_range.start as int - p.va_range.start as int));
    assert(m.pa_range.start as int == orig.pa_range.start as int + (m.va_range.start as int - orig.va_range.start as int));
}

} // verus!
