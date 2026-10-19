use vstd::{prelude::*, set_lib::*};

use crate::specs::arch::{MAX_PADDR, PAGE_SIZE};

use super::view::{Mapping, mappings_disjoint_vaddrs, mappings_well_formed};
use super::{lemma_vaddr_range_spec_user, page_table_managed_end_spec};
use crate::mm::{MAX_USERSPACE_VADDR, Vaddr, vm_space::UserPtConfig};

verus! {

/// Well-formed mapping set: all inv(), pairwise VA-disjoint.
pub open spec fn wf_mapping_set(s: Set<Mapping>) -> bool {
    &&& mappings_well_formed(s)
    &&& mappings_disjoint_vaddrs(s)
}

/// A well-formed mapping set whose VA ranges all lie within `[lo, hi)` has
/// cardinality at most `(hi - lo) / PAGE_SIZE`.
///
/// Proof by induction on `|s|`: pick any element `m`, partition the rest into
/// mappings below `m` and mappings above `m`, recurse on each half.
pub proof fn lemma_mapping_set_cardinality_in_range(s: Set<Mapping>, lo: int, hi: int)
    requires
        wf_mapping_set(s),
        forall|m: Mapping| #[trigger]
            s.contains(m) ==> lo <= m.va_range.start && m.va_range.end <= hi,
        lo <= hi,
    ensures
        s.len() * PAGE_SIZE <= hi - lo,
    decreases s.len(),
{
    if s.len() != 0 {
        let m = s.choose();
        let rest = s.remove(m);
        vstd::set::lemma_set_remove_len(s, m);
        assert(m.inv());

        let below = rest.filter(|n: Mapping| n.va_range.end <= m.va_range.start);
        let above = rest.filter(|n: Mapping| n.va_range.start >= m.va_range.end);

        assert(rest == below.union(above)) by {
            assert forall|n: Mapping| rest.contains(n) implies below.contains(n) || above.contains(
                n,
            ) by {
                assert(s.contains(n) && n != m);
            };
        };

        assert(below.disjoint(above)) by {
            assert forall|n: Mapping| below.contains(n) implies !above.contains(n) by {
                if above.contains(n) {
                    assert(n.inv());
                }
            };
        };

        vstd::set_lib::lemma_set_disjoint_lens(below, above);
        assert(rest.len() == below.len() + above.len());

        assert(wf_mapping_set(below)) by {
            assert forall|a: Mapping, b: Mapping| #[trigger]
                below.contains(a) && #[trigger] below.contains(b) && a != b implies a.va_range.end
                <= b.va_range.start || b.va_range.end <= a.va_range.start by {};
        };
        assert(wf_mapping_set(above)) by {
            assert forall|a: Mapping, b: Mapping| #[trigger]
                above.contains(a) && #[trigger] above.contains(b) && a != b implies a.va_range.end
                <= b.va_range.start || b.va_range.end <= a.va_range.start by {};
        };

        lemma_mapping_set_cardinality_in_range(below, lo, m.va_range.start);
        lemma_mapping_set_cardinality_in_range(above, m.va_range.end, hi);

        vstd::arithmetic::mul::lemma_mul_is_distributive_add(
            PAGE_SIZE as int,
            (below.len() + above.len()) as int,
            1,
        );
        vstd::arithmetic::mul::lemma_mul_is_distributive_add(
            PAGE_SIZE as int,
            below.len() as int,
            above.len() as int,
        );
    }
}

/// **Main lemma**: A well-formed mapping set has cardinality at most
/// `bound / PAGE_SIZE`, where `bound` is its largest element.
pub proof fn lemma_mapping_set_cardinality_bound(s: Set<Mapping>, bound: usize)
    requires
        wf_mapping_set(s),
        forall|m: Mapping| #[trigger]
            s.contains(m) ==> 0 <= m.va_range.start && m.va_range.end <= bound,
    ensures
        s.len() <= bound / PAGE_SIZE,
{
    lemma_mapping_set_cardinality_in_range(s, 0, bound as int);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(bound as int, PAGE_SIZE as int);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(bound as int, PAGE_SIZE as int);
    if s.len() > bound / PAGE_SIZE {
        vstd::arithmetic::mul::lemma_mul_inequality(
            bound as int / PAGE_SIZE as int + 1,
            s.len() as int,
            PAGE_SIZE as int,
        );
        vstd::arithmetic::mul::lemma_mul_is_distributive_add(
            PAGE_SIZE as int,
            bound as int / PAGE_SIZE as int,
            1,
        );
    }
}

/// Corollary: the cardinality fits in usize.
pub proof fn lemma_mapping_set_cardinality_fits_usize(s: Set<Mapping>)
    requires
        wf_mapping_set(s),
        forall|m: Mapping| #[trigger]
            s.contains(m) ==> m.va_range.end <= page_table_managed_end_spec::<UserPtConfig>(),
    ensures
        s.len() < usize::MAX,
{
    lemma_vaddr_range_spec_user();
    // `0 <= m.va_range.start` follows from `wf_mapping_set(s)` ⇒ `m.inv()`,
    // which has `0 <= m.va_range.start`.
    assert forall|m: Mapping| #[trigger] s.contains(m) implies 0 <= m.va_range.start
        && m.va_range.end <= page_table_managed_end_spec::<UserPtConfig>() by {
        assert(m.inv());
    };
    lemma_mapping_set_cardinality_bound(s, page_table_managed_end_spec::<UserPtConfig>() as usize);
    assert(0x0000_8000_0000_0000_usize / PAGE_SIZE < usize::MAX) by (compute_only);
}

/// A subset of a wf_mapping_set is also wf.
pub proof fn lemma_wf_subset(s: Set<Mapping>, sub: Set<Mapping>)
    requires
        wf_mapping_set(s),
        sub.subset_of(s),
    ensures
        wf_mapping_set(sub),
{
}

/// A union of two wf sets is wf if every element of one is VA-disjoint from every element of the other.
pub proof fn lemma_wf_union(a: Set<Mapping>, b: Set<Mapping>)
    requires
        wf_mapping_set(a),
        wf_mapping_set(b),
        forall|m: Mapping, n: Mapping| #[trigger]
            a.contains(m) && #[trigger] b.contains(n) ==> m.va_range.end <= n.va_range.start
                || n.va_range.end <= m.va_range.start,
    ensures
        wf_mapping_set(a.union(b)),
{
}

/// If `m` is a sub-mapping of `p` and `p` is a sub-mapping of `orig`,
/// then `m` is a sub-mapping of `orig` (PA arithmetic composes).
pub proof fn lemma_sub_mapping_pa_compose(m: Mapping, p: Mapping, orig: Mapping)
    requires
        m.inv(),
        orig.inv(),
        p.va_range.start >= orig.va_range.start,
        p.va_range.end <= orig.va_range.end,
        p.pa_range.start == (orig.pa_range.start + (p.va_range.start
            - orig.va_range.start)) as usize,
        p.property == orig.property,
        m.va_range.start >= p.va_range.start,
        m.va_range.end <= p.va_range.end,
        m.pa_range.start == (p.pa_range.start + (m.va_range.start - p.va_range.start)) as usize,
        m.property == p.property,
    ensures
        orig.va_range.start <= m.va_range.start,
        m.va_range.end <= orig.va_range.end,
        m.pa_range.start == (orig.pa_range.start + (m.va_range.start
            - orig.va_range.start)) as usize,
        m.property == orig.property,
{
    assert(MAX_PADDR < usize::MAX) by (compute_only);
}

/// Extends an empty scanned range through an empty slot overlapping its endpoint.
pub proof fn lemma_extend_empty_mapping_range(
    mappings: Set<Mapping>,
    start: Vaddr,
    scanned_end: Vaddr,
    slot_start: Vaddr,
    slot_end: int,
    next: Vaddr,
)
    requires
        slot_start <= scanned_end,
        next <= slot_end,
        mappings.filter(|m: Mapping| start <= m.va_range.start < scanned_end) == Set::<
            Mapping,
        >::empty(),
        mappings.filter(|m: Mapping| slot_start <= m.va_range.start < slot_end) == Set::<
            Mapping,
        >::empty(),
    ensures
        mappings.filter(|m: Mapping| start <= m.va_range.start < next) == Set::<Mapping>::empty(),
{
    assert forall|m: Mapping|
        !(#[trigger] mappings.contains(m) && start <= m.va_range.start < next) by {
        if mappings.contains(m) && start <= m.va_range.start < next {
            if m.va_range.start < scanned_end {
                assert(mappings.filter(
                    |m2: Mapping| start <= m2.va_range.start < scanned_end,
                ).contains(m));
            } else {
                assert(mappings.filter(
                    |m2: Mapping| slot_start <= m2.va_range.start < slot_end,
                ).contains(m));
            }

        }
    };
}

} // verus!
