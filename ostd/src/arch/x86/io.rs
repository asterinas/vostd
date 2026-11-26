// SPDX-License-Identifier: MPL-2.0
use core::{cmp::Ordering, iter::Filter, ops::Range, slice::Iter};
use vstd::{
    arithmetic::power2::is_pow2,
    prelude::*,
    seq_lib::group_filter_ensures,
    std_specs::{
        cmp::OrdSpec,
        iter::{IteratorSpec, filter_fun, filter_keep, filter_post, filter_postcondition},
    },
};
use vstd_extra::{
    arithmetic::nat_align_up,
    external::{
        ilog2::lemma_pow2_is_pow2_to64,
        iter::{
            axiom_iterator_max_by_postcondition, comparator_agrees_with_preorder,
            iterator_max_by_post,
        },
    },
    seq_extra::lemma_filter_index_take_len_lt,
};

use crate::{
    boot::{EarlyBootInfoInit, memory_region::MemoryRegion},
    io::io_mem::usize_ranges_match_registered,
};

use alloc::vec::Vec;

use align_ext::AlignExt;

use crate::{boot::memory_region::MemoryRegionType, io::IoMemAllocatorBuilder};

verus! {

/// Whether `r` is included when searching for TOLM / TOHM boundaries.
pub(super) open spec fn is_mmio_candidate_region(r: MemoryRegion) -> bool {
    r.typ() != MemoryRegionType::Unknown && r.typ() != MemoryRegionType::Reserved && r.typ()
        != MemoryRegionType::Framebuffer
}

/// Low-memory (< 4 GiB - 1) candidate region for TOLM discovery.
pub(super) open spec fn is_low_mmio_candidate(r: MemoryRegion) -> bool {
    is_mmio_candidate_region(r) && r.base() < u32::MAX as usize
}

/// High-memory (>= 4 GiB - 1) candidate region for TOHM discovery.
pub(super) open spec fn is_high_mmio_candidate(r: MemoryRegion) -> bool {
    is_mmio_candidate_region(r) && r.base() >= u32::MAX as usize
}

/// Last region with maximal `base()` in `regions`, matching `Iterator::max_by`.
pub(super) open spec fn max_by_base(regions: Seq<MemoryRegion>) -> Option<MemoryRegion> {
    regions.fold_left(
        None,
        |acc: Option<MemoryRegion>, r: MemoryRegion|
            match acc {
                None => Some(r),
                Some(best) => if best.base() > r.base() {
                    Some(best)
                } else {
                    Some(r)
                },
            },
    )
}

/// The low-memory region selected to determine TOLM.
pub(super) open spec fn tolm_region(regions: Seq<MemoryRegion>) -> Option<MemoryRegion> {
    max_by_base(regions.filter(|r: MemoryRegion| is_low_mmio_candidate(r)))
}

/// The high-memory region selected to determine TOHM.
pub(super) open spec fn tohm_region(regions: Seq<MemoryRegion>) -> Option<MemoryRegion> {
    max_by_base(regions.filter(|r: MemoryRegion| is_high_mmio_candidate(r)))
}

/// Aligned low-MMIO start address derived from `regions`.
pub(super) open spec fn low_mmio_start(regions: Seq<MemoryRegion>) -> usize {
    let low = tolm_region(regions)->0;
    nat_align_up((low.base() + low.len()) as nat, 0x1000_0000) as usize
}

/// Aligned high-MMIO start address derived from `regions`.
pub(super) open spec fn high_mmio_start(regions: Seq<MemoryRegion>) -> usize {
    match tohm_region(regions) {
        Some(high) => nat_align_up((high.base() + high.len()) as nat, 0x1_0000_0000) as usize,
        None => 0x1_0000_0000,
    }
}

/// Expected `[low_mmio, high_mmio]` windows constructed from `regions`.
pub(super) open spec fn expected_mmio_ranges(regions: Seq<MemoryRegion>) -> Seq<Range<usize>> {
    seq![
        low_mmio_start(regions)..0x1_0000_0000usize,
        high_mmio_start(regions)..0x8000_0000_0000usize,
    ]
}

} // verus!
/// Initializes the allocatable MMIO area based on the x86-64 memory distribution map.
///
/// In x86-64, the available physical memory area is divided into two regions below 32 bits (Low memory)
/// and above (High memory). The area from the top of low memory to 0xffff_ffff and the area after the
/// top of high memory are available MMIO areas.
#[verus_spec(ret =>
    with Tracked(boot_info): Tracked<&EarlyBootInfoInit>
    requires
        tolm_region(boot_info@.memory_regions@) matches Some(low)
            && low.base() + low.len() <= 0xF000_0000,
        tohm_region(boot_info@.memory_regions@) matches Some(high)
            ==> high.base() + high.len() <= 0x7FFF_0000_0000,
    ensures
        ret@ == expected_mmio_ranges(boot_info@.memory_regions@),
        ret.has_registered_windows() == usize_ranges_match_registered(ret@),
        low_mmio_start(boot_info@.memory_regions@) < 0x1_0000_0000
            <= high_mmio_start(boot_info@.memory_regions@) < 0x8000_0000_0000,
        low_mmio_start(boot_info@.memory_regions@) % 0x1000_0000 == 0,
        high_mmio_start(boot_info@.memory_regions@) % 0x1_0000_0000 == 0,
)]
pub(super) fn construct_io_mem_allocator_builder() -> IoMemAllocatorBuilder {
    // TODO: Add MMIO regions below 1MB (e.g., VGA framebuffer).
    /* Verus cannot reference `spin::Once` static `EARLY_INFO` directly.
     * Origin Rust: let regions = &crate::boot::EARLY_INFO.get().unwrap().memory_regions;
     */
    let regions = &(#[verus_spec(with Tracked(Some(boot_info)))]
    crate::boot::get_early_info())
    .unwrap()
    .memory_regions;
    let mut ranges = Vec::with_capacity(2);

    /* Verus does not recognize `Clone` on closure-backed `Filter` iterators, so
     * construct the same filter twice instead of cloning `reserved_filter`.
     * Origin Rust:
     * let reserved_filter = regions.iter().filter(|r| {
     *     r.typ() != MemoryRegionType::Unknown
     *         && r.typ() != MemoryRegionType::Reserved
     *         && r.typ() != MemoryRegionType::Framebuffer
     * });
     */

    // Find the TOLM (Top of Low Memory) and initialize Low MMIO region (TOLM ~ LOW_MMIO_TOP).
    // Align start address to LOW_MMIO_ALIGN
    const LOW_MMIO_TOP: usize = 0x1_0000_0000;
    const LOW_MMIO_ALIGN: usize = 0x1000_0000;
    /* Bind intermediate iterators and closures so Verus proofs can relate each stage's model.
     * Origin Rust:
     * let (lower_half_base, lower_half_len) = reserved_filter
     *     .clone()
     *     .filter(|r| r.base() < u32::MAX as usize)
     *     .max_by(|a, b| a.base().cmp(&b.base()))
     *     .map(|reg| (reg.base(), reg.len()))
     *     .unwrap();
     */
    let low_iter0 = regions.iter();
    let low_iter1 = low_iter0.filter(
        #[verus_spec(b: bool =>
            ensures
                b == is_mmio_candidate_region(**r),
        )]
        |r| {
            r.typ() != MemoryRegionType::Unknown
                && r.typ() != MemoryRegionType::Reserved
                && r.typ() != MemoryRegionType::Framebuffer
        },
    );
    let low_iter2 = low_iter1.filter(
        #[verus_spec(b: bool =>
            ensures
                b == ((**r).base() < u32::MAX as usize),
        )]
        |r| r.base() < u32::MAX as usize,
    );
    let low_cmp = #[verus_spec(o: Ordering =>
        ensures
            o == (**a).base().cmp_spec(&(**b).base()),
    )]
    |a: &&MemoryRegion, b: &&MemoryRegion| a.base().cmp(&b.base());
    proof_decl! {
        let ghost low_iter2_snap = low_iter2;
    }
    let low_max = low_iter2.max_by(low_cmp);
    proof! {
        lemma_filtered_max_by_base(
            boot_info@.memory_regions@,
            low_iter0,
            low_iter1,
            low_iter2_snap,
            low_cmp,
            low_max,
            |r: MemoryRegion| is_mmio_candidate_region(r),
            |r: MemoryRegion| r.base() < u32::MAX as usize,
            |r: MemoryRegion| is_low_mmio_candidate(r),
        );
    }
    let (lower_half_base, lower_half_len) = low_max
        .map(
            #[verus_spec(p: (usize, usize) =>
                ensures
                    p == (reg.base(), reg.len()),
            )]
            |reg| (reg.base(), reg.len()),
        )
        .unwrap();

    proof! {
        assert(is_pow2(0x1000_0000) && is_pow2(0x1_0000_0000)) by {
            lemma_pow2_is_pow2_to64();
        };
    }
    let mmio_start_addr = (lower_half_base + lower_half_len).align_up(LOW_MMIO_ALIGN);
    assert!(mmio_start_addr < LOW_MMIO_TOP);
    ranges.push(mmio_start_addr..LOW_MMIO_TOP);

    // Find the TOHM (Top of High Memory) and initialize High MMIO region.
    // Here, using HIGH_MMIO_TOP as the top of High MMIO region.
    //
    // TODO: Update the High MMIO region in runtime.
    const HIGH_MMIO_TOP: usize = 0x8000_0000_0000;
    const HIGH_MMIO_ALIGN: usize = 0x1_0000_0000;
    /* Bind intermediate iterators and closures so Verus proofs can relate each stage's model.
     * Origin Rust:
     * let (upper_half_base, upper_half_len) = reserved_filter
     *     .filter(|r| r.base() >= u32::MAX as usize)
     *     .max_by(|a, b| a.base().cmp(&b.base()))
     *     .map(|reg| (reg.base(), reg.len()))
     *     .unwrap_or((HIGH_MMIO_ALIGN, 0));
     */
    let high_iter0 = regions.iter();
    let high_iter1 = high_iter0.filter(
        #[verus_spec(b: bool =>
            ensures
                b == is_mmio_candidate_region(**r),
        )]
        |r| {
            r.typ() != MemoryRegionType::Unknown
                && r.typ() != MemoryRegionType::Reserved
                && r.typ() != MemoryRegionType::Framebuffer
        },
    );
    let high_iter2 = high_iter1.filter(
        #[verus_spec(b: bool =>
            ensures
                b == ((**r).base() >= u32::MAX as usize),
        )]
        |r| r.base() >= u32::MAX as usize,
    );
    let high_cmp = #[verus_spec(o: Ordering =>
        ensures
            o == (**a).base().cmp_spec(&(**b).base()),
    )]
    |a: &&MemoryRegion, b: &&MemoryRegion| a.base().cmp(&b.base());
    proof_decl! {
        let ghost high_iter2_snap = high_iter2;
    }
    let high_max = high_iter2.max_by(high_cmp);
    proof! {
        lemma_filtered_max_by_base(
            boot_info@.memory_regions@,
            high_iter0,
            high_iter1,
            high_iter2_snap,
            high_cmp,
            high_max,
            |r: MemoryRegion| is_mmio_candidate_region(r),
            |r: MemoryRegion| r.base() >= u32::MAX as usize,
            |r: MemoryRegion| is_high_mmio_candidate(r),
        );
    }
    let (upper_half_base, upper_half_len) = high_max
        .map(
            #[verus_spec(p: (usize, usize) =>
                ensures
                    p == (reg.base(), reg.len()),
            )]
            |reg| (reg.base(), reg.len()),
        )
        .unwrap_or((HIGH_MMIO_ALIGN, 0));

    let mmio_start_addr = (upper_half_base + upper_half_len).align_up(HIGH_MMIO_ALIGN);
    assert!(mmio_start_addr < HIGH_MMIO_TOP);
    ranges.push(mmio_start_addr..HIGH_MMIO_TOP);

    // SAFETY: The range is guaranteed not to access physical memory.
    unsafe { IoMemAllocatorBuilder::new(ranges) }
}
/// Port I/O definition reference: <https://bochs.sourceforge.io/techspec/PORTS.LST>.
#[verus_verify]
pub const MAX_IO_PORT: u16 = u16::MAX;

// Auxiliary proof helpers for MMIO boundary selection and alignment.
verus! {

/// Connects a doubly-filtered slice iterator's `max_by` result to `max_by_base(base.filter(p12))`.
proof fn lemma_filtered_max_by_base<
    'a,
    P1: FnMut(&&'a MemoryRegion) -> bool,
    P2: FnMut(&&'a MemoryRegion) -> bool,
    F: FnMut(&&'a MemoryRegion, &&'a MemoryRegion) -> Ordering,
>(
    base: Seq<MemoryRegion>,
    iter0: Iter<'a, MemoryRegion>,
    iter1: Filter<Iter<'a, MemoryRegion>, P1>,
    iter2: Filter<Filter<Iter<'a, MemoryRegion>, P1>, P2>,
    cmp: F,
    ret: Option<&'a MemoryRegion>,
    p1: spec_fn(MemoryRegion) -> bool,
    p2: spec_fn(MemoryRegion) -> bool,
    p12: spec_fn(MemoryRegion) -> bool,
)
    requires
        iter0.remaining() == base.as_ref(),
        iter0.obeys_prophetic_iter_laws(),
        iter0.produces().all(|p: bool| p),
        filter_post(iter0, filter_fun(iter1), iter1),
        filter_post(iter1, filter_fun(iter2), iter2),
        iterator_max_by_post(iter2, cmp, ret),
        forall|r: &'a MemoryRegion, b: bool| #[trigger]
            filter_fun(iter1).ensures((&r,), b) ==> b == p1(*r),
        forall|r: &'a MemoryRegion, b: bool| #[trigger]
            filter_fun(iter2).ensures((&r,), b) ==> b == p2(*r),
        forall|a: &'a MemoryRegion, b: &'a MemoryRegion, o: Ordering| #[trigger]
            cmp.ensures((&a, &b), o) ==> o == a.base().cmp_spec(&b.base()),
        forall|r: MemoryRegion| #[trigger] p12(r) == (p1(r) && p2(r)),
    ensures
        ret is None <==> max_by_base(base.filter(p12)) is None,
        ret matches Some(greatest) ==> {
            &&& max_by_base(base.filter(p12)) == Some(*greatest)
            &&& p12(*greatest)
        },
{
    broadcast use group_filter_ensures;

    proof fn lemma_filter_index_eq_filter<A>(s: Seq<A>, keep: Seq<bool>, pred: spec_fn(A) -> bool)
        requires
            keep.len() == s.len(),
            forall|j: int| 0 <= j < s.len() ==> #[trigger] keep[j] == pred(s[j]),
        ensures
            s.filter_index(|j: int| keep[j]) == s.filter(pred),
        decreases s.len(),
    {
        reveal(Seq::filter);
        reveal(Seq::filter_index);
        if s.len() > 0 {
            lemma_filter_index_eq_filter(s.drop_last(), keep.drop_last(), pred);
            assert(s.drop_last().filter_index(|j: int| keep.drop_last()[j])
                == s.drop_last().filter_index(|j: int| keep[j])) by {
                s.drop_last().filter_index_ext(|j: int| keep.drop_last()[j], |j: int| keep[j]);
            }
        }
    }

    proof fn lemma_filter_unref<A>(s: Seq<&A>, pred: spec_fn(A) -> bool)
        ensures
            s.filter(|r: &A| pred(*r)).map_values(|r: &A| *r) == s.map_values(|r: &A| *r).filter(
                pred,
            ),
        decreases s.len(),
    {
        reveal(Seq::filter);
        if s.len() > 0 {
            lemma_filter_unref(s.drop_last(), pred);
            assert(s.map_values(|r: &A| *r).drop_last() == s.drop_last().map_values(|r: &A| *r));
        }
    }

    proof fn lemma_filter_nested<A>(
        s: Seq<A>,
        p1: spec_fn(A) -> bool,
        p2: spec_fn(A) -> bool,
        p12: spec_fn(A) -> bool,
    )
        requires
            forall|x: A| #[trigger] p12(x) == (p1(x) && p2(x)),
        ensures
            s.filter(p1).filter(p2) == s.filter(p12),
        decreases s.len(),
    {
        reveal(Seq::filter);
        if s.len() > 0 {
            lemma_filter_nested(s.drop_last(), p1, p2, p12);
            if p1(s.last()) {
                assert(s.filter(p1).drop_last() == s.drop_last().filter(p1));
            }
        }
    }

    proof fn lemma_double_filter_unref<
        'a,
        P1: FnMut(&&'a MemoryRegion) -> bool,
        P2: FnMut(&&'a MemoryRegion) -> bool,
    >(
        base: Seq<MemoryRegion>,
        iter0: Iter<'a, MemoryRegion>,
        iter1: Filter<Iter<'a, MemoryRegion>, P1>,
        iter2: Filter<Filter<Iter<'a, MemoryRegion>, P1>, P2>,
        p1: spec_fn(MemoryRegion) -> bool,
        p2: spec_fn(MemoryRegion) -> bool,
        p12: spec_fn(MemoryRegion) -> bool,
    )
        requires
            iter0.remaining().map_values(|r: &'a MemoryRegion| *r) == base,
            iter0.obeys_prophetic_iter_laws(),
            iter0.produces().all(|p: bool| p),
            filter_post(iter0, filter_fun(iter1), iter1),
            filter_post(iter1, filter_fun(iter2), iter2),
            iter2.produces().all(|p: bool| p),
            forall|r: &'a MemoryRegion, b: bool| #[trigger]
                filter_fun(iter1).ensures((&r,), b) ==> b == p1(*r),
            forall|r: &'a MemoryRegion, b: bool| #[trigger]
                filter_fun(iter2).ensures((&r,), b) ==> b == p2(*r),
            forall|r: MemoryRegion| #[trigger] p12(r) == (p1(r) && p2(r)),
        ensures
            iter2.remaining().map_values(|r: &'a MemoryRegion| *r) == base.filter(p12),
    {
        broadcast use filter_postcondition;

        let keep2 = filter_keep(iter2);
        assert forall|j: int| 0 <= j < iter1.remaining().len() implies #[trigger] keep2[j] == p2(
            *iter1.remaining()[j],
        ) by {
            if keep2[j] {
                let k = iter1.remaining()[..j].filter_index(|idx: int| keep2[idx]).len();
                assert(0 <= k < iter2.remaining().len()) by {
                    lemma_filter_index_take_len_lt(iter1.remaining(), |idx: int| keep2[idx], j);
                };
            }
        };
        assert(iter1.produces().all(|p: bool| p)) by {
            assert forall|j: int|
                0 <= j < iter1.produces().len() implies #[trigger] iter1.produces()[j] by {
                if keep2[j] {
                    let k = iter1.remaining()[..j].filter_index(|idx: int| keep2[idx]).len();
                    assert(0 <= k < iter2.remaining().len()) by {
                        lemma_filter_index_take_len_lt(iter1.remaining(), |idx: int| keep2[idx], j);
                    };
                }
            }
        };
        let keep1 = filter_keep(iter1);
        assert forall|j: int| 0 <= j < iter0.remaining().len() implies #[trigger] keep1[j] == p1(
            *iter0.remaining()[j],
        ) by {
            if keep1[j] {
                let k = iter0.remaining()[..j].filter_index(|idx: int| keep1[idx]).len();
                assert(0 <= k < iter1.remaining().len()) by {
                    lemma_filter_index_take_len_lt(iter0.remaining(), |idx: int| keep1[idx], j);
                };
            }
        };
        lemma_filter_index_eq_filter(iter0.remaining(), keep1, |r: &'a MemoryRegion| p1(*r));
        lemma_filter_index_eq_filter(iter1.remaining(), keep2, |r: &'a MemoryRegion| p2(*r));
        lemma_filter_unref(iter0.remaining(), p1);
        lemma_filter_unref(iter1.remaining(), p2);
        lemma_filter_nested(base, p1, p2, p12);
    }

    proof fn lemma_max_by_base_props(s: Seq<MemoryRegion>)
        ensures
            max_by_base(s) is None <==> s.len() == 0,
            max_by_base(s) matches Some(best) ==> {
                &&& exists|j: int|
                    0 <= j < s.len() && s[j] == best && (forall|k: int|
                        0 <= k < s.len() ==> best.base() >= #[trigger] s[k].base()) && (forall|
                        k: int,
                    |
                        j < k < s.len() ==> best.base() > #[trigger] s[k].base())
            },
        decreases s.len(),
    {
        if s.len() > 0 {
            let prev = s.drop_last();
            lemma_max_by_base_props(prev);
            if let Some(best) = max_by_base(prev) {
                let j_prev = choose|j: int|
                    0 <= j < prev.len() && prev[j] == best && (forall|k: int|
                        0 <= k < prev.len() ==> best.base() >= #[trigger] prev[k].base()) && (
                    forall|k: int| j < k < prev.len() ==> best.base() > #[trigger] prev[k].base());
                if best.base() > s.last().base() {
                    assert forall|k: int| 0 <= k < s.len() implies best.base()
                        >= #[trigger] s[k].base() by {
                        if k < prev.len() {
                            assert(s[k] == prev[k]);
                        }
                    };
                    assert forall|k: int| j_prev < k < s.len() implies best.base()
                        > #[trigger] s[k].base() by {
                        if k < prev.len() {
                            assert(s[k] == prev[k]);
                        }
                    };
                } else {
                    assert forall|k: int| 0 <= k < s.len() implies s.last().base()
                        >= #[trigger] s[k].base() by {
                        if k < prev.len() {
                            assert(best.base() >= prev[k].base());
                        }
                    };
                }
            }
        }
    }

    proof fn lemma_max_by_base_matches<'a>(
        rem: Seq<&'a MemoryRegion>,
        vals: Seq<MemoryRegion>,
        ord: spec_fn(&'a MemoryRegion, &'a MemoryRegion) -> Ordering,
        ret: Option<&'a MemoryRegion>,
    )
        requires
            rem.map_values(|r: &'a MemoryRegion| *r) == vals,
            forall|a: &'a MemoryRegion, b: &'a MemoryRegion| #[trigger]
                ord(a, b) == a.base().cmp_spec(&b.base()),
            ret is None <==> rem.len() == 0,
            ret matches Some(greatest) ==> {
                &&& rem.contains(greatest)
                &&& forall|k: int|
                    #![trigger rem[k]]
                    0 <= k < rem.len() ==> ord(greatest, rem[k]) != Ordering::Less
                &&& exists|j: int|
                    0 <= j < rem.len() && rem[j] == greatest && forall|k: int|
                        j < k < rem.len() ==> ord(greatest, #[trigger] rem[k]) == Ordering::Greater
            },
        ensures
            ret is None <==> max_by_base(vals) is None,
            ret matches Some(greatest) ==> max_by_base(vals) == Some(*greatest),
    {
        lemma_max_by_base_props(vals);
        if let Some(greatest) = ret {
            let j1 = choose|j: int|
                0 <= j < rem.len() && rem[j] == greatest && forall|k: int|
                    j < k < rem.len() ==> ord(greatest, #[trigger] rem[k]) == Ordering::Greater;
            let best = max_by_base(vals)->0;
            let j2 = choose|j: int|
                0 <= j < vals.len() && vals[j] == best && (forall|k: int|
                    0 <= k < vals.len() ==> best.base() >= #[trigger] vals[k].base()) && (forall|
                    k: int,
                |
                    j < k < vals.len() ==> best.base() > #[trigger] vals[k].base());
            assert(vals[j1] == *greatest);
            assert(*rem[j2] == best);
            if j1 < j2 {
                assert(ord(greatest, rem[j2]) == Ordering::Greater);
                assert(greatest.base() > rem[j2].base());
                assert(best.base() >= vals[j1].base());
            } else if j2 < j1 {
                assert(ord(greatest, rem[j2]) != Ordering::Less);
            }
            assert(j1 == j2);
        }
    }

    assert(iter0.remaining().map_values(|r: &'a MemoryRegion| *r) == base);
    axiom_iterator_max_by_postcondition(iter2, cmp, ret);
    lemma_double_filter_unref(base, iter0, iter1, iter2, p1, p2, p12);
    let filtered = base.filter(p12);
    let ord = |a: &'a MemoryRegion, b: &'a MemoryRegion| a.base().cmp_spec(&b.base());
    assert(comparator_agrees_with_preorder(iter2.remaining(), cmp, ord)) by {
        reveal(comparator_agrees_with_preorder);
    };
    lemma_max_by_base_matches(iter2.remaining(), filtered, ord, ret);
}

} // verus!
