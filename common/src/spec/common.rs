use std::{io::Write, path, result};
use std::ops::Range;

use vstd::{prelude::*, seq::*};
use vstd::bits::{low_bits_mask, lemma_low_bits_mask_values};
use vstd_extra::{ghost_tree::Node, seq_extra::*};

use crate::mm::nr_subpage_per_huge;
use crate::mm::page_table::{lemma_pte_index_spec_in_range, pte_index_spec};
use crate::mm::{
    PagingLevel, Vaddr,
    page_table::{PageTableConfig, PagingConstsTrait},
};
use crate::spec::node_helper::{self, group_node_helper_lemmas};

verus! {

pub type CpuId = nat;

pub type NodeId = nat;

pub open spec fn valid_cpu(cpu_num: CpuId, cpu: CpuId) -> bool {
    0 <= cpu < cpu_num
}

pub open spec fn valid_pte_offset<C: PageTableConfig>(offset: nat) -> bool {
    0 <= offset < nr_subpage_per_huge::<C>()
}

pub open spec fn valid_vaddr<C: PageTableConfig>(va: Vaddr) -> bool {
    0 <= va < (1u64 << C::ADDRESS_WIDTH())
}

pub open spec fn valid_va_range<C: PageTableConfig>(va: Range<Vaddr>) -> bool {
    0 <= va.start <= va.end <= (1u64 << C::ADDRESS_WIDTH())
}

pub open spec fn vaddr_is_aligned<C: PageTableConfig>(va: Vaddr) -> (res: bool)
    recommends
        valid_vaddr::<C>(va),
{
    va % C::BASE_PAGE_SIZE_SPEC() as usize == 0
}

pub open spec fn va_level_to_offset<C: PageTableConfig>(va: Vaddr, level: PagingLevel) -> nat
    recommends
        valid_vaddr::<C>(va),
        1 <= level <= C::NR_LEVELS_SPEC(),
{
    pte_index_spec::<C>(va, level) as nat
}

} // verus!
verus! {

pub open spec fn va_level_to_trace<C: PageTableConfig>(va: Vaddr, level: PagingLevel) -> Seq<nat>
    recommends
        1 <= level <= C::NR_LEVELS_SPEC(),
{
    Seq::new(
        (C::NR_LEVELS_SPEC() - level) as nat,
        |i| va_level_to_offset::<C>(va, (C::NR_LEVELS_SPEC() - i) as PagingLevel),
    )
}

pub open spec fn va_level_to_nid<C: PageTableConfig>(va: Vaddr, level: PagingLevel) -> NodeId {
    node_helper::trace_to_nid::<C>(va_level_to_trace::<C>(va, level))
}

pub proof fn lemma_va_level_to_nid_inc<C: PageTableConfig>(
    va: Vaddr,
    level: PagingLevel,
    nid: NodeId,
    idx: nat,
)
    requires
        valid_vaddr::<C>(va),
        1 <= level < C::NR_LEVELS_SPEC(),
        node_helper::valid_nid::<C>(nid),
        nid == va_level_to_nid::<C>(va, (level + 1) as PagingLevel),
        valid_pte_offset::<C>(idx),
        idx == pte_index_spec::<C>(va, (level + 1) as PagingLevel),
    ensures
        node_helper::get_child::<C>(nid, idx) == va_level_to_nid::<C>(va, level),
{
    broadcast use group_node_helper_lemmas;
    // Establish the relationship between traces at consecutive levels

    let trace_level_plus_1 = va_level_to_trace::<C>(va, (level + 1) as PagingLevel);
    let trace_level = va_level_to_trace::<C>(va, level);

    // Show that trace_level = trace_level_plus_1.push(idx)
    assert(trace_level == trace_level_plus_1.push(idx));

    // Now use the fact that nid = trace_to_nid(trace_level_plus_1)
    // and get_child(nid, idx) = trace_to_nid(nid_to_trace::<C>(nid).push(idx))
    assert(node_helper::nid_to_trace::<C>(nid) == trace_level_plus_1) by {
        // First establish that trace_level_plus_1 is a valid trace
        assert(node_helper::valid_trace::<C>(trace_level_plus_1)) by {
            lemma_va_level_to_trace_valid::<C>(va, (level + 1) as PagingLevel);
        };
        node_helper::lemma_trace_to_nid_bijective::<C>();
    };
}

pub proof fn lemma_va_level_to_trace_valid<C: PageTableConfig>(va: Vaddr, level: PagingLevel)
    requires
        1 <= level <= C::NR_LEVELS_SPEC(),
    ensures
        node_helper::valid_trace::<C>(va_level_to_trace::<C>(va, level)),
    decreases C::NR_LEVELS_SPEC() - level,
{
    if level < C::NR_LEVELS_SPEC() {
        lemma_va_level_to_trace_valid::<C>(va, (level + 1) as PagingLevel);
        lemma_pte_index_spec_in_range::<C>(va, (level + 1) as PagingLevel);
        C::lemma_nr_subpage_per_huge_is_512();
        assert(va_level_to_trace::<C>(va, level) == va_level_to_trace::<C>(
            va,
            (level + 1) as PagingLevel,
        ).push(va_level_to_offset::<C>(va, (level + 1) as PagingLevel)));
    }
}

pub proof fn lemma_va_level_to_nid_valid<C: PageTableConfig>(va: Vaddr, level: PagingLevel)
    requires
        valid_vaddr::<C>(va),
        1 <= level <= C::NR_LEVELS_SPEC(),
    ensures
        node_helper::valid_nid::<C>(va_level_to_nid::<C>(va, level)),
{
    broadcast use group_node_helper_lemmas;

    lemma_va_level_to_trace_valid::<C>(va, level);
}

} // verus!
