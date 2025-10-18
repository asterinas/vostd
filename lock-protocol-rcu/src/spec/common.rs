use std::{io::Write, path, result};
use std::ops::Range;

use vstd::{prelude::*, seq::*};
use vstd::bits::{low_bits_mask, lemma_low_bits_mask_values};
use vstd_extra::{ghost_tree::Node, seq_extra::*};

use crate::mm::{PagingLevel, Vaddr};
use crate::spec::utils::{NodeHelper, group_node_helper_lemmas};

verus! {

pub type CpuId = nat;

pub type NodeId = nat;

pub open spec fn valid_cpu(cpu_num: CpuId, cpu: CpuId) -> bool {
    0 <= cpu < cpu_num
}

pub open spec fn valid_pte_offset(offset: nat) -> bool {
    0 <= offset < 512
}

pub open spec fn valid_vaddr(va: Vaddr) -> bool {
    0 <= va < (1u64 << 48)
}

pub open spec fn valid_va_range(va: Range<Vaddr>) -> bool {
    0 <= va.start <= va.end <= (1u64 << 48)
}

pub open spec fn vaddr_is_aligned(va: Vaddr) -> (res: bool)
    recommends
        valid_vaddr(va),
{
    (va & (low_bits_mask(12) as usize)) == 0
}

pub open spec fn va_level_to_offset(va: Vaddr, level: PagingLevel) -> nat
    recommends
        valid_vaddr(va),
        1 <= level <= 4,
{
    ((va >> (12 + (level - 1) * 9)) & low_bits_mask(9) as usize) as nat
}

} // verus!
verus! {

pub open spec fn va_level_to_trace(va: Vaddr, level: PagingLevel) -> Seq<nat>
    recommends
        1 <= level <= 4,
{
    Seq::new((4 - level) as nat, |i| va_level_to_offset(va, (4 - i) as PagingLevel))
}

pub open spec fn va_level_to_nid(va: Vaddr, level: PagingLevel) -> NodeId {
    NodeHelper::trace_to_nid(va_level_to_trace(va, level))
}

pub proof fn lemma_va_level_to_nid_inc(va: Vaddr, level: PagingLevel, nid: NodeId, idx: nat)
    requires
        valid_vaddr(va),
        1 <= level < 4,
        NodeHelper::valid_nid(nid),
        nid == va_level_to_nid(va, (level + 1) as PagingLevel),
        valid_pte_offset(idx),
        idx == va_level_to_offset(va, (level + 1) as PagingLevel),
    ensures
        NodeHelper::get_child(nid, idx) == va_level_to_nid(va, level),
{
    broadcast use group_node_helper_lemmas;
    // Establish the relationship between traces at consecutive levels

    let trace_level_plus_1 = va_level_to_trace(va, (level + 1) as PagingLevel);
    let trace_level = va_level_to_trace(va, level);

    // Show that trace_level = trace_level_plus_1.push(idx)
    assert(trace_level == trace_level_plus_1.push(idx));

    // Now use the fact that nid = trace_to_nid(trace_level_plus_1)
    // and get_child(nid, idx) = trace_to_nid(nid_to_trace(nid).push(idx))
    assert(NodeHelper::nid_to_trace(nid) == trace_level_plus_1) by {
        // First establish that trace_level_plus_1 is a valid trace
        assert(NodeHelper::valid_trace(trace_level_plus_1)) by {
            lemma_va_level_to_trace_valid(va, (level + 1) as PagingLevel);
        };
        NodeHelper::lemma_trace_to_nid_bijective();
    };
}

pub proof fn lemma_va_level_to_offset_range(va: Vaddr, level: PagingLevel)
    requires
        1 <= level <= 4,
    ensures
        0 <= va_level_to_offset(va, level) < 512,
{
    let offset = va_level_to_offset(va, level);
    assert(offset < 512) by {
        assert(low_bits_mask(9) == 511) by {
            lemma_low_bits_mask_values();
        };
        assert((va >> (12 + (level - 1) as usize * 9)) & 511 <= 511) by (bit_vector);
    }
}

pub proof fn lemma_va_level_to_trace_valid(va: Vaddr, level: PagingLevel)
    requires
        1 <= level <= 4,
    ensures
        NodeHelper::valid_trace(va_level_to_trace(va, level)),
    decreases 4 - level,
{
    if level < 4 {
        lemma_va_level_to_trace_valid(va, (level + 1) as PagingLevel);
        lemma_va_level_to_offset_range(va, (level + 1) as PagingLevel);
        assert(va_level_to_trace(va, level) == va_level_to_trace(
            va,
            (level + 1) as PagingLevel,
        ).push(va_level_to_offset(va, (level + 1) as PagingLevel)));
    }
}

} // verus!
