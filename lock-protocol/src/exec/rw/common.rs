use std::ops::Range;

use vstd::prelude::*;
use vstd::vstd::arithmetic::power2::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::seq::*;

use crate::helpers::bits::*;
use crate::helpers::extern_const::*;
use crate::spec::{common::*, utils::*};

pub use super::configs::*;
pub use crate::mm::{Paddr, Vaddr, PagingLevel};

verus! {

// pub const MAX_FRAME_NUM: u64 = 256;
pub const INVALID_PADDR: Paddr = 0xffff_ffff_ffff_ffff;

// extern_const!(
// pub MAX_RC [MAX_RC_SPEC, CONST_MAX_RC]: u64 = 382);
} // verus!
verus! {

// Maybe introduce a MAX_PADDR constant in the future.
pub open spec fn valid_paddr(pa: Paddr) -> bool {
    true
}

pub uninterp spec fn paddr_to_vaddr_spec(pa: Paddr) -> Vaddr;

#[inline(always)]
#[verifier::when_used_as_spec(paddr_to_vaddr_spec)]
#[verifier::external_body]
pub fn paddr_to_vaddr(pa: Paddr) -> (va: Vaddr)
// requires
// valid_paddr(pa),

    ensures
        va == paddr_to_vaddr_spec(pa),
{
    unimplemented!()
}

} // verus!
verus! {

pub open spec fn valid_vaddr(va: Vaddr) -> bool {
    0 <= va < (1u64 << 48)
}

pub open spec fn valid_va_range(va: Range<Vaddr>) -> bool {
    0 <= va.start <= va.end <= (1u64 << 48)
}

#[verifier::allow_in_spec]
pub fn vaddr_is_aligned(va: Vaddr) -> (res: bool)
    requires
        valid_vaddr(va),
    returns
        (va & (low_bits_mask(12) as usize)) == 0,
{
    (va & low_bits_mask_usize(12)) == 0
}

pub open spec fn va_level_to_offset(va: Vaddr, level: PagingLevel) -> nat
    recommends
        valid_vaddr(va),
        1 <= level <= 4,
{
    ((va >> (12 + (level - 1) * 9)) & low_bits_mask(9) as usize) as nat
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

#[verifier::allow_in_spec]
pub fn pte_index(va: Vaddr, level: PagingLevel) -> (res: usize)
    requires
        valid_vaddr(va),
        1 <= level <= 4,
    ensures
        valid_pte_offset(res as nat),
    returns
        va_level_to_offset(va, level) as usize,
{
    let offset = (va >> (12 + (level - 1) * 9)) & low_bits_mask_usize(9);

    proof {
        lemma2_to64();
        let num = (va >> (12 + (level - 1) * 9));
        assert((num & 511) < 512) by (bit_vector);
    }

    offset
}

pub open spec fn va_level_to_trace(va: Vaddr, level: PagingLevel) -> Seq<nat>
    recommends
        1 <= level <= 4,
{
    Seq::new((4 - level) as nat, |i| va_level_to_offset(va, (4 - i) as PagingLevel))
}

pub open spec fn va_level_to_nid(va: Vaddr, level: PagingLevel) -> NodeId {
    NodeHelper::trace_to_nid(va_level_to_trace(va, level))
}

pub proof fn lemma_va_level_to_nid_valid(va: Vaddr, level: PagingLevel)
    requires
        valid_vaddr(va),
        1 <= level <= 4,
    ensures
        NodeHelper::valid_nid(va_level_to_nid(va, level)),
{
    lemma_va_level_to_trace_valid(va, level);
    NodeHelper::lemma_trace_to_nid_sound(va_level_to_trace(va, level));
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
    let trace_level_plus_1 = va_level_to_trace(va, (level + 1) as PagingLevel);
    let trace_level = va_level_to_trace(va, level);

    assert(trace_level == trace_level_plus_1.push(idx));
    assert(NodeHelper::nid_to_trace(nid) == trace_level_plus_1) by {
        assert(NodeHelper::valid_trace(trace_level_plus_1)) by {
            lemma_va_level_to_trace_valid(va, (level + 1) as PagingLevel);
        };
        NodeHelper::lemma_nid_to_trace_sound(nid);
        NodeHelper::lemma_trace_to_nid_sound(trace_level_plus_1);
        NodeHelper::lemma_trace_to_nid_bijective();
    };
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
