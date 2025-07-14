use std::ops::Range;

use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::vstd::arithmetic::power2::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;

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

pub open spec fn va_level_to_trace_rec(va: Vaddr, level: PagingLevel) -> Seq<nat>
    recommends
        1 <= level <= 4,
    decreases 4 - level,
    when 1 <= level <= 4
{
    if level == 4 {
        Seq::empty()
    } else {
        va_level_to_trace_rec(va, (level + 1) as PagingLevel).push(
            ((va >> (level * 9)) & low_bits_mask(9) as usize) as nat,
        )
    }
}

pub open spec fn va_level_to_trace(va: Vaddr, level: PagingLevel) -> Seq<nat> {
    va_level_to_trace_rec(va >> 12, level)
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
    // Establish the relationship between traces at consecutive levels
    let trace_level_plus_1 = va_level_to_trace(va, (level + 1) as PagingLevel);
    let trace_level = va_level_to_trace(va, level);

    // Show that trace_level = trace_level_plus_1.push(idx)
    assert(trace_level == trace_level_plus_1.push(idx)) by {
        // By definition: va_level_to_trace(va, level) = va_level_to_trace_rec(va >> 12, level)
        // And: va_level_to_trace_rec(va >> 12, level) = va_level_to_trace_rec(va >> 12, level + 1).push(((va >> 12 >> (level * 9)) & mask) as nat)
        // We need to show that ((va >> 12 >> (level * 9)) & mask) as nat == idx
        // Since idx = va_level_to_offset(va, level + 1) = ((va >> (12 + level * 9)) & mask) as nat
        // And (va >> 12 >> (level * 9)) = (va >> (12 + level * 9)) by bit shift properties
        // reveal(va_level_to_trace_rec);
        assert(va_level_to_trace_rec(va >> 12, level) == va_level_to_trace_rec(
            va >> 12,
            (level + 1) as PagingLevel,
        ).push(((va >> 12 >> (level * 9)) & low_bits_mask(9) as usize) as nat));

        // Show the bit extraction equivalence
        let offset = (va >> 12 >> (level * 9)) & low_bits_mask(9) as usize;
        assert(offset as nat == idx) by {
            // va_level_to_offset(va, level + 1) = ((va >> (12 + ((level + 1) - 1) * 9)) & mask) as nat
            //                                   = ((va >> (12 + level * 9)) & mask) as nat
            // We need to show: (va >> 12 >> (level * 9)) & mask == (va >> (12 + level * 9)) & mask
            // This follows from bit shift associativity: a >> b >> c == a >> (b + c)
            assert(low_bits_mask(9) == 511) by {
                lemma_low_bits_mask_values();
            };
            assert((va >> 12 >> (level * 9)) == (va >> (12 + level * 9))) by (bit_vector);
            assert(((va >> 12 >> (level * 9)) & 511 as usize) == ((va >> (12 + level * 9))
                & 511 as usize)) by (bit_vector);
        }
    };

    // Now use the fact that nid = trace_to_nid(trace_level_plus_1)
    // and get_child(nid, idx) = trace_to_nid(nid_to_trace(nid).push(idx))
    assert(NodeHelper::nid_to_trace(nid) == trace_level_plus_1) by {
        // First establish that trace_level_plus_1 is a valid trace
        assert(NodeHelper::valid_trace(trace_level_plus_1)) by {
            // trace_level_plus_1 = va_level_to_trace(va, level + 1)
            // Use the lemma that directly proves va_level_to_trace produces valid traces
            lemma_va_level_to_trace_valid(va, (level + 1) as PagingLevel);
        };

        // Since nid = trace_to_nid(trace_level_plus_1) and trace_to_nid is bijective
        NodeHelper::lemma_nid_to_trace_sound(nid);
        NodeHelper::lemma_trace_to_nid_sound(trace_level_plus_1);
        // From the precondition: nid == va_level_to_nid(va, level + 1)
        // And va_level_to_nid(va, level + 1) == trace_to_nid(trace_level_plus_1)
        // So nid == trace_to_nid(trace_level_plus_1)
        // Since trace_to_nid is bijective, nid_to_trace(nid) == trace_level_plus_1
        assert(NodeHelper::trace_to_nid(NodeHelper::nid_to_trace(nid)) == NodeHelper::trace_to_nid(
            trace_level_plus_1,
        ));
        NodeHelper::lemma_trace_to_nid_bijective();
    };
}

pub proof fn lemma_va_level_to_trace_rec_len(va: Vaddr, level: PagingLevel)
    requires
        1 <= level <= 4,
    ensures
        va_level_to_trace_rec(va, level).len() == 4 - level,
    decreases 4 - level,
{
    if level < 4 {
        lemma_va_level_to_trace_rec_len(va, (level + 1) as PagingLevel);
    }
}

pub proof fn lemma_va_level_to_trace_valid(va: Vaddr, level: PagingLevel)
    requires
        1 <= level <= 4,
    ensures
        NodeHelper::valid_trace(va_level_to_trace(va, level)),
{
    lemma_va_level_to_trace_rec_valid(va >> 12, level);
}

pub proof fn lemma_va_level_to_trace_rec_valid(va: Vaddr, level: PagingLevel)
    requires
        1 <= level <= 4,
    ensures
        NodeHelper::valid_trace(va_level_to_trace_rec(va, level)),
    decreases 4 - level,
{
    if level < 4 {
        lemma_va_level_to_trace_rec_valid(va, (level + 1) as PagingLevel);
        let offset = (va >> (level * 9)) & low_bits_mask(9) as usize;
        assert(offset < 512) by {
            assert(low_bits_mask(9) == 511) by {
                lemma_low_bits_mask_values();
            };
            assert((va >> (level * 9)) & 511 <= 511) by (bit_vector);
        }
        // By inductive hypothesis, the recursive trace is valid
        assert(NodeHelper::valid_trace(va_level_to_trace_rec(va, (level + 1) as PagingLevel)));
        assert(va_level_to_trace_rec(va, (level + 1) as PagingLevel).len() + 1 <= 3) by {
            lemma_va_level_to_trace_rec_len(va, (level + 1) as PagingLevel);
        };
    }
}

} // verus!
