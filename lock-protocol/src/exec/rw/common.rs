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

verus! {

pub type Paddr = usize;

pub type Vaddr = usize;

pub type PagingLevel = usize;

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
    requires
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

pub open spec fn vaddr_is_aligned_spec(va: Vaddr) -> bool {
    (va & (low_bits_mask(12) as usize)) == 0
}

#[verifier::when_used_as_spec(vaddr_is_aligned_spec)]
pub fn vaddr_is_aligned(va: Vaddr) -> (res: bool)
    requires
        valid_vaddr(va),
    returns
        vaddr_is_aligned_spec(va),
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
        res == va_level_to_offset(va, level),
        valid_pte_offset(res as nat),
{
    let offset = (va >> (12 + (level - 1) * 9)) & low_bits_mask_usize(9);
    assert(valid_pte_offset(offset as nat)) by {
        // let x: usize = va >> (12 + (level - 1) * 9);
        // lemma_u64_low_bits_mask_is_mod(x, 9);
        // lemma2_to64();
        // lemma_mod_bound(x as int, pow2(9) as int);
        admit();
    };
    offset
}

pub open spec fn va_level_to_trace_rec(va: Vaddr, level: PagingLevel) -> Seq<nat>
    recommends
        1 <= level <= 4,
    decreases 4 - level,
{
    if 1 <= level <= 4 {
        if level == 4 {
            Seq::empty()
        } else {
            va_level_to_trace_rec(va, (level + 1) as PagingLevel).push(
                ((va >> (level * 9)) & low_bits_mask(9) as usize) as nat,
            )
        }
    } else {
        arbitrary()
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
    admit();  // TODO
}

} // verus!
