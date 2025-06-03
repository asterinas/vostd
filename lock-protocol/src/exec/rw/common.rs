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

verus! {

pub type Paddr = u64;

pub type Vaddr = u64;

pub type Level = u64;

// Configurations
pub spec const GLOBAL_CPU_NUM: nat = 2;

pub const INVALID_PADDR: Paddr = 0xffff_ffff_ffff_ffff;

extern_const!(
pub MAX_RC [MAX_RC_SPEC, CONST_MAX_RC]: u64 = 382);

} // verus!
verus! {

pub open spec fn valid_vaddr(va: Vaddr) -> bool {
    0 <= va < pow2(48)
}

pub open spec fn valid_va_range(va: Range<Vaddr>) -> bool {
    0 <= va.start <= va.end <= pow2(48)
}

pub open spec fn vaddr_is_aligned_spec(va: Vaddr) -> bool {
    (va & (low_bits_mask(12) as u64)) == 0
}

#[verifier::when_used_as_spec(vaddr_is_aligned_spec)]
pub fn vaddr_is_aligned(va: Vaddr) -> (res: bool)
    requires
        valid_vaddr(va),
    ensures
        res == vaddr_is_aligned_spec(va),
{
    (va & low_bits_mask_u64(12)) == 0
}

pub open spec fn va_level_to_offset(va: Vaddr, level: Level) -> nat
    recommends
        valid_vaddr(va),
        1 <= level <= 4,
{
    ((va >> (12 + (level - 1) * 9)) & low_bits_mask(9) as u64) as nat
}

pub fn pte_index(va: Vaddr, level: Level) -> (res: u64)
    requires
        valid_vaddr(va),
        1 <= level <= 4,
    ensures
        res == va_level_to_offset(va, level),
        valid_pte_offset(res as nat),
{
    let offset = (va >> (12 + (level - 1) * 9)) & low_bits_mask_u64(9);
    assert(valid_pte_offset(offset as nat)) by {
        let x: u64 = va >> (12 + (level - 1) * 9);
        lemma_u64_low_bits_mask_is_mod(x, 9);
        lemma2_to64();
        lemma_mod_bound(x as int, pow2(9) as int);
    };
    offset
}

pub open spec fn va_level_to_trace_rec(va: Vaddr, level: Level) -> Seq<nat>
    recommends
        1 <= level <= 4,
    decreases 4 - level,
{
    if 1 <= level <= 4 {
        if level == 4 {
            Seq::empty()
        } else {
            va_level_to_trace_rec(va, (level + 1) as Level).push(
                ((va >> (level * 9)) & low_bits_mask(9) as u64) as nat,
            )
        }
    } else {
        arbitrary()
    }
}

pub open spec fn va_level_to_trace(va: Vaddr, level: Level) -> Seq<nat> {
    va_level_to_trace_rec(va >> 12, level)
}

pub open spec fn va_level_to_nid(va: Vaddr, level: Level) -> NodeId {
    NodeHelper::trace_to_nid(va_level_to_trace(va, level))
}

} // verus!
