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
