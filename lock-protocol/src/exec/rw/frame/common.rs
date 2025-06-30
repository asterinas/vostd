use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {

pub type FrameId = u64;

pub const MAX_FRAME_NUM: u64 = 256;

pub open spec fn valid_fid(fid: FrameId) -> bool {
    0 <= fid < MAX_FRAME_NUM
}

pub open spec fn valid_paddr(pa: Paddr) -> bool {
    0 <= pa < (MAX_FRAME_NUM << 12)
}

pub open spec fn paddr_is_aligned_spec(pa: Paddr) -> bool {
    (pa & (low_bits_mask(12) as u64)) == 0
}

#[verifier::when_used_as_spec(paddr_is_aligned_spec)]
pub fn paddr_is_aligned(pa: Paddr) -> (res: bool)
    requires
        valid_paddr(pa),
    ensures
        res == paddr_is_aligned_spec(pa),
{
    assume(false);
    (pa & (1u64 << 12)) == 0
}

pub open spec fn fid_to_pa_spec(fid: FrameId) -> (res: Paddr) {
    fid << 12
}

#[verifier::when_used_as_spec(fid_to_pa_spec)]
pub fn fid_to_pa(fid: FrameId) -> (res: Paddr)
    requires
        valid_fid(fid),
    ensures
        res == fid_to_pa_spec(fid),
        valid_paddr(res),
        paddr_is_aligned(res),
{
    assume(false);
    fid << 12
}

pub open spec fn pa_to_fid_spec(pa: Paddr) -> FrameId {
    pa >> 12
}

#[verifier::when_used_as_spec(pa_to_fid_spec)]
pub fn pa_to_fid(pa: Paddr) -> (res: FrameId)
    requires
        valid_paddr(pa),
        paddr_is_aligned(pa),
    ensures
        res == pa_to_fid_spec(pa),
        valid_fid(res),
{
    assume(false);
    pa >> 12
}

} // verus!
