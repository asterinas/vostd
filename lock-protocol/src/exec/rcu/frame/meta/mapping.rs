use core::ops::Range;
use core::mem::size_of;

use vstd::prelude::*;

use super::super::super::common::*;
use super::MetaSlot;

verus! {

// global layout MetaSlot is size == 12, align == 12;
pub uninterp spec fn frame_to_meta_spec(paddr: Paddr) -> Vaddr;

/// Converts a physical address of a base frame to the virtual address of the metadata slot.
#[inline(always)]
#[verifier::when_used_as_spec(frame_to_meta_spec)]
#[verifier::external_body]
pub const fn frame_to_meta(paddr: Paddr) -> Vaddr
    returns
        frame_to_meta_spec(paddr),
{
    // let base = FRAME_METADATA_RANGE.start;
    // let offset = paddr / PAGE_SIZE;
    // base + offset * size_of::<MetaSlot>()
    unimplemented!()
}

pub uninterp spec fn meta_to_frame_spec(vaddr: Vaddr) -> Paddr;

/// Converts a virtual address of the metadata slot to the physical address of the frame.
#[inline(always)]
#[verifier::when_used_as_spec(meta_to_frame_spec)]
#[verifier::external_body]
pub const fn meta_to_frame(vaddr: Vaddr) -> Paddr
    returns
        meta_to_frame_spec(vaddr),
{
    // let base = FRAME_METADATA_RANGE.start;
    // let offset = (vaddr - base) / size_of::<MetaSlot>();
    // offset * PAGE_SIZE
    unimplemented!()
}

} // verus!
