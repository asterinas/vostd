use vstd::prelude::*;
use vstd_extra::extern_const::*;

use core::ops::Range;

use super::*;

verus! {

extern_const!(
/// Kernel virtual address range for storing the page frame metadata.
pub FRAME_METADATA_RANGE
    [FRAME_METADATA_RANGE_SPEC, CONST_FRAME_METADATA_RANGE]: Range<Vaddr>
    = 0xffff_fe00_0000_0000..0xffff_ff00_0000_0000
);

} // verus!
