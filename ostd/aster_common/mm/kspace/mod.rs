use vstd::prelude::*;

use core::ops::Range;

use super::*;

verus! {

/// Kernel virtual address range for storing the page frame metadata.
pub const FRAME_METADATA_RANGE: Range<Vaddr> = 0xffff_fe00_0000_0000..0xffff_ff00_0000_0000;

} // verus!
