// SPDX-License-Identifier: MPL-2.0
//! Bitwise-OR lemmas used by the `vaddr_range_bounds_spec` sanity check.
//!
//! Factored into a leaf module because Verus's `assert ... by (bit_vector)`
//! tactic currently trips over `impl Iterator` return types elsewhere in
//! the parent module (`largest_pages`), producing an ill-typed AIR panic.

use vstd::prelude::*;

verus! {

pub proof fn lemma_kernel_mask_or_bits()
    ensures
        (0x0000_8000_0000_0000_usize | 0xFFFF_0000_0000_0000_usize)
            == 0xFFFF_8000_0000_0000_usize,
        (0x0000_FFFF_FFFF_FFFF_usize | 0xFFFF_0000_0000_0000_usize)
            == 0xFFFF_FFFF_FFFF_FFFF_usize,
{
    assert((0x0000_8000_0000_0000_usize | 0xFFFF_0000_0000_0000_usize)
        == 0xFFFF_8000_0000_0000_usize) by (bit_vector);
    assert((0x0000_FFFF_FFFF_FFFF_usize | 0xFFFF_0000_0000_0000_usize)
        == 0xFFFF_FFFF_FFFF_FFFF_usize) by (bit_vector);
}

} // verus!
