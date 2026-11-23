// SPDX-License-Identifier: MPL-2.0
//! Access to the x86 trap handler table defined in `trap.S`.
use vstd::prelude::*;
use vstd_extra::external::x86_idt::{
    is_canonical, software_interrupt_safe, valid_handler, valid_vector,
};

#[verus_verify]
pub(crate) const NUM_INTERRUPTS: usize = 256;

extern "C" {
    #[link_name = "trap_handler_table"]
    static VECTORS: [usize; NUM_INTERRUPTS];
}

/// # Safety
/// The linker must have relocated all 256 entries. The table must remain aligned,
/// readable and immutable for the lifetime of the kernel.
#[verifier::when_used_as_spec(vector_table_spec)]
#[verifier::external_body]
#[verus_spec(
    requires vectors_ready(),
    returns vector_table(),
    opens_invariants none
    no_unwind
)]
pub(crate) unsafe fn vector_table() -> &'static [usize; NUM_INTERRUPTS] {
    unsafe { &VECTORS }
}

verus! {

/// The relocated table is an aligned, initialized, immutable region of 256
/// `usize` entries that remains readable for the lifetime of the kernel.
pub(crate) uninterp spec fn vectors_ready() -> bool;

pub(crate) uninterp spec fn vector_table_spec() -> &'static [usize; NUM_INTERRUPTS];

pub(crate) open spec fn valid_vectors(vectors: &[usize; NUM_INTERRUPTS]) -> bool {
    forall|i: int|
        0 <= i < vectors@.len() ==> {
            &&& is_canonical(#[trigger] vectors@[i] as u64)
            &&& valid_handler::<()>(vectors@[i] as u64)
            &&& valid_vector(vectors@[i] as u64, i)
            &&& (i == 3 || i == 4) ==> software_interrupt_safe(vectors@[i] as u64, i)
        }
}

} // verus!
