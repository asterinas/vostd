use vstd::prelude::*;

use crate::mm::Paddr;

pub mod model;
pub use model::*;

// Compatibility re-exports for proof modules that still use `specs::arch`.
// The authoritative values live in the executable memory/architecture modules.
pub use crate::{
    arch::mm::{NR_ENTRIES, NR_LEVELS, PAGE_SIZE},
    mm::{MAX_NR_PAGES, MAX_PADDR},
};

mod x86;
pub use x86::*;

verus! {

/// The architecture selected by the current verification target.
pub type CurrentArch = x86::X86Arch;

/// A physical address that can identify a base-page frame on the selected architecture.
pub open spec fn valid_frame_paddr(paddr: Paddr) -> bool {
    valid_frame_paddr_for::<CurrentArch>(paddr)
}

} // verus!
