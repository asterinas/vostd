//! Architecture selection and shared memory specifications.
//!
//! # Verified Properties
//!
//! [`CurrentArch`] selects the target's implementation of the contracts in [`model`].
//! The erased [`valid_frame_paddr`] predicate requires base-page alignment and an
//! address below that implementation's modeled physical-memory bound. Shared
//! constants are re-exported from the executable architecture and memory modules.
//! The model's conversion lemmas establish bounds, round trips, and alignment
//! within the linear mapping window. Page-table proofs that call
//! [`crate::mm::PagingConstsTrait::axiom_current_paging_consts_hardcoded`] still
//! trust the current layout; that restriction is not enforced for other configurations.
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

#[cfg(target_arch = "x86_64")]
mod x86;
#[cfg(target_arch = "x86_64")]
pub use x86::*;

verus! {

/// The architecture selected by the current verification target.
#[cfg(target_arch = "x86_64")]
pub type CurrentArch = x86::X86Arch;

/// A physical address that can identify a base-page frame on the selected architecture.
pub open spec fn valid_frame_paddr(paddr: Paddr) -> bool {
    valid_frame_paddr_for::<CurrentArch>(paddr)
}

} // verus!
