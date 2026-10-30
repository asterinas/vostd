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

use crate::mm::{
    Paddr, Vaddr,
    kspace::{LINEAR_MAPPING_BASE_VADDR, VMALLOC_BASE_VADDR, paddr_to_vaddr},
};

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

#[cfg(target_arch = "riscv64")]
mod riscv;
#[cfg(target_arch = "riscv64")]
pub use riscv::*;

#[cfg(target_arch = "loongarch64")]
mod loongarch;
#[cfg(target_arch = "loongarch64")]
pub use loongarch::*;
verus! {

// Asterinas is designed for 64-bit architectures.
global size_of usize == 8;

global size_of isize == 8;

/// The architecture selected by the current verification target.
#[cfg(target_arch = "x86_64")]
pub type CurrentArch = x86::X86Arch;

/// The architecture selected by the current verification target.
#[cfg(target_arch = "riscv64")]
pub type CurrentArch = riscv::RiscvArch;

#[cfg(target_arch = "loongarch64")]
pub type CurrentArch = loongarch::LoongArch;

/// A physical address that can identify a base-page frame on the selected architecture.
pub open spec fn valid_frame_paddr(paddr: Paddr) -> bool {
    valid_frame_paddr_for::<CurrentArch>(paddr)
}

pub proof fn lemma_linear_mapping_base_vaddr_properties()
    ensures
        LINEAR_MAPPING_BASE_VADDR % PAGE_SIZE == 0,
        LINEAR_MAPPING_BASE_VADDR < VMALLOC_BASE_VADDR,
{
    CurrentArch::lemma_model_requirements();
}

/// Converts a virtual address in the linear mapping to a physical address.
#[verifier::inline]
pub open spec fn vaddr_to_paddr(va: Vaddr) -> usize
    recommends
        LINEAR_MAPPING_BASE_VADDR <= va < VMALLOC_BASE_VADDR,
{
    model::vaddr_to_paddr_for::<CurrentArch>(va)
}

/// Relates the current linear mapping to its architecture model and inverse.
pub broadcast proof fn lemma_paddr_to_vaddr_properties(pa: Paddr)
    requires
        pa < VMALLOC_BASE_VADDR - LINEAR_MAPPING_BASE_VADDR,
    ensures
        #[trigger] paddr_to_vaddr(pa) == model::paddr_to_vaddr_for::<CurrentArch>(pa),
        LINEAR_MAPPING_BASE_VADDR <= #[trigger] paddr_to_vaddr(pa) < VMALLOC_BASE_VADDR,
        #[trigger] vaddr_to_paddr(paddr_to_vaddr(pa)) == pa,
{
    lemma_paddr_to_vaddr_properties_for::<CurrentArch>(pa);
}

pub broadcast proof fn lemma_vaddr_to_paddr_properties(va: Vaddr)
    requires
        LINEAR_MAPPING_BASE_VADDR <= va < VMALLOC_BASE_VADDR,
    ensures
        #[trigger] vaddr_to_paddr(va) < VMALLOC_BASE_VADDR - LINEAR_MAPPING_BASE_VADDR,
        #[trigger] paddr_to_vaddr(vaddr_to_paddr(va)) == va,
{
    lemma_vaddr_to_paddr_properties_for::<CurrentArch>(va);
}

pub proof fn lemma_max_paddr_range()
    ensures
        MAX_PADDR < VMALLOC_BASE_VADDR - LINEAR_MAPPING_BASE_VADDR,
        MAX_PADDR + LINEAR_MAPPING_BASE_VADDR < usize::MAX,
{
    CurrentArch::lemma_model_requirements();
}

} // verus!
