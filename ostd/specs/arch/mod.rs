//! Target selection and the public interface to architecture address-space models.
//!
//! [`model`] defines the common contract. Each target implements that contract,
//! and the current-target adapters connect it to the executable memory layout.
mod current;
pub mod model;

pub use current::{lemma_max_paddr_range, lemma_paddr_to_vaddr_properties, valid_frame_paddr};
pub use model::ArchAddressSpaceModel;

// Compatibility re-exports for proof modules that still use `specs::arch`.
// The authoritative values live in the executable memory/architecture modules.
pub use crate::{
    arch::mm::{NR_ENTRIES, NR_LEVELS, PAGE_SIZE},
    mm::{MAX_NR_PAGES, MAX_PADDR},
};

#[cfg(target_arch = "x86_64")]
mod x86;
/// The architecture selected by the current verification target.
#[cfg(target_arch = "x86_64")]
pub use x86::X86Arch as CurrentArch;

#[cfg(target_arch = "riscv64")]
mod riscv;
/// The architecture selected by the current verification target.
#[cfg(target_arch = "riscv64")]
pub use riscv::RiscvArch as CurrentArch;

#[cfg(target_arch = "loongarch64")]
mod loongarch;
/// The architecture selected by the current verification target.
#[cfg(target_arch = "loongarch64")]
pub use loongarch::LoongArch as CurrentArch;
