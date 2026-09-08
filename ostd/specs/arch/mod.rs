pub mod model;
pub use model::*;

// Compatibility re-exports for proof modules that still use `specs::arch`.
// The authoritative values live in the executable memory/architecture modules.
pub use crate::{
    arch::mm::{NR_ENTRIES, NR_LEVELS},
    mm::{MAX_NR_PAGES, MAX_PADDR},
};

mod x86;
pub use x86::*;
