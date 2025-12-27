// SPDX-License-Identifier: MPL-2.0
//! Virtual memory (VM).
/// Virtual addresses.
pub type Vaddr = usize;

/// Physical addresses.
pub type Paddr = usize;

//pub(crate) mod dma;
pub mod frame;
//pub mod heap;
pub mod io;
// pub(crate) mod kspace;
pub(crate) mod page_prop;
pub(crate) mod page_table;
//pub mod tlb;
pub mod vm_space;

#[cfg(ktest)]
mod test;

use core::{fmt::Debug, ops::Range};

pub use aster_common::prelude::*;

/// The maximum virtual address of user space (non inclusive).
///
/// Typical 64-bit systems have at least 48-bit virtual address space.
/// A typical way to reserve half of the address space for the kernel is
/// to use the highest 48-bit virtual address space.
///
/// Also, the top page is not regarded as usable since it's a workaround
/// for some x86_64 CPUs' bugs. See
/// <https://github.com/torvalds/linux/blob/480e035fc4c714fb5536e64ab9db04fedc89e910/arch/x86/include/asm/page_64.h#L68-L78>
/// for the rationale.
pub const MAX_USERSPACE_VADDR: Vaddr = 0x0000_8000_0000_0000 - PAGE_SIZE();

/// The kernel address space.
///
/// There are the high canonical addresses defined in most 48-bit width
/// architectures.
pub const KERNEL_VADDR_RANGE: Range<Vaddr> = 0xffff_8000_0000_0000..0xffff_ffff_ffff_0000;

/// Gets physical address trait
pub trait HasPaddr {
    /// Returns the physical address.
    fn paddr(&self) -> Paddr;
}

/// Checks if the given address is page-aligned.
pub const fn is_page_aligned(p: usize) -> bool {
    (p & (PAGE_SIZE() - 1)) == 0
}
