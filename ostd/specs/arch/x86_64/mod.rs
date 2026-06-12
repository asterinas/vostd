#![allow(unused_imports)]

pub mod kspace;

use vstd::prelude::*;
use core::ops::Range;
use crate::mm::Vaddr;

use super::*;

pub use kspace::*;

verus! {

global size_of usize == 8;

global size_of isize == 8;


/// Page size.
pub const PAGE_SIZE: usize = 4096;

/// The maximum number of entries in a page table node
pub const NR_ENTRIES: usize = 512;

/// The maximum level of a page table node.
pub const NR_LEVELS: usize = 4;

/// Parameterized maximum physical address.
pub const MAX_PADDR: usize = 0x8000_0000;

pub const MAX_NR_PAGES: u64 = (MAX_PADDR / PAGE_SIZE) as u64;

/// The maximum virtual address of user space (non inclusive).
pub const MAX_USERSPACE_VADDR: Vaddr = 0x0000_8000_0000_0000_usize - PAGE_SIZE;

/// The kernel address space.
/// There are the high canonical addresses defined in most 48-bit width
/// architectures.
pub const KERNEL_VADDR_RANGE: Range<Vaddr> =
    0xffff_8000_0000_0000_usize..0xffff_ffff_ffff_0000_usize;


} // verus!
