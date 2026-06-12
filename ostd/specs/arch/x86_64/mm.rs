use vstd::prelude::*;

use vstd_extra::prelude::*;

use core::ops::Range;

use super::*;
use crate::mm::{Paddr, Vaddr, page_prop::CachePolicy};

verus! {

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

pub uninterp spec fn current_page_table_paddr_spec() -> Paddr;

/// Activates the given level 4 page table.
/// The cache policy of the root page table node is controlled by `root_pt_cache`.
///
/// # Safety
///
/// Changing the level 4 page table is unsafe, because it's possible to violate memory safety by
/// changing the page mapping.
#[verifier::external_body]
pub unsafe fn activate_page_table(root_paddr: Paddr, root_pt_cache: CachePolicy) {
    unimplemented!()
}

#[verifier::external_body]
#[verifier::when_used_as_spec(current_page_table_paddr_spec)]
#[verus_spec(
    returns
        current_page_table_paddr_spec(),
)]
pub fn current_page_table_paddr() -> Paddr {
    unimplemented!()
}

} // verus!