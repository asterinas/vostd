use vstd::prelude::*;

use vstd_extra::prelude::*;

use core::ops::Range;

use super::*;
use crate::mm::{Vaddr, Paddr, page_prop::CachePolicy};

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
pub const KERNEL_VADDR_RANGE: Range<Vaddr> = 0xffff_8000_0000_0000_usize..0xffff_ffff_ffff_0000_usize;


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
pub fn current_page_table_paddr() -> Paddr {
    unimplemented!()
}

} // verus!
verus! {

/// Flush any TLB entry that contains the map of the given virtual address.
///
/// This flush performs regardless of the global-page bit. So it can flush both global
/// and non-global entries.
#[verifier::external_body]
pub fn tlb_flush_addr(vaddr: Vaddr) {
    // tlb::flush(VirtAddr::new(vaddr as u64));
    unimplemented!()
}

/// Flush any TLB entry that intersects with the given address range.
#[verifier::external_body]
pub fn tlb_flush_addr_range(range: &Range<Vaddr>) {
    for vaddr in range.clone().step_by(PAGE_SIZE) {
        tlb_flush_addr(vaddr);
    }
}

/// Flush all TLB entries except for the global-page entries.
#[verifier::external_body]
pub fn tlb_flush_all_excluding_global() {
    // tlb::flush_all();
    unimplemented!()
}

/// Flush all TLB entries, including global-page entries.
#[verifier::external_body]
pub fn tlb_flush_all_including_global() {
    // SAFETY: updates to CR4 here only change the global-page bit, the side effect
    // is only to invalidate the TLB, which doesn't affect the memory safety.
    // unsafe {
    //     // To invalidate all entries, including global-page
    //     // entries, disable global-page extensions (CR4.PGE=0).
    //     x86_64::registers::control::Cr4::update(|cr4| {
    //         *cr4 -= x86_64::registers::control::Cr4Flags::PAGE_GLOBAL;
    //     });
    //     x86_64::registers::control::Cr4::update(|cr4| {
    //         *cr4 |= x86_64::registers::control::Cr4Flags::PAGE_GLOBAL;
    //     });
    // }
    unimplemented!()
}

} // verus!
