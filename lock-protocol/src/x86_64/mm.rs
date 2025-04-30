use vstd::prelude::*;
use crate::mm::{page_prop::CachePolicy, Paddr, Vaddr};
use core::ops::Range;

use crate::extern_const;

extern_const!(
/// Page size.
pub PAGE_SIZE [PAGE_SIZE_SPEC, CONST_PAGE_SIZE]: usize = 4096);

extern_const!(
/// The maximum number of entries in a page table node
pub NR_ENTRIES [NR_ENTRIES_SPEC, CONST_NR_ENTRIES]: usize = 512);

extern_const!(
/// The maximum level of a page table node.
pub NR_LEVELS [NR_LEVELS_SPEC, CONST_NR_LEVELS]: usize = 4);

extern_const!(
/// Parameterized maximum physical address.
pub MAX_PADDR [MAX_PADDR_SPEC, CONST_MAX_PADDR]: usize = 0x8000_0000);

extern_const!(
pub MAX_NR_PAGES [MAX_NR_PAGES_SPEC, CONST_MAX_NR_PAGES]: u64 = (CONST_MAX_PADDR / CONST_PAGE_SIZE) as u64);

extern_const!(
/// The maximum virtual address of user space (non inclusive).
pub MAX_USERSPACE_VADDR
    [MAX_USERSPACE_VADDR_SPEC, CONST_MAX_USERSPACE_VADDR] : Vaddr =
    0x0000_8000_0000_0000_usize - CONST_PAGE_SIZE);

extern_const!(
/// The kernel address space.
/// There are the high canonical addresses defined in most 48-bit width
/// architectures.
pub KERNEL_VADDR_RANGE
    [KERNEL_VADDR_RANGE_SPEC, CONST_KERNEL_VADDR_RANGE] : Range<Vaddr> =
    0xffff_8000_0000_0000_usize..0xffff_ffff_ffff_0000_usize);

verus! {

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
    for vaddr in range.clone().step_by(PAGE_SIZE()) {
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
