use vstd::prelude::*;

use vstd::arithmetic::power2::{lemma_pow2_adds, lemma2_to64, lemma2_to64_rest, pow2};
use vstd_extra::prelude::*;

use crate::specs::mm::{
    frame::mapping::lemma_meta_to_frame_soundness,
    page_table::{nr_pte_index_bits_spec, pte_index_bit_offset_spec},
};

use crate::mm::{
    Paddr, PagingConstsTrait, Vaddr,
    frame::meta::{META_SLOT_SIZE, mapping::meta_to_frame},
    kspace::{FRAME_METADATA_RANGE, LINEAR_MAPPING_BASE_VADDR, VMALLOC_BASE_VADDR, paddr_to_vaddr},
    page_size,
};

verus! {

// Asterinas is designed for 64-bit architectures.
global size_of usize == 8;

global size_of isize == 8;

// The following constants are the same as those defined in `ostd::arch::mm::x86_64`,
// but we record their actual values for better proof automation.
/// Page size.
pub const PAGE_SIZE: usize = 4096;

/// The maximum number of entries in a page table node
pub const NR_ENTRIES: usize = 512;

/// The maximum level of a page table node.
pub const NR_LEVELS: usize = 4;

/// Parameterized maximum physical address.
pub const MAX_PADDR: usize = 0x8000_0000;

pub const MAX_NR_PAGES: u64 = (MAX_PADDR / PAGE_SIZE) as u64;

pub open spec fn has_safe_slot(paddr: Paddr) -> bool {
    &&& paddr % PAGE_SIZE == 0
    &&& paddr < MAX_PADDR
}

} // verus!
verus! {

pub proof fn lemma_linear_mapping_base_vaddr_properties()
    ensures
        LINEAR_MAPPING_BASE_VADDR % PAGE_SIZE == 0,
        LINEAR_MAPPING_BASE_VADDR < VMALLOC_BASE_VADDR,
{
    assert(LINEAR_MAPPING_BASE_VADDR % PAGE_SIZE == 0) by (compute_only);
    assert(LINEAR_MAPPING_BASE_VADDR < VMALLOC_BASE_VADDR) by (compute_only);
}

/// There is not an executable version in the source code.
#[verifier::inline]
pub open spec fn vaddr_to_paddr(va: Vaddr) -> usize
    recommends
        LINEAR_MAPPING_BASE_VADDR <= va < VMALLOC_BASE_VADDR,
{
    (va - LINEAR_MAPPING_BASE_VADDR) as usize
}

pub broadcast proof fn lemma_paddr_to_vaddr_properties(pa: Paddr)
    requires
        pa < VMALLOC_BASE_VADDR - LINEAR_MAPPING_BASE_VADDR,
    ensures
        LINEAR_MAPPING_BASE_VADDR <= #[trigger] paddr_to_vaddr(pa) < VMALLOC_BASE_VADDR,
        #[trigger] vaddr_to_paddr(paddr_to_vaddr(pa)) == pa,
{
}

pub broadcast proof fn lemma_vaddr_to_paddr_properties(va: Vaddr)
    requires
        LINEAR_MAPPING_BASE_VADDR <= va < VMALLOC_BASE_VADDR,
    ensures
        #[trigger] vaddr_to_paddr(va) < VMALLOC_BASE_VADDR - LINEAR_MAPPING_BASE_VADDR,
        #[trigger] paddr_to_vaddr(vaddr_to_paddr(va)) == va,
{
}

pub proof fn lemma_max_paddr_range()
    ensures
        MAX_PADDR < VMALLOC_BASE_VADDR - LINEAR_MAPPING_BASE_VADDR,
        MAX_PADDR + LINEAR_MAPPING_BASE_VADDR < usize::MAX,
{
    assert(MAX_PADDR < VMALLOC_BASE_VADDR - LINEAR_MAPPING_BASE_VADDR) by (compute_only);
    assert(MAX_PADDR + LINEAR_MAPPING_BASE_VADDR < usize::MAX) by (compute_only);
}

pub broadcast proof fn lemma_meta_frame_vaddr_properties(meta: Vaddr)
    requires
        meta % META_SLOT_SIZE == 0,
        FRAME_METADATA_RANGE.start <= meta < FRAME_METADATA_RANGE.start + MAX_NR_PAGES
            * META_SLOT_SIZE,
    ensures
        LINEAR_MAPPING_BASE_VADDR <= #[trigger] paddr_to_vaddr(meta_to_frame(meta))
            < VMALLOC_BASE_VADDR,
        #[trigger] paddr_to_vaddr(meta_to_frame(meta)) % PAGE_SIZE == 0,
{
    let pa = meta_to_frame(meta);
    lemma_meta_to_frame_soundness(meta);
    lemma_max_paddr_range();
    let va = paddr_to_vaddr(pa);
    lemma_linear_mapping_base_vaddr_properties();
    assert(va % PAGE_SIZE == 0) by {
        lemma_mod_0_add(pa as int, LINEAR_MAPPING_BASE_VADDR as int, PAGE_SIZE as int);
    };
}

// Here are some architecture-specific const value properties.
// Any use of this lemma in architecture-independent code should be removed.
pub(crate) proof fn lemma_arch_specific_consts_properties<C: PagingConstsTrait>()
    ensures
        C::BASE_PAGE_SIZE().ilog2() == 12u32,
        nr_pte_index_bits_spec::<C>() == 9usize,
        pow2(9) == NR_ENTRIES,
        pte_index_bit_offset_spec::<C>(4) == 39,
        0 * pow2(39) == 0,
        256 * pow2(39) == pow2(47),
        512 * pow2(39) == pow2(48),
        pow2(47) - 1 == 0x0000_7FFF_FFFF_FFFF,
        0xffff_int * 0x1_0000_0000_0000int + pow2(47) == 0xffff_8000_0000_0000int,
        0xffff_int * 0x1_0000_0000_0000int + pow2(48) - 1 == 0xffff_ffff_ffff_ffffint,
{
    C::lemma_paging_consts_properties();
    lemma2_to64();
    lemma2_to64_rest();
    lemma_usize_pow2_ilog2(12);
    lemma_usize_pow2_ilog2(9);
    lemma_usize_pow2_ilog2(12);
    lemma_usize_pow2_ilog2(9);
    lemma_pow2_adds(8, 39);
}

} // verus!
