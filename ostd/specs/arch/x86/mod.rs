use vstd::prelude::*;

use vstd::arithmetic::power2::{lemma_pow2_adds, lemma2_to64, lemma2_to64_rest, pow2};
use vstd_extra::prelude::*;

use super::model::{self, ArchAddressSpaceModel, ArchPagingModel, ArchTrait};

use crate::arch::mm::{NR_ENTRIES, NR_LEVELS};
use crate::specs::mm::{
    frame::mapping::lemma_meta_to_frame_soundness,
    page_table::{nr_pte_index_bits_spec, pte_index_bit_offset_spec},
};

use crate::mm::{
    CurrentPagingConstsTrait, MAX_NR_PAGES, MAX_PADDR, Paddr, PagingConstsTrait, PagingLevel,
    Vaddr,
    frame::meta::{META_SLOT_SIZE, mapping::meta_to_frame},
    kspace::{FRAME_METADATA_RANGE, LINEAR_MAPPING_BASE_VADDR, VMALLOC_BASE_VADDR, paddr_to_vaddr},
    page_size,
};

verus! {

// Asterinas is designed for 64-bit architectures.
global size_of usize == 8;

global size_of isize == 8;

/// Page size used by the current verification target.
pub const PAGE_SIZE: usize = crate::arch::mm::x86_base_page_size!();

pub open spec fn valid_frame_paddr(paddr: Paddr) -> bool {
    model::valid_frame_paddr_for::<CurrentArch>(paddr)
}

/// The x86 instance of the architecture-wide specification contract.
pub struct X86Arch;

impl ArchPagingModel for X86Arch {
    type C = crate::arch::mm::PagingConsts;

    open spec fn max_paddr_spec() -> Paddr {
        MAX_PADDR
    }

    proof fn lemma_paging_model_requirements() {
        Self::C::lemma_paging_consts_requirements();

    }
}

impl ArchAddressSpaceModel for X86Arch {
    open spec fn linear_mapping_base_vaddr_spec() -> Vaddr {
        LINEAR_MAPPING_BASE_VADDR
    }

    open spec fn vmalloc_base_vaddr_spec() -> Vaddr {
        VMALLOC_BASE_VADDR
    }

    proof fn lemma_address_space_model_requirements() {
        Self::C::lemma_paging_consts_requirements();
        Self::lemma_paging_model_requirements();
        assert(Self::linear_mapping_base_vaddr_spec() % Self::C::BASE_PAGE_SIZE() == 0)
            by (compute_only);

        assert(Self::max_paddr_spec() < Self::vmalloc_base_vaddr_spec()
            - Self::linear_mapping_base_vaddr_spec()) by (compute_only);

    }
}

impl ArchTrait for X86Arch {

}

/// The architecture selected by the current verification target.
pub type CurrentArch = X86Arch;

pub proof fn lemma_valid_frame_paddr_model_equivalent(paddr: Paddr)
    ensures
        valid_frame_paddr(paddr) == model::valid_frame_paddr_for::<CurrentArch>(paddr),
{
    CurrentArch::lemma_paging_model_requirements();
}

pub proof fn lemma_linear_mapping_base_vaddr_properties()
    ensures
        LINEAR_MAPPING_BASE_VADDR % PAGE_SIZE == 0,
        LINEAR_MAPPING_BASE_VADDR < VMALLOC_BASE_VADDR,
{
    CurrentArch::lemma_address_space_model_requirements();

}

/// There is not an executable version in the source code.
#[verifier::inline]
pub open spec fn vaddr_to_paddr(va: Vaddr) -> usize
    recommends
        LINEAR_MAPPING_BASE_VADDR <= va < VMALLOC_BASE_VADDR,
{
    model::vaddr_to_paddr_for::<CurrentArch>(va)
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
    CurrentArch::lemma_address_space_model_requirements();

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
pub(crate) proof fn lemma_arch_specific_consts_properties<C: CurrentPagingConstsTrait>()
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
    C::lemma_current_paging_consts_requirements();
    lemma2_to64();
    lemma2_to64_rest();
    lemma_usize_pow2_ilog2(12);
    lemma_usize_pow2_ilog2(9);
    lemma_usize_pow2_ilog2(12);
    lemma_usize_pow2_ilog2(9);
    lemma_pow2_adds(8, 39);
}

} // verus!
