use vstd::{
    arithmetic::power2::{lemma_pow2_adds, lemma2_to64, lemma2_to64_rest, pow2},
    prelude::*,
};
use vstd_extra::prelude::*;

use super::{
    CurrentArch,
    model::{
        self, ArchAddressSpaceModel, lemma_paddr_to_vaddr_aligned_for,
        lemma_paddr_to_vaddr_properties_for, lemma_vaddr_to_paddr_properties_for,
    },
};

use crate::specs::mm::{
    frame::mapping::lemma_meta_to_frame_soundness,
    page_table::{nr_pte_index_bits_spec, pte_index_bit_offset_spec},
};

use crate::{
    arch::mm::{NR_ENTRIES, NR_LEVELS, PAGE_SIZE},
    mm::{
        MAX_NR_PAGES, MAX_PADDR, Paddr, PagingConstsTrait, PagingLevel, Vaddr,
        frame::meta::{META_SLOT_SIZE, mapping::meta_to_frame},
        kspace::{
            FRAME_METADATA_RANGE, LINEAR_MAPPING_BASE_VADDR, VMALLOC_BASE_VADDR, paddr_to_vaddr,
        },
        page_size,
    },
};

verus! {

// Asterinas is designed for 64-bit architectures.
global size_of usize == 8;

global size_of isize == 8;

/// The x86 instance of the architecture-wide specification contract.
pub ghost struct X86Arch;

impl ArchAddressSpaceModel for X86Arch {
    type C = crate::arch::mm::PagingConsts;

    open spec fn max_paddr_spec() -> Paddr {
        MAX_PADDR
    }

    open spec fn linear_mapping_base_vaddr_spec() -> Vaddr {
        LINEAR_MAPPING_BASE_VADDR
    }

    open spec fn vmalloc_base_vaddr_spec() -> Vaddr {
        VMALLOC_BASE_VADDR
    }

    proof fn lemma_paging_model_requirements() {
        Self::C::lemma_paging_consts_requirements();
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
    lemma_paddr_to_vaddr_properties(pa);
    lemma_paddr_to_vaddr_aligned_for::<CurrentArch>(pa);
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
    C::axiom_current_paging_consts_hardcoded();
    lemma2_to64();
    lemma2_to64_rest();
    lemma_usize_pow2_ilog2(12);
    lemma_usize_pow2_ilog2(9);
    lemma_usize_pow2_ilog2(12);
    lemma_usize_pow2_ilog2(9);
    lemma_pow2_adds(8, 39);
}

} // verus!
