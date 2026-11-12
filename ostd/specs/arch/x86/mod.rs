use vstd::{
    arithmetic::power2::{lemma_pow2_adds, lemma2_to64, lemma2_to64_rest, pow2},
    prelude::*,
};
use vstd_extra::prelude::*;

use crate::specs::{
    arch::{
        CurrentArch, lemma_max_paddr_range, lemma_paddr_to_vaddr_properties,
        model::{ArchAddressSpaceModel, lemma_paddr_to_vaddr_aligned_for},
    },
    mm::{
        frame::mapping::lemma_meta_to_frame_soundness,
        page_table::{
            leading_bits_spec, nr_page_table_coverage_bits_spec, nr_pte_index_bits_spec,
            page_table_managed_end_spec, page_table_managed_start_spec, pte_index_bit_offset_spec,
            vaddr_range_proofs, vaddr_range_spec,
        },
    },
};

use crate::{
    arch::mm::{NR_ENTRIES, PAGE_SIZE, PagingConsts},
    mm::{
        MAX_NR_PAGES, MAX_PADDR, Paddr, PagingConstsTrait, Vaddr,
        frame::meta::{META_SLOT_SIZE, mapping::meta_to_frame},
        kspace::{
            FRAME_METADATA_RANGE, KernelPtConfig, LINEAR_MAPPING_BASE_VADDR, VMALLOC_BASE_VADDR,
            paddr_to_vaddr,
        },
        vm_space::UserPtConfig,
    },
};

verus! {

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

    proof fn lemma_model_requirements() {
        Self::C::lemma_paging_consts_requirements();
        assert(Self::linear_mapping_base_vaddr_spec() % Self::C::BASE_PAGE_SIZE() == 0)
            by (compute_only);

        assert(0 < Self::max_paddr_spec()) by (compute_only);
        assert(Self::C::BASE_PAGE_SIZE() <= Self::max_paddr_spec()) by (compute_only);
        assert(Self::max_paddr_spec() % Self::C::BASE_PAGE_SIZE() == 0) by (compute_only);
        assert(Self::max_paddr_spec() + Self::linear_mapping_base_vaddr_spec()
            < Self::vmalloc_base_vaddr_spec()) by (compute_only);
    }
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
    lemma_pow2_adds(8, 39);
}

/// Checks the user address range for x86-64 four-level paging.
pub(crate) proof fn lemma_vaddr_range_spec_user()
    ensures
        leading_bits_spec::<UserPtConfig>() == 0,
        page_table_managed_start_spec::<UserPtConfig>() == 0,
        page_table_managed_end_spec::<UserPtConfig>() == 0x0000_8000_0000_0000int,
        vaddr_range_spec::<UserPtConfig>().start == 0,
        vaddr_range_spec::<UserPtConfig>().end == 0x0000_7FFF_FFFF_FFFF,
{
    lemma_arch_specific_consts_properties::<PagingConsts>();
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma2_to64_rest();
}

/// Checks the kernel address range for x86-64 four-level paging.
pub(crate) proof fn lemma_vaddr_range_spec_kernel()
    ensures
        leading_bits_spec::<KernelPtConfig>() == 0xffff,
        page_table_managed_start_spec::<KernelPtConfig>() == 0xFFFF_8000_0000_0000,
        page_table_managed_end_spec::<KernelPtConfig>() == 0x1_0000_0000_0000_0000int,
        vaddr_range_spec::<KernelPtConfig>().start == 0xFFFF_8000_0000_0000,
        vaddr_range_spec::<KernelPtConfig>().end == 0xFFFF_FFFF_FFFF_FFFF,
{
    lemma_arch_specific_consts_properties::<PagingConsts>();
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma2_to64_rest();
    vstd::layout::unsigned_int_max_values();
    assert(nr_page_table_coverage_bits_spec::<PagingConsts>() == 48);
    vaddr_range_proofs::lemma_leading_bits_properties::<KernelPtConfig>();
    assert((256 * pow2(39) as int / pow2(47) as int) % 2 == 1);
}

} // verus!
