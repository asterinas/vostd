use vstd::{
    arithmetic::power2::{lemma2_to64, lemma2_to64_rest, pow2},
    prelude::*,
};
use vstd_extra::external::ilog2::lemma_usize_pow2_ilog2;

use crate::specs::{
    arch::model::ArchAddressSpaceModel,
    mm::page_table::{
        leading_bits_spec, nr_page_table_coverage_bits_spec, nr_pte_index_bits_spec,
        page_table_managed_end_spec, page_table_managed_start_spec, pte_index_bit_offset_spec,
        vaddr_range_proofs, vaddr_range_spec,
    },
};

use crate::{
    arch::mm::{NR_ENTRIES, PagingConsts},
    mm::{
        MAX_PADDR, Paddr, PagingConstsTrait, Vaddr,
        kspace::{KernelPtConfig, LINEAR_MAPPING_BASE_VADDR, VMALLOC_BASE_VADDR},
        vm_space::UserPtConfig,
    },
};

verus! {

/// The RISC-V instance of the architecture-wide specification contract.
///
/// The address constants are shared by all architectures in `mm::kspace`, so
/// the numeric requirements below follow from the shared values. Sv48 page-table
/// semantics and the linear-mapping window connection are not established here.
pub ghost struct RiscvArch;

impl ArchAddressSpaceModel for RiscvArch {
    type C = PagingConsts;

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
        assert(Self::linear_mapping_base_vaddr_spec() % Self::C::BASE_PAGE_SIZE() == 0)
            by (compute_only);

        assert(Self::max_paddr_spec() + Self::linear_mapping_base_vaddr_spec()
            < Self::vmalloc_base_vaddr_spec()) by (compute_only);
    }
}

/// Supplies the layout facts expected by shared page-table proofs.
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
    // TODO: Replace the shared hardcoded axiom with architecture-specific layout proofs.
    C::axiom_current_paging_consts_hardcoded();
    lemma2_to64();
    lemma2_to64_rest();
    lemma_usize_pow2_ilog2(12);
    lemma_usize_pow2_ilog2(9);
}

/// Checks the user address range for RISC-V Sv48.
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

/// Checks the kernel address range for RISC-V Sv48.
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
