use vstd::prelude::*;

use crate::specs::arch::model::ArchAddressSpaceModel;

use crate::{
    arch::mm::PagingConsts,
    mm::{
        MAX_PADDR, Paddr, PagingConstsTrait, Vaddr,
        kspace::{LINEAR_MAPPING_BASE_VADDR, VMALLOC_BASE_VADDR},
    },
};

verus! {

/// The LoongArch address-space model.
///
/// Checks address bounds; MMU and direct-mapping-window setup remain unverified.
pub ghost struct LoongArch;

impl ArchAddressSpaceModel for LoongArch {
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

} // verus!
