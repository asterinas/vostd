//! Address-space specifications instantiated for the current target.
//!
//! # Verified Properties
//!
//! The frame-address predicate combines base-page alignment with the current
//! model's physical-address bound. For physical offsets within the linear
//! mapping window, the bridge lemma proves that the executable conversion
//! agrees with the architecture model and stays within that window. The modeled
//! physical range fits in the window without address overflow. These erased
//! specifications instantiate the common contract for [`CurrentArch`].
use vstd::prelude::*;

use crate::specs::arch::{
    CurrentArch,
    model::{
        self, ArchAddressSpaceModel, lemma_paddr_to_vaddr_properties_for, valid_frame_paddr_for,
    },
};

use crate::mm::{
    MAX_PADDR, Paddr,
    kspace::{LINEAR_MAPPING_BASE_VADDR, VMALLOC_BASE_VADDR, paddr_to_vaddr},
};

verus! {

/// A physical address that can identify a base-page frame on the selected architecture.
pub open spec fn valid_frame_paddr(paddr: Paddr) -> bool {
    valid_frame_paddr_for::<CurrentArch>(paddr)
}

/// Relates the executable linear mapping to its model and establishes its bounds.
pub proof fn lemma_paddr_to_vaddr_properties(pa: Paddr)
    requires
        pa < VMALLOC_BASE_VADDR - LINEAR_MAPPING_BASE_VADDR,
    ensures
        paddr_to_vaddr(pa) == model::paddr_to_vaddr_for::<CurrentArch>(pa),
        LINEAR_MAPPING_BASE_VADDR <= paddr_to_vaddr(pa) < VMALLOC_BASE_VADDR,
{
    lemma_paddr_to_vaddr_properties_for::<CurrentArch>(pa);
}

/// The modeled physical range fits inside the current linear mapping without overflow.
pub proof fn lemma_max_paddr_range()
    ensures
        MAX_PADDR < VMALLOC_BASE_VADDR - LINEAR_MAPPING_BASE_VADDR,
        MAX_PADDR + LINEAR_MAPPING_BASE_VADDR < usize::MAX,
{
    CurrentArch::lemma_model_requirements();
}

} // verus!
