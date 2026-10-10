//! Architecture contracts for modeled frames and linear address mappings.
//!
//! # Verified Properties
//!
//! These erased contracts require each architecture instance to prove that its
//! modeled physical-address bound is page-aligned and that its linear mapping
//! has room for those addresses without overflow. The bound limits tracked
//! memory; it does not describe the processor's physical-address width.
//! Within each architecture's linear mapping window, the address conversions
//! preserve bounds and are mutual inverses. Physical-to-virtual conversion also
//! preserves base-page alignment.
//! `CurrentArch` selects the instance for this target. Calls to
//! `PagingConstsTrait::axiom_current_paging_consts_hardcoded` mark proofs that
//! still depend on the constants used by executable page-table layouts.
use vstd::prelude::*;
use vstd_extra::arithmetic::lemma_mod_0_add;

use crate::mm::{Paddr, PagingConstsTrait, Vaddr};

verus! {

/// The architecture contract for modeled physical frames and their linear mapping.
///
/// The associated paging constants are still supplied by the existing
/// `PagingConstsTrait`; this trait supplies the modeled physical-address bound
/// and the kernel's linear mapping, together with their compatibility proofs.
pub trait ArchAddressSpaceModel {
    type C: PagingConstsTrait;

    /// The exclusive upper bound for modeled physical frame addresses.
    spec fn max_paddr_spec() -> Paddr;

    /// The base of the kernel's physical-to-virtual linear mapping.
    spec fn linear_mapping_base_vaddr_spec() -> Vaddr;

    /// The first virtual address reserved for vmalloc mappings.
    spec fn vmalloc_base_vaddr_spec() -> Vaddr;

    /// Proves that the modeled physical-address range contains whole base pages.
    proof fn lemma_paging_model_requirements()
        ensures
            0 < Self::max_paddr_spec(),
            Self::C::BASE_PAGE_SIZE() <= Self::max_paddr_spec(),
            Self::max_paddr_spec() % Self::C::BASE_PAGE_SIZE() == 0,
    ;

    /// Proves that the aligned linear mapping fits modeled memory before vmalloc without overflow.
    proof fn lemma_address_space_model_requirements()
        ensures
            Self::linear_mapping_base_vaddr_spec() % Self::C::BASE_PAGE_SIZE() == 0,
            Self::linear_mapping_base_vaddr_spec() < Self::vmalloc_base_vaddr_spec(),
            Self::max_paddr_spec() < Self::vmalloc_base_vaddr_spec()
                - Self::linear_mapping_base_vaddr_spec(),
            Self::max_paddr_spec() + Self::linear_mapping_base_vaddr_spec() < usize::MAX,
    ;
}

/// A physical address that can identify a base-page frame for architecture `A`.
pub open spec fn valid_frame_paddr_for<A: ArchAddressSpaceModel>(pa: Paddr) -> bool {
    pa % A::C::BASE_PAGE_SIZE() == 0 && pa < A::max_paddr_spec()
}

/// Convert a physical address through architecture `A`'s linear mapping.
pub open spec fn paddr_to_vaddr_for<A: ArchAddressSpaceModel>(pa: Paddr) -> Vaddr {
    (pa + A::linear_mapping_base_vaddr_spec()) as usize
}

/// Convert a linear-mapped virtual address back to a physical address.
pub open spec fn vaddr_to_paddr_for<A: ArchAddressSpaceModel>(va: Vaddr) -> Paddr {
    (va - A::linear_mapping_base_vaddr_spec()) as usize
}

/// Maps a physical offset into the linear mapping window and back without loss.
pub proof fn lemma_paddr_to_vaddr_properties_for<A: ArchAddressSpaceModel>(pa: Paddr)
    requires
        pa < A::vmalloc_base_vaddr_spec() - A::linear_mapping_base_vaddr_spec(),
    ensures
        A::linear_mapping_base_vaddr_spec() <= paddr_to_vaddr_for::<A>(pa)
            < A::vmalloc_base_vaddr_spec(),
        vaddr_to_paddr_for::<A>(paddr_to_vaddr_for::<A>(pa)) == pa,
{
}

/// Maps a linear-mapped virtual address to a physical offset and back without loss.
pub proof fn lemma_vaddr_to_paddr_properties_for<A: ArchAddressSpaceModel>(va: Vaddr)
    requires
        A::linear_mapping_base_vaddr_spec() <= va < A::vmalloc_base_vaddr_spec(),
    ensures
        vaddr_to_paddr_for::<A>(va) < A::vmalloc_base_vaddr_spec()
            - A::linear_mapping_base_vaddr_spec(),
        paddr_to_vaddr_for::<A>(vaddr_to_paddr_for::<A>(va)) == va,
{
}

/// Preserves base-page alignment when mapping a physical offset into the linear window.
pub proof fn lemma_paddr_to_vaddr_aligned_for<A: ArchAddressSpaceModel>(pa: Paddr)
    requires
        pa < A::vmalloc_base_vaddr_spec() - A::linear_mapping_base_vaddr_spec(),
        pa % A::C::BASE_PAGE_SIZE() == 0,
    ensures
        paddr_to_vaddr_for::<A>(pa) % A::C::BASE_PAGE_SIZE() == 0,
{
    A::C::lemma_paging_consts_requirements();
    A::lemma_address_space_model_requirements();
    lemma_mod_0_add(
        pa as int,
        A::linear_mapping_base_vaddr_spec() as int,
        A::C::BASE_PAGE_SIZE() as int,
    );
}

} // verus!
