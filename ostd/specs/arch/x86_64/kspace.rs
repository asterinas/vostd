use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;

use super::*;
use crate::mm::{
    frame::meta::mapping::{lemma_meta_to_frame_soundness, meta_to_frame},
    frame::*,
    kspace::{
        ADDR_WIDTH_SHIFT, FRAME_METADATA_BASE_VADDR, FRAME_METADATA_CAP_VADDR, KERNEL_BASE_VADDR,
        KERNEL_END_VADDR, LINEAR_MAPPING_BASE_VADDR, LINEAR_MAPPING_VADDR_RANGE,
        VMALLOC_BASE_VADDR,
    },
    Paddr, PagingConsts, Vaddr,
};
use crate::specs::mm::frame::mapping::META_SLOT_SIZE;

use core::ops::Range;

verus! {

/// Kernel virtual address range for storing the page frame metadata.
pub const FRAME_METADATA_RANGE: Range<Vaddr> = 0xffff_fff0_0000_0000..0xffff_fff0_8000_0000;

#[verifier::inline]
pub open spec fn paddr_to_vaddr_spec(pa: Paddr) -> usize
    recommends
        pa < VMALLOC_BASE_VADDR - LINEAR_MAPPING_BASE_VADDR,
{
    (pa + LINEAR_MAPPING_BASE_VADDR) as usize
}

#[inline(always)]
#[verifier::when_used_as_spec(paddr_to_vaddr_spec)]
pub fn paddr_to_vaddr(pa: Paddr) -> (res: usize)
    requires
        pa < VMALLOC_BASE_VADDR - LINEAR_MAPPING_BASE_VADDR,
    ensures
        res == paddr_to_vaddr_spec(pa),
{
    (pa + LINEAR_MAPPING_BASE_VADDR) as usize
}

pub proof fn lemma_linear_mapping_base_vaddr_properties()
    ensures
        LINEAR_MAPPING_BASE_VADDR % PAGE_SIZE == 0,
        LINEAR_MAPPING_BASE_VADDR < VMALLOC_BASE_VADDR,
{
    assert(LINEAR_MAPPING_BASE_VADDR % PAGE_SIZE == 0) by (compute_only);
    assert(LINEAR_MAPPING_BASE_VADDR < VMALLOC_BASE_VADDR) by (compute_only);
}

#[verifier::inline]
pub open spec fn vaddr_to_paddr_spec(va: Vaddr) -> usize
    recommends
        LINEAR_MAPPING_BASE_VADDR <= va < VMALLOC_BASE_VADDR,
{
    (va - LINEAR_MAPPING_BASE_VADDR) as usize
}

#[inline(always)]
#[verifier::when_used_as_spec(vaddr_to_paddr_spec)]
pub fn vaddr_to_paddr(va: Vaddr) -> (res: usize)
    requires
        LINEAR_MAPPING_BASE_VADDR <= va < VMALLOC_BASE_VADDR,
    ensures
        res == vaddr_to_paddr(va),
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
        MAX_PADDR <= VMALLOC_BASE_VADDR - LINEAR_MAPPING_BASE_VADDR,
{
    assert(MAX_PADDR <= VMALLOC_BASE_VADDR - LINEAR_MAPPING_BASE_VADDR) by (compute_only);
}

pub proof fn lemma_mod_0_add(a: int, b: int, m: int)
    requires
        0 < m,
        a % m == 0,
        b % m == 0,
    ensures
        (a + b) % m == 0,
{
    lemma_mod_adds(a, b, m);
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

} // verus!
