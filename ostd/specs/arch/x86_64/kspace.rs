use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;
use vstd_extra::extern_const::*;

use super::*;
use crate::mm::{
    frame::meta::mapping::{lemma_meta_to_frame_soundness, meta_to_frame},
    frame::*,
    Paddr, PagingConsts, Vaddr,
};
use crate::specs::mm::frame::mapping::META_SLOT_SIZE;

use core::ops::Range;

verus! {

extern_const!(
/// The shortest supported address width is 39 bits. And the literal
/// values are written for 48 bits address width. Adjust the values
/// by arithmetic left shift.
pub ADDR_WIDTH_SHIFT [ADDR_WIDTH_SHIFT_SPEC, CONST_ADDR_WIDTH_SHIFT]:
    isize = /* PagingConsts::ADDRESS_WIDTH() */ 48 - 48
);

extern_const!(
/// Start of the kernel address space.
/// This is the _lowest_ address of the x86-64's _high_ canonical addresses.
pub KERNEL_BASE_VADDR [KERNEL_BASE_VADDR_SPEC, CONST_KERNEL_BASE_VADDR]:
    Vaddr = 0xffff_8000_0000_0000_usize << CONST_ADDR_WIDTH_SHIFT
);

extern_const!(
/// End of the kernel address space (non inclusive).
pub KERNEL_END_VADDR [KERNEL_END_VADDR_SPEC, CONST_KERNEL_END_VADDR]:
    Vaddr = 0xffff_ffff_ffff_0000_usize << CONST_ADDR_WIDTH_SHIFT
);

extern_const!(
/// Kernel virtual address range for storing the page frame metadata.
pub FRAME_METADATA_RANGE
    [FRAME_METADATA_RANGE_SPEC, CONST_FRAME_METADATA_RANGE]: Range<Vaddr>
    = 0xffff_fff0_0000_0000..0xffff_fff0_8000_0000
);

extern_const!(
pub FRAME_METADATA_CAP_VADDR [FRAME_METADATA_CAP_VADDR_SPEC, CONST_FRAME_METADATA_CAP_VADDR]:
    Vaddr = 0xffff_fff0_8000_0000_usize << CONST_ADDR_WIDTH_SHIFT
);

extern_const!(
pub FRAME_METADATA_BASE_VADDR [FRAME_METADATA_BASE_VADDR_SPEC, CONST_FRAME_METADATA_BASE_VADDR]:
    Vaddr = 0xffff_fff0_0000_0000_usize << CONST_ADDR_WIDTH_SHIFT
);

pub const LINEAR_MAPPING_BASE_VADDR: Vaddr = 0xffff_8000_0000_0000_usize << CONST_ADDR_WIDTH_SHIFT;

pub const VMALLOC_BASE_VADDR: Vaddr = 0xffff_fd00_0000_0000_usize << CONST_ADDR_WIDTH_SHIFT;

pub const LINEAR_MAPPING_VADDR_RANGE: Range<Vaddr> = LINEAR_MAPPING_BASE_VADDR..VMALLOC_BASE_VADDR;


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
        LINEAR_MAPPING_BASE_VADDR % PAGE_SIZE() == 0,
        LINEAR_MAPPING_BASE_VADDR < VMALLOC_BASE_VADDR,
{
    assert(LINEAR_MAPPING_BASE_VADDR == 0xffff_8000_0000_0000) by (compute_only);
    assert(VMALLOC_BASE_VADDR == 0xffff_fd00_0000_0000) by (compute_only);
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
        MAX_PADDR() <= VMALLOC_BASE_VADDR - LINEAR_MAPPING_BASE_VADDR,
{
    assert(VMALLOC_BASE_VADDR == 0xffff_fd00_0000_0000) by (compute_only);
    assert(LINEAR_MAPPING_BASE_VADDR == 0xffff_8000_0000_0000) by (compute_only);
    assert(VMALLOC_BASE_VADDR - LINEAR_MAPPING_BASE_VADDR == 0x7d00_0000_0000);
    assert(MAX_PADDR() == 0x8000_0000);
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
        FRAME_METADATA_RANGE().start <= meta < FRAME_METADATA_RANGE().start + MAX_NR_PAGES()
            * META_SLOT_SIZE,
    ensures
        LINEAR_MAPPING_BASE_VADDR <= #[trigger] paddr_to_vaddr(meta_to_frame(meta))
            < VMALLOC_BASE_VADDR,
        #[trigger] paddr_to_vaddr(meta_to_frame(meta)) % PAGE_SIZE() == 0,
{
    let pa = meta_to_frame(meta);
    lemma_meta_to_frame_soundness(meta);
    assert(pa < MAX_PADDR());
    assert(pa % PAGE_SIZE() == 0);
    lemma_max_paddr_range();
    assert(pa < VMALLOC_BASE_VADDR - LINEAR_MAPPING_BASE_VADDR);
    let va = paddr_to_vaddr(pa);
    lemma_linear_mapping_base_vaddr_properties();
    assert(LINEAR_MAPPING_BASE_VADDR % PAGE_SIZE() == 0);
    assert(va % PAGE_SIZE() == 0) by {
        lemma_mod_0_add(pa as int, LINEAR_MAPPING_BASE_VADDR as int, PAGE_SIZE() as int);
    };
}

} // verus!
