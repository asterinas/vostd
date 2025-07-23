use vstd::prelude::*;
use vstd::arithmetic::div_mod::*;

use crate::extern_const;
use crate::mm::*;
// use crate::page::meta::mapping::*;
use crate::x86_64::mm::{MAX_NR_PAGES, MAX_PADDR};
use core::ops::Range;

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
pub FRAME_METADATA_CAP_VADDR [FRAME_METADATA_CAP_VADDR_SPEC, CONST_FRAME_METADATA_CAP_VADDR]:
    Vaddr = 0xffff_ffff_ffff_0000_usize << CONST_ADDR_WIDTH_SHIFT
);

extern_const!(
pub LINEAR_MAPPING_BASE_VADDR [LINEAR_MAPPING_BASE_VADDR_SPEC, CONST_LINEAR_MAPPING_BASE_VADDR]:
    Vaddr = 0xffff_8000_0000_0000_usize << CONST_ADDR_WIDTH_SHIFT
);

extern_const!(
pub VMALLOC_BASE_VADDR [VMALLOC_BASE_VADDR_SPEC, CONST_VMALLOC_BASE_VADDR]:
    Vaddr = 0xffff_fd00_0000_0000_usize << CONST_ADDR_WIDTH_SHIFT
);

extern_const!(
pub LINEAR_MAPPING_VADDR_RANGE [LINEAR_MAPPING_VADDR_RANGE_SPEC, CONST_LINEAR_MAPPING_VADDR_RANGE]:
    Range<Vaddr> = CONST_LINEAR_MAPPING_BASE_VADDR..CONST_VMALLOC_BASE_VADDR
);

verus! {

#[inline(always)]
#[verifier::allow_in_spec]
pub fn paddr_to_vaddr(pa: Paddr) -> (res: usize)
    requires
        pa < VMALLOC_BASE_VADDR() - LINEAR_MAPPING_BASE_VADDR(),
    returns
        (pa + LINEAR_MAPPING_BASE_VADDR()) as usize,
{
    (pa + LINEAR_MAPPING_BASE_VADDR()) as usize
}

pub proof fn lemma_linear_mapping_base_vaddr_properties()
    ensures
        LINEAR_MAPPING_BASE_VADDR() % PAGE_SIZE() == 0,
        LINEAR_MAPPING_BASE_VADDR() < VMALLOC_BASE_VADDR(),
{
    assert(LINEAR_MAPPING_BASE_VADDR() == 0xffff_8000_0000_0000) by (compute_only);
    assert(VMALLOC_BASE_VADDR() == 0xffff_fd00_0000_0000) by (compute_only);
}

#[inline(always)]
#[verifier::allow_in_spec]
pub fn vaddr_to_paddr(va: Vaddr) -> (res: usize)
    requires
        LINEAR_MAPPING_BASE_VADDR() <= va < VMALLOC_BASE_VADDR(),
    returns
        (va - LINEAR_MAPPING_BASE_VADDR()) as usize,
{
    (va - LINEAR_MAPPING_BASE_VADDR()) as usize
}

pub broadcast proof fn lemma_paddr_to_vaddr_properties(pa: Paddr)
    requires
        pa < VMALLOC_BASE_VADDR() - LINEAR_MAPPING_BASE_VADDR(),
    ensures
        LINEAR_MAPPING_BASE_VADDR() <= #[trigger] paddr_to_vaddr(pa) < VMALLOC_BASE_VADDR(),
        #[trigger] vaddr_to_paddr(paddr_to_vaddr(pa)) == pa,
{
}

pub broadcast proof fn lemma_vaddr_to_paddr_properties(va: Vaddr)
    requires
        LINEAR_MAPPING_BASE_VADDR() <= va < VMALLOC_BASE_VADDR(),
    ensures
        #[trigger] vaddr_to_paddr(va) < VMALLOC_BASE_VADDR() - LINEAR_MAPPING_BASE_VADDR(),
        #[trigger] paddr_to_vaddr(vaddr_to_paddr(va)) == va,
{
}

pub proof fn lemma_max_paddr_range()
    ensures
        MAX_PADDR() <= VMALLOC_BASE_VADDR() - LINEAR_MAPPING_BASE_VADDR(),
{
    assert(VMALLOC_BASE_VADDR() == 0xffff_fd00_0000_0000) by (compute_only);
    assert(LINEAR_MAPPING_BASE_VADDR() == 0xffff_8000_0000_0000) by (compute_only);
    assert(VMALLOC_BASE_VADDR() - LINEAR_MAPPING_BASE_VADDR() == 0x7d00_0000_0000);
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

// TODO: fix this lemma?
// pub broadcast proof fn lemma_meta_frame_vaddr_properties(meta: Vaddr)
//     requires
//         meta % META_SLOT_SIZE() == 0,
//         FRAME_METADATA_RANGE().start <= meta < FRAME_METADATA_RANGE().start + MAX_NR_PAGES() * META_SLOT_SIZE(),
//     ensures
//         LINEAR_MAPPING_BASE_VADDR() <= #[trigger] paddr_to_vaddr(meta_to_page(meta)) < VMALLOC_BASE_VADDR(),
//         #[trigger] paddr_to_vaddr(meta_to_page(meta)) % PAGE_SIZE() == 0,
// {
//     let pa = meta_to_page(meta);
//     lemma_meta_to_page_soundness(meta);
//     assert(pa < MAX_PADDR());
//     assert(pa % PAGE_SIZE() == 0);
//     lemma_max_paddr_range();
//     assert(pa < VMALLOC_BASE_VADDR() - LINEAR_MAPPING_BASE_VADDR());
//     let va = paddr_to_vaddr(pa);
//     lemma_linear_mapping_base_vaddr_properties();
//     assert(LINEAR_MAPPING_BASE_VADDR() % PAGE_SIZE() == 0);
//     assert(va % PAGE_SIZE() == 0) by {
//         lemma_mod_0_add(pa as int, LINEAR_MAPPING_BASE_VADDR() as int, PAGE_SIZE() as int);
//     };
// }
extern_const!(
    pub TRACKED_MAPPED_PAGES_BASE_VADDR [TRACKED_MAPPED_PAGES_BASE_VADDR_SPEC, CONST_TRACKED_MAPPED_PAGES_BASE_VADDR]:
        Vaddr = 0xffff_d000_0000_0000 << CONST_ADDR_WIDTH_SHIFT
);

extern_const!(
    pub VMALLOC_VADDR_RANGE [VMALLOC_VADDR_RANGE_SPEC, CONST_VMALLOC_VADDR_RANGE]:
        Range<Vaddr> = CONST_VMALLOC_BASE_VADDR..CONST_TRACKED_MAPPED_PAGES_BASE_VADDR
);

} // verus!
