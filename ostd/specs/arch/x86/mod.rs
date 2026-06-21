use crate::arch::mm::PagingConsts;
use crate::mm::kspace::FRAME_METADATA_RANGE;
use crate::mm::kspace::{LINEAR_MAPPING_BASE_VADDR, VMALLOC_BASE_VADDR, paddr_to_vaddr};
use crate::mm::{
    KERNEL_VADDR_RANGE, Paddr, PagingConstsTrait, Vaddr, nr_subpage_per_huge, page_size,
};
use crate::specs::mm::frame::mapping::{
    META_SLOT_SIZE, lemma_meta_to_frame_soundness, meta_to_frame,
};
use crate::specs::mm::page_table::{vaddr_make, vaddr_shift_bits};
use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;
use vstd_extra::prelude::*;

verus! {

// Asterinas is designed for 64-bit architectures.
global size_of usize == 8;

global size_of isize == 8;

// The following constants are the same as those defined in `ostd::arch::mm::x86_64`,
// but we record their actual values for better proof automation.
/// Page size.
pub const PAGE_SIZE: usize = 4096;

/// The maximum number of entries in a page table node
pub const NR_ENTRIES: usize = 512;

/// The maximum level of a page table node.
pub const NR_LEVELS: usize = 4;

/// Parameterized maximum physical address.
pub const MAX_PADDR: usize = 0x8000_0000;

pub const MAX_NR_PAGES: u64 = (MAX_PADDR / PAGE_SIZE) as u64;

pub open spec fn has_safe_slot(paddr: Paddr) -> bool {
    &&& paddr % PAGE_SIZE == 0
    &&& paddr < MAX_PADDR
}

} // verus!
verus! {

pub proof fn lemma_linear_mapping_base_vaddr_properties()
    ensures
        LINEAR_MAPPING_BASE_VADDR % PAGE_SIZE == 0,
        LINEAR_MAPPING_BASE_VADDR < VMALLOC_BASE_VADDR,
{
    assert(LINEAR_MAPPING_BASE_VADDR % PAGE_SIZE == 0) by (compute_only);
    assert(LINEAR_MAPPING_BASE_VADDR < VMALLOC_BASE_VADDR) by (compute_only);
}

/// There is not an executable version in the source code.
#[verifier::inline]
pub open spec fn vaddr_to_paddr(va: Vaddr) -> usize
    recommends
        LINEAR_MAPPING_BASE_VADDR <= va < VMALLOC_BASE_VADDR,
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
        MAX_PADDR < VMALLOC_BASE_VADDR - LINEAR_MAPPING_BASE_VADDR,
        MAX_PADDR + LINEAR_MAPPING_BASE_VADDR < usize::MAX,
{
    assert(MAX_PADDR < VMALLOC_BASE_VADDR - LINEAR_MAPPING_BASE_VADDR) by (compute_only);
    assert(MAX_PADDR + LINEAR_MAPPING_BASE_VADDR < usize::MAX) by (compute_only);
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

pub proof fn lemma_nr_subpage_per_huge_eq_nr_entries()
    ensures
        crate::mm::nr_subpage_per_huge::<PagingConsts>() == NR_ENTRIES,
{
    assert(crate::mm::nr_subpage_per_huge::<PagingConsts>() == 4096usize / 8usize);
}

pub proof fn lemma_page_size_spec_values()
    ensures
        page_size::<PagingConsts>(1) == 4096,
        page_size::<PagingConsts>(2) == 2097152,
        page_size::<PagingConsts>(3) == 1073741824,
        page_size::<PagingConsts>(4) == 549755813888,
        page_size::<PagingConsts>(5) == 281474976710656,
{
    vstd_extra::external::ilog2::lemma_usize_ilog2_to32();
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma2_to64_rest();
    vstd::bits::lemma_usize_pow2_no_overflow(48);
}

/// Proves the concrete values of `vaddr_make` for the x86_64 paging configuration.
///
/// For any `C: PagingConstsTrait`, since all configs share
/// `BASE_PAGE_SIZE == 4096`, `nr_subpage_per_huge == 512`, and `NR_LEVELS == 4`:
///   - `vaddr_make::<C, NR_LEVELS>(0, i) == page_size::<C>(4) * i == 0x80_0000_0000 * i`
///   - `vaddr_make::<C, NR_LEVELS>(1, i) == page_size::<C>(3) * i == 0x4000_0000 * i`
///   - `vaddr_make::<C, NR_LEVELS>(2, i) == page_size::<C>(2) * i == 0x20_0000 * i`
///   - `vaddr_make::<C, NR_LEVELS>(3, i) == page_size::<C>(1) * i == 0x1000 * i`
pub proof fn lemma_vaddr_make_values<C: PagingConstsTrait>(idx: int, i: usize)
    requires
        0 <= idx <= 3,
        i < NR_ENTRIES,
    ensures
        idx == 0 ==> vaddr_make::<C, NR_LEVELS>(idx, i) == 0x80_0000_0000usize * i,
        idx == 1 ==> vaddr_make::<C, NR_LEVELS>(idx, i) == 0x4000_0000usize * i,
        idx == 2 ==> vaddr_make::<C, NR_LEVELS>(idx, i) == 0x20_0000usize * i,
        idx == 3 ==> vaddr_make::<C, NR_LEVELS>(idx, i) == 0x1000usize * i,
{
    C::lemma_paging_consts_properties();
    vstd_extra::external::ilog2::lemma_usize_ilog2_to32();
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma2_to64_rest();
    // After the above lemmas:
    //   C::BASE_PAGE_SIZE() == 4096, (4096usize).ilog2() == 12
    //   nr_subpage_per_huge::<C>() == 512, (512usize).ilog2() == 9
    //   NR_LEVELS == 4
    // So vaddr_shift_bits::<C, NR_LEVELS>(idx) = (12 + 9 * (3 - idx)) as nat
    //   idx=0: 39, idx=1: 30, idx=2: 21, idx=3: 12
    // And pow2(39) == 0x8000000000, pow2(30) == 0x40000000,
    //     pow2(21) == 0x200000, pow2(12) == 0x1000
    // vaddr_make(idx, i) = (pow2(shift_bits) as usize * i) as usize
    if idx == 0 {
        assert(vaddr_shift_bits::<C, NR_LEVELS>(0) == 39nat);
        assert(pow2(39) == 0x8000000000int);
        assert(vaddr_make::<C, NR_LEVELS>(0, i) == (0x8000000000int * i as int) as usize);
        assert(0x80_0000_0000usize * i == (0x8000000000int * i as int) as usize)
            by (nonlinear_arith)
            requires
                i < 512,
        ;
    } else if idx == 1 {
        assert(vaddr_shift_bits::<C, NR_LEVELS>(1) == 30nat);
        assert(pow2(30) == 0x40000000int);
        assert(vaddr_make::<C, NR_LEVELS>(1, i) == (0x40000000int * i as int) as usize);
        assert(0x4000_0000usize * i == (0x40000000int * i as int) as usize) by (nonlinear_arith)
            requires
                i < 512,
        ;
    } else if idx == 2 {
        assert(vaddr_shift_bits::<C, NR_LEVELS>(2) == 21nat);
        assert(pow2(21) == 0x200000int);
        assert(vaddr_make::<C, NR_LEVELS>(2, i) == (0x200000int * i as int) as usize);
        assert(0x20_0000usize * i == (0x200000int * i as int) as usize) by (nonlinear_arith)
            requires
                i < 512,
        ;
    } else {
        assert(idx == 3);
        assert(vaddr_shift_bits::<C, NR_LEVELS>(3) == 12nat);
        assert(pow2(12) == 0x1000int);
        assert(vaddr_make::<C, NR_LEVELS>(3, i) == (0x1000int * i as int) as usize);
        assert(0x1000usize * i == (0x1000int * i as int) as usize) by (nonlinear_arith)
            requires
                i < 512,
        ;
    }
}

/// Proves `page_size` values for any `C: PagingConstsTrait`. All configs share
/// `BASE_PAGE_SIZE == 4096` and `nr_subpage_per_huge == 512`, so page sizes are fixed.
pub proof fn lemma_page_size_values<C: PagingConstsTrait>()
    ensures
        page_size::<C>(1) == 0x1000usize,
        page_size::<C>(2) == 0x20_0000usize,
        page_size::<C>(3) == 0x4000_0000usize,
        page_size::<C>(4) == 0x80_0000_0000usize,
        page_size::<C>(5) == 0x1_0000_0000_0000usize,
{
    C::lemma_paging_consts_properties();
    vstd_extra::external::ilog2::lemma_usize_ilog2_to32();
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma2_to64_rest();
    vstd::bits::lemma_usize_pow2_no_overflow(48);
}

/// Arch-specific arithmetic step for `AbstractVaddr::from_vaddr_to_vaddr_roundtrip`.
/// Proves the 64-bit positional decomposition identity for any 64-bit `va`,
/// using the x86_64 layout (12-bit offset, 4 × 9-bit indices, 16-bit leading bits).
pub proof fn lemma_from_vaddr_to_vaddr_roundtrip<C: PagingConstsTrait>(va: crate::mm::Vaddr)
    ensures
        crate::specs::mm::page_table::AbstractVaddr::<C>::from_vaddr(va).to_vaddr() == va,
{
    use crate::specs::mm::page_table::AbstractVaddr;
    C::lemma_paging_consts_properties();
    vstd_extra::external::ilog2::lemma_usize_ilog2_to32();
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma2_to64_rest();
    let abs = AbstractVaddr::<C>::from_vaddr(va);
    assert(abs.to_vaddr_indices(NR_LEVELS as int) == 0);
    assert(abs.to_vaddr_indices(3) == abs.index[3] * pow2(39nat) as int + abs.to_vaddr_indices(4));
    assert(abs.to_vaddr_indices(2) == abs.index[2] * pow2(30nat) as int + abs.to_vaddr_indices(3));
    assert(abs.to_vaddr_indices(1) == abs.index[1] * pow2(21nat) as int + abs.to_vaddr_indices(2));
    assert(abs.to_vaddr_indices(0) == abs.index[0] * pow2(12nat) as int + abs.to_vaddr_indices(1));
    assert(va == (va % 4096usize) + ((va / 4096usize) % 512usize) * 4096usize + ((va
        / 0x20_0000usize) % 512usize) * 0x20_0000usize + ((va / 0x4000_0000usize) % 512usize)
        * 0x4000_0000usize + ((va / 0x80_0000_0000usize) % 512usize) * 0x80_0000_0000usize + (va
        / 0x1_0000_0000_0000usize) * 0x1_0000_0000_0000usize) by (bit_vector);
}

/// Arch-specific arithmetic step for `AbstractVaddr::to_vaddr_from_vaddr_roundtrip`.
/// Proves that reconstructing a 64-bit `va` from a well-formed `AbstractVaddr`
/// and extracting its components yields the same `AbstractVaddr`, using the
/// x86_64 layout (12-bit offset, 4 × 9-bit indices, 16-bit leading bits).
pub proof fn lemma_to_vaddr_from_vaddr_roundtrip<C: PagingConstsTrait>(
    abs: crate::specs::mm::page_table::AbstractVaddr<C>,
)
    requires
        abs.inv(),
    ensures
        crate::specs::mm::page_table::AbstractVaddr::<C>::from_vaddr(abs.to_vaddr()) == abs,
{
    use crate::specs::mm::page_table::AbstractVaddr;
    C::lemma_paging_consts_properties();
    vstd_extra::external::ilog2::lemma_usize_ilog2_to32();
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma2_to64_rest();
    abs.to_vaddr_bounded();
    assert(abs.to_vaddr_indices(NR_LEVELS as int) == 0);
    assert(abs.to_vaddr_indices(3) == abs.index[3] * pow2(39nat) as int + abs.to_vaddr_indices(4));
    assert(abs.to_vaddr_indices(2) == abs.index[2] * pow2(30nat) as int + abs.to_vaddr_indices(3));
    assert(abs.to_vaddr_indices(1) == abs.index[1] * pow2(21nat) as int + abs.to_vaddr_indices(2));
    assert(abs.to_vaddr_indices(0) == abs.index[0] * pow2(12nat) as int + abs.to_vaddr_indices(1));

    assert(abs.index.contains_key(0));
    assert(abs.index.contains_key(1));
    assert(abs.index.contains_key(2));
    assert(abs.index.contains_key(3));
    let i0 = abs.index[0] as usize;
    let i1 = abs.index[1] as usize;
    let i2 = abs.index[2] as usize;
    let i3 = abs.index[3] as usize;
    let o = abs.offset as usize;
    let tb = abs.leading_bits as usize;
    let va = abs.to_vaddr();
    assert(i0 < 512usize);
    assert(i1 < 512usize);
    assert(i2 < 512usize);
    assert(i3 < 512usize);
    assert(va == o + i0 * 4096usize + i1 * 0x20_0000usize + i2 * 0x4000_0000usize + i3
        * 0x80_0000_0000usize + tb * 0x1_0000_0000_0000usize);

    assert(va % 4096usize == o) by (bit_vector)
        requires
            va == o + i0 * 4096usize + i1 * 0x20_0000usize + i2 * 0x4000_0000usize + i3
                * 0x80_0000_0000usize + tb * 0x1_0000_0000_0000usize,
            o < 4096usize,
            i0 < 512usize,
            i1 < 512usize,
            i2 < 512usize,
            i3 < 512usize,
            tb < 0x1_0000usize,
    ;
    assert((va / 4096usize) % 512usize == i0) by (bit_vector)
        requires
            va == o + i0 * 4096usize + i1 * 0x20_0000usize + i2 * 0x4000_0000usize + i3
                * 0x80_0000_0000usize + tb * 0x1_0000_0000_0000usize,
            o < 4096usize,
            i0 < 512usize,
            i1 < 512usize,
            i2 < 512usize,
            i3 < 512usize,
            tb < 0x1_0000usize,
    ;
    assert((va / 0x20_0000usize) % 512usize == i1) by (bit_vector)
        requires
            va == o + i0 * 4096usize + i1 * 0x20_0000usize + i2 * 0x4000_0000usize + i3
                * 0x80_0000_0000usize + tb * 0x1_0000_0000_0000usize,
            o < 4096usize,
            i0 < 512usize,
            i1 < 512usize,
            i2 < 512usize,
            i3 < 512usize,
            tb < 0x1_0000usize,
    ;
    assert((va / 0x4000_0000usize) % 512usize == i2) by (bit_vector)
        requires
            va == o + i0 * 4096usize + i1 * 0x20_0000usize + i2 * 0x4000_0000usize + i3
                * 0x80_0000_0000usize + tb * 0x1_0000_0000_0000usize,
            o < 4096usize,
            i0 < 512usize,
            i1 < 512usize,
            i2 < 512usize,
            i3 < 512usize,
            tb < 0x1_0000usize,
    ;
    assert((va / 0x80_0000_0000usize) % 512usize == i3) by (bit_vector)
        requires
            va == o + i0 * 4096usize + i1 * 0x20_0000usize + i2 * 0x4000_0000usize + i3
                * 0x80_0000_0000usize + tb * 0x1_0000_0000_0000usize,
            o < 4096usize,
            i0 < 512usize,
            i1 < 512usize,
            i2 < 512usize,
            i3 < 512usize,
            tb < 0x1_0000usize,
    ;
    assert(va / 0x1_0000_0000_0000usize == tb) by (bit_vector)
        requires
            va == o + i0 * 4096usize + i1 * 0x20_0000usize + i2 * 0x4000_0000usize + i3
                * 0x80_0000_0000usize + tb * 0x1_0000_0000_0000usize,
            o < 4096usize,
            i0 < 512usize,
            i1 < 512usize,
            i2 < 512usize,
            i3 < 512usize,
            tb < 0x1_0000usize,
    ;

    let back = AbstractVaddr::<C>::from_vaddr(va);
    assert forall|i: int| 0 <= i < NR_LEVELS implies #[trigger] back.index[i] == abs.index[i] by {
        if i == 0 {
        } else if i == 1 {
        } else if i == 2 {
        } else if i == 3 {
        }
    }
    assert(back.index == abs.index);
}

} // verus!
