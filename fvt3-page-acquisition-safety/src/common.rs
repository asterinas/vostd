use vstd::prelude::*;
use core::mem::size_of;
use core::ops::Range;
use crate::page::meta::MetaSlot;

verus! {

pub type Paddr = u64;

pub type Vaddr = u64;

pub const PAGE_SIZE: u64 = 4096;

// TODO: parameterize the maximum physical address
pub const MAX_PADDR: u64 = 0x8000_0000;

pub const FRAME_METADATA_RANGE: Range<u64> = 0xffff_fe00_0000_0000..0xffff_ff00_0000_0000;

pub const META_SLOT_SIZE: u64 = 16;

pub const MAX_NR_PAGES: u64 = MAX_PADDR / PAGE_SIZE;

#[allow(non_snake_case)]
pub proof fn lemma_FRAME_METADATA_RANGE_is_page_aligned()
    ensures
        FRAME_METADATA_RANGE.start % PAGE_SIZE == 0,
        FRAME_METADATA_RANGE.end % PAGE_SIZE == 0,
{
}

#[allow(non_snake_case)]
pub proof fn lemma_FRAME_METADATA_RANGE_is_large_enough()
    ensures
        FRAME_METADATA_RANGE.end >= FRAME_METADATA_RANGE.start + MAX_NR_PAGES * META_SLOT_SIZE,
{
}

} // verus!
verus! {

global size_of MetaSlot == 16;

pub proof fn lemma_meta_slot_size() {
    assert(size_of::<MetaSlot>() == META_SLOT_SIZE);
}

pub open spec fn page_to_meta_spec(paddr: Paddr) -> Vaddr {
    (FRAME_METADATA_RANGE.start as int + paddr as int / 256) as Vaddr
}

pub open spec fn meta_to_page_spec(vaddr: Vaddr) -> Paddr {
    ((vaddr as int - FRAME_METADATA_RANGE.start as int) * 256) as Paddr
}

pub open spec fn page_to_index_spec(paddr: int) -> int {
    paddr / (PAGE_SIZE as int)
}

pub open spec fn index_to_page_spec(index: int) -> int {
    index * (PAGE_SIZE as int)
}

} // verus!
verus! {

/// Converts a physical address of a base page to the virtual address of the metadata slot.
#[verifier::when_used_as_spec(page_to_meta_spec)]
pub fn page_to_meta(paddr: Paddr) -> (res: Vaddr)
    requires
        paddr % PAGE_SIZE == 0,
        paddr < MAX_PADDR,
    ensures
        res == page_to_meta_spec(paddr),
        res % META_SLOT_SIZE == 0,
{
    let base = FRAME_METADATA_RANGE.start;
    let offset = paddr / PAGE_SIZE;
    assert(size_of::<MetaSlot>() as u64 == 16);
    assert(offset * (size_of::<MetaSlot>() as u64) == paddr / 256);
    base + offset * (size_of::<MetaSlot>() as u64)
}

#[verifier::when_used_as_spec(meta_to_page_spec)]
pub fn meta_to_page(vaddr: Vaddr) -> (res: Paddr)
    requires
        FRAME_METADATA_RANGE.start <= vaddr && vaddr < FRAME_METADATA_RANGE.end,
        vaddr % META_SLOT_SIZE == 0,
    ensures
        res == meta_to_page_spec(vaddr),
        res % PAGE_SIZE == 0,
{
    let base = FRAME_METADATA_RANGE.start;
    let offset = (vaddr - base) / (size_of::<MetaSlot>() as u64);
    assert(offset == (vaddr - base) / 16);
    offset * PAGE_SIZE
}

} // verus!
verus! {

pub proof fn lemma_meta_to_page_bijectivity(paddr: Paddr)
    requires
        paddr % PAGE_SIZE == 0,
        paddr < MAX_PADDR,
    ensures
        paddr == meta_to_page(page_to_meta(paddr)),
{
}

pub proof fn lemma_page_to_meta_bijectivity(vaddr: Vaddr)
    requires
        FRAME_METADATA_RANGE.start <= vaddr && vaddr < FRAME_METADATA_RANGE.end,
        vaddr % META_SLOT_SIZE == 0,
    ensures
        vaddr == page_to_meta(meta_to_page(vaddr)),
{
}

} // verus!
verus! {

pub proof fn lemma_meta_to_page_soundness(page: Paddr, meta: Vaddr)
    requires
        page == meta_to_page(meta),
        meta % META_SLOT_SIZE == 0,
        FRAME_METADATA_RANGE.start <= meta && meta < FRAME_METADATA_RANGE.start + MAX_NR_PAGES
            * META_SLOT_SIZE,
    ensures
        page % PAGE_SIZE == 0,
        page < MAX_PADDR,
{
}

pub proof fn lemma_page_to_meta_soundness(page: Paddr, meta: Vaddr)
    requires
        meta == page_to_meta(page),
        page % PAGE_SIZE == 0,
        page < MAX_PADDR,
    ensures
        meta % META_SLOT_SIZE == 0,
        FRAME_METADATA_RANGE.start <= meta && meta < FRAME_METADATA_RANGE.start + MAX_NR_PAGES
            * META_SLOT_SIZE,
{
}

pub proof fn lemma_meta_to_page_alignment(meta: Vaddr)
    requires
        meta % META_SLOT_SIZE == 0,
        FRAME_METADATA_RANGE.start <= meta && meta < FRAME_METADATA_RANGE.start + MAX_NR_PAGES
            * META_SLOT_SIZE,
    ensures
        meta_to_page(meta) % PAGE_SIZE == 0,
        meta_to_page(meta) < MAX_PADDR,
{
}

} // verus!
