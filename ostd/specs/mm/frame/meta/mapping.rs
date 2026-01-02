use vstd::prelude::*;

use super::*;

use core::mem::size_of;
use core::ops::Range;

verus! {

/// Metaslot size.
pub const META_SLOT_SIZE: usize = 64;

pub open spec fn max_meta_slots() -> int {
    (FRAME_METADATA_RANGE.end - FRAME_METADATA_RANGE.start) / META_SLOT_SIZE as int
}

pub open spec fn meta_addr(i: usize) -> (res: usize)
    recommends
        0 <= i < max_meta_slots() as usize,
{
    (FRAME_METADATA_RANGE.start + i * META_SLOT_SIZE) as usize
}

#[allow(non_snake_case)]
pub broadcast proof fn lemma_FRAME_METADATA_RANGE_is_page_aligned()
    ensures
        #[trigger] FRAME_METADATA_RANGE.start % PAGE_SIZE == 0,
        FRAME_METADATA_RANGE.end % PAGE_SIZE == 0,
{
}

#[allow(non_snake_case)]
pub broadcast proof fn lemma_FRAME_METADATA_RANGE_is_large_enough()
    ensures
        #[trigger] FRAME_METADATA_RANGE.end >= FRAME_METADATA_RANGE.start + MAX_NR_PAGES
            * META_SLOT_SIZE,
{
}

} // verus!
verus! {

#[verifier::inline]
pub open spec fn frame_to_meta_spec(paddr: Paddr) -> (res: Vaddr)
    recommends
        paddr % PAGE_SIZE == 0,
        paddr < MAX_PADDR,
{
    (FRAME_METADATA_RANGE.start + (paddr / PAGE_SIZE) * super::meta_slot_size()) as usize
}

#[verifier::inline]
pub open spec fn meta_to_frame_spec(vaddr: Vaddr) -> Paddr
    recommends
        vaddr % size_of::<super::MetaSlot>() == 0,
        FRAME_METADATA_RANGE.start <= vaddr < FRAME_METADATA_RANGE.end,
{
    ((vaddr - FRAME_METADATA_RANGE.start) / META_SLOT_SIZE as int * PAGE_SIZE) as usize
}

#[verifier::inline]
pub open spec fn frame_to_index_spec(paddr: Paddr) -> usize {
    paddr / PAGE_SIZE
}

#[verifier::inline]
pub open spec fn index_to_frame_spec(index: usize) -> Paddr {
    (index * PAGE_SIZE) as usize
}

#[verifier::when_used_as_spec(frame_to_index_spec)]
pub fn frame_to_index(paddr: Paddr) -> (res: usize)
    requires
        paddr % PAGE_SIZE == 0,
    ensures
        res == frame_to_index_spec(paddr),
{
    paddr / PAGE_SIZE
}

#[verifier::when_used_as_spec(index_to_frame_spec)]
pub fn index_to_frame(index: usize) -> (res: Paddr)
    requires
        index < max_meta_slots(),
    ensures
        res == index_to_frame_spec(index),
{
    index * PAGE_SIZE
}

} // verus!
verus! {

#[inline(always)]
#[verifier::when_used_as_spec(frame_to_meta_spec)]
pub fn frame_to_meta(paddr: Paddr) -> (res: Vaddr)
    requires
        paddr % PAGE_SIZE == 0,
        paddr < MAX_PADDR,
    ensures
        res == frame_to_meta_spec(paddr),
        res % META_SLOT_SIZE == 0,
{
    let base = FRAME_METADATA_RANGE.start;
    let offset = paddr / PAGE_SIZE;
    base + offset * META_SLOT_SIZE
}

#[inline(always)]
#[verifier::when_used_as_spec(meta_to_frame_spec)]
pub fn meta_to_frame(vaddr: Vaddr) -> (res: Paddr)
    requires
        FRAME_METADATA_RANGE.start <= vaddr && vaddr < FRAME_METADATA_RANGE.end,
        vaddr % META_SLOT_SIZE == 0,
    ensures
        res == meta_to_frame_spec(vaddr),
        res % PAGE_SIZE == 0,
{
    let base = FRAME_METADATA_RANGE.start;
    let offset = (vaddr - base) / META_SLOT_SIZE;
    offset * PAGE_SIZE
}

pub broadcast proof fn lemma_paddr_to_meta_biinjective(paddr: Paddr)
    requires
        paddr % PAGE_SIZE == 0,
        paddr < MAX_PADDR,
    ensures
        #[trigger] meta_to_frame(frame_to_meta(paddr)) == paddr,
{
}

pub broadcast proof fn lemma_meta_to_paddr_biinjective(vaddr: Vaddr)
    requires
        FRAME_METADATA_RANGE.start <= vaddr && vaddr < FRAME_METADATA_RANGE.end,
        vaddr % META_SLOT_SIZE == 0,
    ensures
        #[trigger] frame_to_meta(meta_to_frame(vaddr)) == vaddr,
{
}

pub broadcast proof fn lemma_meta_to_frame_soundness(meta: Vaddr)
    requires
        meta % META_SLOT_SIZE == 0,
        FRAME_METADATA_RANGE.start <= meta && meta < FRAME_METADATA_RANGE.start + MAX_NR_PAGES
            * META_SLOT_SIZE,
    ensures
        #[trigger] meta_to_frame(meta) % PAGE_SIZE == 0,
        meta_to_frame(meta) < MAX_PADDR,
{
}

pub broadcast proof fn lemma_frame_to_meta_soundness(page: Paddr)
    requires
        page % PAGE_SIZE == 0,
        page < MAX_PADDR,
    ensures
        #[trigger] frame_to_meta(page) % META_SLOT_SIZE == 0,
        FRAME_METADATA_RANGE.start <= frame_to_meta(page) && frame_to_meta(page)
            < FRAME_METADATA_RANGE.start + MAX_NR_PAGES * META_SLOT_SIZE,
{
}

pub broadcast proof fn lemma_meta_to_frame_alignment(meta: Vaddr)
    requires
        meta % META_SLOT_SIZE == 0,
        FRAME_METADATA_RANGE.start <= meta && meta < FRAME_METADATA_RANGE.start + MAX_NR_PAGES
            * META_SLOT_SIZE,
    ensures
        #[trigger] meta_to_frame(meta) % PAGE_SIZE == 0,
        meta_to_frame(meta) < MAX_PADDR,
{
}

pub broadcast group group_page_meta {
    lemma_meta_slot_size,
    lemma_FRAME_METADATA_RANGE_is_page_aligned,
    lemma_FRAME_METADATA_RANGE_is_large_enough,
    lemma_paddr_to_meta_biinjective,
    lemma_meta_to_paddr_biinjective,
    lemma_meta_to_frame_soundness,
    lemma_frame_to_meta_soundness,
    lemma_meta_to_frame_alignment,
}

} // verus!
