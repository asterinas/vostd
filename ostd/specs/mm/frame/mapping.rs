use core::{mem::size_of, ops::Range};

use vstd::prelude::*;

use crate::specs::arch::*;

use crate::mm::{
    Paddr, Vaddr,
    frame::meta::{
        META_SLOT_SIZE, MetaSlot,
        mapping::{frame_to_meta, meta_to_frame},
    },
    kspace::FRAME_METADATA_RANGE,
};

use super::*;

verus! {

pub open spec fn max_meta_slots() -> int {
    (FRAME_METADATA_RANGE.end - FRAME_METADATA_RANGE.start) / META_SLOT_SIZE as int
}

pub open spec fn index_to_meta(i: usize) -> (res: Vaddr)
    recommends
        0 <= i < max_meta_slots() as usize,
{
    (FRAME_METADATA_RANGE.start + i * META_SLOT_SIZE) as usize
}

#[verifier::inline]
pub open spec fn frame_to_index(paddr: Paddr) -> usize
    recommends
        paddr % PAGE_SIZE == 0,
{
    paddr / PAGE_SIZE
}

#[verifier::inline]
pub open spec fn index_to_frame(index: usize) -> Paddr
    recommends
        index < max_meta_slots(),
{
    (index * PAGE_SIZE) as usize
}

/// `frame_to_index` is injective on page-aligned paddrs.
pub broadcast proof fn lemma_frame_to_index_injective(p1: Paddr, p2: Paddr)
    requires
        p1 % PAGE_SIZE == 0,
        p2 % PAGE_SIZE == 0,
        p1 != p2,
    ensures
        #[trigger] frame_to_index(p1) != #[trigger] frame_to_index(p2),
{
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
    lemma_paddr_to_meta_biinjective,
    lemma_meta_to_paddr_biinjective,
    lemma_meta_to_frame_soundness,
    lemma_frame_to_meta_soundness,
    lemma_meta_to_frame_alignment,
}

} // verus!
