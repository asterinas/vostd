use std::{
    any::TypeId,
    borrow::{Borrow, BorrowMut},
    cell::Cell,
    char::MAX,
    marker::PhantomData,
    ops::Range,
};

use vstd::simple_pptr::*;
use vstd::{invariant, layout::is_power_2, pervasive::VecAdditionalExecFns, prelude::*};
use vstd::bits::*;
use vstd::tokens::SetToken;

use crate::{
    helpers::align_ext::align_down,
    mm::{
        child::Child, entry::Entry, frame::{self, allocator::AllocatorModel}, meta::AnyFrameMeta, node::PageTableNode,
        nr_subpage_per_huge, page_prop::PageProperty, page_size, vm_space::Token, Frame,
        MapTrackingStatus, Paddr, PageTableLockTrait, Vaddr, MAX_USERSPACE_VADDR, NR_ENTRIES,
        PAGE_SIZE,
    },
    task::DisabledPreemptGuard,
    x86_64::VMALLOC_VADDR_RANGE,
};

use super::{
    pte_index, PageTable, PageTableEntryTrait, PageTableError, PagingConsts, PagingConstsTrait,
    PagingLevel,
};

use crate::spec::sub_page_table;
use crate::exec;

verus! {

pub open spec fn level_is_greate_than_one(level: PagingLevel) -> bool {
    &&& level > 1
    &&& level <= PagingConsts::NR_LEVELS_SPEC()
}

pub open spec fn path_index_at_level(level: PagingLevel) -> int {
    level - 1
}

pub open spec fn level_at_path_index(index: int) -> PagingLevel {
    (index + 1) as PagingLevel
}

pub open spec fn spt_contains_no_unallocated_frames(
    spt: &exec::SubPageTable,
    alloc_model: &AllocatorModel,
) -> bool {
    &&& forall|i: usize| #[trigger] spt.frames@.value().contains_key(
            exec::frame_index_to_addr(i) as int,
        ) ==> alloc_model.allocated_addrs.contains(
            exec::frame_index_to_addr(i) as int,
        )
    &&& forall|i: usize| #[trigger] spt.ptes@.value().contains_key(
            i as int,
        ) ==> alloc_model.allocated_addrs.contains(
            spt.ptes@[i].frame_pa as int,
        )
}

pub open spec fn frame_keys_do_not_change(
    spt: &exec::SubPageTable,
    old_mpt: &exec::SubPageTable,
) -> bool {
    &&& forall|i|
        old_mpt.frames@.value().contains_key(i) ==> #[trigger] spt.frames@.value().contains_key(i)
    &&& forall|i|
        spt.frames@.value().contains_key(i) ==> #[trigger] old_mpt.frames@.value().contains_key(i)
    &&& forall|i|
        !old_mpt.frames@.value().contains_key(i) ==> !#[trigger] spt.frames@.value().contains_key(i)
    &&& forall|i|
        !old_mpt.frames@.value().contains_key(i) ==> !#[trigger] spt.frames@.value().contains_key(i)
}

pub open spec fn pte_keys_do_not_change(
    spt: &exec::SubPageTable,
    old_mpt: &exec::SubPageTable,
) -> bool {
    &&& forall|i|
        old_mpt.ptes@.value().contains_key(i) ==> #[trigger] spt.ptes@.value().contains_key(i)
    &&& forall|i|
        spt.ptes@.value().contains_key(i) ==> #[trigger] old_mpt.ptes@.value().contains_key(i)
    &&& forall|i|
        !old_mpt.ptes@.value().contains_key(i) ==> !#[trigger] spt.ptes@.value().contains_key(i)
    &&& forall|i|
        !old_mpt.ptes@.value().contains_key(i) ==> !#[trigger] spt.ptes@.value().contains_key(i)
}

} // verus!
