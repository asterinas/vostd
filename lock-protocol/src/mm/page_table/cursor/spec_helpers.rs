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
        child::Child, entry::Entry, frame, meta::AnyFrameMeta, node::PageTableNode,
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

use crate::spec::simple_page_table;
use crate::exec;

verus! {

pub open spec fn level_is_greate_than_one(level: PagingLevel) -> bool {
    &&& level > 1
    &&& level <= PagingConsts::NR_LEVELS_SPEC()
}

pub open spec fn instance_match(spt: &exec::SubPageTable, tokens: exec::Tokens) -> bool {
    &&& forall|i|
        tokens.unused_addrs.contains_key(i) ==> #[trigger] tokens.unused_addrs[i].instance_id()
            == spt.instance@.id()
    &&& forall|i|
        tokens.unused_pte_addrs.contains_key(i)
            ==> #[trigger] tokens.unused_pte_addrs[i].instance_id() == spt.instance@.id()
}

pub open spec fn instance_match_addrs(
    spt: &exec::SubPageTable,
    unused_addrs: Map<int, simple_page_table::SimplePageTable::unused_addrs>,
    unused_pte_addrs: Map<int, simple_page_table::SimplePageTable::unused_pte_addrs>,
) -> bool {
    &&& forall|i|
        unused_addrs.contains_key(i) ==> #[trigger] unused_addrs[i].instance_id()
            == spt.instance@.id()
    &&& forall|i|
        unused_pte_addrs.contains_key(i) ==> #[trigger] unused_pte_addrs[i].instance_id()
            == spt.instance@.id()
}

pub open spec fn path_index_at_level(level: PagingLevel) -> int {
    // level - 1
    level - 1
}

pub open spec fn mpt_and_tokens_wf(spt: &exec::SubPageTable, tokens: exec::Tokens) -> bool {
    &&& instance_match(spt, tokens)
    &&& forall|i: usize|
        0 <= i < exec::MAX_FRAME_NUM && spt.mem@[i].1@.is_uninit()
            ==> #[trigger] tokens.unused_addrs.contains_key(exec::frame_index_to_addr(i) as int)
            && forall|j: usize|
            0 <= j < NR_ENTRIES ==> #[trigger] tokens.unused_pte_addrs.contains_key(
                exec::frame_addr_to_index(i) + j * exec::SIZEOF_PAGETABLEENTRY as int,
            )
    &&& forall|i: usize|
        0 <= i < exec::MAX_FRAME_NUM && #[trigger] spt.mem@[i].1@.is_init() ==> forall|j: usize|
            0 <= j < NR_ENTRIES ==> #[trigger] spt.mem@[i].1@.value().ptes[j as int].frame_pa == 0
                ==> #[trigger] tokens.unused_pte_addrs.contains_key(
                spt.mem@[i].1@.value().ptes[j as int].frame_pa as int,
            )
}

pub open spec fn mpt_not_contains_not_allocated_frames(
    spt: &exec::SubPageTable,
    cur_alloc_index: usize,
) -> bool {
    &&& forall|i: usize|
        cur_alloc_index <= i < exec::MAX_FRAME_NUM ==> !spt.frames@.value().contains_key(
            #[trigger] exec::frame_index_to_addr(i) as int,
        ) && forall|j: usize|
            0 <= j < NR_ENTRIES ==> !#[trigger] spt.ptes@.value().contains_key(
                exec::frame_addr_to_index(i) + j * exec::SIZEOF_PAGETABLEENTRY as int,
            )
    &&& forall|i: usize|
        cur_alloc_index <= i < exec::MAX_FRAME_NUM ==> forall|j: int| #[trigger]
            spt.ptes@.value().contains_key(j) ==> spt.ptes@.value()[j].frame_pa
                != #[trigger] exec::frame_index_to_addr(i) as int
}

pub open spec fn unallocated_frames_are_unused(
    unused_addrs: Map<int, simple_page_table::SimplePageTable::unused_addrs>,
    unused_pte_addrs: Map<int, simple_page_table::SimplePageTable::unused_pte_addrs>,
    cur_alloc_index: usize,
) -> bool {
    &&& forall|i: usize|
        cur_alloc_index <= i < exec::MAX_FRAME_NUM ==> #[trigger] unused_addrs.contains_key(
            exec::frame_index_to_addr(i) as int,
        )
    &&& forall|i: usize|
        cur_alloc_index <= i < exec::MAX_FRAME_NUM ==> forall|j: int|
            0 <= j < NR_ENTRIES ==> #[trigger] unused_pte_addrs.contains_key(
                #[trigger] exec::frame_addr_to_index(i) + j * exec::SIZEOF_PAGETABLEENTRY as int,
            )
}

pub open spec fn tokens_wf(
    unused_addrs: Map<int, simple_page_table::SimplePageTable::unused_addrs>,
    unused_pte_addrs: Map<int, simple_page_table::SimplePageTable::unused_pte_addrs>,
) -> bool {
    &&& forall|key|
        { unused_addrs.dom().contains(key) ==> #[trigger] unused_addrs[key].element() == key }
    &&& forall|key|
        { unused_pte_addrs.dom().contains(key) ==> #[trigger] unused_pte_addrs[key].element() == key
        }
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
