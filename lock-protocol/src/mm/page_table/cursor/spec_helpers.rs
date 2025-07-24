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
        child::Child,
        entry::Entry,
        frame::{self, allocator::AllocatorModel},
        meta::AnyFrameMeta,
        node::PageTableNode,
        nr_subpage_per_huge,
        page_prop::PageProperty,
        page_size,
        vm_space::Token,
        Frame, Paddr, PageTableConfig, Vaddr, MAX_USERSPACE_VADDR, NR_ENTRIES, PAGE_SIZE,
    },
    task::DisabledPreemptGuard,
    x86_64::VMALLOC_VADDR_RANGE,
};

use super::{
    pte_index, PageTable, PageTableEntryTrait, PageTableError, PagingConsts, PagingConstsTrait,
    PagingLevel,
};

use crate::spec::sub_pt::SubPageTable;
use crate::exec;

verus! {

pub open spec fn spt_do_not_change_above_level<C: PageTableConfig>(
    spt: &SubPageTable<C>,
    old_spt: &SubPageTable<C>,
    level: PagingLevel,
) -> bool {
    &&& spt.wf()
    &&& old_spt.wf()
    &&& spt.instance.id() == old_spt.instance.id()
    &&& spt.instance.root() == old_spt.instance.root()
    &&& spt_do_not_remove_above_level(spt, old_spt, level)
    &&& spt_do_not_remove_above_level(old_spt, spt, level)
}

pub open spec fn spt_do_not_remove_above_level<C: PageTableConfig>(
    spt: &SubPageTable<C>,
    old_spt: &SubPageTable<C>,
    level: PagingLevel,
) -> bool {
    &&& forall|i: int| #[trigger]
        spt.frames.value().contains_key(i) ==> {
            spt.frames.value()[i].level >= level ==> {
                &&& #[trigger] old_spt.frames.value().contains_key(i)
                &&& spt.frames.value()[i] == old_spt.frames.value()[i]
            }
        }
    &&& forall|i: int| #[trigger]
        spt.ptes.value().contains_key(i) ==> {
            spt.ptes.value()[i].level > level ==> {
                &&& #[trigger] old_spt.ptes.value().contains_key(i)
                &&& spt.ptes.value()[i] == old_spt.ptes.value()[i]
            }
        }
    &&& forall|i: int| #[trigger]
        spt.i_ptes.value().contains_key(i) ==> {
            spt.i_ptes.value()[i].level > level ==> {
                &&& #[trigger] old_spt.i_ptes.value().contains_key(i)
                &&& spt.i_ptes.value()[i] == old_spt.i_ptes.value()[i]
            }
        }
}

} // verus!
