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

pub open spec fn spt_do_not_change_except<C: PageTableConfig>(
    spt: &SubPageTable<C>,
    old_spt: &SubPageTable<C>,
    pte_addr: int,
) -> bool {
    &&& spt.wf()
    &&& old_spt.wf()
    &&& spt.instance.id() == old_spt.instance.id()
    &&& spt.instance.root() == old_spt.instance.root()
    &&& forward_spt_do_not_change_except(spt, old_spt, pte_addr)
    &&& forward_spt_do_not_change_except(old_spt, spt, pte_addr)
}

pub open spec fn spt_do_not_change_except_frames_change<C: PageTableConfig>(
    spt: &SubPageTable<C>,
    old_spt: &SubPageTable<C>,
    pte_addr: int,
) -> bool {
    &&& spt.wf()
    &&& old_spt.wf()
    &&& spt.instance.id() == old_spt.instance.id()
    &&& spt.instance.root() == old_spt.instance.root()
    &&& forward_spt_do_not_change_except(spt, old_spt, pte_addr)
}

pub open spec fn forward_spt_do_not_change_except<C: PageTableConfig>(
    spt: &SubPageTable<C>,
    old_spt: &SubPageTable<C>,
    pte_addr: int,
) -> bool {
    &&& forall|i: int| #[trigger]
        spt.frames.value().contains_key(i) ==> {
            !(exists|l: int| #[trigger]
                spt.frames.value()[i].ancestor_chain.contains_key(l)
                    && #[trigger] spt.frames.value()[i].ancestor_chain[l].entry_pa() != pte_addr)
                ==> {
                &&& #[trigger] old_spt.frames.value().contains_key(i)
                &&& spt.frames.value()[i] == old_spt.frames.value()[i]
                &&& #[trigger] spt.alloc_model.meta_map.contains_key(i)
                &&& #[trigger] old_spt.alloc_model.meta_map.contains_key(i)
                &&& spt.alloc_model.meta_map[i] == old_spt.alloc_model.meta_map[i]
            }
        }
    &&& forall|i: int| #[trigger]
        spt.ptes.value().contains_key(i) ==> {
            i != pte_addr ==> {
                &&& #[trigger] old_spt.ptes.value().contains_key(i)
                &&& spt.ptes.value()[i] == old_spt.ptes.value()[i]
            }
        }
    &&& forall|i: int| #[trigger]
        spt.i_ptes.value().contains_key(i) ==> {
            i != pte_addr ==> {
                &&& #[trigger] old_spt.i_ptes.value().contains_key(i)
                &&& spt.i_ptes.value()[i] == old_spt.i_ptes.value()[i]
            }
        }
}

} // verus!
