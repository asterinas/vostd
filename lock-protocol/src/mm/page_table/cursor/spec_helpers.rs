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
        page_table::{child::Child, entry::Entry, node::PageTableNode, PageTableConfig},
        frame::{self, allocator::AllocatorModel},
        meta::AnyFrameMeta,
        nr_subpage_per_huge,
        page_prop::PageProperty,
        page_size,
        vm_space::Token,
        Frame, Paddr, Vaddr, MAX_USERSPACE_VADDR, NR_ENTRIES, PAGE_SIZE,
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

pub open spec fn spt_do_not_change_except_modify_pte<C: PageTableConfig>(
    spt: &SubPageTable<C>,
    old_spt: &SubPageTable<C>,
    pte_addr: int,
) -> bool {
    &&& spt.wf()
    &&& old_spt.wf()
    &&& spt.instance.id() == old_spt.instance.id()
    &&& spt.instance.root()
        == old_spt.instance.root()  // &&& forward_spt_do_not_change_except(spt, old_spt, pte_addr)
    // not correct?
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
            (forall|l: int| #[trigger]
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

pub open spec fn spt_do_not_change_above_level<C: PageTableConfig>(
    spt: &SubPageTable<C>,
    old_spt: &SubPageTable<C>,
    level: PagingLevel,
) -> bool {
    &&& forall|i: int|
        {
            (old_spt.frames.value().contains_key(i) && old_spt.frames.value()[i].level as int
                >= level) ==> {
                &&& #[trigger] spt.frames.value().contains_key(i)
                &&& #[trigger] spt.frames.value()[i] == old_spt.frames.value()[i]
            }
        }
    &&& forall|i: int|
        {
            (old_spt.alloc_model.meta_map.contains_key(i)
                && old_spt.alloc_model.meta_map[i].value().level as int >= level) ==> {
                &&& #[trigger] spt.alloc_model.meta_map.contains_key(i)
                &&& spt.alloc_model.meta_map[i].pptr() == old_spt.alloc_model.meta_map[i].pptr()
                &&& spt.alloc_model.meta_map[i].value() == old_spt.alloc_model.meta_map[i].value()
            }
        }
}

pub open spec fn alloc_model_do_not_change_except_add_frame<C: PageTableConfig>(
    spt: &SubPageTable<C>,
    old_spt: &SubPageTable<C>,
    new_frame: Paddr,
) -> bool {
    &&& {
        forall|i: int| #[trigger]
            spt.alloc_model.meta_map.contains_key(i) && i != new_frame as int ==> {
                &&& #[trigger] old_spt.alloc_model.meta_map.contains_key(i)
                &&& spt.alloc_model.meta_map[i].pptr() == old_spt.alloc_model.meta_map[i].pptr()
                &&& spt.alloc_model.meta_map[i].value() == old_spt.alloc_model.meta_map[i].value()
            }
    }
    &&& {
        forall|i: int| #[trigger]
            old_spt.alloc_model.meta_map.contains_key(i) ==> {
                &&& #[trigger] spt.alloc_model.meta_map.contains_key(i)
                &&& spt.alloc_model.meta_map[i].pptr() == old_spt.alloc_model.meta_map[i].pptr()
                &&& spt.alloc_model.meta_map[i].value() == old_spt.alloc_model.meta_map[i].value()
            }
    }
}

} // verus!
