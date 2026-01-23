use vstd::prelude::*;

use vstd_extra::ownership::*;

use crate::mm::frame::*;
use crate::mm::page_prop::PageProperty;
use crate::mm::page_table::*;
use crate::mm::{Paddr, PagingConstsTrait, PagingLevel, Vaddr};
use crate::specs::arch::mm::{NR_ENTRIES, NR_LEVELS, PAGE_SIZE};
use crate::specs::arch::paging_consts::PagingConsts;
use crate::specs::mm::frame::meta_owners::MetaSlotOwner;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;

verus! {

impl<C: PageTableConfig> Child<C> {
    #[rustc_allow_incoherent_impl]
    pub open spec fn into_pte_pt_spec(self, slot_own: MetaSlotOwner) -> C::E {
        C::E::new_pt_spec(meta_to_frame(slot_own.self_addr))
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn into_pte_frame_spec(self, tuple: (Paddr, PagingLevel, PageProperty)) -> C::E {
        let (paddr, level, prop) = tuple;
        C::E::new_page_spec(paddr, level, prop)
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn into_pte_none_spec(self) -> C::E {
        C::E::new_absent_spec()
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn from_pte_frame_spec(pte: C::E, level: PagingLevel) -> Self {
        Self::Frame(pte.paddr(), level, pte.prop())
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn from_pte_pt_spec(paddr: Paddr, regions: MetaRegionOwners) -> Self {
        Self::PageTable(PageTableNode::from_raw_spec(paddr))
    }
}

} // verus!
