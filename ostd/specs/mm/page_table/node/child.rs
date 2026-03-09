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

impl<C: PageTableConfig> OwnerOf for Child<C> {
    type Owner = EntryOwner<C>;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        match self {
            Self::PageTable(node) => {
                &&& owner.is_node()
                &&& node.ptr.addr() == owner.node.unwrap().meta_perm.addr()
                &&& node.index() == frame_to_index(meta_to_frame(node.ptr.addr()))
            },
            Self::Frame(paddr, level, prop) => {
                &&& owner.is_frame()
                &&& owner.frame.unwrap().mapped_pa == paddr
                &&& owner.frame.unwrap().prop == prop
                &&& level == owner.parent_level
            },
            Self::None => owner.is_absent(),
        }
    }
}


impl<'a, C: PageTableConfig> OwnerOf for ChildRef<'a, C> {
    type Owner = EntryOwner<C>;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        match self {
            Self::PageTable(node) => {
                &&& owner.is_node()
                &&& node.inner.0.ptr.addr() == owner.node.unwrap().meta_perm.addr()
            },
            Self::Frame(paddr, level, prop) => {
                &&& owner.is_frame()
                &&& owner.frame.unwrap().mapped_pa == paddr
                &&& owner.frame.unwrap().prop == prop
            },
            Self::None => owner.is_absent(),
        }
    }
}    

impl<C: PageTableConfig> Child<C> {

    pub open spec fn get_node(self) -> Option<PageTableNode<C>> {
        match self {
            Self::PageTable(node) => Some(node),
            _ => None,
        }
    }

    pub open spec fn get_frame_tuple(self) -> Option<(Paddr, PagingLevel, PageProperty)> {
        match self {
            Self::Frame(paddr, level, prop) => Some((paddr, level, prop)),
            _ => None,
        }
    }

    pub open spec fn into_pte_frame_spec(self, tuple: (Paddr, PagingLevel, PageProperty)) -> C::E {
        let (paddr, level, prop) = tuple;
        C::E::new_page_spec(paddr, level, prop)
    }


    pub open spec fn into_pte_none_spec(self) -> C::E {
        C::E::new_absent_spec()
    }


    pub open spec fn from_pte_spec(pte: C::E, level: PagingLevel, regions: MetaRegionOwners) -> Self {
        if !pte.is_present() {
            Self::None
        } else if pte.is_last(level) {
            Self::Frame(pte.paddr(), level, pte.prop())
        } else {
            Self::PageTable(PageTableNode::from_raw_spec(pte.paddr()))
        }
    }

    pub open spec fn from_pte_frame_spec(pte: C::E, level: PagingLevel) -> Self {
        Self::Frame(pte.paddr(), level, pte.prop())
    }


    pub open spec fn from_pte_pt_spec(paddr: Paddr, regions: MetaRegionOwners) -> Self {
        Self::PageTable(PageTableNode::from_raw_spec(paddr))
    }

    pub open spec fn invariants(self, owner: EntryOwner<C>, regions: MetaRegionOwners) -> bool {
        &&& owner.inv()
        &&& regions.inv()
        &&& self.wf(owner)
        &&& owner.relate_region(regions)
        &&& owner.in_scope
    }
}

impl<C: PageTableConfig> ChildRef<'_, C> {
    pub open spec fn invariants(self, owner: EntryOwner<C>, regions: MetaRegionOwners) -> bool {
        &&& owner.inv()
        &&& regions.inv()
        &&& self.wf(owner)
        &&& owner.relate_region(regions)
        &&& !owner.in_scope
    }
}

impl<C: PageTableConfig> EntryOwner<C> {

    pub open spec fn from_pte_regions_spec(self, regions: MetaRegionOwners) -> MetaRegionOwners {
        if self.is_node() {
            let index = frame_to_index(self.meta_slot_paddr().unwrap());
            let old_slot = regions.slot_owners[index];
            let new_slot = MetaSlotOwner {
                raw_count: 0usize,
                ..old_slot
            };
            MetaRegionOwners {
                slots: regions.slots.insert(index, self.node.unwrap().meta_perm.points_to),
                slot_owners: regions.slot_owners.insert(index, new_slot),
            }
        } else {
            regions
        }
    }

    pub open spec fn into_pte_regions_spec(self, regions: MetaRegionOwners) -> MetaRegionOwners {
        if self.is_node() {
            let index = frame_to_index(self.meta_slot_paddr().unwrap());
            let old_slot = regions.slot_owners[index];
            let new_slot = MetaSlotOwner {
                raw_count: (old_slot.raw_count + 1) as usize,
                ..old_slot
            };
            MetaRegionOwners {
                slots: regions.slots,
                slot_owners: regions.slot_owners.insert(index, new_slot),
                ..regions
            }
        } else {
            regions
        }
    }

    pub open spec fn into_pte_owner_spec(self) -> EntryOwner<C> {
        EntryOwner {
            in_scope: false,
            ..self
        }
    }

    pub open spec fn from_pte_owner_spec(self) -> EntryOwner<C> {
        EntryOwner {
            in_scope: true,
            ..self
        }
    }

    /// This is equivalent to the other `invariants` relations, combining the `inv` predicates for each
    /// object and the well-formedness relations between them.
    pub open spec fn pte_invariants(self, pte: C::E, regions: MetaRegionOwners) -> bool {
        &&& self.inv()
        &&& regions.inv()
        &&& self.match_pte(pte, self.parent_level)
        &&& self.relate_region(regions)
        &&& !self.in_scope
    }

}

} // verus!
