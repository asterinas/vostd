use vstd::prelude::*;

use vstd_extra::ownership::*;

use crate::arch::mm::PagingConsts;
use crate::mm::frame::*;
use crate::mm::page_prop::PageProperty;
use crate::mm::page_table::*;
use crate::mm::{Paddr, PagingConstsTrait, PagingLevel, Vaddr};
use crate::specs::arch::mm::{NR_ENTRIES, NR_LEVELS, PAGE_SIZE};
use crate::specs::mm::frame::meta_owners::MetaSlotOwner;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;

verus! {

impl<C: PageTableConfig> OwnerOf for Child<C> {
    type Owner = EntryOwner<C>;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        match self {
            Self::PageTable(node) => {
                &&& owner.is_node()
                &&& node.ptr.addr() == owner.node().meta_addr_self()
                &&& node.index() == frame_to_index(meta_to_frame(node.ptr.addr()))
            },
            Self::Frame(paddr, level, prop) => {
                &&& owner.is_frame()
                &&& owner.frame().mapped_pa == paddr
                &&& owner.frame().prop == prop
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
                &&& node.inner.0.ptr.addr() == owner.node().meta_addr_self()
            },
            Self::Frame(paddr, level, prop) => {
                &&& owner.is_frame()
                &&& owner.frame().mapped_pa == paddr
                &&& owner.frame().prop == prop
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

    pub open spec fn from_pte_spec(
        pte: C::E,
        level: PagingLevel,
        regions: MetaRegionOwners,
    ) -> Self {
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
        &&& owner.inv_base()
        &&& regions.inv()
        &&& self.wf(owner)
        &&& owner.metaregion_sound(regions)
        &&& owner.in_scope
    }
}

impl<C: PageTableConfig> ChildRef<'_, C> {
    pub open spec fn invariants(self, owner: EntryOwner<C>, regions: MetaRegionOwners) -> bool {
        &&& owner.inv()
        &&& regions.inv()
        &&& self.wf(owner)
        &&& owner.metaregion_sound(regions)
        &&& !owner.in_scope
    }
}

impl<C: PageTableConfig> EntryOwner<C> {
    pub open spec fn from_pte_regions_spec(self, regions: MetaRegionOwners) -> MetaRegionOwners {
        if self.is_node() {
            let index = frame_to_index(self.meta_slot_paddr().unwrap());
            MetaRegionOwners {
                frame_obligations: regions.frame_obligations.insert(index),
                ..regions
            }
        } else {
            regions
        }
    }

    pub open spec fn into_pte_regions_spec(self, regions: MetaRegionOwners) -> MetaRegionOwners {
        if self.is_node() {
            let index = frame_to_index(self.meta_slot_paddr().unwrap());
            // Canonical model: forgetting a live PT-node into a PTE CONSUMES
            // its pending-Drop obligation (the body's `MD::new` redeems one
            // entry at the node's slot), mirroring `Frame::into_raw`. `slots`
            // / `slot_owners` are untouched; the owner's `in_scope = false`
            // records the ownership transfer. Balances the `+1` minted by
            // `from_pte` (`from_pte_regions_spec`) / `PageTableNode::alloc`.
            MetaRegionOwners {
                frame_obligations: regions.frame_obligations.remove(index),
                ..regions
            }
        } else {
            // Forgetting a mapped frame / clearing an absent entry leaves the
            // per-frame ledger untouched (`item_into_raw` is `external_body`).
            regions
        }
    }

    pub open spec fn into_pte_owner_spec(self) -> EntryOwner<C> {
        EntryOwner { in_scope: false, ..self }
    }

    pub open spec fn from_pte_owner_spec(self) -> EntryOwner<C> {
        EntryOwner { in_scope: true, ..self }
    }

    /// This is equivalent to the other `invariants` relations, combining the `inv` predicates for each
    /// object and the well-formedness relations between them.
    pub open spec fn pte_invariants(self, pte: C::E, regions: MetaRegionOwners) -> bool {
        &&& self.inv()
        &&& regions.inv()
        &&& self.match_pte(pte, self.parent_level)
        &&& self.metaregion_sound(regions)
        &&& !self.in_scope
    }
}

} // verus!
