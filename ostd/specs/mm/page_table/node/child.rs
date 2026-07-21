use vstd::prelude::*;

use vstd_extra::ownership::*;

use crate::specs::mm::frame::{FramePermission, meta_region_owners::MetaRegionOwners};

use crate::arch::mm::PagingConsts;
use crate::mm::{
    Paddr, PagingConstsTrait, PagingLevel, Vaddr,
    frame::{meta::mapping::meta_to_frame, *},
    page_prop::PageProperty,
    page_table::*,
};

verus! {

impl<C: PageTableConfig> OwnerOf for Child<C> {
    type Owner = EntryOwner<C>;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        match self {
            Self::PageTable(node) => {
                &&& owner.is_node()
                &&& owner.node_permission() is None
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
                &&& owner.node_permission() is Some
                &&& node.frame().ptr.addr() == owner.node().meta_addr_self()
                &&& *node.permission() == owner.node_permission()->0
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

    pub open spec fn permission(self) -> Option<FramePermission> {
        match self {
            Self::PageTable(node) => node.tracked_perm@,
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
        &&& match self {
            Self::Frame(paddr, level, prop) => C::E::new_page_req(paddr, level, prop),
            _ => true,
        }
        &&& owner.metaregion_sound(regions)
        &&& self matches Self::PageTable(node) ==> node.wf_with_region(regions)
    }
}

impl<C: PageTableConfig> ChildRef<'_, C> {
    pub open spec fn invariants(self, owner: EntryOwner<C>, regions: MetaRegionOwners) -> bool {
        &&& owner.inv()
        &&& regions.inv()
        &&& self.wf(owner)
        &&& owner.metaregion_sound(regions)
    }
}

impl<C: PageTableConfig> EntryOwner<C> {
    pub open spec fn from_pte_regions_spec(self, regions: MetaRegionOwners) -> MetaRegionOwners {
        regions
    }

    pub open spec fn into_pte_regions_spec(self, regions: MetaRegionOwners) -> MetaRegionOwners {
        regions
    }

    pub open spec fn into_pte_owner_spec(
        self,
        permission: Option<FramePermission>,
    ) -> EntryOwner<C> {
        if self.is_node() {
            EntryOwner { kind: EntryOwnerKind::Node(self.node(), permission), ..self }
        } else {
            self
        }
    }

    pub open spec fn from_pte_owner_spec(self) -> EntryOwner<C> {
        if self.is_node() {
            EntryOwner { kind: EntryOwnerKind::Node(self.node(), None), ..self }
        } else {
            self
        }
    }

    /// This is equivalent to the other `invariants` relations, combining the `inv` predicates for each
    /// object and the well-formedness relations between them.
    pub open spec fn pte_invariants(self, pte: C::E, regions: MetaRegionOwners) -> bool {
        &&& self.inv()
        &&& regions.inv()
        &&& self.match_pte(pte, self.parent_level)
        &&& self.metaregion_sound(regions)
        &&& self.is_node() ==> {
            let idx = frame_to_index(self.meta_slot_paddr()->0);
            &&& self.node_permission() is Some
            &&& self.node_permission()->0.frac() == 1
            &&& self.node_permission()->0.id() == regions.slots[idx].id()
            &&& self.node_permission()->0.resource().pptr().addr()
                == self.node().meta_addr_self()
        }
    }
}

} // verus!
