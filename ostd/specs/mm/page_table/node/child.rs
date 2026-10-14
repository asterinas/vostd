use vstd::prelude::*;
use vstd_extra::ownership::*;

use crate::specs::mm::frame::{
    frame_specs::FrameRawPerms,
    mapping::meta_to_index,
    meta_region_owners::MetaRegionOwners,
};

use crate::arch::mm::PagingConsts;
use crate::mm::{
    Paddr, PagingConstsTrait, PagingLevel, Vaddr, frame::*, page_prop::PageProperty, page_table::*,
};

verus! {

impl<C: PageTableConfig> OwnerOf for Child<C> {
    type Owner = EntryOwner<C>;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        match self {
            Self::PageTable(node) => {
                &&& owner.is_node()
                &&& node.ptr.addr() == owner.node().slot_vaddr()
                &&& node.index() == meta_to_index(node.ptr.addr())
                &&& node.ptr_inv()
                &&& node.inv()
                &&& owner.node().permission_matches(node.frac_metadata_perm())
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
                &&& node.inner@.ptr.addr() == owner.node().slot_vaddr()
                &&& node.inner@.ptr_inv()
                &&& node.inv()
                &&& owner.node().permission_matches(**node.tracked_metadata_perm)
                &&& node.inner@.external_meta_wf(owner.node().metadata, ())
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
    /// A temporary loan keeps a live executable handle's token in stable
    /// storage while its Frame is about to be consumed into a PTE. No second
    /// counted reference is created and no executable consumption is moved.
    pub open spec fn wf_with_metadata_loan(
        self,
        owner: EntryOwner<C>,
        loan: Option<NodeMetadataLoan<'_>>,
    ) -> bool {
        match loan {
            Some(permission) => self matches Self::PageTable(node) && {
                &&& owner.is_node()
                &&& node.ptr_inv()
                &&& node.ptr.addr() == owner.node().slot_vaddr()
                &&& node.tracked_metadata_perm@ is None
                &&& permission.value().inv()
                &&& permission.key() == node.start_paddr_spec()
                &&& permission.value().slot_perm == node.tracked_slot_perm@
                &&& owner.node().permission_matches(permission.value().metadata_perm)
            },
            None => self.wf(owner),
        }
    }

    pub open spec fn from_pte_spec(
        pte: C::E,
        level: PagingLevel,
        regions: MetaRegionOwners,
        raw_permission: Option<FrameRawPerms>,
    ) -> Self {
        if !pte.is_present() {
            Self::None
        } else if pte.is_last(level) {
            Self::Frame(pte.paddr(), level, pte.prop())
        } else {
            Self::PageTable(
                PageTableNode::from_raw_spec(
                    pte.paddr(),
                    regions.slots[crate::specs::mm::frame::mapping::frame_to_index(pte.paddr())],
                    Some(raw_permission->0.metadata_perm),
                ),
            )
        }
    }

    pub open spec fn invariants(self, owner: EntryOwner<C>, regions: MetaRegionOwners) -> bool {
        &&& owner.inv()
        &&& regions.inv()
        &&& self.wf(owner)
        &&& match self {
            Self::Frame(paddr, level, prop) => C::E::new_page_req(paddr, level, prop),
            _ => true,
        }
        &&& owner.metaregion_sound(regions)
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
    /// The raw entry's original count is present independently of the
    /// mutable metadata-region bookkeeping and recursive structural owner.
    pub open spec fn raw_node_token_in_store(
        self,
        permissions: Map<Paddr, FrameRawPerms>,
    ) -> bool {
        if self.is_node() {
            let paddr = self.meta_slot_paddr().unwrap();
            &&& permissions.contains_key(paddr)
            &&& permissions[paddr].inv()
            &&& permissions[paddr].slot_vaddr() == self.node().slot_vaddr()
            &&& self.node().permission_matches(permissions[paddr].metadata_perm)
        } else {
            true
        }
    }

    /// Relates this raw node entry to its independently stored counted token.
    pub open spec fn raw_node_permission_in_store(
        self,
        permissions: Map<Paddr, FrameRawPerms>,
        regions: MetaRegionOwners,
    ) -> bool {
        self.raw_node_token_in_store(permissions)
    }

    /// Only raw node entries carry a node-count permission. Mapped data-frame
    /// permissions remain in FrameEntryOwner and are not part of this store.
    pub open spec fn raw_node_permission_matches(
        self,
        permission: Option<FrameRawPerms>,
        regions: MetaRegionOwners,
    ) -> bool {
        if self.is_node() {
            permission matches Some(raw) && {
                &&& raw.inv()
                &&& raw.slot_vaddr() == self.node().slot_vaddr()
                // The PTE invariant separately relates the installed metadata
                // to the region's slot permission. Restoration uses that slot
                // permission and consumes this exact counted metadata token;
                // it does not require equality of the two shared slot witnesses.
                &&& self.node().permission_matches(raw.metadata_perm)
            }
        } else {
            permission is None
        }
    }

    pub open spec fn into_pte_owner_spec(self) -> EntryOwner<C> {
        self
    }

    pub open spec fn from_pte_owner_spec(self) -> EntryOwner<C> {
        self
    }

    /// This is equivalent to the other `invariants` relations, combining the `inv` predicates for each
    /// object and the well-formedness relations between them.
    pub open spec fn pte_invariants(self, pte: C::E, regions: MetaRegionOwners) -> bool {
        &&& self.inv()
        &&& regions.inv()
        &&& self.match_pte(pte, self.parent_level)
        &&& self.metaregion_sound(regions)
    }
}

} // verus!
