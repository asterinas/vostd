pub mod entry_owners;
pub mod metadata_permissions;
pub mod owners;

use vstd::prelude::*;
use vstd_extra::{cast_ptr::Repr, drop_tracking::*, ownership::Inv};

use crate::specs::mm::frame::{
    frame_specs::FrameRawPerms,
    mapping::frame_to_index,
    meta_owners::{MetaSlotStorage, StoredPageTablePageMeta},
    meta_region_owners::MetaRegionOwners,
};

use crate::mm::{
    Paddr,
    frame::Frame,
    frame::meta::{REF_COUNT_UNUSED, mapping::meta_to_frame},
    page_table::{PageTableConfig, PageTableGuard, PageTablePageMeta},
};
use core::marker::PhantomData;
pub use entry_owners::*;
pub use owners::*;

verus! {

/// Distributed counts owned by raw page-table entries, not structural owners
/// or the metadata-region authority. Live frames keep their counts in `Frame`.
pub type RawNodeMetadataPerms = Map<Paddr, FrameRawPerms>;
pub type NodeMetadataPartition<'a> = metadata_permissions::MetadataPermissionPartition<
    'a, Paddr, FrameRawPerms,
>;
pub type NodeMetadataLoans<'a> = metadata_permissions::MetadataPermissionLoans<
    'a, Paddr, FrameRawPerms,
>;
pub type NodeMetadataLoan<'a> = metadata_permissions::MetadataPermissionLoan<
    'a, Paddr, FrameRawPerms,
>;

/// Every stored count refers to an allocated raw page-table node. In
/// particular, an allocator's UNUSED slot cannot already occur in this map.
pub open spec fn raw_node_metadata_wf(
    permissions: RawNodeMetadataPerms,
    regions: MetaRegionOwners,
) -> bool {
    forall|paddr: Paddr| #[trigger] permissions.contains_key(paddr) ==> {
        let raw = permissions[paddr];
        let idx = frame_to_index(paddr);
        &&& raw.inv()
        &&& paddr == meta_to_frame(raw.slot_vaddr())
        &&& regions.contains(idx)
        &&& regions.ref_count(idx) != REF_COUNT_UNUSED
        &&& raw.slot_perm == regions.slots[idx]
        &&& raw.metadata_perm.id() == regions.slot_owners[idx].metadata_perm.id()
        &&& regions.slot_owners[idx].usage is PageTable
    }
}

pub tracked struct Guards {
    /// The set of node addresses that are currently guarded (locked).
    pub ghost guards: Set<usize>,
}

impl Guards {
    pub open spec fn unlocked(self, addr: usize) -> bool {
        !self.guards.contains(addr)
    }

    pub open spec fn lock_held(self, addr: usize) -> bool {
        self.guards.contains(addr)
    }
}

impl<'rcu, C: PageTableConfig> TrackDrop for PageTableGuard<'rcu, C> {
    type State = Guards;

    /// The node address whose lock this guard holds. The token
    /// thus identifies *which* guard it tracks; `drop_requires`'s key
    /// match prevents a guard's obligation from being used to drop a
    /// different guard. The real lock-set ledger is `Guards::guards`;
    /// this trait's discipline lifts the existing state-side discipline
    /// onto the obligation token by carrying the locked address.
    type Obligation = DropObligation<usize>;

    open spec fn tracked_redeem_requires(self, s: Self::State) -> bool {
        s.lock_held(self.inner.inner@.ptr.addr())
    }

    open spec fn tracked_redeem_ensures(
        self,
        s0: Self::State,
        s1: Self::State,
        obl: Self::Obligation,
    ) -> bool {
        &&& s1.guards == s0.guards.remove(self.inner.inner@.ptr.addr())
        &&& obl.value() == self.inner.inner@.ptr.addr()
    }

    proof fn tracked_redeem(self, tracked s: &mut Self::State) -> (tracked obl: Self::Obligation) {
        s.guards = s.guards.remove(self.inner.inner@.ptr.addr());
        DropObligation::tracked_mint(self.inner.inner@.ptr.addr())
    }

    open spec fn drop_requires(self, s: Self::State, obl: Self::Obligation) -> bool {
        &&& s.unlocked(self.inner.inner@.ptr.addr())
        &&& obl.value() == self.inner.inner@.ptr.addr()
    }

    open spec fn drop_ensures(
        self,
        s0: Self::State,
        s1: Self::State,
        obl: Self::Obligation,
    ) -> bool {
        s1.guards == s0.guards.insert(self.inner.inner@.ptr.addr())
    }
}

impl<C: PageTableConfig> PageTablePageMeta<C> {
    pub open spec fn into_spec(self) -> StoredPageTablePageMeta {
        StoredPageTablePageMeta {
            nr_children: self.nr_children,
            stray: self.stray,
            level: self.level,
            lock: self.lock,
        }
    }

    #[verifier::when_used_as_spec(into_spec)]
    pub fn into(self) -> StoredPageTablePageMeta
        returns
            self.into_spec(),
    {
        StoredPageTablePageMeta {
            nr_children: self.nr_children,
            stray: self.stray,
            level: self.level,
            lock: self.lock,
        }
    }
}

impl StoredPageTablePageMeta {
    pub open spec fn into_spec<C: PageTableConfig>(self) -> PageTablePageMeta<C> {
        PageTablePageMeta::<C> {
            nr_children: self.nr_children,
            stray: self.stray,
            level: self.level,
            lock: self.lock,
            _phantom: PhantomData,
        }
    }

    #[verifier::when_used_as_spec(into_spec)]
    pub fn into<C: PageTableConfig>(self) -> PageTablePageMeta<C>
        returns
            self.into_spec::<C>(),
    {
        PageTablePageMeta::<C> {
            nr_children: self.nr_children,
            stray: self.stray,
            level: self.level,
            lock: self.lock,
            _phantom: PhantomData,
        }
    }
}

pub uninterp spec fn drop_tree_spec<C: PageTableConfig>(
    _page: Frame<PageTablePageMeta<C>>,
) -> Frame<PageTablePageMeta<C>>;

impl<C: PageTableConfig> Repr<MetaSlotStorage> for PageTablePageMeta<C> {
    type ReprPerm = ();

    open spec fn wf(r: MetaSlotStorage, perm: ()) -> bool {
        matches!(r, MetaSlotStorage::PTNode(_))
    }

    open spec fn to_repr_spec(self, perm: ()) -> (MetaSlotStorage, ()) {
        (MetaSlotStorage::PTNode(self.into_spec()), ())
    }

    #[verifier::external_body]
    fn to_repr(self, Tracked(perm): Tracked<&mut ()>) -> MetaSlotStorage {
        unimplemented!()
    }

    open spec fn from_repr_spec(r: MetaSlotStorage, perm: ()) -> Self {
        match r {
            MetaSlotStorage::PTNode(node) => node.into_spec::<C>(),
            _ => arbitrary(),
        }
    }

    #[verifier::external_body]
    fn from_repr(r: MetaSlotStorage, Tracked(perm): Tracked<&()>) -> Self {
        unimplemented!()
    }

    #[verifier::external_body]
    fn from_borrowed<'a>(r: &'a MetaSlotStorage, Tracked(perm): Tracked<&'a ()>) -> &'a Self {
        unimplemented!()
    }

    #[verifier::external_body]
    fn from_borrowed_mut<'a>(
        r: &'a mut MetaSlotStorage,
        Tracked(perm): Tracked<&'a mut ()>,
    ) -> &'a mut Self {
        unimplemented!()
    }

    proof fn from_to_repr(self, perm: ()) {
    }

    proof fn to_from_repr(r: MetaSlotStorage, perm: ()) {
        match r {
            MetaSlotStorage::PTNode(node) => {},
            _ => {
                assert(false);
            },
        }
    }

    proof fn to_repr_wf(self, perm: ()) {
    }
}

} // verus!
