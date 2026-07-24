//! The model of a metadata slot. It includes:
//! - The model of the metadata slot: `MetaSlotModel`.
//! - The invariants for both MetaSlot and MetaSlotModel.
//! - The primitives for MetaSlot.
use vstd::prelude::*;

use vstd::{atomic::*, cell::pcell_maybe_uninit, simple_pptr::*};
use vstd_extra::{
    cast_ptr::{self, Repr},
    ghost_tree::TreePath,
    ownership::*,
};

use crate::specs::{arch::NR_ENTRIES, mm::frame::linked_list::linked_list_owners::StoredLink};

use crate::mm::{
    Paddr, PagingLevel, Vaddr,
    frame::{
        AnyFrameMeta,
        meta::{
            META_SLOT_SIZE, MetaSlot, REF_COUNT_MAX, REF_COUNT_UNIQUE, REF_COUNT_UNUSED,
            mapping::meta_to_frame,
        },
    },
    kspace::FRAME_METADATA_RANGE,
};

use super::*;

verus! {

#[allow(non_camel_case_types)]
pub ghost enum MetaSlotStatus {
    UNUSED,
    UNIQUE,
    SHARED,
    OVERFLOW,
    UNDER_CONSTRUCTION,
}

pub ghost enum PageUsage {
    // The zero variant is reserved for the unused type. Only an unused page
    // can be designated for one of the other purposes.
    Unused,
    /// The page is reserved or unusable. The kernel should not touch it.
    Reserved,
    /// The page is used as a frame, i.e., a page of untyped memory.
    Frame,
    /// The page is used by a page table.
    PageTable,
    /// The page stores metadata of other pages.
    Meta,
    /// The page stores the kernel such as kernel code, data, etc.
    Kernel,
    /// The page maps memory-mapped I/O (MMIO). Untracked: no refcount, slot
    /// stays in the free pool, but distinguishable from `Unused` so the
    /// kernel allocator never collides with an MMIO mapping.
    MMIO,
}

/// Whether `pa` falls in an MMIO physical-address range. Uninterpreted at the
/// spec level — concrete arch- and machine-specific MMIO range layouts are
/// outside the verification surface, but the kernel allocator (which picks
/// slots with `PageUsage::Unused`) is guaranteed disjoint from MMIO mappings.
pub uninterp spec fn is_mmio_paddr(pa: Paddr) -> bool;

/// Connects a slot's `PageUsage::MMIO` discriminant to its paddr's range
/// membership. Used to derive disjointness between MMIO mappings and the
/// regular allocator pool: a slot can be `MMIO` iff its paddr is in MMIO
/// range, so a slot with `usage != MMIO` (e.g. `Unused`) cannot share an idx
/// with any MMIO mapping.
pub broadcast axiom fn axiom_mmio_usage_iff_mmio_paddr(slot: MetaSlotOwner)
    ensures
        (#[trigger] slot.usage == PageUsage::MMIO) <==> is_mmio_paddr(
            meta_to_frame(slot.slot_vaddr),
        ),
;

/// MMIO ranges are aligned to (and closed under) huge-page granularities:
/// every sub-paddr within a huge frame inherits the huge frame's MMIO-ness.
/// This is a hardware-layout convention — MMIO BARs are mapped at huge-page
/// boundaries, and the verified `split_if_mapped_huge` relies on it to
/// transfer MMIO-ness from a huge frame to its 4KB sub-pages. Non-broadcast:
/// callers invoke this explicitly with the relevant `page_size`.
pub axiom fn axiom_mmio_paddr_huge_page_closed(pa: Paddr, page_size: usize, offset: usize)
    requires
        pa % page_size == 0,
        offset < page_size,
    ensures
        is_mmio_paddr((pa + offset) as Paddr) == is_mmio_paddr(pa),
;

pub struct StoredPageTablePageMeta {
    pub nr_children: pcell_maybe_uninit::PCell<u16>,
    pub stray: pcell_maybe_uninit::PCell<bool>,
    pub level: PagingLevel,
    pub lock: PAtomicU8,
}

pub enum MetaSlotStorage {
    Empty([u8; 39]),
    Untyped,
    FrameLink(StoredLink),
    PTNode(StoredPageTablePageMeta),
}

/// `MetaSlotStorage` is an inductive tagged union of all of the frame meta types that
/// we work with in this development. So, it should itself implement `AnyFrameMeta`, and
/// it can then be used to stand in for `dyn AnyFrameMeta`.
unsafe impl AnyFrameMeta for MetaSlotStorage {
    uninterp spec fn vtable_ptr(&self) -> usize;
}

impl Repr<MetaSlotStorage> for MetaSlotStorage {
    type ReprPerm = ();

    open spec fn wf(slot: MetaSlotStorage, perm: ()) -> bool {
        true
    }

    open spec fn to_repr_spec(self, perm: ()) -> (MetaSlotStorage, ()) {
        (self, ())
    }

    fn to_repr(self, Tracked(perm): Tracked<&mut ()>) -> MetaSlotStorage {
        self
    }

    open spec fn from_repr_spec(slot: MetaSlotStorage, perm: ()) -> Self {
        slot
    }

    fn from_repr(slot: MetaSlotStorage, Tracked(perm): Tracked<&()>) -> Self {
        slot
    }

    fn from_borrowed<'a>(slot: &'a MetaSlotStorage, Tracked(perm): Tracked<&'a ()>) -> &'a Self {
        slot
    }

    fn from_borrowed_mut<'a>(
        slot: &'a mut MetaSlotStorage,
        Tracked(perm): Tracked<&'a mut ()>,
    ) -> &'a mut Self {
        slot
    }

    proof fn from_to_repr(self, perm: ()) {
    }

    proof fn to_from_repr(slot: MetaSlotStorage, perm: ()) {
    }

    proof fn to_repr_wf(self, perm: ()) {
    }
}

impl MetaSlotStorage {
    pub open spec fn get_link_spec(self) -> Option<StoredLink> {
        match self {
            MetaSlotStorage::FrameLink(link) => Some(link),
            _ => None,
        }
    }

    #[verifier::when_used_as_spec(get_link_spec)]
    pub fn get_link(self) -> (res: Option<StoredLink>)
        ensures
            res == self.get_link_spec(),
    {
        match self {
            MetaSlotStorage::FrameLink(link) => Some(link),
            _ => None,
        }
    }

    pub open spec fn get_node_spec(self) -> Option<StoredPageTablePageMeta> {
        match self {
            MetaSlotStorage::PTNode(node) => Some(node),
            _ => None,
        }
    }

    #[verifier::when_used_as_spec(get_node_spec)]
    pub fn get_node(self) -> (res: Option<StoredPageTablePageMeta>)
        ensures
            res == self.get_node_spec(),
    {
        match self {
            MetaSlotStorage::PTNode(node) => Some(node),
            _ => None,
        }
    }
}

pub tracked struct MetadataInnerPerms {
    pub storage: pcell_maybe_uninit::PointsTo<MetaSlotStorage>,
    pub ref_count: PermissionU64,
    pub vtable_ptr: vstd::simple_pptr::PointsTo<usize>,
    pub in_list: PermissionU64,
}

/// Well-formedness of a concrete metadata representation. The permissions for
/// the outer slot and its storage remain owned by `MetaRegionOwners`; only the
/// representation-specific permission is supplied by the concrete metadata
/// owner.
pub open spec fn typed_meta_wf<M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    points_to: vstd::simple_pptr::PointsTo<MetaSlot>,
    storage: pcell_maybe_uninit::PointsTo<MetaSlotStorage>,
    repr_perm: M::ReprPerm,
) -> bool {
    &&& points_to.is_init()
    &&& storage.is_init()
    &&& storage.id() == points_to.value().storage.id()
    &&& M::wf(storage.value(), repr_perm)
}

pub open spec fn typed_meta_value<M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    storage: pcell_maybe_uninit::PointsTo<MetaSlotStorage>,
    repr_perm: M::ReprPerm,
) -> M
    recommends
        storage.is_init(),
        M::wf(storage.value(), repr_perm),
{
    M::from_repr_spec(storage.value(), repr_perm)
}

pub fn borrow_meta<'a, M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    ptr: cast_ptr::ReprPtr<MetaSlotStorage, M>,
    Tracked(points_to): Tracked<&'a vstd::simple_pptr::PointsTo<MetaSlot>>,
    Tracked(storage): Tracked<&'a pcell_maybe_uninit::PointsTo<MetaSlotStorage>>,
    Tracked(repr_perm): Tracked<&'a M::ReprPerm>,
) -> (res: &'a M)
    requires
        typed_meta_wf::<M>(*points_to, *storage, *repr_perm),
        ptr.addr() == points_to.addr(),
    ensures
        *res == typed_meta_value::<M>(*storage, *repr_perm),
{
    let slot = PPtr::<MetaSlot>::from_addr(ptr.addr()).borrow(Tracked(points_to));
    M::from_borrowed(slot.storage.borrow(Tracked(storage)), Tracked(repr_perm))
}

pub fn borrow_meta_mut<'a, M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    ptr: cast_ptr::ReprPtr<MetaSlotStorage, M>,
    Tracked(points_to): Tracked<&'a vstd::simple_pptr::PointsTo<MetaSlot>>,
    Tracked(slot_owner): Tracked<&'a mut MetaSlotOwner>,
    Tracked(repr_perm): Tracked<&'a mut M::ReprPerm>,
) -> (res: &'a mut M)
    requires
        old(slot_owner).inv(),
        points_to.value().wf(*old(slot_owner)),
        typed_meta_wf::<M>(*points_to, old(slot_owner).inner_perms.storage, *old(repr_perm)),
        ptr.addr() == points_to.addr(),
    ensures
        *res == typed_meta_value::<M>(old(slot_owner).inner_perms.storage, *old(repr_perm)),
        final(slot_owner).inv(),
        points_to.value().wf(*final(slot_owner)),
        final(slot_owner).slot_vaddr == old(slot_owner).slot_vaddr,
        final(slot_owner).usage == old(slot_owner).usage,
        final(slot_owner).paths_in_pt == old(slot_owner).paths_in_pt,
        final(slot_owner).inner_perms.ref_count == old(slot_owner).inner_perms.ref_count,
        final(slot_owner).inner_perms.vtable_ptr == old(slot_owner).inner_perms.vtable_ptr,
        final(slot_owner).inner_perms.in_list == old(slot_owner).inner_perms.in_list,
        typed_meta_wf::<M>(*points_to, final(slot_owner).inner_perms.storage, *final(repr_perm)),
        *final(res) == typed_meta_value::<M>(
            final(slot_owner).inner_perms.storage,
            *final(repr_perm),
        ),
{
    let slot = PPtr::<MetaSlot>::from_addr(ptr.addr()).borrow(Tracked(points_to));
    let tracked inner_perms = slot_owner.tracked_borrow_mut_inner_perms();
    M::from_borrowed_mut(
        slot.storage.borrow_mut(Tracked(&mut inner_perms.storage)),
        Tracked(repr_perm),
    )
}

pub tracked struct MetaSlotOwner {
    pub inner_perms: MetadataInnerPerms,
    pub ghost slot_vaddr: Vaddr,
    pub ghost usage: PageUsage,
    /// The set of tree paths at which this slot is referenced. For PT-node
    /// slots this is a singleton. For data-frame slots this tracks every
    /// location the frame is currently mapped — allowing a single frame to be
    /// mapped at multiple addresses.
    pub ghost paths_in_pt: Set<TreePath<NR_ENTRIES>>,
}

impl Inv for MetaSlotOwner {
    open spec fn inv(self) -> bool {
        // A managed slot at `REF_COUNT_UNUSED` is free — it has no live
        // PTE mapping, since a mapping is itself a reference that would
        // keep the count above the unused sentinel. Hence `paths_in_pt`
        // is empty. Maintained by the teardown path: the sole transition
        // *into* `UNUSED` is `drop_last_in_place`, whose
        // `drop_last_in_place_safety_cond` requires an empty
        // `paths_in_pt`. MMIO slots are excluded — they are not
        // ref-counted as ordinary frames (an MMIO region may sit at the
        // `UNUSED` sentinel while still mapped), exactly as the embedding
        // accounting and the huge-page split loop invariant scope out
        // `usage == MMIO`.
        &&& self.inner_perms.ref_count.value() == REF_COUNT_UNUSED ==> {
            &&& self.inner_perms.storage.is_uninit()
            &&& self.inner_perms.vtable_ptr.is_uninit()
            &&& self.inner_perms.in_list.value() == 0
            &&& (self.usage != PageUsage::MMIO ==> self.paths_in_pt.is_empty())
        }
        &&& self.inner_perms.ref_count.value() == REF_COUNT_UNIQUE ==> {
            &&& self.inner_perms.vtable_ptr.is_init()
            &&& self.inner_perms.storage.is_init()
            // A UNIQUE non-MMIO slot has no live PTE mapping (same rationale as
            // the UNUSED branch): a mapping would be a reference keeping the
            // count above the unique sentinel. Lets the list-store embedding
            // discharge `paths_in_pt.is_empty()` for linked-list frames.
            &&& (self.usage != PageUsage::MMIO ==> self.paths_in_pt.is_empty())
        }
        // A SHARED slot (`0 < rc <= REF_COUNT_MAX`) is genuinely in use:
        // metadata storage is written, `vtable_ptr` resolves the
        // dynamic type, and the slot is *not* on the allocator's free
        // list. `storage.is_init()` and `in_list.value() == 0` were
        // previously asserted only in the `UNIQUE` branch and via the
        // `rc == 1 ⟹ ...` guard on `Frame::drop_requires`; they are
        // universally true of any in-use slot, so they live here. Once
        // these are invariants, the embedding's `op_pre[FrameDrop]` can
        // drop its `rc == 1 ⟹ storage.is_init ∧ in_list == 0` residual
        // (it follows from `regions.inv() ⟹ slot_owners[idx].inv()`).
        &&& 0 < self.inner_perms.ref_count.value() <= REF_COUNT_MAX ==> {
            &&& self.inner_perms.vtable_ptr.is_init()
            &&& self.inner_perms.storage.is_init()
            &&& self.inner_perms.in_list.value() == 0
        }
        &&& REF_COUNT_MAX < self.inner_perms.ref_count.value() < REF_COUNT_UNIQUE ==> { false }
        &&& self.inner_perms.ref_count.value() == 0 ==> {
            &&& self.inner_perms.in_list.value() == 0
        }
        &&& FRAME_METADATA_RANGE.start <= self.slot_vaddr < FRAME_METADATA_RANGE.end
        &&& self.slot_vaddr % META_SLOT_SIZE == 0
    }
}

pub ghost struct MetaSlotModel {
    pub status: MetaSlotStatus,
    pub storage: MemContents<MetaSlotStorage>,
    pub ref_count: u64,
    pub vtable_ptr: MemContents<usize>,
    pub in_list: u64,
    pub slot_vaddr: Vaddr,
    pub usage: PageUsage,
}

impl Inv for MetaSlotModel {
    open spec fn inv(self) -> bool {
        match self.ref_count {
            REF_COUNT_UNUSED => {
                &&& self.vtable_ptr.is_uninit()
                &&& self.in_list == 0
            },
            REF_COUNT_UNIQUE => { &&& self.vtable_ptr.is_init() },
            0 => { &&& self.in_list == 0 },
            _ if self.ref_count <= REF_COUNT_MAX => { &&& self.vtable_ptr.is_init() },
            _ => { false },
        }
    }
}

impl View for MetaSlotOwner {
    type V = MetaSlotModel;

    open spec fn view(&self) -> Self::V {
        let storage = self.inner_perms.storage.mem_contents();
        let ref_count = self.inner_perms.ref_count.value();
        let vtable_ptr = self.inner_perms.vtable_ptr.mem_contents();
        let in_list = self.inner_perms.in_list.value();
        let slot_vaddr = self.slot_vaddr;
        let usage = self.usage;
        let status = match ref_count {
            REF_COUNT_UNUSED => MetaSlotStatus::UNUSED,
            REF_COUNT_UNIQUE => MetaSlotStatus::UNIQUE,
            0 => MetaSlotStatus::UNDER_CONSTRUCTION,
            _ if ref_count <= REF_COUNT_MAX => MetaSlotStatus::SHARED,
            _ => MetaSlotStatus::OVERFLOW,
        };
        MetaSlotModel { status, storage, ref_count, vtable_ptr, in_list, slot_vaddr, usage }
    }
}

impl InvView for MetaSlotOwner {
    proof fn view_preserves_inv(self) {
    }
}

impl OwnerOf for MetaSlot {
    type Owner = MetaSlotOwner;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& self.storage.id() == owner.inner_perms.storage.id()
        &&& self.ref_count.id() == owner.inner_perms.ref_count.id()
        &&& self.vtable_ptr == owner.inner_perms.vtable_ptr.pptr()
        &&& self.in_list.id() == owner.inner_perms.in_list.id()
    }
}

impl MetaSlotOwner {
    pub proof fn tracked_borrow_mut_inner_perms(tracked &mut self) -> (tracked res:
        &mut MetadataInnerPerms)
        ensures
            *res == old(self).inner_perms,
            *final(self) == (Self { inner_perms: *final(res), ..*old(self) }),
    {
        &mut self.inner_perms
    }
}

/// Writes `metadata` into the byte storage and establishes its direct
/// `Repr<MetaSlotStorage>` interpretation.
pub exec fn write_metadata_into_storage<M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    cell: &pcell_maybe_uninit::PCell<MetaSlotStorage>,
    Tracked(storage): Tracked<&mut pcell_maybe_uninit::PointsTo<MetaSlotStorage>>,
    Tracked(repr_perm): Tracked<&mut M::ReprPerm>,
    metadata: M,
)
    requires
        cell.id() == old(storage).id(),
    ensures
        final(storage).id() == old(storage).id(),
        final(storage).is_init(),
        M::wf(final(storage).value(), *final(repr_perm)),
        M::from_repr_spec(final(storage).value(), *final(repr_perm)) == metadata,
{
    proof {
        M::from_to_repr(metadata, *repr_perm);
        M::to_repr_wf(metadata, *repr_perm);
    }
    let repr = metadata.to_repr(Tracked(repr_perm));
    cell.write(Tracked(storage), repr);
}

} // verus!
