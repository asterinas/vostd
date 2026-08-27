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

/// Permissions whose initialized contents belong to one installed metadata
/// value.
pub tracked struct MetadataPerms {
    pub storage_perm: pcell_maybe_uninit::PointsTo<MetaSlotStorage>,
    pub vtable_ptr_perm: vstd::simple_pptr::PointsTo<usize>,
}

/// Well-formedness of a concrete metadata representation. The outer slot
/// permission remains permanently in `MetaRegionOwners`; the metadata bundle
/// describes the permissions tied to the currently installed metadata.
pub open spec fn typed_meta_wf<M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    points_to: vstd::simple_pptr::PointsTo<MetaSlot>,
    metadata_perms: MetadataPerms,
    repr_perm: M::ReprPerm,
) -> bool {
    &&& points_to.is_init()
    &&& metadata_perms.storage_perm.is_init()
    &&& metadata_perms.storage_perm.id() == points_to.value().storage.id()
    &&& M::wf(metadata_perms.storage_perm.value(), repr_perm)
}

pub open spec fn typed_meta_value<M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    metadata_perms: MetadataPerms,
    repr_perm: M::ReprPerm,
) -> M {
    M::from_repr_spec(metadata_perms.storage_perm.value(), repr_perm)
}

pub fn borrow_meta<'a, M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    ptr: cast_ptr::ReprPtr<MetaSlotStorage, M>,
    Tracked(points_to): Tracked<&'a vstd::simple_pptr::PointsTo<MetaSlot>>,
    Tracked(metadata_perms): Tracked<&'a MetadataPerms>,
    Tracked(repr_perm): Tracked<&'a M::ReprPerm>,
) -> (res: &'a M)
    requires
        typed_meta_wf::<M>(*points_to, *metadata_perms, *repr_perm),
        ptr.addr() == points_to.addr(),
    ensures
        *res == typed_meta_value::<M>(*metadata_perms, *repr_perm),
{
    let slot = PPtr::<MetaSlot>::from_addr(ptr.addr()).borrow(Tracked(points_to));
    M::from_borrowed(slot.storage.borrow(Tracked(&metadata_perms.storage_perm)), Tracked(repr_perm))
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
        typed_meta_wf::<M>(*points_to, old(slot_owner).metadata_perm, *old(repr_perm)),
        ptr.addr() == points_to.addr(),
    ensures
        *res == typed_meta_value::<M>(old(slot_owner).metadata_perm, *old(repr_perm)),
        final(slot_owner).inv(),
        points_to.value().wf(*final(slot_owner)),
        final(slot_owner).slot_vaddr == old(slot_owner).slot_vaddr,
        final(slot_owner).usage == old(slot_owner).usage,
        final(slot_owner).paths_in_pt == old(slot_owner).paths_in_pt,
        final(slot_owner).ref_count_perm == old(slot_owner).ref_count_perm,
        final(slot_owner).vtable_ptr_perm() == old(slot_owner).vtable_ptr_perm(),
        final(slot_owner).in_list_perm == old(slot_owner).in_list_perm,
        typed_meta_wf::<M>(*points_to, final(slot_owner).metadata_perm, *final(repr_perm)),
        *final(res) == typed_meta_value::<M>(final(slot_owner).metadata_perm, *final(repr_perm)),
{
    let slot = PPtr::<MetaSlot>::from_addr(ptr.addr()).borrow(Tracked(points_to));
    let tracked metadata_perms = slot_owner.tracked_borrow_mut_metadata_perms();
    M::from_borrowed_mut(
        slot.storage.borrow_mut(Tracked(&mut metadata_perms.storage_perm)),
        Tracked(repr_perm),
    )
}

/// Permissions that remain under the authority of `MetaRegionOwners`.
///
/// `ref_count` and `in_list` exist for the complete lifetime of the
/// corresponding `MetaSlot` (i.e., `'static`).
pub tracked struct MetaSlotOwner {
    pub metadata_perm: MetadataPerms,
    pub ref_count_perm: PermissionU64,
    pub in_list_perm: PermissionU64,
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
        &&& self.ref_count() == REF_COUNT_UNUSED ==> {
            &&& self.storage_perm().is_uninit()
            &&& self.vtable_ptr_perm().is_uninit()
            &&& self.in_list_perm.value() == 0
            &&& (self.usage != PageUsage::MMIO ==> self.paths_in_pt.is_empty())
        }
        &&& self.ref_count() == REF_COUNT_UNIQUE ==> {
            &&& self.vtable_ptr_perm().is_init()
            &&& self.storage_perm().is_init()
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
        &&& 0 < self.ref_count() <= REF_COUNT_MAX ==> {
            &&& self.vtable_ptr_perm().is_init()
            &&& self.storage_perm().is_init()
            &&& self.in_list_perm.value() == 0
        }
        &&& REF_COUNT_MAX < self.ref_count() < REF_COUNT_UNIQUE ==> { false }
        &&& self.ref_count() == 0 ==> {
            &&& self.in_list_perm.value() == 0
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
        let storage = self.storage_perm().mem_contents();
        let ref_count = self.ref_count();
        let vtable_ptr = self.vtable_ptr_perm().mem_contents();
        let in_list = self.in_list_perm.value();
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
        &&& self.storage.id() == owner.storage_perm().id()
        &&& self.ref_count.id() == owner.ref_count_perm.id()
        &&& self.vtable_ptr == owner.vtable_ptr_perm().pptr()
        &&& self.in_list.id() == owner.in_list_perm.id()
    }
}

impl MetaSlotOwner {
    pub open spec fn same_permissions(self, other: Self) -> bool {
        &&& self.metadata_perm == other.metadata_perm
        &&& self.ref_count_perm == other.ref_count_perm
        &&& self.in_list_perm == other.in_list_perm
    }

    pub open spec fn ref_count(self) -> u64 {
        self.ref_count_perm.value()
    }

    pub open spec fn storage_perm(self) -> pcell_maybe_uninit::PointsTo<MetaSlotStorage> {
        self.metadata_perm.storage_perm
    }

    pub open spec fn vtable_ptr_perm(self) -> vstd::simple_pptr::PointsTo<usize> {
        self.metadata_perm.vtable_ptr_perm
    }

    pub proof fn tracked_borrow_mut_metadata_perms(tracked &mut self) -> (tracked res:
        &mut MetadataPerms)
        ensures
            *res == old(self).metadata_perm,
            *final(self) == (Self { metadata_perm: *final(res), ..*old(self) }),
    {
        &mut self.metadata_perm
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
