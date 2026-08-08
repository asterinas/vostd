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
    resource::ghost_resource::count_auth::{Count, CountResource},
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
/// value. Shared frames receive fractional access to this bundle, while a
/// unique frame owns the bundle exclusively.
pub tracked struct MetadataPerms {
    pub storage_perm: pcell_maybe_uninit::PointsTo<MetaSlotStorage>,
    pub vtable_ptr_perm: vstd::simple_pptr::PointsTo<usize>,
}

pub const REF_COUNT_MAX_USIZE: usize = REF_COUNT_MAX as usize; 

/// One unit of shared ownership of the currently installed metadata.
pub type FracMetadataPerm = Count<MetadataPerms, REF_COUNT_MAX_USIZE>;
/// The undistributed part of a metadata permission.
pub type FracMetadataPermResource = CountResource<MetadataPerms, REF_COUNT_MAX_USIZE>;

/// Permissions that remain under the authority of `MetaRegionOwners`.
///
/// `ref_count_perm` and `in_list_perm` exist for the complete lifetime of the
/// corresponding `MetaSlot` (i.e., `'static`).
pub tracked struct MetaSlotOwner {
    /// The undistributed fractions of the currently installed [`MetadataPerms`].
    pub metadata_perm: FracMetadataPermResource,
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

impl MetaSlotOwner {
    pub open spec fn same_permissions(self, other: Self) -> bool {
        &&& self.metadata_perm == other.metadata_perm
        &&& self.ref_count_perm == other.ref_count_perm
        &&& self.in_list_perm == other.in_list_perm
    }

    pub open spec fn ref_count(self) -> u64 {
        self.ref_count_perm.value()
    }

    pub open spec fn metadata_perms(self) -> MetadataPerms {
        self.metadata_perm.resource()
    }

    pub open spec fn storage_perm(self) -> pcell_maybe_uninit::PointsTo<MetaSlotStorage> {
        self.metadata_perms().storage_perm
    }

    pub open spec fn vtable_ptr_perm(self) -> vstd::simple_pptr::PointsTo<usize> {
        self.metadata_perms().vtable_ptr_perm
    }

    pub proof fn tracked_borrow_metadata_perms(tracked &self) -> (tracked res: &MetadataPerms)
        requires
            !self.metadata_perm.is_resource_vacant(),
        returns
            self.metadata_perms(),
    {
        self.metadata_perm.tracked_borrow()
    }
}

/// Well-formedness of a concrete metadata representation.
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

/// The value of a concrete metadata.
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
    returns
        typed_meta_value::<M>(*metadata_perms, *repr_perm),
{
    let slot = PPtr::<MetaSlot>::from_addr(ptr.addr()).borrow(Tracked(points_to));
    M::from_borrowed(slot.storage.borrow(Tracked(&metadata_perms.storage_perm)), Tracked(repr_perm))
}

pub fn borrow_meta_mut<'a, M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    ptr: cast_ptr::ReprPtr<MetaSlotStorage, M>,
    Tracked(points_to): Tracked<&'a vstd::simple_pptr::PointsTo<MetaSlot>>,
    Tracked(metadata_perms): Tracked<&'a mut MetadataPerms>,
    Tracked(repr_perm): Tracked<&'a mut M::ReprPerm>,
) -> (res: &'a mut M)
    requires
        points_to.value().vtable_ptr == old(metadata_perms).vtable_ptr_perm.pptr(),
        typed_meta_wf::<M>(*points_to, *old(metadata_perms), *old(repr_perm)),
        ptr.addr() == points_to.addr(),
    ensures
        *res == typed_meta_value::<M>(*old(metadata_perms), *old(repr_perm)),
        final(metadata_perms).storage_perm.id() == old(metadata_perms).storage_perm.id(),
        final(metadata_perms).vtable_ptr_perm == old(metadata_perms).vtable_ptr_perm,
        typed_meta_wf::<M>(*points_to, *final(metadata_perms), *final(repr_perm)),
        *final(res) == typed_meta_value::<M>(*final(metadata_perms), *final(repr_perm)),
{
    let slot = PPtr::<MetaSlot>::from_addr(ptr.addr()).borrow(Tracked(points_to));
    M::from_borrowed_mut(
        slot.storage.borrow_mut(Tracked(&mut metadata_perms.storage_perm)),
        Tracked(repr_perm),
    )
}

impl Inv for MetaSlotOwner {
    open spec fn inv(self) -> bool {
        &&& self.ref_count() == REF_COUNT_UNUSED ==> {
            &&& self.metadata_perm.is_full()
            &&& self.storage_perm().is_uninit()
            &&& self.vtable_ptr_perm().is_uninit()
            &&& self.in_list_perm.value()
                == 0
            // A managed slot at `REF_COUNT_UNUSED` has no live PTE mapping. Hence `paths_in_pt` is empty.
            // MMIO slots are excluded — they are not  ref-counted as ordinary frames.
            &&& (self.usage != PageUsage::MMIO ==> self.paths_in_pt.is_empty())
        }
        &&& self.ref_count() == REF_COUNT_UNIQUE ==> {
            &&& self.metadata_perm.is_resource_vacant()
            // A UNIQUE non-MMIO slot has no live PTE mapping.
            &&& (self.usage != PageUsage::MMIO ==> self.paths_in_pt.is_empty())
        }
        &&& 0 < self.ref_count() <= REF_COUNT_MAX ==> {
            &&& self.metadata_perm.frac() + self.ref_count() == REF_COUNT_MAX
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
            REF_COUNT_UNIQUE => { true },
            0 => { &&& self.in_list == 0 },
            _ if self.ref_count <= REF_COUNT_MAX => { true },
            _ => { false },
        }
    }
}

impl View for MetaSlotOwner {
    type V = MetaSlotModel;

    open spec fn view(&self) -> Self::V {
        let storage = if self.metadata_perm.not_empty() {
            self.storage_perm().mem_contents()
        } else {
            arbitrary()
        };
        let ref_count = self.ref_count();
        let vtable_ptr = if self.metadata_perm.not_empty() {
            self.vtable_ptr_perm().mem_contents()
        } else {
            arbitrary()
        };
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
        &&& self.ref_count.id() == owner.ref_count_perm.id()
        &&& self.in_list.id() == owner.in_list_perm.id()
        &&& owner.metadata_perm.not_empty() ==> {
            &&& self.storage.id() == owner.storage_perm().id()
            &&& self.vtable_ptr == owner.vtable_ptr_perm().pptr()
        }
    }
}

/// Writes `metadata` into the byte storage and establishes its direct
/// `Repr<MetaSlotStorage>` interpretation.
pub exec fn write_metadata_into_storage<M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    cell: &pcell_maybe_uninit::PCell<MetaSlotStorage>,
    Tracked(metadata_perms): Tracked<&mut MetadataPerms>,
    Tracked(repr_perm): Tracked<&mut M::ReprPerm>,
    metadata: M,
)
    requires
        cell.id() == old(metadata_perms).storage_perm.id(),
    ensures
        final(metadata_perms).storage_perm.id() == old(metadata_perms).storage_perm.id(),
        final(metadata_perms).storage_perm.is_init(),
        final(metadata_perms).vtable_ptr_perm == old(metadata_perms).vtable_ptr_perm,
        M::wf(final(metadata_perms).storage_perm.value(), *final(repr_perm)),
        M::from_repr_spec(final(metadata_perms).storage_perm.value(), *final(repr_perm))
            == metadata,
{
    proof {
        M::from_to_repr(metadata, *repr_perm);
        M::to_repr_wf(metadata, *repr_perm);
    }
    let repr = metadata.to_repr(Tracked(repr_perm));
    cell.write(Tracked(&mut metadata_perms.storage_perm), repr);
}

} // verus!
