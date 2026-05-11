//! The model of a metadata slot. It includes:
//! - The model of the metadata slot: `MetaSlotModel`.
//! - The invariants for both MetaSlot and MetaSlotModel.
//! - The primitives for MetaSlot.
use vstd::atomic::*;
use vstd::cell::pcell_maybe_uninit;
use vstd::prelude::*;
use vstd::simple_pptr::*;

use vstd_extra::cast_ptr::{self, Repr};
use vstd_extra::ghost_tree::TreePath;
use vstd_extra::ownership::*;

use super::*;
use crate::mm::frame::meta::MetaSlot;
use crate::mm::frame::AnyFrameMeta;
use crate::mm::{Paddr, PagingLevel};
use crate::specs::arch::kspace::FRAME_METADATA_RANGE;
use crate::specs::arch::mm::NR_ENTRIES;
use crate::specs::mm::frame::linked_list::linked_list_owners::StoredLink;
use crate::specs::mm::frame::mapping::{meta_addr, meta_to_frame, META_SLOT_SIZE};

verus! {

#[allow(non_camel_case_types)]
pub enum MetaSlotStatus {
    UNUSED,
    UNIQUE,
    SHARED,
    OVERFLOW,
    UNDER_CONSTRUCTION,
}

pub enum PageState {
    Unused,
    Typed,
    Untyped,
}

#[repr(u8)]
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum PageUsage {
    // The zero variant is reserved for the unused type. Only an unused page
    // can be designated for one of the other purposes.
    #[allow(dead_code)]
    Unused,
    /// The page is reserved or unusable. The kernel should not touch it.
    #[allow(dead_code)]
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
    #[allow(dead_code)]
    MMIO,
}

impl PageUsage {
    pub open spec fn as_u8_spec(&self) -> u8 {
        match self {
            PageUsage::Unused => 0,
            PageUsage::Reserved => 1,
            PageUsage::Frame => 32,
            PageUsage::PageTable => 64,
            PageUsage::Meta => 65,
            PageUsage::Kernel => 66,
            PageUsage::MMIO => 67,
        }
    }

    #[verifier::external_body]
    #[verifier::when_used_as_spec(as_u8_spec)]
    pub fn as_u8(&self) -> (res: u8)
        ensures
            res == self.as_u8_spec(),
    {
        *self as u8
    }

    #[vstd::contrib::auto_spec]
    pub fn as_state(&self) -> (res: PageState) {
        match &self {
            PageUsage::Unused => PageState::Unused,
            PageUsage::Frame => PageState::Untyped,
            _ => PageState::Typed,
        }
    }
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
        (#[trigger] slot.usage == PageUsage::MMIO)
            <==> is_mmio_paddr(meta_to_frame(slot.self_addr));

/// MMIO ranges are aligned to (and closed under) huge-page granularities:
/// every sub-paddr within a huge frame inherits the huge frame's MMIO-ness.
/// This is a hardware-layout convention — MMIO BARs are mapped at huge-page
/// boundaries, and the verified `split_if_mapped_huge` relies on it to
/// transfer MMIO-ness from a huge frame to its 4KB sub-pages. Non-broadcast:
/// callers invoke this explicitly with the relevant `page_size`.
pub axiom fn axiom_mmio_paddr_huge_page_closed(
    pa: crate::mm::Paddr,
    page_size: usize,
    offset: usize,
)
    requires
        pa % page_size == 0,
        offset < page_size,
    ensures
        is_mmio_paddr((pa + offset) as crate::mm::Paddr) == is_mmio_paddr(pa);

pub const REF_COUNT_UNUSED: u64 = u64::MAX;

pub const REF_COUNT_UNIQUE: u64 = u64::MAX - 1;

pub const REF_COUNT_MAX: u64 = i64::MAX as u64;

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
impl AnyFrameMeta for MetaSlotStorage {
    uninterp spec fn vtable_ptr(&self) -> usize;
}

impl Repr<MetaSlotStorage> for MetaSlotStorage {
    type Perm = ();

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

pub tracked struct MetaSlotOwner {
    pub inner_perms: MetadataInnerPerms,
    pub self_addr: usize,
    pub usage: PageUsage,
    pub raw_count: usize,
    /// The set of tree paths at which this slot is referenced. For PT-node
    /// slots this is a singleton. For data-frame slots this tracks every
    /// location the frame is currently mapped — allowing a single frame to be
    /// mapped at multiple addresses.
    pub ghost paths_in_pt: Set<TreePath<NR_ENTRIES>>,
}

impl Inv for MetaSlotOwner {
    open spec fn inv(self) -> bool {
        &&& self.inner_perms.ref_count.value() == REF_COUNT_UNUSED ==> {
            &&& self.raw_count == 0
            &&& self.inner_perms.storage.is_uninit()
            &&& self.inner_perms.vtable_ptr.is_uninit()
            &&& self.inner_perms.in_list.value() == 0
        }
        &&& self.inner_perms.ref_count.value() == REF_COUNT_UNIQUE ==> {
            &&& self.inner_perms.vtable_ptr.is_init()
            &&& self.inner_perms.storage.is_init()
            &&& self.inner_perms.in_list.value() == 0
        }
        &&& 0 < self.inner_perms.ref_count.value() <= REF_COUNT_MAX ==> {
            &&& self.inner_perms.vtable_ptr.is_init()
        }
        &&& REF_COUNT_MAX < self.inner_perms.ref_count.value() < REF_COUNT_UNIQUE ==> { false }
        &&& self.inner_perms.ref_count.value() == 0 ==> {
            &&& self.inner_perms.in_list.value() == 0
        }
        &&& FRAME_METADATA_RANGE.start <= self.self_addr < FRAME_METADATA_RANGE.end
        &&& self.self_addr % META_SLOT_SIZE == 0
    }
}

pub ghost struct MetaSlotModel {
    pub status: MetaSlotStatus,
    pub storage: MemContents<MetaSlotStorage>,
    pub ref_count: u64,
    pub vtable_ptr: MemContents<usize>,
    pub in_list: u64,
    pub self_addr: usize,
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
            0 => {
                &&& self.in_list == 0
            },
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
        let self_addr = self.self_addr;
        let usage = self.usage;
        let status = match ref_count {
            REF_COUNT_UNUSED => MetaSlotStatus::UNUSED,
            REF_COUNT_UNIQUE => MetaSlotStatus::UNIQUE,
            0 => MetaSlotStatus::UNDER_CONSTRUCTION,
            _ if ref_count <= REF_COUNT_MAX => MetaSlotStatus::SHARED,
            _ => MetaSlotStatus::OVERFLOW,
        };
        MetaSlotModel { status, storage, ref_count, vtable_ptr, in_list, self_addr, usage }
    }
}

impl InvView for MetaSlotOwner {
    proof fn view_preserves_inv(self) { }
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

impl ModelOf for MetaSlot {

}

impl MetaSlotOwner {
    pub axiom fn take_inner_perms(tracked &mut self) -> (tracked res: MetadataInnerPerms)
        ensures
            res == old(self).inner_perms,
            final(self).self_addr == old(self).self_addr,
            final(self).usage == old(self).usage,
            final(self).raw_count == old(self).raw_count,
            final(self).paths_in_pt == old(self).paths_in_pt;

    pub axiom fn sync_inner(tracked &mut self, inner_perms: &MetadataInnerPerms)
        ensures *final(self) == (Self { inner_perms: *inner_perms, ..*old(self) });
}

pub struct Metadata<M: AnyFrameMeta> {
    pub metadata: M,
    pub ref_count: u64,
    pub vtable_ptr: MemContents<usize>,
    pub in_list: u64,
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage>> Metadata<M> {
    /// The metadata value is an abstract function of the inner permissions,
    /// since extracting `M` from `MetaSlotStorage` requires `M::Perm` which
    /// is not stored in `MetadataInnerPerms`.
    pub uninterp spec fn metadata_from_inner_perms(perm: pcell_maybe_uninit::PointsTo<MetaSlotStorage>) -> M;

    /// Inverse of [`metadata_from_inner_perms`]: given an `M` and a base
    /// storage permission, produce a new permission with the same cell id
    /// whose `metadata_from_inner_perms` interpretation yields `m`.
    pub uninterp spec fn inner_perms_from_metadata(
        m: M,
        base: pcell_maybe_uninit::PointsTo<MetaSlotStorage>,
    ) -> pcell_maybe_uninit::PointsTo<MetaSlotStorage>;

    /// Axiomatic roundtrip laws for the metadata ↔ storage-perm pair. The
    /// conversion is a transmute / reinterpret at exec level, so these laws
    /// live at the `cast_ptr` trust boundary.
    pub axiom fn metadata_perms_inverse(
        m: M,
        base: pcell_maybe_uninit::PointsTo<MetaSlotStorage>,
    )
        ensures
            Self::metadata_from_inner_perms(Self::inner_perms_from_metadata(m, base)) == m,
            Self::inner_perms_from_metadata(m, base).id() == base.id();

    pub axiom fn inner_perms_from_metadata_roundtrip(
        perm: pcell_maybe_uninit::PointsTo<MetaSlotStorage>,
    )
        ensures
            Self::inner_perms_from_metadata(Self::metadata_from_inner_perms(perm), perm) == perm;
}

/// Value-updaters for the opaque tracked permission types inside
/// [`MetadataInnerPerms`]. Each uninterp operation produces a new permission
/// with the same id as the input but a specified value; the paired axioms
/// document the expected behavior. The conversions are implemented in exec
/// by `external_body` primitives, so the laws are axiomatic.
pub uninterp spec fn perm_u64_with(p: PermissionU64, v: u64) -> PermissionU64;

pub axiom fn perm_u64_with_value(p: PermissionU64, v: u64)
    ensures
        perm_u64_with(p, v).value() == v,
        perm_u64_with(p, v).id() == p.id();

/// Setting a `PermissionU64` to its own current value is a no-op.
pub axiom fn perm_u64_with_identity(p: PermissionU64)
    ensures perm_u64_with(p, p.value()) == p;

pub uninterp spec fn pptr_usize_with(
    p: vstd::simple_pptr::PointsTo<usize>,
    c: MemContents<usize>,
) -> vstd::simple_pptr::PointsTo<usize>;

pub axiom fn pptr_usize_with_value(
    p: vstd::simple_pptr::PointsTo<usize>,
    c: MemContents<usize>,
)
    ensures
        pptr_usize_with(p, c).mem_contents() == c,
        pptr_usize_with(p, c).pptr() == p.pptr();

/// Setting a `PointsTo<usize>` to its own contents is a no-op.
pub axiom fn pptr_usize_with_identity(p: vstd::simple_pptr::PointsTo<usize>)
    ensures pptr_usize_with(p, p.mem_contents()) == p;

/// Reconstruct a [`MetaSlot`] from its underlying cell ids. The exec
/// implementation is a cast; the laws pin `.id()` / `.pptr()` equalities.
pub uninterp spec fn meta_slot_from_perm(perm: MetadataInnerPerms) -> MetaSlot;

pub axiom fn meta_slot_from_perm_ids(perm: MetadataInnerPerms)
    ensures
        meta_slot_from_perm(perm).storage.id() == perm.storage.id(),
        meta_slot_from_perm(perm).ref_count.id() == perm.ref_count.id(),
        meta_slot_from_perm(perm).vtable_ptr == perm.vtable_ptr.pptr(),
        meta_slot_from_perm(perm).in_list.id() == perm.in_list.id();

/// A `MetaSlot` is uniquely determined by its cell ids + vtable_ptr address.
/// This is a structural fact about the opaque atomic/cell primitives — two
/// `MetaSlot` values whose ids agree on every field are equal.
pub axiom fn meta_slot_eq_by_ids(a: MetaSlot, b: MetaSlot)
    ensures
        (a.storage.id() == b.storage.id()
         && a.ref_count.id() == b.ref_count.id()
         && a.vtable_ptr == b.vtable_ptr
         && a.in_list.id() == b.in_list.id())
        ==> a == b;

impl<M: AnyFrameMeta + Repr<MetaSlotStorage>> Repr<MetaSlot> for Metadata<M> {
    type Perm = MetadataInnerPerms;

    open spec fn wf(r: MetaSlot, perm: MetadataInnerPerms) -> bool {
        &&& perm.storage.id() == r.storage.id()
        &&& perm.ref_count.id() == r.ref_count.id()
        &&& perm.vtable_ptr.pptr() == r.vtable_ptr
        &&& perm.in_list.id() == r.in_list.id()
    }

    open spec fn to_repr_spec(self, perm: MetadataInnerPerms) -> (MetaSlot, MetadataInnerPerms) {
        let new_perm = MetadataInnerPerms {
            storage: Self::inner_perms_from_metadata(self.metadata, perm.storage),
            ref_count: perm_u64_with(perm.ref_count, self.ref_count),
            vtable_ptr: pptr_usize_with(perm.vtable_ptr, self.vtable_ptr),
            in_list: perm_u64_with(perm.in_list, self.in_list),
        };
        (meta_slot_from_perm(new_perm), new_perm)
    }

    #[verifier::external_body]
    fn to_repr(self, Tracked(perm): Tracked<&mut MetadataInnerPerms>) -> MetaSlot {
        unimplemented!()
    }

    open spec fn from_repr_spec(r: MetaSlot, perm: MetadataInnerPerms) -> Self {
        Metadata {
            metadata: Self::metadata_from_inner_perms(perm.storage),
            ref_count: perm.ref_count.value(),
            vtable_ptr: perm.vtable_ptr.mem_contents(),
            in_list: perm.in_list.value(),
        }
    }

    #[verifier::external_body]
    fn from_repr(r: MetaSlot, Tracked(perm): Tracked<&MetadataInnerPerms>) -> Self {
        unimplemented!()
    }

    #[verifier::external_body]
    fn from_borrowed<'a>(r: &'a MetaSlot, Tracked(perm): Tracked<&'a MetadataInnerPerms>) -> &'a Self {
        unimplemented!()
    }

    proof fn from_to_repr(self, perm: MetadataInnerPerms) {
        Self::metadata_perms_inverse(self.metadata, perm.storage);
        perm_u64_with_value(perm.ref_count, self.ref_count);
        perm_u64_with_value(perm.in_list, self.in_list);
        pptr_usize_with_value(perm.vtable_ptr, self.vtable_ptr);
        let (r, np) = self.to_repr_spec(perm);
        assert(Self::from_repr_spec(r, np) =~= self);
    }

    proof fn to_from_repr(r: MetaSlot, perm: MetadataInnerPerms) {
        // wf(r, perm) gives us: r's ids match perm's ids; r.vtable_ptr == perm.vtable_ptr.pptr().
        Self::inner_perms_from_metadata_roundtrip(perm.storage);
        perm_u64_with_identity(perm.ref_count);
        perm_u64_with_identity(perm.in_list);
        pptr_usize_with_identity(perm.vtable_ptr);
        // Each field of np2 equals the corresponding field of perm:
        //   np2.storage    = inner_perms_from_metadata(metadata_from_inner_perms(perm.storage), perm.storage)
        //                  = perm.storage                   (inner_perms_from_metadata_roundtrip)
        //   np2.ref_count  = perm_u64_with(perm.ref_count, perm.ref_count.value())
        //                  = perm.ref_count                 (perm_u64_with_identity)
        //   np2.vtable_ptr = pptr_usize_with(perm.vtable_ptr, perm.vtable_ptr.mem_contents())
        //                  = perm.vtable_ptr                (pptr_usize_with_identity)
        //   np2.in_list    = perm.in_list                   (perm_u64_with_identity)
        let md = Self::from_repr_spec(r, perm);
        let (r2, np2) = md.to_repr_spec(perm);
        assert(np2 =~= perm);
        // r2 is produced from np2 == perm; its ids match perm's; perm's ids match r's (by wf).
        meta_slot_from_perm_ids(np2);
        meta_slot_eq_by_ids(r2, r);
        assert(r2 == r);
    }

    proof fn to_repr_wf(self, perm: MetadataInnerPerms) {
        let (r, np) = self.to_repr_spec(perm);
        meta_slot_from_perm_ids(np);
        Self::metadata_perms_inverse(self.metadata, perm.storage);
        perm_u64_with_value(perm.ref_count, self.ref_count);
        perm_u64_with_value(perm.in_list, self.in_list);
        pptr_usize_with_value(perm.vtable_ptr, self.vtable_ptr);
        // wf checks id equality between np's perms and r's slot fields.
    }
}

/// A permission token for frame metadata.
///
/// [`Frame<M>`] the high-level representation of the low-level pointer
/// to the [`super::meta::MetaSlot`].
pub type MetaPerm<M/*: AnyFrameMeta + Repr<MetaSlotStorage>*/> = cast_ptr::PointsTo<MetaSlot, Metadata<M>>;

} // verus!
