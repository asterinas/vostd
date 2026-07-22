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

/// Reconstructs the representation permission paired with a concrete view of
/// the type-erased metadata storage.
pub uninterp spec fn repr_perm_from_storage<M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    perm: pcell_maybe_uninit::PointsTo<MetaSlotStorage>,
) -> M::Perm;

/// Typed ownership of the payload at the beginning of one metadata slot.
/// The outer slot permission is retained only so executable code can reach
/// `MetaSlot::storage`; the interpreted value is directly `M`, not a synthetic
/// value representing the whole `MetaSlot`.
#[verifier::accept_recursive_types(M)]
pub tracked struct MetaPerm<M: AnyFrameMeta + Repr<MetaSlotStorage>> {
    pub points_to: vstd::simple_pptr::PointsTo<MetaSlot>,
    pub storage: pcell_maybe_uninit::PointsTo<MetaSlotStorage>,
    pub repr_perm: M::Perm,
    pub ref_count: PermissionU64,
    pub vtable_ptr: vstd::simple_pptr::PointsTo<usize>,
    pub in_list: PermissionU64,
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage>> MetaPerm<M> {
    pub open spec fn new_spec(
        points_to: vstd::simple_pptr::PointsTo<MetaSlot>,
        inner: MetadataInnerPerms,
    ) -> Self {
        Self {
            points_to,
            storage: inner.storage,
            repr_perm: repr_perm_from_storage::<M>(inner.storage),
            ref_count: inner.ref_count,
            vtable_ptr: inner.vtable_ptr,
            in_list: inner.in_list,
        }
    }

    pub open spec fn wf(self) -> bool {
        &&& self.points_to.is_init()
        &&& self.storage.is_init()
        &&& M::wf(self.storage.value(), self.repr_perm)
        &&& self.storage.id() == self.points_to.value().storage.id()
        &&& self.ref_count.id() == self.points_to.value().ref_count.id()
        &&& self.vtable_ptr.pptr() == self.points_to.value().vtable_ptr
        &&& self.in_list.id() == self.points_to.value().in_list.id()
    }

    pub open spec fn addr(self) -> usize {
        self.points_to.addr()
    }

    pub open spec fn pptr(self) -> PPtr<MetaSlot> {
        self.points_to.pptr()
    }

    pub open spec fn is_init(self) -> bool {
        self.points_to.is_init() && self.storage.is_init()
    }

    pub open spec fn mem_contents(self) -> MemContents<M> {
        match self.storage.mem_contents() {
            MemContents::<MetaSlotStorage>::Uninit => MemContents::<M>::Uninit,
            MemContents::<MetaSlotStorage>::Init(storage) => {
                MemContents::<M>::Init(M::from_repr_spec(storage, self.repr_perm))
            },
        }
    }

    pub open spec fn value(self) -> M
        recommends
            self.wf(),
    {
        M::from_repr_spec(self.storage.value(), self.repr_perm)
    }

    pub fn borrow<'a>(ptr: PPtr<MetaSlot>, Tracked(perm): Tracked<&'a Self>) -> (res: &'a M)
        requires
            perm.wf(),
            ptr == perm.points_to.pptr(),
        ensures
            *res == perm.value(),
    {
        let slot = ptr.borrow(Tracked(&perm.points_to));
        M::from_borrowed(slot.storage.borrow(Tracked(&perm.storage)), Tracked(&perm.repr_perm))
    }

    #[verifier::external_body]
    pub fn borrow_mut<'a>(ptr: PPtr<MetaSlot>, Tracked(perm): Tracked<&'a mut Self>) -> (res:
        &'a mut M)
        requires
            old(perm).wf(),
            ptr == old(perm).points_to.pptr(),
        ensures
            *res == old(perm).value(),
            final(perm).wf(),
            final(perm).value() == *final(res),
            final(perm).points_to == old(perm).points_to,
            final(perm).ref_count == old(perm).ref_count,
            final(perm).vtable_ptr == old(perm).vtable_ptr,
            final(perm).in_list == old(perm).in_list,
    {
        let slot = ptr.borrow(Tracked(&perm.points_to));
        M::from_borrowed_mut(
            slot.storage.borrow_mut(Tracked(&mut perm.storage)),
            Tracked(&mut perm.repr_perm),
        )
    }
}

pub fn borrow_meta<'a, M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    ptr: cast_ptr::ReprPtr<MetaSlotStorage, M>,
    Tracked(perm): Tracked<&'a MetaPerm<M>>,
) -> (res: &'a M)
    requires
        perm.wf(),
        ptr.addr() == perm.points_to.addr(),
    ensures
        *res == perm.value(),
{
    MetaPerm::borrow(PPtr::<MetaSlot>::from_addr(ptr.addr()), Tracked(perm))
}

pub fn borrow_meta_mut<'a, M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    ptr: cast_ptr::ReprPtr<MetaSlotStorage, M>,
    Tracked(perm): Tracked<&'a mut MetaPerm<M>>,
) -> (res: &'a mut M)
    requires
        old(perm).wf(),
        ptr.addr() == old(perm).points_to.addr(),
    ensures
        *res == old(perm).value(),
        final(perm).wf(),
        final(perm).value() == *final(res),
        final(perm).points_to == old(perm).points_to,
        final(perm).ref_count == old(perm).ref_count,
        final(perm).vtable_ptr == old(perm).vtable_ptr,
        final(perm).in_list == old(perm).in_list,
{
    MetaPerm::borrow_mut(PPtr::<MetaSlot>::from_addr(ptr.addr()), Tracked(perm))
}

/// Reconstructs the typed view parked in a type-erased region owner.
pub open spec fn typed_meta_perm<M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    points_to: vstd::simple_pptr::PointsTo<MetaSlot>,
    inner: MetadataInnerPerms,
) -> MetaPerm<M> {
    MetaPerm::new_spec(points_to, inner)
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

/// Permission state produced after writing a concrete metadata value into the
/// type-erased storage cell.
pub uninterp spec fn storage_perm_after_write<M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    metadata: M,
    base: pcell_maybe_uninit::PointsTo<MetaSlotStorage>,
) -> pcell_maybe_uninit::PointsTo<MetaSlotStorage>;

/// The write keeps the cell allocation and makes its contents directly
/// interpretable as the supplied `M`.
pub axiom fn storage_perm_after_write_properties<M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    metadata: M,
    base: pcell_maybe_uninit::PointsTo<MetaSlotStorage>,
)
    ensures
        storage_perm_after_write(metadata, base).id() == base.id(),
        storage_perm_after_write(metadata, base).is_init(),
        M::wf(
            storage_perm_after_write(metadata, base).value(),
            repr_perm_from_storage::<M>(storage_perm_after_write(metadata, base)),
        ),
        M::from_repr_spec(
            storage_perm_after_write(metadata, base).value(),
            repr_perm_from_storage::<M>(storage_perm_after_write(metadata, base)),
        ) == metadata,
;

#[verifier::external_body]
pub proof fn tracked_set_storage_perm<M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    tracked perm: &mut pcell_maybe_uninit::PointsTo<MetaSlotStorage>,
    metadata: M,
)
    requires
        old(perm).is_init(),
    ensures
        *final(perm) == storage_perm_after_write(metadata, *old(perm)),
{
}

/// Writes `metadata` into the byte storage and establishes its direct
/// `Repr<MetaSlotStorage>` interpretation.
pub exec fn write_metadata_into_storage<M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    cell: &pcell_maybe_uninit::PCell<MetaSlotStorage>,
    Tracked(perm): Tracked<&mut pcell_maybe_uninit::PointsTo<MetaSlotStorage>>,
    metadata: M,
)
    requires
        cell.id() == old(perm).id(),
    ensures
        final(perm).id() == old(perm).id(),
        final(perm).is_init(),
        M::wf(final(perm).value(), repr_perm_from_storage::<M>(*final(perm))),
        M::from_repr_spec(final(perm).value(), repr_perm_from_storage::<M>(*final(perm)))
            == metadata,
{
    cell.write(Tracked(perm), MetaSlotStorage::Untyped);
    proof {
        let ghost base = *perm;
        tracked_set_storage_perm(perm, metadata);
        storage_perm_after_write_properties(metadata, base);
    }
}

} // verus!
