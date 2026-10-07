use vstd::{atomic::*, cell::pcell_maybe_uninit, prelude::*, simple_pptr::*};
#[cfg(feature = "type_id")]
use core::any::TypeId;
#[cfg(feature = "type_id")]
use vstd_extra::typing::types::Any;
use vstd::std_specs::convert::{IntoSpecImpl, TryFromSpecImpl};
use vstd_extra::typing::tagged::{
    ByteRepr, ByteSized, TaggedArray, recorded_id,
};
use vstd_extra::{
    cast_ptr::{self, BijectiveRepr, Repr},
    ghost_tree::TreePath,
    ownership::*,
    resource::ghost_resource::count_auth::{Count, CountResource},
};

use crate::specs::{arch::NR_ENTRIES, mm::frame::frame_specs::FrameRawPerms};

use super::*;
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
/// Gated because its only uses here are: both untyped-segment reparam axioms need
/// `dyn_supertrait`, so an unconditional import would be dead in every other
/// configuration.
#[cfg(feature = "dyn_supertrait")]
use crate::mm::frame::untyped::AnyUFrameMeta;

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

pub const META_STORAGE_SIZE: usize = META_SLOT_SIZE - 3 * 8;

pub uninterp spec fn pt_node_encode(v: StoredPageTablePageMeta) -> [u8; META_STORAGE_SIZE];

pub uninterp spec fn pt_node_decode(b: [u8; META_STORAGE_SIZE]) -> Result<
    StoredPageTablePageMeta,
    (),
>;

#[verifier::external_body]
pub broadcast proof fn axiom_pt_node_round_trip(v: StoredPageTablePageMeta)
    ensures
        #[trigger] pt_node_decode(pt_node_encode(v)) == Ok(v),
{
}

impl TryFrom<[u8; META_STORAGE_SIZE]> for StoredPageTablePageMeta {
    type Error = ();

    #[verifier::external_body]
    fn try_from(b: [u8; META_STORAGE_SIZE]) -> Result<Self, Self::Error> {
        unimplemented!()
    }
}

impl TryFromSpecImpl<[u8; META_STORAGE_SIZE]> for StoredPageTablePageMeta {
    open spec fn obeys_try_from_spec() -> bool {
        true
    }

    open spec fn try_from_spec(b: [u8; META_STORAGE_SIZE]) -> Result<Self, Self::Error> {
        pt_node_decode(b)
    }
}

#[allow(clippy::from_over_into)]
impl Into<[u8; META_STORAGE_SIZE]> for StoredPageTablePageMeta {
    #[verifier::external_body]
    fn into(self) -> [u8; META_STORAGE_SIZE] {
        unimplemented!()
    }
}

impl IntoSpecImpl<[u8; META_STORAGE_SIZE]> for StoredPageTablePageMeta {
    open spec fn obeys_into_spec() -> bool {
        true
    }

    open spec fn into_spec(self) -> [u8; META_STORAGE_SIZE] {
        pt_node_encode(self)
    }
}

impl ByteSized<{ META_STORAGE_SIZE }> for StoredPageTablePageMeta {
    /// Axiomatized: a layout fact. Upstream's `impl_frame_meta_for!` asserts the
    /// same inequality with a `const` check.
    #[verifier::external_body]
    proof fn size_correct() {
    }
}

impl ByteRepr<{ META_STORAGE_SIZE }> for StoredPageTablePageMeta {
    proof fn round_trip(self) {
        broadcast use axiom_pt_node_round_trip;
    }

    proof fn obeys() {
    }
}

/// A frame's metadata, as stored in its slot.
pub struct MetaSlotStorage(pub TaggedArray<META_STORAGE_SIZE>);

impl MetaSlotStorage {
    /// This slot holds an `M`.
    pub open spec fn holds<M: ByteRepr<META_STORAGE_SIZE>>(self) -> bool {
        self.0.holds::<M>()
    }

    /// Build a slot holding `data` as an `M`.
    pub open spec fn tagged<M: ByteRepr<META_STORAGE_SIZE>>(
        data: [u8; META_STORAGE_SIZE],
    ) -> MetaSlotStorage {
        MetaSlotStorage(TaggedArray { id: Ghost(recorded_id::<M>()), data })
    }
}

unsafe impl AnyFrameMeta for MetaSlotStorage {
    uninterp spec fn vtable_ptr(&self) -> usize;

    #[cfg(feature = "type_id")]
    open spec fn meta_id(&self) -> TypeId {
        type_id::<Self>()
    }

    #[cfg(feature = "type_id")]
    proof fn meta_id_correct(&self) {
    }

    #[cfg(feature = "type_id")]
    fn to_any(&self) -> (r: &dyn Any) {
        let d: &dyn Any = self;
        assert(d.type_id_spec() == self.type_id_spec());
        d
    }
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

    proof fn to_repr_wf(self, perm: ()) {
    }
}

/// The identity representation is trivially a bijection.
impl BijectiveRepr<MetaSlotStorage> for MetaSlotStorage {
    proof fn to_from_repr(slot: MetaSlotStorage, perm: ()) {
    }
}

/// The type of a recorded metadata identity.
#[cfg(feature = "type_id")]
pub type MetaTypeId = TypeId;

#[cfg(not(feature = "type_id"))]
pub type MetaTypeId = int;

/// The identity recorded for a slot holding metadata of type `M`.
#[cfg(feature = "type_id")]
pub open spec fn recorded_meta_id<M: ?Sized>() -> MetaTypeId {
    type_id::<M>()
}

#[cfg(not(feature = "type_id"))]
pub uninterp spec fn recorded_meta_id<M: ?Sized>() -> MetaTypeId;

/// Whether metadata recorded under `id` describes *untyped* memory
pub uninterp spec fn id_is_untyped(id: MetaTypeId) -> bool;

/// Untypedness is a property of the metadata *type*, not of a value of that type
#[cfg(feature = "type_id")]
#[verifier::external_body]
pub proof fn axiom_untyped_recorded_by_id<M: AnyFrameMeta + ?Sized>(m: &M)
    ensures
        m.is_untyped_spec() == id_is_untyped(m.meta_id()),
{
}

/// Permissions to access metadata.
pub tracked struct MetadataPerm {
    pub storage_perm: pcell_maybe_uninit::PointsTo<MetaSlotStorage>,
    pub vtable_ptr_perm: vstd::simple_pptr::PointsTo<usize>,
    pub ghost meta_type_id: MetaTypeId,
}

/// How a permission is reinterpreted when a handle is reparameterized from
/// metadata type `A` to metadata type `B`. Uninterpreted and axiomatized
/// for individual pairs `A` and `B`.
pub uninterp spec fn reparam_perm<A: ?Sized, B: ?Sized, P>(p: P) -> P;

// ---------------------------------------------------------------------------
// Effect of reparameterization on permissions
// ---------------------------------------------------------------------------

/// Erasing a sized metadata type leaves the permission alone.
pub axiom fn axiom_reparam_perm_erase<M: AnyFrameMeta>(p: FracMetadataPerm)
    ensures
        reparam_perm::<M, dyn AnyFrameMeta, FracMetadataPerm>(p) == p,
;

/// Recovering a metadata type from an erased handle leaves the permission alone.
pub axiom fn axiom_reparam_perm_recover<M: AnyFrameMeta>(p: FracMetadataPerm)
    ensures
        reparam_perm::<dyn AnyFrameMeta, M, FracMetadataPerm>(p) == p,
;

/// Reparameterizing between two sized metadata types also converts the permission.
pub axiom fn axiom_reparam_perm_between<A: AnyFrameMeta, B: AnyFrameMeta>(p: MetadataPerm)
    ensures
        reparam_perm::<A, B, MetadataPerm>(p) == (MetadataPerm {
            storage_perm: p.storage_perm,
            vtable_ptr_perm: p.vtable_ptr_perm,
            meta_type_id: recorded_meta_id::<B>(),
        }),
;

/// Erasing an *untyped* metadata type leaves the permission alone.
#[cfg(feature = "dyn_supertrait")]
pub axiom fn axiom_reparam_perm_erase_untyped<M: AnyUFrameMeta>(p: Seq<FrameRawPerms>)
    ensures
        reparam_perm::<M, dyn AnyUFrameMeta, Seq<FrameRawPerms>>(p) == p,
;

/// Narrowing an erased handle to the untyped erasure leaves the permission alone.
#[cfg(all(feature = "type_id", feature = "dyn_supertrait"))]
pub axiom fn axiom_reparam_perm_narrow_untyped(p: Seq<FrameRawPerms>)
    ensures
        reparam_perm::<dyn AnyFrameMeta, dyn AnyUFrameMeta, Seq<FrameRawPerms>>(p) == p,
;

pub const REF_COUNT_MAX_USIZE: usize = REF_COUNT_MAX as usize;

/// Fractional metadata permission.
pub type FracMetadataPerm = Count<MetadataPerm, REF_COUNT_MAX_USIZE>;

/// The undistributed part of a metadata permission.
pub type FracMetadataPermResource = CountResource<MetadataPerm, REF_COUNT_MAX_USIZE>;

/// Permissions that remain under the authority of `MetaRegionOwners`.
///
/// `ref_count_perm` and `in_list_perm` exist for the complete lifetime of the
/// corresponding `MetaSlot` (i.e., `'static`).
pub tracked struct MetaSlotOwner {
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

    pub open spec fn metadata_perm(self) -> MetadataPerm {
        self.metadata_perm.resource()
    }

    pub open spec fn storage_perm(self) -> pcell_maybe_uninit::PointsTo<MetaSlotStorage> {
        self.metadata_perm().storage_perm
    }

    pub open spec fn vtable_ptr_perm(self) -> vstd::simple_pptr::PointsTo<usize> {
        self.metadata_perm().vtable_ptr_perm
    }

    pub proof fn tracked_borrow_metadata_perm(tracked &self) -> tracked &MetadataPerm
        requires
            !self.metadata_perm.is_resource_vacant(),
        returns
            self.metadata_perm(),
    {
        self.metadata_perm.tracked_borrow()
    }
}

/// Well-formedness of a concrete metadata representation.
pub open spec fn typed_meta_wf<M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    slot_perm: vstd::simple_pptr::PointsTo<MetaSlot>,
    metadata_perm: MetadataPerm,
    repr_perm: M::ReprPerm,
) -> bool {
    &&& slot_perm.is_init()
    &&& MetaSlot::perms_related(slot_perm, metadata_perm)
    &&& M::wf(metadata_perm.storage_perm.value(), repr_perm)
}

/// The value of a concrete metadata.
pub open spec fn typed_meta_value<M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    metadata_perm: MetadataPerm,
    repr_perm: M::ReprPerm,
) -> M {
    M::from_repr_spec(metadata_perm.storage_perm.value(), repr_perm)
}

pub fn borrow_meta<'a, M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    ptr: cast_ptr::ReprPtr<MetaSlotStorage, M>,
    Tracked(slot_perm): Tracked<&'a vstd::simple_pptr::PointsTo<MetaSlot>>,
    Tracked(metadata_perm): Tracked<&'a MetadataPerm>,
    Tracked(repr_perm): Tracked<&'a M::ReprPerm>,
) -> &'a M
    requires
        ptr.addr() == slot_perm.addr(),
        typed_meta_wf::<M>(*slot_perm, *metadata_perm, *repr_perm),
    returns
        typed_meta_value::<M>(*metadata_perm, *repr_perm),
{
    let slot = PPtr::<MetaSlot>::from_addr(ptr.addr()).borrow(Tracked(slot_perm));
    M::from_borrowed(slot.storage.borrow(Tracked(&metadata_perm.storage_perm)), Tracked(repr_perm))
}

pub fn borrow_meta_mut<'a, M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    ptr: cast_ptr::ReprPtr<MetaSlotStorage, M>,
    Tracked(slot_perm): Tracked<&'a vstd::simple_pptr::PointsTo<MetaSlot>>,
    Tracked(metadata_perms): Tracked<&'a mut MetadataPerm>,
    Tracked(repr_perm): Tracked<&'a mut M::ReprPerm>,
) -> (res: &'a mut M)
    requires
        ptr.addr() == slot_perm.addr(),
        typed_meta_wf::<M>(*slot_perm, *old(metadata_perms), *old(repr_perm)),
    ensures
        *res == typed_meta_value::<M>(*old(metadata_perms), *old(repr_perm)),
        *final(res) == typed_meta_value::<M>(*final(metadata_perms), *final(repr_perm)),
        typed_meta_wf::<M>(*slot_perm, *final(metadata_perms), *final(repr_perm)),
{
    let slot = PPtr::<MetaSlot>::from_addr(ptr.addr()).borrow(Tracked(slot_perm));
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
            // A managed slot at `REF_COUNT_UNUSED` has no live PTE mapping.
            &&& (self.usage != PageUsage::MMIO ==> self.paths_in_pt.is_empty())
        }
        &&& self.ref_count() == REF_COUNT_UNIQUE ==> {
            &&& self.metadata_perm.is_resource_vacant()
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
    Tracked(metadata_perms): Tracked<&mut MetadataPerm>,
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
