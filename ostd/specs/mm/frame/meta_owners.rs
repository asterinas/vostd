#[cfg(feature = "type_id")]
use core::any::TypeId;
use vstd::std_specs::convert::{IntoSpecImpl, TryFromSpecImpl};
use vstd::{atomic::*, cell::pcell_maybe_uninit, prelude::*, simple_pptr::*};
use vstd_extra::substructural::CellAddr;
use vstd_extra::typing::tagged::{ByteRepr, ByteSized, TaggedArray, recorded_id};
#[cfg(feature = "type_id")]
use vstd_extra::typing::types::Any;
use vstd_extra::{
    ghost_tree::TreePath,
    ownership::*,
    resource::ghost_resource::count_auth::{Count, CountResource},
};

use crate::specs::{arch::NR_ENTRIES, mm::frame::frame_specs::FrameRawPerms};

use super::*;
/// Gated because its only uses here are: both untyped-segment reparam axioms need
/// `dyn_supertrait`, so an unconditional import would be dead in every other
/// configuration.
#[cfg(feature = "dyn_supertrait")]
use crate::mm::frame::untyped::AnyUFrameMeta;
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
    /// Initial purpose before metadata is installed. Reuse is governed by refcount.
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
}

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

/// A frame's metadata, as stored in its slot.
pub struct MetaSlotStorage(pub TaggedArray<META_STORAGE_SIZE>);

impl MetaSlotStorage {
    /// This slot holds an `M`.
    pub open spec fn holds<M: ByteRepr<META_STORAGE_SIZE>>(self) -> bool {
        self.0.holds::<M>()
    }

    /// The `M` this slot holds. Meaningful only where [`Self::holds`] does.
    pub open spec fn value<M: ByteRepr<META_STORAGE_SIZE>>(self) -> M {
        self.0.value::<M>()
    }

    /// Build a slot holding `data` as an `M`.
    pub open spec fn tagged<M: ByteRepr<META_STORAGE_SIZE>>(
        data: [u8; META_STORAGE_SIZE],
    ) -> MetaSlotStorage {
        MetaSlotStorage(TaggedArray { id: Ghost(recorded_id::<M>()), data })
    }
}

impl MetaSlotStorage {
    /// The purpose established by the installed metadata representation.
    pub open spec fn usage(self) -> PageUsage {
        usage_of_id(self.0.id@)
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

/// The purpose a slot serves while it holds metadata recorded under `id`.
///
/// Uninterpreted for the same reason as [`id_is_untyped`]: the open-world
/// representation is bytes plus a recorded id, so usage can no longer be read
/// off a variant the way it was off the tagged union this replaced. Usage is a
/// property of the metadata *type*, and the id is what survives erasure, so it
/// is recovered through the id rather than from the stored bytes.
pub uninterp spec fn usage_of_id(id: MetaTypeId) -> PageUsage;

/// Untypedness is a property of the metadata *type*, not of a value of that type
#[cfg(feature = "type_id")]
pub axiom fn axiom_untyped_recorded_by_id<M: AnyFrameMeta + ?Sized>(m: &M)
    ensures
        m.is_untyped_spec() == id_is_untyped(m.meta_id()),
;

/// Usage, like untypedness, is a property of the metadata *type*, so the
/// recorded id determines it.
///
/// Keyed on [`recorded_id`] rather than on `AnyFrameMeta::meta_id`, which is
/// `type_id`-gated: without that feature ids are opaque but still a function
/// of the type, which is all this needs.
///
/// Taking a value of `M` is what makes `usage_spec` usable here, and the
/// equation holds for *every* such value -- which is the claim that usage is
/// type-level, not per-value. Every impl in the tree satisfies it: all take the
/// default, except `PageTablePageMeta`, which returns a constant too.
pub axiom fn axiom_usage_of_recorded_id<M: AnyFrameMeta + ByteRepr<META_STORAGE_SIZE>>(m: M)
    ensures
        usage_of_id(recorded_id::<M>()) == m.usage_spec(),
;

/// A slot that holds an `M` has `M`'s usage.
///
/// The step the open-world representation needs: `usage()` reads the recorded
/// id, `holds::<M>()` says which id that is, and the axiom above ties it back
/// to the type's own `usage_spec`.
pub proof fn lemma_usage_of_held<M: AnyFrameMeta + ByteRepr<META_STORAGE_SIZE>>(perm: MetadataPerm)
    requires
        perm.storage_perm.is_init(),
        perm.storage_perm.value().holds::<M>(),
    ensures
        perm.usage() == typed_meta_value::<M>(perm).usage_spec(),
{
    axiom_usage_of_recorded_id::<M>(typed_meta_value::<M>(perm));
}

/// Permissions to access metadata.
pub tracked struct MetadataPerm {
    pub storage_perm: pcell_maybe_uninit::PointsTo<MetaSlotStorage>,
    pub vtable_ptr_perm: vstd::simple_pptr::PointsTo<usize>,
    pub ghost meta_type_id: MetaTypeId,
}

impl MetadataPerm {
    /// The purpose of the metadata described by this permission.
    pub open spec fn usage(self) -> PageUsage {
        self.storage_perm.value().usage()
    }
}

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

/// Well-formedness of a concrete metadata representation: the storage bytes
/// carry `M`'s tag and decode to an `M`.
///
/// There is no permission parameter. The representation is a plain byte array,
/// so deciding well-formedness needs nothing but the bytes themselves -- which
/// is what retiring `Repr` in favour of [`ByteRepr`] bought.
pub open spec fn typed_meta_wf<M: AnyFrameMeta + ByteRepr<META_STORAGE_SIZE>>(
    slot_perm: vstd::simple_pptr::PointsTo<MetaSlot>,
    metadata_perm: MetadataPerm,
) -> bool {
    &&& slot_perm.is_init()
    &&& MetaSlot::perms_related(slot_perm, metadata_perm)
    &&& metadata_perm.storage_perm.value().holds::<M>()
}

/// The value of a concrete metadata.
pub open spec fn typed_meta_value<M: AnyFrameMeta + ByteRepr<META_STORAGE_SIZE>>(
    metadata_perm: MetadataPerm,
) -> M {
    metadata_perm.storage_perm.value().value::<M>()
}

/// Borrows the metadata of a slot as an `M`.
///
/// `ptr` addresses the [`MetaSlot`] itself, not its metadata. Upstream the
/// metadata is a cell inside the slot -- `storage: UnsafeCell<[u8;
/// FRAME_METADATA_MAX_SIZE]>` -- and we model it as one, a
/// `PCell<MetaSlotStorage>`. So its contents are reached through
/// `metadata_perm.storage_perm`, never by casting the slot pointer: the
/// two addresses coincide only because the cell sits at offset 0.
pub fn borrow_meta<'a, M: AnyFrameMeta + ByteRepr<META_STORAGE_SIZE>>(
    ptr: PPtr<MetaSlot>,
    Tracked(slot_perm): Tracked<&'a vstd::simple_pptr::PointsTo<MetaSlot>>,
    Tracked(metadata_perm): Tracked<&'a MetadataPerm>,
) -> &'a M
    requires
        ptr.addr() == slot_perm.addr(),
        typed_meta_wf::<M>(*slot_perm, *metadata_perm),
    returns
        typed_meta_value::<M>(*metadata_perm),
{
    proof {
        MetaSlot::axiom_storage_at_slot_start(*slot_perm);
    }
    // The cell permission, borrowed as a permission to the same bytes at the
    // slot's address. Borrowed rather than exchanged outright: the `&'a M` we
    // return outlives this body, so there is no point at which the cell
    // permission could be handed back.
    let tracked storage_perm = <pcell_maybe_uninit::PCell<MetaSlotStorage> as CellAddr>::unwrap_ref(
        &metadata_perm.storage_perm,
    );
    let storage = PPtr::<MetaSlotStorage>::from_addr(ptr.addr()).borrow(Tracked(storage_perm));
    vstd_extra::typing::tagged::borrow_as::<META_STORAGE_SIZE, M>(&storage.0.data)
}

pub fn borrow_meta_mut<'a, M: AnyFrameMeta + ByteRepr<META_STORAGE_SIZE>>(
    ptr: PPtr<MetaSlot>,
    Tracked(slot_perm): Tracked<&'a vstd::simple_pptr::PointsTo<MetaSlot>>,
    Tracked(metadata_perms): Tracked<&'a mut MetadataPerm>,
) -> (res: &'a mut M)
    requires
        ptr.addr() == slot_perm.addr(),
        typed_meta_wf::<M>(*slot_perm, *old(metadata_perms)),
    ensures
        *res == typed_meta_value::<M>(*old(metadata_perms)),
        *final(res) == typed_meta_value::<M>(*final(metadata_perms)),
        typed_meta_wf::<M>(*slot_perm, *final(metadata_perms)),
{
    proof {
        MetaSlot::axiom_storage_at_slot_start(*slot_perm);
    }
    let tracked storage_perm = <pcell_maybe_uninit::PCell<MetaSlotStorage> as CellAddr>::unwrap_mut(
        &mut metadata_perms.storage_perm,
    );
    let storage = PPtr::<MetaSlotStorage>::from_addr(ptr.addr()).borrow_mut(Tracked(storage_perm));
    vstd_extra::typing::tagged::borrow_as_mut::<META_STORAGE_SIZE, M>(&mut storage.0.data)
}

impl Inv for MetaSlotOwner {
    open spec fn inv(self) -> bool {
        &&& self.ref_count() == REF_COUNT_UNUSED ==> {
            &&& self.metadata_perm.is_full()
            &&& self.storage_perm().is_uninit()
            &&& self.vtable_ptr_perm().is_uninit()
            &&& self.in_list_perm.value() == 0
            &&& self.paths_in_pt.is_empty()
        }
        &&& self.ref_count() == REF_COUNT_UNIQUE ==> {
            &&& self.metadata_perm.is_resource_vacant()
            &&& self.paths_in_pt.is_empty()
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

/// Writes `metadata` into the byte storage, tagging it so the slot afterwards
/// `holds::<M>()`.
pub exec fn write_metadata_into_storage<M: AnyFrameMeta + ByteRepr<META_STORAGE_SIZE>>(
    cell: &pcell_maybe_uninit::PCell<MetaSlotStorage>,
    Tracked(metadata_perms): Tracked<&mut MetadataPerm>,
    metadata: M,
)
    requires
        cell.id() == old(metadata_perms).storage_perm.id(),
    ensures
        final(metadata_perms).storage_perm.id() == old(metadata_perms).storage_perm.id(),
        final(metadata_perms).storage_perm.is_init(),
        final(metadata_perms).vtable_ptr_perm == old(metadata_perms).vtable_ptr_perm,
        final(metadata_perms).storage_perm.value().holds::<M>(),
        final(metadata_perms).storage_perm.value().value::<M>() == metadata,
{
    // `store` tags the bytes with `recorded_id::<M>()` and discharges the round
    // trip itself, so there is no separate encoding law to invoke here.
    let repr = MetaSlotStorage(
        vstd_extra::typing::tagged::TaggedArray::<META_STORAGE_SIZE>::store(metadata),
    );
    cell.write(Tracked(&mut metadata_perms.storage_perm), repr);
}

} // verus!
