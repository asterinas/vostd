use vstd::{atomic::*, cell::pcell_maybe_uninit, prelude::*};
use vstd_extra::{
    cast_ptr::{self, Repr},
    ghost_tree::TreePath,
    ownership::*,
    raw_ptr::{ExposedPointsTo, ptr_from_addr, ptr_ref},
    resource::ghost_resource::count_auth::{Count, CountResource},
};

use crate::specs::{arch::NR_ENTRIES, mm::frame::linked_list::linked_list_owners::StoredLink};

use super::*;
use crate::mm::{
    Paddr, PagingLevel, Vaddr,
    frame::{
        MockFrameMeta, MockUFrameMeta,
        meta::{
            AnyFrameMeta, META_SLOT_SIZE, MetaSlot, REF_COUNT_MAX, REF_COUNT_UNIQUE,
            REF_COUNT_UNUSED, mapping::meta_to_frame,
        },
    },
    kspace::FRAME_METADATA_RANGE,
};

verus! {

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

pub enum MetaSlotStorage {
    Empty([u8; 39]),
    Untyped,
    MockU(MockUFrameMeta),
    Mock(MockFrameMeta),
    FrameLink(StoredLink),
    PTNode(StoredPageTablePageMeta),
}

} // verus!
macro_rules! impl_u32_frame_meta_repr {
    ($meta:ident, $variant:ident, $field:ident) => {
        verus! {
            impl Inv for $meta {
                open spec fn inv(self) -> bool {
                    true
                }
            }

            impl OwnerOf for $meta {
                type Owner = Self;

                open spec fn wf(self, owner: Self) -> bool {
                    self == owner
                }
            }

            impl Repr<MetaSlotStorage> for $meta {
                open spec fn wf(r: MetaSlotStorage) -> bool {
                    r is $variant
                }

                fn to_repr(self) -> MetaSlotStorage {
                    MetaSlotStorage::$variant(self)
                }

                open spec fn from_repr_spec(r: MetaSlotStorage) -> Self {
                    r->$field
                }

                fn from_borrowed<'a>(r: &'a MetaSlotStorage) -> &'a Self {
                    match r {
                        MetaSlotStorage::$variant(meta) => meta,
                        _ => unreachable!(),
                    }
                }

                fn from_borrowed_mut<'a>(r: &'a mut MetaSlotStorage) -> &'a mut Self {
                    match r {
                        MetaSlotStorage::$variant(meta) => meta,
                        _ => unreachable!(),
                    }
                }
            }
        }
    };
}

impl_u32_frame_meta_repr!(MockUFrameMeta, MockU, MockU_0);
impl_u32_frame_meta_repr!(MockFrameMeta, Mock, Mock_0);

verus! {

// SAFETY: The default `on_drop` callback does not access frame memory.
unsafe impl AnyFrameMeta for MockUFrameMeta {
    uninterp spec fn vtable_ptr(&self) -> usize;

    fn is_untyped(&self) -> bool
        returns
            true,
    {
        true
    }
}

impl crate::mm::frame::untyped::AnyUFrameMeta for MockUFrameMeta {

}

// SAFETY: The default `on_drop` callback does not access frame memory.
unsafe impl AnyFrameMeta for MockFrameMeta {
    uninterp spec fn vtable_ptr(&self) -> usize;
}

impl MetaSlotStorage {
    /// The purpose established by the installed metadata representation.
    pub open spec fn usage(self) -> PageUsage {
        if self is PTNode {
            PageUsage::PageTable
        } else {
            PageUsage::Frame
        }
    }
}

/// `MetaSlotStorage` is an inductive tagged union of all of the frame meta types that
/// we work with in this development. So, it should itself implement `AnyFrameMeta`, and
/// it can then be used to stand in for `dyn AnyFrameMeta`.
unsafe impl AnyFrameMeta for MetaSlotStorage {
    uninterp spec fn vtable_ptr(&self) -> usize;
}

impl Repr<MetaSlotStorage> for MetaSlotStorage {
    open spec fn wf(slot: MetaSlotStorage) -> bool {
        true
    }

    open spec fn from_repr_spec(slot: MetaSlotStorage) -> Self {
        slot
    }

    fn to_repr(self) -> MetaSlotStorage {
        self
    }

    fn from_borrowed<'a>(slot: &'a MetaSlotStorage) -> &'a Self {
        slot
    }

    fn from_borrowed_mut<'a>(slot: &'a mut MetaSlotStorage) -> &'a mut Self {
        slot
    }
}

/// Permissions to access metadata.
pub tracked struct MetadataPerm {
    pub storage_perm: pcell_maybe_uninit::PointsTo<MetaSlotStorage>,
    pub vtable_ptr_perm: vstd::simple_pptr::PointsTo<usize>,
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
}

/// Well-formedness of a concrete metadata representation.
pub open spec fn typed_meta_wf<M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    slot_perm: ExposedPointsTo<MetaSlot>,
    metadata_perm: MetadataPerm,
) -> bool {
    &&& slot_perm.is_init()
    &&& MetaSlot::perms_related(slot_perm, metadata_perm)
    &&& M::wf(metadata_perm.storage_perm.value())
}

/// The value of a concrete metadata.
pub open spec fn typed_meta_value<M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    metadata_perm: MetadataPerm,
) -> M {
    M::from_repr_spec(metadata_perm.storage_perm.value())
}

pub fn borrow_meta<'a, M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    ptr: cast_ptr::ReprPtr<MetaSlotStorage, M>,
    Tracked(slot_perm): Tracked<&'a ExposedPointsTo<MetaSlot>>,
    Tracked(metadata_perm): Tracked<&'a MetadataPerm>,
) -> &'a M
    requires
        ptr.addr() == slot_perm.addr(),
        typed_meta_wf::<M>(*slot_perm, *metadata_perm),
    returns
        typed_meta_value::<M>(*metadata_perm),
{
    let slot = ptr_ref(
        ptr_from_addr::<MetaSlot>(ptr.addr(), Tracked(slot_perm)),
        Tracked(slot_perm),
    );
    M::from_borrowed(slot.storage.borrow(Tracked(&metadata_perm.storage_perm)))
}

pub fn borrow_meta_mut<'a, M: AnyFrameMeta + Repr<MetaSlotStorage>>(
    ptr: cast_ptr::ReprPtr<MetaSlotStorage, M>,
    Tracked(slot_perm): Tracked<&'a ExposedPointsTo<MetaSlot>>,
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
    let slot = ptr_ref(
        ptr_from_addr::<MetaSlot>(ptr.addr(), Tracked(slot_perm)),
        Tracked(slot_perm),
    );
    M::from_borrowed_mut(slot.storage.borrow_mut(Tracked(&mut metadata_perms.storage_perm)))
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
            &&& !self.metadata_perm.is_resource_vacant()
            &&& self.metadata_perm.frac() + self.ref_count() == REF_COUNT_MAX
            &&& self.vtable_ptr_perm().is_init()
            &&& self.storage_perm().is_init()
            &&& self.in_list_perm.value() == 0
        }
        &&& REF_COUNT_MAX < self.ref_count() < REF_COUNT_UNIQUE ==> { false }
        &&& self.ref_count() == 0 ==> {
            &&& self.metadata_perm.is_full()
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
    metadata: M,
)
    requires
        cell.id() == old(metadata_perms).storage_perm.id(),
    ensures
        final(metadata_perms).storage_perm.id() == old(metadata_perms).storage_perm.id(),
        final(metadata_perms).storage_perm.is_init(),
        final(metadata_perms).vtable_ptr_perm == old(metadata_perms).vtable_ptr_perm,
        M::wf(final(metadata_perms).storage_perm.value()),
        M::from_repr_spec(final(metadata_perms).storage_perm.value()) == metadata,
{
    let repr = metadata.to_repr();
    cell.write(Tracked(&mut metadata_perms.storage_perm), repr);
}

} // verus!
