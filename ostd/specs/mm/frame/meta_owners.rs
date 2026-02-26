//! The model of a metadata slot. It includes:
//! - The model of the metadata slot: `MetaSlotModel`.
//! - The invariants for both MetaSlot and MetaSlotModel.
//! - The primitives for MetaSlot.
use vstd::atomic::*;
use vstd::cell::{self, PCell, PointsTo};
use vstd::prelude::*;
use vstd::simple_pptr::*;

use vstd_extra::cast_ptr::{self, Repr};
use vstd_extra::ghost_tree::TreePath;
use vstd_extra::ownership::*;

use super::*;
use crate::mm::frame::meta::MetaSlot;
use crate::mm::frame::AnyFrameMeta;
use crate::mm::PagingLevel;
use crate::specs::arch::kspace::FRAME_METADATA_RANGE;
use crate::specs::arch::mm::NR_ENTRIES;
use crate::specs::mm::frame::linked_list::linked_list_owners::StoredLink;
use crate::specs::mm::frame::mapping::META_SLOT_SIZE;

use core::marker::PhantomData;

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

pub const REF_COUNT_UNUSED: u64 = u64::MAX;

pub const REF_COUNT_UNIQUE: u64 = u64::MAX - 1;

pub const REF_COUNT_MAX: u64 = i64::MAX as u64;

pub struct StoredPageTablePageMeta {
    pub nr_children: PCell<u16>,
    pub stray: PCell<bool>,
    pub level: PagingLevel,
    pub lock: PAtomicU8,
}

pub enum MetaSlotStorage {
    Empty([u8; 39]),
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
    pub storage: cell::PointsTo<MetaSlotStorage>,
    pub ref_count: PermissionU64,
    pub vtable_ptr: vstd::simple_pptr::PointsTo<usize>,
    pub in_list: PermissionU64,
}

pub tracked struct MetaSlotOwner {
    /// The inner permissions of the metadata slot. When the slot is in use, these will be transferred to its current owner.
    pub inner_perms: Option<MetadataInnerPerms>,
    pub self_addr: usize,
    pub usage: PageUsage,
    pub raw_count: usize,
    pub path_if_in_pt: Option<TreePath<NR_ENTRIES>>,
}

impl Inv for MetaSlotOwner {
    open spec fn inv(self) -> bool {
        &&& self.inner_perms.unwrap().ref_count.value() == REF_COUNT_UNUSED ==> {
            /// An unused slot had better not have any raw pointer hanging around.
            &&& self.raw_count == 0
            &&& self.inner_perms is Some
            &&& self.inner_perms.unwrap().storage.is_uninit()
            &&& self.inner_perms.unwrap().vtable_ptr.is_uninit()
            &&& self.inner_perms.unwrap().in_list.value() == 0
        }
        &&& self.inner_perms.unwrap().ref_count.value() == REF_COUNT_UNIQUE ==> {
            &&& self.inner_perms.unwrap().vtable_ptr.is_init()
        }
        &&& 0 < self.inner_perms.unwrap().ref_count.value() <= REF_COUNT_MAX ==> {
            &&& self.inner_perms.unwrap().vtable_ptr.is_init()
        }
        &&& REF_COUNT_MAX <= self.inner_perms.unwrap().ref_count.value() < REF_COUNT_UNUSED ==> { false }
        &&& self.inner_perms.unwrap().ref_count.value() == 0 ==> {
            // If we ever have 0 ref count, there had better be a `ManuallyDrop` somewhere keeping us from getting garbage collected.
            &&& self.raw_count > 0
            &&& self.inner_perms.unwrap().vtable_ptr.is_uninit()
            &&& self.inner_perms.unwrap().in_list.value() == 0
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
                &&& self.vtable_ptr.is_uninit()
                &&& self.in_list == 0
            },
            _ if self.ref_count < REF_COUNT_MAX => { &&& self.vtable_ptr.is_init() },
            _ => { false },
        }
    }
}

impl View for MetaSlotOwner {
    type V = MetaSlotModel;

    open spec fn view(&self) -> Self::V {
        let storage = self.inner_perms.unwrap().storage.mem_contents();
        let ref_count = self.inner_perms.unwrap().ref_count.value();
        let vtable_ptr = self.inner_perms.unwrap().vtable_ptr.mem_contents();
        let in_list = self.inner_perms.unwrap().in_list.value();
        let self_addr = self.self_addr;
        let usage = self.usage;
        let status = match ref_count {
            REF_COUNT_UNUSED => MetaSlotStatus::UNUSED,
            REF_COUNT_UNIQUE => MetaSlotStatus::UNIQUE,
            0 => MetaSlotStatus::UNDER_CONSTRUCTION,
            _ if ref_count < REF_COUNT_MAX => MetaSlotStatus::SHARED,
            _ => MetaSlotStatus::OVERFLOW,
        };
        MetaSlotModel { status, storage, ref_count, vtable_ptr, in_list, self_addr, usage }
    }
}

impl InvView for MetaSlotOwner {
    proof fn view_preserves_inv(self) {
    }
}

impl OwnerOf for MetaSlot {
    type Owner = MetaSlotOwner;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& owner.inner_perms is Some
        &&& self.storage.id() == owner.inner_perms.unwrap().storage.id()
        &&& self.ref_count.id() == owner.inner_perms.unwrap().ref_count.id()
        &&& self.vtable_ptr == owner.inner_perms.unwrap().vtable_ptr.pptr()
        &&& self.in_list.id() == owner.inner_perms.unwrap().in_list.id()
    }
}

impl ModelOf for MetaSlot {

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
    pub uninterp spec fn metadata_from_inner_perms(perm: cell::PointsTo<MetaSlotStorage>) -> M;
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage>> Repr<MetaSlot> for Metadata<M> {
    type Perm = MetadataInnerPerms;

    open spec fn wf(r: MetaSlot, perm: MetadataInnerPerms) -> bool {
        &&& perm.storage.id() == r.storage.id()
        &&& perm.ref_count.id() == r.ref_count.id()
        &&& perm.vtable_ptr.pptr() == r.vtable_ptr
        &&& perm.in_list.id() == r.in_list.id()
    }

    uninterp spec fn to_repr_spec(self, perm: MetadataInnerPerms) -> (MetaSlot, MetadataInnerPerms);

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
        admit()
    }

    proof fn to_from_repr(r: MetaSlot, perm: MetadataInnerPerms) {
        admit()
    }

    proof fn to_repr_wf(self, perm: MetadataInnerPerms) {
        admit()
    }
}

/// A permission token for frame metadata.
///
/// [`Frame<M>`] the high-level representation of the low-level pointer
/// to the [`super::meta::MetaSlot`].
pub type MetaPerm<M: AnyFrameMeta + Repr<MetaSlotStorage>> = cast_ptr::PointsTo<MetaSlot, Metadata<M>>;


} // verus!
