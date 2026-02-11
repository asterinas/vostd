//! The model of a metadata slot. It includes:
//! - The model of the metadata slot: `MetaSlotModel`.
//! - The invariants for both MetaSlot and MetaSlotModel.
//! - The primitives for MetaSlot.
use vstd::atomic::*;
use vstd::cell;
use vstd::prelude::*;
use vstd::simple_pptr::*;

use vstd_extra::cast_ptr::{self, Repr};
use vstd_extra::ghost_tree::TreePath;
use vstd_extra::ownership::*;

use super::*;
use crate::mm::frame::meta::{MetaSlot, MetaSlotStorage};
use crate::specs::arch::kspace::FRAME_METADATA_RANGE;
use crate::specs::arch::mm::CONST_NR_ENTRIES;
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
#[rustc_has_incoherent_inherent_impls]
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

} // verus!
verus! {

pub tracked struct MetaSlotOwner {
    pub storage: PointsTo<MetaSlotStorage>,
    pub ref_count: PermissionU64,
    pub vtable_ptr: PointsTo<usize>,
    pub in_list: PermissionU64,
    pub self_addr: usize,
    pub usage: PageUsage,
    pub path_if_in_pt: Option<TreePath<CONST_NR_ENTRIES>>,
}

impl Inv for MetaSlotOwner {
    open spec fn inv(self) -> bool {
        &&& self.ref_count.value() == REF_COUNT_UNUSED ==> {
            &&& self.vtable_ptr.is_uninit()
            &&& self.in_list.value() == 0
        }
        &&& self.ref_count.value() == REF_COUNT_UNIQUE ==> {
            &&& self.vtable_ptr.is_init()
        }
        &&& 0 < self.ref_count.value() < REF_COUNT_MAX ==> {
            &&& self.vtable_ptr.is_init()
        }
        &&& REF_COUNT_MAX <= self.ref_count.value() < REF_COUNT_UNUSED ==> { false }
        &&& self.ref_count.value() == 0 ==> {
            &&& self.vtable_ptr.is_uninit()
            &&& self.in_list.value() == 0
        }
        &&& FRAME_METADATA_RANGE().start <= self.self_addr < FRAME_METADATA_RANGE().end
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
        let storage = self.storage.mem_contents();
        let ref_count = self.ref_count.value();
        let vtable_ptr = self.vtable_ptr.mem_contents();
        let in_list = self.in_list.value();
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
        &&& self.storage == owner.storage.pptr()
        &&& self.ref_count.id() == owner.ref_count.id()
        &&& self.vtable_ptr == owner.vtable_ptr.pptr()
        &&& self.in_list.id() == owner.in_list.id()
    }
}

impl ModelOf for MetaSlot {

}

} // verus!
