mod mapping;
pub use mapping::*;

use vstd::atomic::PAtomicU64;
use vstd::atomic::PAtomicU8;
use vstd::cell::{self, PCell};
use vstd::prelude::*;
use vstd::simple_pptr::{self, PPtr};
use vstd_extra::cast_ptr::*;
use vstd_extra::ownership::*;

use super::*;
use core::ops::Deref;
use std::marker::PhantomData;

verus! {

/// The error type for getting the frame from a physical address.
#[derive(Debug)]
pub enum GetFrameError {
    /// The frame is in use.
    InUse,
    /// The frame is not in use.
    Unused,
    /// The frame is being initialized or destructed.
    Busy,
    /// The frame is private to an owner of [`UniqueFrame`].
    ///
    /// [`UniqueFrame`]: super::unique::UniqueFrame
    Unique,
    /// The provided physical address is out of bound.
    OutOfBound,
    /// The provided physical address is not aligned.
    NotAligned,
    /// Verification only: `compare_exchange` returned `Err`, retry
    Retry,
}

pub open spec fn get_slot_spec(paddr: Paddr) -> (res: PPtr<MetaSlot>)
    recommends
        paddr % 4096 == 0,
        paddr < MAX_PADDR(),
{
    let slot = frame_to_meta(paddr);
    PPtr(slot, PhantomData::<MetaSlot>)
}

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

/*
// TODO: figure out how this can actually be done (the issue is that Verus cells aren't clonable)
impl Clone for MetaSlotStorage {
    #[verifier::external_body]
    fn clone(&self) -> Self {
        unimplemented!()
    }
}
*/

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

/// `MetaSlotStorage` is an inductive tagged union of all of the frame meta types that
/// we work with in this development. So, it should itself implement `AnyFrameMeta`, and
/// it can then be used to stand in for `dyn AnyFrameMeta`.
impl AnyFrameMeta for MetaSlotStorage {
    uninterp spec fn vtable_ptr(&self) -> usize;
}

#[rustc_has_incoherent_inherent_impls]
pub struct MetaSlot {
    pub storage: PPtr<MetaSlotStorage>,
    pub ref_count: PAtomicU64,
    pub vtable_ptr: PPtr<usize>,
    pub in_list: PAtomicU64,
}

//global layout MetaSlot is size == 64, align == 8;
pub broadcast proof fn lemma_meta_slot_size()
    ensures
        #[trigger] size_of::<MetaSlot>() == META_SLOT_SIZE(),
{
    admit()
}

pub proof fn size_of_meta_slot()
    ensures
        size_of::<MetaSlot>() == 64,
        align_of::<MetaSlot>() == 8,
{
    admit()
}

#[inline(always)]
#[verifier::allow_in_spec]
pub const fn meta_slot_size() -> (res: usize)
    returns
        64usize,
{
    proof {
        size_of_meta_slot();
    }
    size_of::<MetaSlot>()
}

impl MetaSlot {
    // These are the axioms for casting meta slots into other things
    /// This is the equivalent of &self as *const as Vaddr, but we need to axiomatize it.
    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub fn addr_of(&self, Tracked(perm): Tracked<&vstd::simple_pptr::PointsTo<MetaSlot>>) -> Paddr
        requires
            self == perm.value(),
        returns
            perm.addr(),
    {
        unimplemented!()
    }

    pub fn cast_slot<T: Repr<MetaSlot>>(
        &self,
        addr: usize,
        Tracked(perm): Tracked<&vstd::simple_pptr::PointsTo<MetaSlot>>,
    ) -> (res: ReprPtr<MetaSlot, T>)
        requires
            perm.value() == self,
            addr == perm.addr(),
        ensures
            res.ptr.addr() == addr,
            res.addr == addr,
    {
        ReprPtr::<MetaSlot, T> { addr: addr, ptr: PPtr::from_addr(addr), _T: PhantomData }
    }

    pub fn cast_perm<T: Repr<MetaSlot>>(
        addr: usize,
        Tracked(perm): Tracked<vstd::simple_pptr::PointsTo<MetaSlot>>,
    ) -> Tracked<PointsTo<MetaSlot, T>> {
        Tracked(PointsTo { addr: addr, points_to: perm, _T: PhantomData })
    }
}

/// Space-holder of the AnyFrameMeta virtual table.
pub trait AnyFrameMeta: Repr<MetaSlot> {
    exec fn on_drop(&mut self) {
    }

    exec fn is_untyped(&self) -> bool {
        false
    }

    spec fn vtable_ptr(&self) -> usize;
}

impl Repr<MetaSlot> for MetaSlotStorage {
    uninterp spec fn wf(slot: mm::frame::meta::MetaSlot) -> bool;

    uninterp spec fn to_repr_spec(self) -> mm::frame::meta::MetaSlot;
    
    #[verifier::external_body]
    fn to_repr(self) -> mm::frame::meta::MetaSlot { todo!() }
    
    uninterp spec fn from_repr_spec(slot: mm::frame::meta::MetaSlot) -> Self;
    
    #[verifier::external_body]
    fn from_repr(slot: mm::frame::meta::MetaSlot) -> Self { todo!() }
    
    #[verifier::external_body]
    fn from_borrowed<'a>(slot: &'a mm::frame::meta::MetaSlot) -> &'a Self { todo!() }
    
    proof fn from_to_repr(self) { admit() }
    
    proof fn to_from_repr(slot: mm::frame::meta::MetaSlot) { admit() }
    
    proof fn to_repr_wf(self) { admit() }
}

} // verus!
