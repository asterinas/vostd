pub mod child;
pub mod entry;

use std::cell::Cell;
use std::cell::SyncUnsafeCell;
use std::marker::PhantomData;
use std::ops::Range;

use entry::Entry;
use vstd::cell::PCell;
use vstd::prelude::*;

#[allow(unused_imports)]
use child::*;
use vstd::simple_pptr::MemContents;
use crate::mm::meta::AnyFrameMeta;
use crate::mm::nr_subpage_per_huge;
use crate::mm::Paddr;
use crate::mm::PageTableEntryTrait;
use crate::mm::PagingConstsTrait;
use crate::mm::PagingConsts;

use crate::mm::frame::{Frame, allocator::AllocatorModel};
use crate::mm::PagingLevel;

use crate::sync::spin;
// TODO: Use a generic style?
use crate::x86_64::paddr_to_vaddr;

use crate::exec::{self, SubPageTable};
use crate::spec::sub_page_table;

use crate::mm::NR_ENTRIES;

use super::cursor::spec_helpers;
use super::PageTableConfig;

verus! {

// #[derive(Debug)] // TODO: Debug for PageTableNode
pub type PageTableNode = Frame;

// We add PageTableLockTrait to make the verification easier.
// Originally, it is just a struct that holds a frame.
// TODO: Can we also change the source code?
pub trait PageTableLockTrait<C: PageTableConfig>: Sized {
    #[verifier::inline]
    open spec fn wf(&self) -> bool {
        &&& self.paddr() < exec::PHYSICAL_BASE_ADDRESS_SPEC() + exec::SIZEOF_FRAME
            * exec::MAX_FRAME_NUM
    }

    // fn entry(&self, idx: usize) -> Entry<'_, E, C, Self>
    // requires
    //     idx < nr_subpage_per_huge();
    spec fn paddr_spec(&self) -> Paddr;

    #[verifier::when_used_as_spec(paddr_spec)]
    /// Gets the physical address of the page table node.
    fn paddr(&self) -> (res: Paddr)
        ensures
            res == self.paddr_spec(),
    ;

    /// Gets the level of the page table node.
    fn level(&self) -> PagingLevel;

    /// Gets the tracking status of the page table node.
    fn is_tracked(&self) -> MapTrackingStatus;

    fn alloc(
        level: PagingLevel,
        is_tracked: MapTrackingStatus,
        Tracked(alloc_model): Tracked<&mut AllocatorModel>,
    ) -> (res: Self) where Self: Sized
        requires
            old(alloc_model).invariants(),
        ensures
            alloc_model.invariants(),
    ;

    fn unlock(&mut self) -> PageTableNode;

    fn into_raw_paddr(self: Self) -> (res: Paddr) where Self: Sized
        ensures
            res == self.paddr(),
    ;

    fn from_raw_paddr(paddr: Paddr) -> (res: Self) where Self: Sized
        ensures
            res.paddr() == paddr,
            res.wf(),
    ;

    fn nr_children(&self) -> u16;

    fn read_pte(&self, idx: usize, spt: &exec::SubPageTable) -> (res: C::E)
        requires
            idx < nr_subpage_per_huge::<C>(),
            spt.wf(),
        ensures
            spt.wf(),
            res.pte_paddr() == self.paddr() + idx * exec::SIZEOF_PAGETABLEENTRY,
            res.pte_paddr() == exec::get_pte_from_addr_spec(res.pte_paddr(), spt).pte_addr,
            res.frame_paddr() == exec::get_pte_from_addr_spec(res.pte_paddr(), spt).frame_pa,
            res.frame_paddr() == 0 ==> !spt.ptes@.value().contains_key(res.pte_paddr() as int),
            res.frame_paddr() != 0 ==> {
                &&& spt.ptes@.value().contains_key(res.pte_paddr() as int)
                &&& spt.ptes@.value()[res.pte_paddr() as int].frame_pa == res.frame_paddr() as int
                &&& spt.frames@.value().contains_key(res.frame_paddr() as int)
            },
    ;

    fn write_pte(
        &self,
        idx: usize,
        pte: C::E,
        level: PagingLevel,
        spt: &mut SubPageTable,
        Tracked(alloc_model): Tracked<&mut AllocatorModel>,
    )
        requires
            idx < nr_subpage_per_huge::<C>(),
            old(spt).wf(),
            old(alloc_model).invariants(),
        ensures
            spt.wf(),
            alloc_model.invariants(),
            spt.ptes@.instance_id() == old(spt).ptes@.instance_id(),
            spt.frames@.instance_id() == old(spt).frames@.instance_id(),
            spec_helpers::frame_keys_do_not_change(spt, old(spt)),
    ;

    // fn nr_children_mut(&mut self) -> &mut u16;
    fn change_children(&self, delta: i16);

    fn meta(&self) -> &PageTablePageMeta<C>;
}

/// The metadata of any kinds of page table pages.
/// Make sure the the generic parameters don't effect the memory layout.
// #[derive(Debug)] // TODO: Debug for PageTablePageMeta
pub struct PageTablePageMeta<C: PageTableConfig> {
    /// The lock for the page table page.
    pub lock: spin::queued::LockBody,
    /// The number of valid PTEs. It is mutable if the lock is held.
    // TODO: PCell or Cell?
    // pub nr_children: SyncUnsafeCell<u16>,
    pub nr_children: PCell<u16>,
    /// If the page table is detached from its parent.
    ///
    /// A page table can be detached from its parent while still being accessed,
    /// since we use a RCU scheme to recycle page tables. If this flag is set,
    /// it means that the parent is recycling the page table.
    pub astray: PCell<bool>,
    /// The level of the page table page. A page table page cannot be
    /// referenced by page tables of different levels.
    pub level: PagingLevel,
    /// Whether the pages mapped by the node is tracked.
    pub is_tracked: MapTrackingStatus,
    pub _phantom: core::marker::PhantomData<C>,
}

/// Describe if the physical address recorded in this page table refers to a
/// page tracked by metadata.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum MapTrackingStatus {
    /// The page table node cannot contain references to any pages. It can only
    /// contain references to child page table nodes.
    NotApplicable,
    /// The mapped pages are not tracked by metadata. If any child page table
    /// nodes exist, they should also be tracked.
    Untracked,
    /// The mapped pages are tracked by metadata. If any child page table nodes
    /// exist, they should also be tracked.
    Tracked,
}

impl<C: PageTableConfig> PageTablePageMeta<C> {
    pub fn new_locked(level: PagingLevel, is_tracked: MapTrackingStatus) -> Self {
        Self {
            // nr_children: SyncUnsafeCell::new(0),
            // astray: SyncUnsafeCell::new(false),
            nr_children: PCell::new(0u16).0,
            astray: PCell::new(false).0,
            level,
            lock: spin::queued::LockBody::new_locked(),
            is_tracked,
            _phantom: PhantomData,
        }
    }
}

// SAFETY: The layout of the `PageTablePageMeta` is ensured to be the same for
// all possible generic parameters. And the layout fits the requirements.
// unsafe
impl<C: PageTableConfig> AnyFrameMeta for PageTablePageMeta<C> {
    // TODO: Implement AnyFrameMeta for PageTablePageMeta

}

} // verus!
