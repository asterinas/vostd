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
use vstd::simple_pptr::PPtr;
use crate::mm::allocator::alloc_page_table;
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

use crate::exec::{
    self, create_new_frame, MAX_FRAME_NUM, get_pte_from_addr_spec, SIZEOF_PAGETABLEENTRY,
    frame_addr_to_index, frame_addr_to_index_spec, MockPageTableEntry, MockPageTablePage,
};
use crate::spec::sub_pt::{pa_is_valid_pt_address, SubPageTable, level_is_in_range, index_pte_paddr};

use crate::mm::NR_ENTRIES;

use super::cursor::spec_helpers;
use super::PageTableConfig;

verus! {

// #[derive(Debug)] // TODO: Debug for PageTableNode
pub type PageTableNode = Frame;

pub struct PageTableGuard<C: PageTableConfig> {
    pub paddr: Paddr,
    pub level: PagingLevel,
    pub phantom: core::marker::PhantomData<C>,
}

impl<C: PageTableConfig> PageTableGuard<C> {
    pub open spec fn wf(&self) -> bool {
        &&& pa_is_valid_pt_address(self.paddr as int)
        &&& level_is_in_range(self.level as int)
    }

    #[verifier::when_used_as_spec(paddr_spec)]
    pub fn paddr(&self) -> Paddr
        returns
            self.paddr_spec(),
    {
        self.paddr
    }

    pub open spec fn paddr_spec(&self) -> Paddr {
        self.paddr
    }

    #[verifier::when_used_as_spec(level_spec)]
    pub fn level(&self) -> PagingLevel
        returns
            self.level_spec(),
    {
        self.level
    }

    pub open spec fn level_spec(&self) -> PagingLevel {
        self.level
    }

    pub fn alloc(level: PagingLevel, Tracked(alloc_model): Tracked<&mut AllocatorModel>) -> (res:
        Self) where Self: Sized
        requires
            old(alloc_model).invariants(),
            level_is_in_range(level as int),
        ensures
            alloc_model.invariants(),
            res.wf(),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use vstd::hash_map::group_hash_map_axioms;

        let (p, Tracked(pt)) = alloc_page_table(Tracked(alloc_model));
        let f = create_new_frame(p.addr(), level);
        p.write(Tracked(&mut pt), f);

        let frame_address = p.addr();

        Self { paddr: frame_address as Paddr, level, phantom: std::marker::PhantomData }
    }

    #[verifier::external_body]
    fn unlock(&mut self) -> PageTableNode {
        todo!()
    }

    pub fn into_raw_paddr(self: Self) -> Paddr where Self: Sized {
        self.paddr
    }

    #[verifier::external_body]
    pub fn from_raw_paddr(paddr: Paddr, level: PagingLevel) -> (res: Self) where Self: Sized
        ensures
            res.wf(),
            res.paddr_spec() == paddr,
            res.level_spec() == level,
    {
        Self { paddr, level, phantom: std::marker::PhantomData }
    }

    #[verifier::external_body]
    fn read_pte(&self, idx: usize, Tracked(spt): Tracked<&SubPageTable>) -> (res: C::E)
        requires
            idx < nr_subpage_per_huge::<C>(),
            spt.wf(),
        ensures
            spt.wf(),
            res.frame_paddr() == get_pte_from_addr_spec(
                index_pte_paddr(self.paddr as int, idx as int) as usize,
                spt,
            ).frame_pa,
            res.pte_paddr() == index_pte_paddr(self.paddr as int, idx as int),
            res.frame_paddr() == 0 ==> !spt.ptes.value().contains_key(
                index_pte_paddr(self.paddr as int, idx as int),
            ),
            res.frame_paddr() != 0 ==> {
                &&& spt.ptes.value().contains_key(res.pte_paddr() as int)
                &&& spt.ptes.value()[res.pte_paddr() as int].frame_pa == res.frame_paddr() as int
                &&& spt.frames.value().contains_key(res.frame_paddr() as int)
            },
    {
        unimplemented!();  // FIXME! use the pptr to read the pte
    }

    fn write_pte(
        &self,
        idx: usize,
        pte: C::E,
        level: PagingLevel,
        Tracked(spt): Tracked<&mut SubPageTable>,
    )
        requires
            idx < nr_subpage_per_huge::<C>(),
            old(spt).wf(),
            old(spt).perms.contains_key(self.paddr),
            self.wf(),
        ensures
            spt.wf(),
            spt.ptes.instance_id() == old(spt).ptes.instance_id(),
            spt.frames.instance_id() == old(spt).frames.instance_id(),
            spec_helpers::spt_do_not_change_above_level(spt, old(spt), self.level()),
    {
        assert(spt.perms.contains_key(self.paddr));

        let p = PPtr::from_addr(self.paddr);
        let tracked points_to = spt.perms.tracked_remove(self.paddr);

        // FIXME: Should be correct since spt.wf()?
        assume(points_to.mem_contents().is_init());
        assume(points_to.pptr() == p);

        let mut frame: MockPageTablePage = p.read(Tracked(&points_to));
        assume(idx < frame.ptes.len());
        frame.ptes[idx] = MockPageTableEntry {
            pte_addr: pte.pte_paddr() as u64,
            frame_pa: pte.frame_paddr() as u64,
            level: level as u8,
            prop: pte.prop(),
        };
        // TODO: P0 currently, the last level frame will cause the inconsistency
        // between spt.perms and spt.frames
        p.write(Tracked(&mut points_to), frame);

        proof {
            spt.perms.tracked_insert(self.paddr, points_to);
        }

        assume(spt.wf());  // TODO: P0
        assume(spec_helpers::spt_do_not_change_above_level(spt, old(spt), self.level()));  // TODO: P0
    }

    #[verifier::external_body]
    pub fn meta(&self) -> &PageTablePageMeta<C> {
        unimplemented!("meta")
    }

    // Note: mutable types not supported.
    // #[verifier::external_body]
    // pub fn nr_children_mut(&mut self) -> &mut u16 {
    //     unimplemented!("nr_children_mut")
    // }
    #[verifier::external_body]
    pub fn nr_children(&self) -> u16 {
        unimplemented!("nr_children")
    }

    pub fn change_children(&self, delta: i16) {
        // TODO: implement this function
    }
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
    pub _phantom: core::marker::PhantomData<C>,
}

impl<C: PageTableConfig> PageTablePageMeta<C> {
    pub fn new_locked(level: PagingLevel) -> Self {
        Self {
            // nr_children: SyncUnsafeCell::new(0),
            // astray: SyncUnsafeCell::new(false),
            nr_children: PCell::new(0u16).0,
            astray: PCell::new(false).0,
            level,
            lock: spin::queued::LockBody::new_locked(),
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
