mod rcu;
mod rw;
mod test_map;

use vstd::{invariant, prelude::*};
use core::num;
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::{Mutex, OnceLock};

use vstd::tokens::*;

use crate::mm::allocator::{self, AllocatorModel, pa_is_valid_kernel_address};
use crate::mm::cursor::spec_helpers;
use crate::mm::entry::Entry;
use crate::mm::page_prop::{PageFlags, PageProperty, PrivilegedPageFlags};
use crate::mm::page_table::PageTableNode;

use crate::mm::{page_size_spec, pte_index, Paddr, PageTableConfig, PagingLevel, NR_ENTRIES};
use crate::{
    mm::{
        cursor::{Cursor, CursorMut},
        meta::{AnyFrameMeta, MetaSlot},
        page_prop, Frame, PageTableEntryTrait, PageTablePageMeta, PagingConsts, PagingConstsTrait,
        Vaddr, MAX_USERSPACE_VADDR, NR_LEVELS, PAGE_SIZE,
    },
    task::{disable_preempt, DisabledPreemptGuard},
};
use vstd::simple_pptr::*;

use crate::exec;
use crate::spec::sub_pt::{pa_is_valid_pt_address, SubPageTable};

verus! {

pub const SIZEOF_PAGETABLEENTRY: usize = 24;

global layout MockPageTableEntry is size == 24, align == 8;

pub const SIZEOF_FRAME: usize = SIZEOF_PAGETABLEENTRY * 512;

global layout MockPageTablePage is size == 12288, align == 8;

pub use crate::mm::frame::allocator::MAX_FRAME_NUM;

// TODO: This is a mock implementation of the page table entry.
// Maybe it should be replaced with the actual implementation, e.g., x86_64.
#[derive(Copy, Clone)]
pub struct MockPageTableEntry {
    pub pte_addr: u64,  // 8 bytes
    pub frame_pa: u64,  // 8 bytes
    pub prop: PageProperty,  // 3 bytes
    pub level: u8,  // 1 byte
}

#[derive(Copy, Clone)]
pub struct MockPageTablePage {
    pub ptes: [MockPageTableEntry; NR_ENTRIES],
}

#[verifier::external_body]
pub fn alloc_page_table<C: PageTableConfig>(
    level: PagingLevel,
    Tracked(model): Tracked<&mut AllocatorModel<PageTablePageMeta<C>>>,
) -> (res: (Frame<PageTablePageMeta<C>>, Tracked<PointsTo<MockPageTablePage>>))
    requires
        old(model).invariants(),
        crate::spec::sub_pt::level_is_in_range::<C>(level as int),
    ensures
        res.1@.pptr() == res.0.ptr,
        res.1@.mem_contents().is_init(),
        pa_is_valid_kernel_address(res.0.start_paddr() as int),
        model.invariants(),
        !old(model).meta_map.contains_key(res.0.start_paddr() as int),
        model.meta_map.contains_key(res.0.start_paddr() as int),
        model.meta_map[res.0.start_paddr() as int].pptr() == res.0.meta_ptr,
        model.meta_map[res.0.start_paddr() as int].value().level == level,
        forall|i: int|
            #![trigger res.1@.value().ptes[i]]
            0 <= i < NR_ENTRIES ==> {
                &&& res.1@.value().ptes[i].pte_addr == (res.0.start_paddr() + i
                    * SIZEOF_PAGETABLEENTRY) as u64
                &&& res.1@.value().ptes[i].frame_pa == 0
                &&& res.1@.value().ptes[i].level == level
                &&& res.1@.value().ptes[i].prop == PageProperty::new_absent()
            },
        res.0.start_paddr() % page_size_spec::<C>(level) == 0,
        // old model does not change
        forall|pa: Paddr| #[trigger]
            old(model).meta_map.contains_key(pa as int) ==> #[trigger] model.meta_map.contains_key(
                pa as int,
            ),
        forall|p: Paddr|
            old(model).meta_map.contains_key(p as int) ==> {
                &&& model.meta_map.contains_key(p as int)
                &&& (#[trigger] model.meta_map[p as int]).pptr() == old(
                    model,
                ).meta_map[p as int].pptr()
                &&& model.meta_map[p as int].value() == old(model).meta_map[p as int].value()
            },
{
    let (frame, perm) = allocator::alloc(
        |a| a.alloc(PageTablePageMeta::<C>::new(level), Tracked(model)),
    );

    let mut ptes = [MockPageTableEntry {
        pte_addr: 0,
        frame_pa: frame.start_paddr() as u64,
        level,
        prop: PageProperty::new_absent(),
    };NR_ENTRIES];

    for i in 0..NR_ENTRIES
        invariant
            0 <= i <= NR_ENTRIES,
            forall|j: int|
                #![trigger ptes[j]]
                0 <= j < i ==> {
                    &&& ptes[j].pte_addr == (frame.start_paddr() + j * SIZEOF_PAGETABLEENTRY) as u64
                    &&& ptes[j].frame_pa == 0
                    &&& ptes[j].level == level
                    &&& ptes[j].prop == PageProperty::new_absent()
                },
        decreases NR_ENTRIES - i,
    {
        ptes[i].pte_addr = (frame.start_paddr() + i * SIZEOF_PAGETABLEENTRY) as u64;
    }

    frame.ptr.write(Tracked(perm.borrow_mut()), MockPageTablePage { ptes });

    (frame, perm)
}

impl PageTableEntryTrait for MockPageTableEntry {
    fn is_present(&self) -> bool {
        self.frame_pa != 0
    }

    open spec fn is_present_spec(&self) -> bool {
        self.frame_pa != 0
    }

    fn frame_paddr(&self) -> (res: usize) {
        self.frame_pa as usize
    }

    open spec fn frame_paddr_spec(&self) -> Paddr {
        self.frame_pa as Paddr
    }

    #[verifier::external_body]
    fn is_last(&self, level: u8) -> bool {
        level == 1
    }

    fn new_page(
        paddr: crate::mm::Paddr,
        level: crate::mm::PagingLevel,
        prop: crate::mm::page_prop::PageProperty,
    ) -> Self {
        // NOTE: this function currently does not create a actual page table entry
        MockPageTableEntry {
            pte_addr: 0,
            frame_pa: 0,
            level: 0,  // let's use level 0 represent a page
            prop,
        }
    }

    #[verifier::external_body]
    fn new_pt(paddr: crate::mm::Paddr) -> Self {
        MockPageTableEntry {
            pte_addr: 0,  // invalid
            frame_pa: paddr as u64,
            level: 0,  // invalid
            prop: PageProperty {
                has_map: true,
                flags: PageFlags::R(),
                cache: page_prop::CachePolicy::Uncacheable,
                priv_flags: PrivilegedPageFlags::empty(),
            },
        }
    }

    #[verifier::external_body]
    fn new_token(token: crate::mm::vm_space::Token) -> Self {
        todo!()
    }

    #[verifier::external_body]
    fn prop(&self) -> crate::mm::page_prop::PageProperty {
        self.prop.clone()
    }

    open spec fn prop_spec(&self) -> PageProperty {
        self.prop
    }

    #[verifier::external_body]
    fn set_prop(&mut self, prop: crate::mm::page_prop::PageProperty) {
        todo!()
    }

    #[verifier::external_body]
    fn set_paddr(&mut self, paddr: crate::mm::Paddr) {
        todo!()
    }

    #[verifier::external_body]
    fn new_absent() -> Self {
        // Self::default()
        std::unimplemented!()
    }

    fn pte_paddr(&self) -> (res: Paddr) {
        self.pte_addr as Paddr
    }

    open spec fn pte_paddr_spec(&self) -> Paddr {
        self.pte_addr as Paddr
    }

    fn clone_pte(&self) -> (res: Self) {
        MockPageTableEntry {
            pte_addr: self.pte_addr,
            frame_pa: self.frame_pa,
            level: self.level,
            prop: self.prop,
        }
    }
}

#[verifier::external_body]
pub fn main_test() {
    test_map::test(
        0x123,
        PageProperty {
            has_map: true,
            flags: PageFlags::R(),
            cache: page_prop::CachePolicy::Uncacheable,
            priv_flags: PrivilegedPageFlags::empty(),
        },
    )
}

pub open spec fn get_pte_addr_from_va_frame_addr_and_level_spec<C: PagingConstsTrait>(
    va: usize,
    frame_va: usize,
    level: u8,
) -> int {
    let index = pte_index::<C>(va, level);
    let pte_addr = frame_va + index * SIZEOF_PAGETABLEENTRY;
    pte_addr
}

pub open spec fn get_pte_from_addr_spec<C: PageTableConfig>(
    addr: usize,
    spt: &SubPageTable<C>,
) -> (res: MockPageTableEntry)
    recommends
        spt.wf(),
{
    if (spt.ptes.value().contains_key(addr as int)) {
        MockPageTableEntry {
            pte_addr: addr as u64,
            frame_pa: spt.ptes.value()[addr as int].frame_pa as u64,
            level: spt.ptes.value()[addr as int].level as u8,
            prop: spt.ptes.value()[addr as int].prop,
        }
    } else {
        MockPageTableEntry {
            pte_addr: addr as u64,
            frame_pa: 0,
            level: 0,
            prop: PageProperty::new_absent(),
        }
    }
}

pub open spec fn frame_index_to_addr_spec(index: usize) -> usize {
    (PHYSICAL_BASE_ADDRESS_SPEC() + index * SIZEOF_FRAME) as usize
}

#[verifier::when_used_as_spec(frame_index_to_addr_spec)]
pub fn frame_index_to_addr(index: usize) -> (res: usize)
    requires
        (PHYSICAL_BASE_ADDRESS_SPEC() + index * SIZEOF_FRAME) < usize::MAX,
    ensures
        res == frame_index_to_addr_spec(index),
{
    assert((PHYSICAL_BASE_ADDRESS_SPEC() + index * SIZEOF_FRAME) < usize::MAX);
    (PHYSICAL_BASE_ADDRESS() + index * SIZEOF_FRAME) as usize
}

// TODO: can we eliminate division
pub open spec fn frame_addr_to_index_spec(addr: usize) -> usize {
    ((addr - PHYSICAL_BASE_ADDRESS_SPEC()) / SIZEOF_FRAME as int) as usize
}

#[verifier::when_used_as_spec(frame_addr_to_index_spec)]
pub fn frame_addr_to_index(addr: usize) -> (res: usize)
    requires
        addr >= PHYSICAL_BASE_ADDRESS(),
        addr < PHYSICAL_BASE_ADDRESS_SPEC() + SIZEOF_FRAME * MAX_FRAME_NUM,
    ensures
        res == frame_addr_to_index_spec(addr),
        res < MAX_FRAME_NUM,
{
    ((addr - PHYSICAL_BASE_ADDRESS()) / SIZEOF_FRAME) as usize
}

pub open spec fn pte_addr_to_index_spec(pte_addr: usize) -> usize {
    ((pte_addr - ((pte_addr - PHYSICAL_BASE_ADDRESS_SPEC()) / SIZEOF_FRAME as int) * SIZEOF_FRAME)
        / SIZEOF_PAGETABLEENTRY as int) as usize
}

pub open spec fn PHYSICAL_BASE_ADDRESS_SPEC() -> usize {
    0
}

#[allow(unused_imports)]
use std::alloc::{alloc, dealloc, Layout};

#[verifier::external_body]
#[verifier::when_used_as_spec(PHYSICAL_BASE_ADDRESS_SPEC)]
pub fn PHYSICAL_BASE_ADDRESS() -> (res: usize)
    ensures
        res == PHYSICAL_BASE_ADDRESS_SPEC(),
{
    static MAP: OnceLock<Mutex<usize>> = OnceLock::new();
    if MAP.get().is_none() {
        unsafe {
            let layout = Layout::new::<[MockPageTableEntry; 4096]>();
            let mut ptr = alloc(layout);
            MAP.set(Mutex::new(ptr as *mut u8 as usize)).unwrap();
        }

        let mut guard = MAP.get().unwrap().lock().unwrap();
        let res: usize = *guard;
        println!("PHYSICAL_BASE_ADDRESS: {:#x}", res);
    }
    let mut guard = MAP.get().unwrap().lock().unwrap();
    let res: usize = *guard;
    res
}

#[verifier::external_body]
pub fn print_msg(msg: &str, num: &u8) {
    println!("{}: {:#x}", msg, num);
}

#[verifier::external_body]
pub fn print_num(num: usize) {
    println!("print_num: {:#x}", num);
}

} // verus!
