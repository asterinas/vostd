mod rcu;
mod rw;
mod test_map;

use vstd::{invariant, prelude::*};
use core::num;
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::{Mutex, OnceLock};

use vstd::tokens::*;

use crate::mm::allocator::pa_is_valid_kernel_address;
use crate::mm::cursor::spec_helpers;
use crate::mm::entry::Entry;
use crate::mm::page_prop::{PageFlags, PageProperty, PrivilegedPageFlags};
use crate::mm::page_table::PageTableNode;

use crate::mm::{pte_index, Paddr, PageTableConfig, NR_ENTRIES};
use crate::{
    mm::{
        cursor::{Cursor, CursorMut},
        meta::{AnyFrameMeta, MetaSlot},
        page_prop, Frame, PageTableEntryTrait, PageTablePageMeta, PagingConsts, PagingConstsTrait,
        Vaddr, MAX_USERSPACE_VADDR, NR_LEVELS, PAGE_SIZE,
        frame::allocator::{alloc_page_table, AllocatorModel},
    },
    task::{disable_preempt, DisabledPreemptGuard},
};
use vstd::simple_pptr::*;

use crate::exec;
use crate::spec::sub_pt::{pa_is_valid_pt_address, SubPageTable};

verus! {

pub const SIZEOF_PAGETABLEENTRY: usize = 20;

global layout MockPageTableEntry is size == 24, align == 8;

pub const SIZEOF_FRAME: usize = 20 * 512;

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

pub fn create_new_frame(frame_addr: Paddr, level: u8) -> (res: MockPageTablePage)
    requires
        pa_is_valid_kernel_address(frame_addr as int),
    ensures
        res.ptes.len() == NR_ENTRIES,
        forall|i: int|
            0 <= i < NR_ENTRIES ==> #[trigger] res.ptes[i].pte_addr == (frame_addr + i
                * SIZEOF_PAGETABLEENTRY) as u64,
        forall|i: int| 0 <= i < NR_ENTRIES ==> #[trigger] res.ptes[i].frame_pa == 0,
        forall|i: int| 0 <= i < NR_ENTRIES ==> #[trigger] res.ptes[i].level == level as u8,
{
    let mut ptes = [MockPageTableEntry {
        pte_addr: 0,
        frame_pa: 0,
        level: 0,
        prop: PageProperty::new_absent(),
    };NR_ENTRIES];

    for i in 0..NR_ENTRIES
        invariant
            0 <= i <= NR_ENTRIES,
            forall|j: int|
                #![trigger ptes[j]]
                0 <= j < i ==> {
                    &&& ptes[j].pte_addr == (frame_addr + j * SIZEOF_PAGETABLEENTRY) as u64
                    &&& ptes[j].frame_pa == 0
                    &&& ptes[j].level == level
                    &&& ptes[j].prop == PageProperty::new_absent()
                },
        decreases NR_ENTRIES - i,
    {
        assume(frame_addr + i * SIZEOF_PAGETABLEENTRY < usize::MAX);
        ptes[i] = MockPageTableEntry {
            pte_addr: (frame_addr + i * SIZEOF_PAGETABLEENTRY) as u64,
            frame_pa: 0,
            level: level,
            prop: PageProperty::new_absent(),
        };
    }

    MockPageTablePage { ptes }
}

impl PageTableEntryTrait for MockPageTableEntry {
    fn is_present(&self, Tracked(spt): Tracked<&SubPageTable>) -> bool {
        assert(self.frame_pa == self.frame_paddr());
        assert(self.frame_pa != 0 ==> spt.ptes.value().contains_key(self.pte_addr as int));
        assert(self.frame_pa != 0 ==> spt.frames.value().contains_key(self.frame_pa as int)) by {
            admit();
        }  // TODO: P0
        assert(self.frame_pa == 0 ==> !spt.ptes.value().contains_key(self.pte_addr as int)) by {
            admit();
        }  // TODO: P0
        let res = (self.frame_pa != 0);
        assume(res == self.is_present_spec(spt));  // FIXME: Is present is not well-desinged right now.
        res
    }

    open spec fn is_present_spec(&self, spt: &SubPageTable) -> bool {
        spt.ptes.value().contains_key(self.pte_paddr() as int)
    }

    fn frame_paddr(&self) -> (res: usize) {
        self.frame_pa as usize
    }

    open spec fn frame_paddr_spec(&self) -> Paddr {
        self.frame_pa as Paddr
    }

    #[verifier::external_body]
    fn is_last(&self, level: u8) -> bool {
        unimplemented!()
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
        todo!()
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

    open spec fn pte_addr_spec(&self) -> Paddr {
        self.pte_addr as Paddr
    }
}

pub fn main_test() {
    let va = 0;
    let frame = Frame { ptr: 0 };
    let page_prop = PageProperty {
        flags: PageFlags { bits: 0 },
        cache: page_prop::CachePolicy::Uncacheable,
        priv_flags: PrivilegedPageFlags { bits: 0 },
    };

    // test_map::test(va, frame, page_prop);
    // test_map2::test(va, frame, page_prop);
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

pub open spec fn get_pte_from_addr_spec(addr: usize, spt: &SubPageTable) -> (res:
    MockPageTableEntry)
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

#[verifier::external_body]
pub fn get_pte_from_addr(addr: usize, Tracked(spt): Tracked<&SubPageTable>) -> (res:
    MockPageTableEntry)
    requires
        0 <= addr < PHYSICAL_BASE_ADDRESS_SPEC() + SIZEOF_FRAME * NR_ENTRIES,
        (addr - PHYSICAL_BASE_ADDRESS_SPEC()) % SIZEOF_PAGETABLEENTRY as int == 0,
        spt.wf(),
    ensures
        res == get_pte_from_addr_spec(addr, spt),
        res.frame_paddr() == 0 ==> !spt.ptes.value().contains_key(addr as int),
        res.frame_paddr() != 0 ==> {
            &&& spt.ptes.value().contains_key(res.pte_paddr() as int)
            &&& spt.ptes.value()[res.pte_paddr() as int].frame_pa == res.frame_paddr() as int
        },
{
    let pte = PPtr::<MockPageTableEntry>::from_addr(addr).read(Tracked::assume_new());  // TODO: permission violation
    println!("read_pte_from_addr pte_addr: {:#x}, frame_pa: {:#x}, level: {}", pte.pte_addr, pte.frame_pa, pte.level);
    pte
}

// TODO: is this useful?
pub proof fn number_cast(x: usize)
    ensures
        x == x as int as usize,
        x == x as u64 as usize,
{
}

// TODO: is this useful?
pub broadcast proof fn addr_translation(addr: usize)
    requires
        (addr - PHYSICAL_BASE_ADDRESS()) % SIZEOF_FRAME as int == 0,
    ensures
        addr == #[trigger] frame_index_to_addr_spec(#[trigger] frame_addr_to_index_spec(addr)),
{
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
pub fn print_msg(msg: &str, num: usize) {
    println!("{}: {:#x}", msg, num);
}

#[verifier::external_body]
pub fn print_num(num: usize) {
    println!("print_num: {:#x}", num);
}

} // verus!
