mod rw;
mod test_map;

use vstd::prelude::*;
use core::num;
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::{Mutex, OnceLock};

use vstd::tokens::*;

use crate::mm::cursor::spec_helpers;
use crate::mm::entry::Entry;
use crate::mm::page_prop::{PageFlags, PageProperty, PrivilegedPageFlags};
use crate::mm::page_table::PageTableNode;

use crate::mm::{pte_index, Paddr, PageTableConfig, NR_ENTRIES};
use crate::{
    mm::{
        cursor::{Cursor, CursorMut},
        meta::{AnyFrameMeta, MetaSlot},
        page_prop, Frame, PageTableEntryTrait, PageTableLockTrait, PageTablePageMeta, PagingConsts,
        PagingConstsTrait, Vaddr, MAX_USERSPACE_VADDR, NR_LEVELS, PAGE_SIZE,
        frame::allocator::{alloc_page_table, AllocatorModel},
    },
    spec::sub_page_table,
    task::{disable_preempt, DisabledPreemptGuard},
};
use vstd::simple_pptr::*;

use crate::exec;

verus! {

pub const SIZEOF_PAGETABLEENTRY: usize = 24;

global layout MockPageTableEntry is size == 24, align == 8;

pub const SIZEOF_FRAME: usize = 24 * 512;

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
    ensures
        res.ptes.len() == NR_ENTRIES,
        forall|i: int|
            0 <= i < NR_ENTRIES ==> #[trigger] res.ptes[i].pte_addr == frame_addr + i
                * SIZEOF_PAGETABLEENTRY as u64,
        forall|i: int| 0 <= i < NR_ENTRIES ==> #[trigger] res.ptes[i].frame_pa == 0,
        forall|i: int| 0 <= i < NR_ENTRIES ==> #[trigger] res.ptes[i].level == level as u8,
{
    let mut ptes = [MockPageTableEntry {
        pte_addr: 0,
        frame_pa: 0,
        level: 0,
        prop: PageProperty::new_absent(),
    };NR_ENTRIES];
    for i in 0..NR_ENTRIES {
        assume(frame_addr + i * SIZEOF_PAGETABLEENTRY < usize::MAX as u64);
        ptes[i] = MockPageTableEntry {
            pte_addr: (frame_addr + i * SIZEOF_PAGETABLEENTRY) as u64,
            frame_pa: 0,
            level: level,
            prop: PageProperty::new_absent(),
        };
    }

    let f = MockPageTablePage { ptes };

    // assert(ptes[0].frame_pa == 0); // TODO: don't know why this fails
    assume(forall|i: int|
        0 <= i < NR_ENTRIES ==> (#[trigger] ptes[i]).pte_addr == frame_addr as u64 + i as u64
            * SIZEOF_PAGETABLEENTRY as u64);
    assume(forall|i: int| 0 <= i < NR_ENTRIES ==> (#[trigger] ptes[i]).frame_pa == 0);
    assume(forall|i: int| 0 <= i < NR_ENTRIES ==> (#[trigger] ptes[i]).level == level);

    f
}

impl PageTableEntryTrait for MockPageTableEntry {
    fn is_present(&self, spt: &SubPageTable) -> bool {
        assert(self.frame_pa == self.frame_paddr());
        assert(self.frame_pa != 0 ==> spt.ptes@.value().contains_key(self.pte_addr as int));
        assert(self.frame_pa != 0 ==> spt.frames@.value().contains_key(self.frame_pa as int)) by {
            admit();
        }  // TODO: P0
        assert(self.frame_pa == 0 ==> !spt.ptes@.value().contains_key(self.pte_addr as int)) by {
            admit();
        }  // TODO: P0
        self.frame_pa != 0
    }

    open spec fn is_present_spec(&self, spt: &SubPageTable) -> bool {
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

    #[verifier::external_body]
    fn as_usize(self) -> usize {
        // SAFETY: `Self` is `Pod` and has the same memory representation as `usize`.
        // unsafe { transmute_unchecked(self) }
        // TODO: Implement this function
        std::unimplemented!()
    }

    fn from_usize(pte_raw: usize, spt: &SubPageTable) -> (res: Self)
        ensures
            res == get_pte_from_addr(pte_raw, spt),
            res.frame_paddr() == 0 ==> !spt.ptes@.value().contains_key(pte_raw as int),
            res.frame_paddr() != 0 ==> {
                &&& spt.ptes@.value().contains_key(res.pte_paddr() as int)
                &&& spt.ptes@.value()[res.pte_paddr() as int].frame_pa == res.frame_paddr() as int
                &&& spt.frames@.value().contains_key(res.frame_paddr() as int)
            },
    {
        assert(0 <= pte_raw < PHYSICAL_BASE_ADDRESS_SPEC() + SIZEOF_PAGETABLEENTRY * NR_ENTRIES)
            by {
            admit();
        }  // TODO
        assert((pte_raw - PHYSICAL_BASE_ADDRESS_SPEC()) % SIZEOF_PAGETABLEENTRY as int == 0) by {
            admit();
        }  // TODO
        assert(spt.wf());
        let res = get_pte_from_addr(pte_raw, spt);
        assert(spt.ptes@.value().contains_key(pte_raw as int) ==> res.frame_pa != 0) by {
            // NOTE: this seems not true if we do not add the invariant (convert the frame_pa to u64) in spt.wf() @see spt.wf()
            // assert(spt.ptes@.value()[res.pte_addr as int].frame_pa != 0 ==> spt.ptes@.value()[res.pte_addr as int].frame_pa as u64 != 0);
        }
        assert(res.frame_pa == 0 ==> !spt.ptes@.value().contains_key(res.pte_addr as int));
        if (res.frame_pa != 0) {
            assert(spt.frames@.value().contains_key(res.frame_pa as int)) by {
                assert(spt.ptes@.value().contains_key(res.pte_addr as int));
                assert(spt.ptes@.value()[res.pte_paddr() as int].frame_pa == res.frame_pa as int);
            }
        }
        res
    }

    fn pte_paddr(&self) -> (res: Paddr) {
        self.pte_addr as Paddr
    }

    open spec fn pte_addr_spec(&self) -> Paddr {
        self.pte_addr as Paddr
    }
}

pub struct SimpleFrameMeta {}

impl AnyFrameMeta for SimpleFrameMeta {

}

// TODO: This FakePageTableLock will ignore Entry and MetaSlot.
// TODO: We possibly need to use PageTableNode later.
pub struct FakePageTableLock<C: PageTableConfig> {
    pub paddr: Paddr,
    pub phantom: std::marker::PhantomData<(C)>,
}

impl<C: PageTableConfig> PageTableLockTrait<C> for FakePageTableLock<C> {
    // #[verifier::external_body]
    // fn entry(&self, idx: usize) -> crate::mm::entry::Entry<'_, C, Self> {
    //     Entry::new_at(self, idx)
    // }
    fn paddr(&self) -> crate::mm::Paddr {
        self.paddr
    }

    fn alloc(
        level: crate::mm::PagingLevel,
        is_tracked: crate::mm::MapTrackingStatus,
        Tracked(alloc_model): Tracked<&mut AllocatorModel>,
    ) -> (res: Self) where Self: Sized {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use vstd::hash_map::group_hash_map_axioms;

        let (p, Tracked(pt)) = alloc_page_table(Tracked(alloc_model));
        let f = create_new_frame(p.addr(), level);
        p.write(Tracked(&mut pt), f);

        let frame_address = p.addr();
        let frame_num = frame_addr_to_index(frame_address);

        assert(0 <= frame_num < MAX_FRAME_NUM as usize);

        print_msg("alloc frame", frame_address);

        FakePageTableLock { paddr: frame_address as Paddr, phantom: std::marker::PhantomData }
    }

    #[verifier::external_body]
    fn unlock(&mut self) -> PageTableNode {
        todo!()
    }

    fn into_raw_paddr(self: Self) -> crate::mm::Paddr where Self: Sized {
        self.paddr
    }

    #[verifier::external_body]
    fn from_raw_paddr(paddr: crate::mm::Paddr) -> Self where Self: Sized {
        FakePageTableLock { paddr, phantom: std::marker::PhantomData }
    }

    #[verifier::external_body]
    fn nr_children(&self) -> u16 {
        todo!()
    }

    fn read_pte(&self, idx: usize, spt: &exec::SubPageTable) -> (res: C::E)
        ensures
            spt.wf(),
            res.frame_paddr() == get_pte_from_addr_spec(
                (self.paddr + idx * SIZEOF_PAGETABLEENTRY) as usize,
                spt,
            ).frame_pa,
            res.pte_paddr() == (self.paddr + idx * SIZEOF_PAGETABLEENTRY) as usize,
            res.frame_paddr() == 0 ==> !spt.ptes@.value().contains_key(
                self.paddr + idx * SIZEOF_PAGETABLEENTRY as int,
            ),
            res.frame_paddr() != 0 ==> {
                &&& spt.ptes@.value().contains_key(res.pte_paddr() as int)
                &&& spt.ptes@.value()[res.pte_paddr() as int].frame_pa == res.frame_paddr() as int
                &&& spt.frames@.value().contains_key(res.frame_paddr() as int)
            },
    {
        assert(self.paddr + idx * SIZEOF_PAGETABLEENTRY < usize::MAX) by {
            admit();
        }  // TODO
        C::E::from_usize(self.paddr + idx * SIZEOF_PAGETABLEENTRY, spt)
    }

    fn write_pte(
        &self,
        idx: usize,
        pte: C::E,
        level: crate::mm::PagingLevel,
        spt: &mut SubPageTable,
        Tracked(alloc_model): Tracked<&mut AllocatorModel>,
    ) {
        assume(self.paddr < PHYSICAL_BASE_ADDRESS_SPEC() + SIZEOF_FRAME * MAX_FRAME_NUM);
        let frame_idx = frame_addr_to_index(self.paddr);

        assume(frame_idx < MAX_FRAME_NUM as usize);  // TODO: P0
        assume(spt.perms@[frame_idx].1@.mem_contents().is_init());  // TODO: P0

        assume(spt.perms@.contains_key(frame_idx));
        let (p, Tracked(points_to)) = spt.perms.remove(&frame_idx).unwrap();

        assume(points_to.pptr() == p);
        let mut frame = p.read(Tracked(&points_to));
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

        spt.perms.insert(frame_idx, (p, Tracked(points_to)));

        assume(spt.wf());  // TODO: P0
        assume(spec_helpers::frame_keys_do_not_change(spt, old(spt)));  // TODO: P0
    }

    #[verifier::external_body]
    fn meta(&self) -> &PageTablePageMeta<C> {
        unimplemented!("meta")
    }

    // #[verifier::external_body]
    // fn nr_children_mut(&mut self) -> &mut u16 {
    //     todo!()
    // }
    fn change_children(&self, delta: i16) {
        // TODO: implement this function
    }

    fn is_tracked(&self) -> crate::mm::MapTrackingStatus {
        crate::mm::MapTrackingStatus::Tracked
    }

    open spec fn paddr_spec(&self) -> Paddr {
        self.paddr as Paddr
    }

    #[verifier::external_body]
    fn level(&self) -> crate::mm::PagingLevel {
        // TODO: currently we cannot get level from the page table lock because the meta data is not modeled
        unimplemented!("PageTableLock::level")
    }
}

struct_with_invariants!{
    /// A sub-tree in a page table.
    pub struct SubPageTable {
        /// Only frames in the sub-page-table are stored in this map.
        pub perms: HashMap<usize, (PPtr<MockPageTablePage>, Tracked<PointsTo<MockPageTablePage>>)>,
        // State machine.
        pub frames: Tracked<sub_page_table::SubPageTableStateMachine::frames>,
        pub ptes: Tracked<sub_page_table::SubPageTableStateMachine::ptes>,
        pub instance: Tracked<sub_page_table::SubPageTableStateMachine::Instance>,
    }

    pub open spec fn wf(&self) -> bool {
        predicate {
            &&& self.frames@.instance_id() == self.instance@.id()
            &&& self.ptes@.instance_id() == self.instance@.id()
            &&& self.perms@.dom().finite()
            &&& forall |i: usize| #[trigger] self.perms@.dom().contains(i) ==> {
                &&& #[trigger] self.frames@.value().contains_key(i as int)
                &&& i < PHYSICAL_BASE_ADDRESS() + SIZEOF_FRAME * MAX_FRAME_NUM
            }
            &&& forall |i: usize| #[trigger] self.frames@.value().contains_key(i as int) ==> {
                &&& #[trigger] self.perms@.dom().contains(i)
                &&& i < PHYSICAL_BASE_ADDRESS() + SIZEOF_FRAME * MAX_FRAME_NUM
            }
            &&& forall |i: usize| #[trigger] self.perms@.dom().contains(i) ==> {
                &&& (#[trigger] self.perms@[i]).1@.pptr() == self.perms@[i].0
                &&& (#[trigger] self.perms@[i].0.addr() == PHYSICAL_BASE_ADDRESS() as usize + i * SIZEOF_FRAME)
                &&& (#[trigger] self.perms@[i].1@.mem_contents().is_init())
                &&& (#[trigger] self.frames@.value().contains_key(frame_index_to_addr(i) as int))
                &&& forall |k: int| 0 <= k < NR_ENTRIES ==>
                    if (self.perms@[i].1@.value().ptes[k].frame_pa != 0) {
                        #[trigger] self.ptes@.value().contains_key(self.perms@[i].1@.value().ptes[k].pte_addr as int)
                    } else {
                        !self.ptes@.value().contains_key(self.perms@[i].1@.mem_contents().value().ptes[k].pte_addr as int)
                    }
            }
            &&& forall |i: int| #[trigger] self.ptes@.value().contains_key(i) ==> {
                &&& self.frames@.value().contains_key(self.ptes@.value()[i].frame_pa as int)
                &&& self.ptes@.value()[i].frame_pa != 0
                &&& self.ptes@.value()[i].frame_pa < u64::MAX
                &&& self.ptes@.value()[i].frame_pa as u64 != 0
            }
        }
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
    if (spt.ptes@.value().contains_key(addr as int)) {
        MockPageTableEntry {
            pte_addr: addr as u64,
            frame_pa: spt.ptes@.value()[addr as int].frame_pa as u64,
            level: spt.ptes@.value()[addr as int].level as u8,
            prop: spt.ptes@.value()[addr as int].prop,
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
#[verifier::when_used_as_spec(get_pte_from_addr_spec)]
pub fn get_pte_from_addr(addr: usize, spt: &SubPageTable) -> (res: MockPageTableEntry)
    requires
        0 <= addr < PHYSICAL_BASE_ADDRESS_SPEC() + SIZEOF_FRAME * NR_ENTRIES,
        (addr - PHYSICAL_BASE_ADDRESS_SPEC()) % SIZEOF_PAGETABLEENTRY as int == 0,
        spt.wf(),
    ensures
        res == get_pte_from_addr_spec(addr, spt),
        res.frame_paddr() == 0 ==> !spt.ptes@.value().contains_key(addr as int),
        res.frame_paddr() != 0 ==> {
            &&& spt.ptes@.value().contains_key(res.pte_paddr() as int)
            &&& spt.ptes@.value()[res.pte_paddr() as int].frame_pa == res.frame_paddr() as int
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
