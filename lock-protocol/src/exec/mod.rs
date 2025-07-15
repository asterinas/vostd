mod rw;
// mod test_map;
// mod test_map2;

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
    },
    spec::sub_page_table,
    task::{disable_preempt, DisabledPreemptGuard},
};
use vstd::simple_pptr::*;

use crate::exec;

verus! {

pub const SIZEOF_PAGETABLEENTRY: usize = 24;

global layout SimplePageTableEntry is size == 24, align == 8;

pub const SIZEOF_FRAME: usize = 24 * 512;

// 8 bytes for pa + 8 bytes for each pte
global layout SimpleFrame is size == 12288, align == 8;

pub const MAX_FRAME_NUM: usize = 10000;

// TODO: This is a mock implementation of the page table entry.
// Maybe it should be replaced with the actual implementation, e.g., x86_64.
#[derive(Copy, Clone)]
pub struct SimplePageTableEntry {
    pub pte_addr: u64,
    pub frame_pa: u64,
    pub level: u8,
    // pub prop: PageProperty,
}

#[derive(Copy, Clone)]
pub struct SimpleFrame {
    // TODO: Is this correct?
    pub ptes:
        [SimplePageTableEntry; NR_ENTRIES],
    // pub ptes: Vec<SimplePageTableEntry>,
}

pub fn create_new_frame(frame_addr: Paddr, level: u8) -> (res: SimpleFrame)
    ensures
        res.ptes.len() == NR_ENTRIES,
        forall|i: int|
            0 <= i < NR_ENTRIES ==> #[trigger] res.ptes[i].pte_addr == frame_addr + i
                * SIZEOF_PAGETABLEENTRY as u64,
        forall|i: int| 0 <= i < NR_ENTRIES ==> #[trigger] res.ptes[i].frame_pa == 0,
        forall|i: int| 0 <= i < NR_ENTRIES ==> #[trigger] res.ptes[i].level == level as u8,
{
    let mut ptes = [SimplePageTableEntry { pte_addr: 0, frame_pa: 0, level: 0 };NR_ENTRIES];
    for i in 0..NR_ENTRIES {
        assume(frame_addr + i * SIZEOF_PAGETABLEENTRY < usize::MAX as u64);
        ptes[i] = SimplePageTableEntry {
            pte_addr: (frame_addr + i * SIZEOF_PAGETABLEENTRY) as u64,
            frame_pa: 0,
            level: level,
        };
    }

    let f = SimpleFrame { ptes };

    // assert(ptes[0].frame_pa == 0); // TODO: don't know why this fails
    assume(forall|i: int|
        0 <= i < NR_ENTRIES ==> (#[trigger] ptes[i]).pte_addr == frame_addr as u64 + i as u64
            * SIZEOF_PAGETABLEENTRY as u64);
    assume(forall|i: int| 0 <= i < NR_ENTRIES ==> (#[trigger] ptes[i]).frame_pa == 0);
    assume(forall|i: int| 0 <= i < NR_ENTRIES ==> (#[trigger] ptes[i]).level == level);

    f
}

impl PageTableEntryTrait for SimplePageTableEntry {
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
        spt: &mut SubPageTable,
        ghost_index: usize,
    ) -> Self {
        // NOTE: this function currently does not create a actual page table entry
        SimplePageTableEntry {
            pte_addr: 0,
            frame_pa: 0,
            level: 0,  // let's use level 0 represent a page
        }
    }

    #[verifier::external_body]
    fn new_pt(paddr: crate::mm::Paddr) -> Self {
        SimplePageTableEntry {
            pte_addr: 0,  // invalid
            frame_pa: paddr as u64,
            level: 0,  // invalid
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
        // ghost
        spt: &mut exec::SubPageTable,
        cur_alloc_index: usize,
        used_addr: usize,
        used_addr_token: Tracked<sub_page_table::SubPageTableStateMachine::unused_addrs>,
    ) -> (res: Self) where Self: Sized {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use vstd::hash_map::group_hash_map_axioms;

        let (p, Tracked(pt)) = get_frame_from_index(cur_alloc_index, &spt.mem);  // TODO: permission violation
        let f = create_new_frame(PHYSICAL_BASE_ADDRESS() + cur_alloc_index * SIZEOF_FRAME, level);
        p.write(Tracked(&mut pt), f);

        assert(p.addr() == used_addr);

        spt.mem.remove(&cur_alloc_index);
        assert(spt.mem.len() == MAX_FRAME_NUM - 1);  // NOTE: need to be finite
        spt.mem.insert(cur_alloc_index, (p, Tracked(pt)));
        assert(spt.mem.len() == MAX_FRAME_NUM);
        assert(spt.mem@.contains_key(cur_alloc_index));

        proof {
            assert(!spt.frames@.value().contains_key(used_addr as int));
            spt.instance.get().new_at(
                p.addr() as int,
                sub_page_table::FrameView { pa: p.addr() as int, pte_addrs: Set::empty() },
                spt.frames.borrow_mut(),
                used_addr_token.get(),
                spt.ptes.borrow_mut(),
            );
        }

        assert(0 <= frame_addr_to_index(used_addr) < MAX_FRAME_NUM as usize);
        assert(spt.wf()) by {
            assert(forall|i: usize|
                0 <= i < MAX_FRAME_NUM && i != cur_alloc_index ==> spt.mem@.contains_key(i));
            // all other frames are not changed
            assert(forall|i: usize|
                0 <= i < MAX_FRAME_NUM && i != cur_alloc_index ==> spt.mem@[i].1@.mem_contents()
                    != MemContents::<SimpleFrame>::Uninit ==> {
                    #[trigger] spt.frames@.value().contains_key(frame_index_to_addr(i) as int)
                        && forall|k: int|
                        0 <= k < NR_ENTRIES ==> if ((
                        #[trigger] spt.mem@[i].1@.value().ptes[k]).frame_pa != 0) {
                            spt.ptes@.value().contains_key(
                                spt.mem@[i].1@.value().ptes[k].pte_addr as int,
                            )
                        } else {
                            !spt.ptes@.value().contains_key(
                                spt.mem@[i].1@.mem_contents().value().ptes[k].pte_addr as int,
                            )
                        }
                });
            assert(spt.frames@.value().contains_key(used_addr as int)
                ==> spt.mem@[frame_addr_to_index(used_addr)].1@.mem_contents().is_init());
            assert(forall|i: usize| #[trigger]
                spt.frames@.value().contains_key(i as int) && i != used_addr
                    ==> spt.mem@[frame_addr_to_index(i) as usize].1@.mem_contents().is_init());
            assert(forall|i: int|
                spt.frames@.value().contains_key(i) && i != used_addr ==> i < (
                PHYSICAL_BASE_ADDRESS() + SIZEOF_FRAME * MAX_FRAME_NUM) as int);
        }

        print_msg("alloc frame", used_addr);

        FakePageTableLock { paddr: used_addr as Paddr, phantom: std::marker::PhantomData }
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
        spt: &mut SubPageTable,
        level: crate::mm::PagingLevel,
        ghost_index: usize,
        used_pte_addr_token: Tracked<sub_page_table::SubPageTableStateMachine::unused_pte_addrs>,
    )
        ensures
            spt.wf(),
            spt.ptes@.instance_id() == old(spt).ptes@.instance_id(),
            spt.frames@.instance_id() == old(spt).frames@.instance_id(),
            spec_helpers::frame_keys_do_not_change(spt, old(spt)),
    {
        assume(frame_addr_to_index(self.paddr) < MAX_FRAME_NUM as usize);  // TODO: P0
        assume(spt.mem@[frame_addr_to_index(self.paddr)].1@.mem_contents().is_init());  // TODO: P0
        let (p, Tracked(pt)) = get_frame_from_index(frame_addr_to_index(self.paddr), &spt.mem);  // TODO: permission violation
        let mut frame = p.read(Tracked(&pt));
        assume(idx < frame.ptes.len());
        frame.ptes[idx] = SimplePageTableEntry {
            pte_addr: pte.pte_paddr() as u64,
            frame_pa: pte.frame_paddr() as u64,
            level: level as u8,
        };
        // TODO: P0 currently, the last level frame will cause the inconsistency
        // between spt.mem and spt.frames
        p.write(Tracked(&mut pt), frame);

        // TODO: it seems we should not allocate here
        proof {
            // TODO: P0 assumes, need more wf specs
            assume(self.paddr != pte.frame_paddr());
            assume(pte.frame_paddr() != 0);
            assume(spt.frames@.value().contains_key(self.paddr as int));
            assume(spt.frames@.value().contains_key(pte.frame_paddr() as int));
            assume(!spt.frames@.value()[self.paddr as int].pte_addrs.contains(
                pte.pte_paddr() as int,
            ));
            assume(!spt.frames@.value()[self.paddr as int].pte_addrs.contains(
                self.paddr + idx * SIZEOF_PAGETABLEENTRY as int,
            ));
            // parent has valid ptes
            assume(forall|i: int| #[trigger]
                spt.frames@.value()[self.paddr as int].pte_addrs.contains(i)
                    ==> spt.ptes@.value().contains_key(i));
            // child has no ptes
            assume(spt.frames@.value()[pte.frame_paddr() as int].pte_addrs.is_empty());
            // others points to parent have a higher level
            assume(forall|i: int| #[trigger]
                spt.ptes@.value().contains_key(i) ==> spt.ptes@.value()[i].frame_pa
                    == self.paddr as int ==> spt.ptes@.value()[i].level == level + 1 as u8);
            // parent has the same level ptes
            assume(forall|i: int| #[trigger]
                spt.frames@.value()[self.paddr as int].pte_addrs.contains(i)
                    ==> spt.ptes@.value()[i].level == level as u8);
            // no others points to child
            assume(forall|i: int| #[trigger]
                spt.ptes@.value().contains_key(i) ==> spt.ptes@.value()[i].frame_pa
                    != pte.frame_paddr() as int);
            // TODO: P0 assumes

            spt.instance.get().set_child(
                self.paddr as int,
                idx as usize,
                pte.frame_paddr() as int,
                level as usize,
                spt.frames.borrow_mut(),
                spt.ptes.borrow_mut(),
                used_pte_addr_token.get(),
            );
        }
        assume(spt.wf());  // TODO: P0
        assume(spec_helpers::frame_keys_do_not_change(spt, old(spt)));  // TODO: P0
        assume(spec_helpers::mpt_not_contains_not_allocated_frames(spt, ghost_index));
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
        pub mem: HashMap<usize, (PPtr<SimpleFrame>, Tracked<PointsTo<SimpleFrame>>)>, // mem is indexed by index!
        pub frames: Tracked<sub_page_table::SubPageTableStateMachine::frames>, // frame is indexed by paddr!
        pub ptes: Tracked<sub_page_table::SubPageTableStateMachine::ptes>,
        pub instance: Tracked<sub_page_table::SubPageTableStateMachine::Instance>,
    }

    pub open spec fn wf(&self) -> bool {
        predicate {
        &&& self.frames@.instance_id() == self.instance@.id()
        &&& self.ptes@.instance_id() == self.instance@.id()
        &&& self.mem.len() == MAX_FRAME_NUM
        &&& self.mem@.dom().finite()
        &&& forall |i: usize| 0 <= i < MAX_FRAME_NUM ==> {
            &&& (#[trigger] self.mem@.dom().contains(i))
        }
        &&& forall |i: usize| 0 <= i < MAX_FRAME_NUM ==> {
            &&& (#[trigger] self.mem@[i]).1@.pptr() == self.mem@[i].0
        }
        &&& forall |i: usize| 0 <= i < MAX_FRAME_NUM ==> {
            &&& (#[trigger] self.mem@[i].0.addr() == PHYSICAL_BASE_ADDRESS() as usize + i * SIZEOF_FRAME)
        }
        &&& forall |i: usize| 0 <= i < MAX_FRAME_NUM ==>
                if (self.mem@[i].1@.mem_contents().is_init()) {
                    #[trigger] self.frames@.value().contains_key(frame_index_to_addr(i) as int)
                    &&
                    forall |k: int| 0 <= k < NR_ENTRIES ==>
                        if (self.mem@[i].1@.value().ptes[k].frame_pa != 0) {
                            #[trigger] self.ptes@.value().contains_key(self.mem@[i].1@.value().ptes[k].pte_addr as int)
                        }
                        else {
                            !self.ptes@.value().contains_key(self.mem@[i].1@.mem_contents().value().ptes[k].pte_addr as int)
                        }
                } else {
                    // TODO: there could be leaking because we continously allocate frames
                    !self.frames@.value().contains_key(frame_index_to_addr(i) as int)
                    && forall |j: int| 0 <= j < NR_ENTRIES ==>
                        ! #[trigger] self.ptes@.value().contains_key(frame_index_to_addr(i) as int + j * SIZEOF_PAGETABLEENTRY as int)
                }
        &&& forall |i: int| #[trigger] self.frames@.value().contains_key(i) ==>
                self.mem@[frame_addr_to_index(i as usize)].1@.mem_contents().is_init()
        &&& forall |i: int| #[trigger] self.ptes@.value().contains_key(i) ==> // TODO: why we need this? Isn't it preserved by page_wf?
                self.ptes@.value()[i].frame_pa != 0
                && self.ptes@.value()[i].frame_pa < u64::MAX
                && self.ptes@.value()[i].frame_pa as u64 != 0 // TODO: this is so wired
        &&& forall |i: int| #[trigger] self.ptes@.value().contains_key(i) ==> // TODO: why we need this? Isn't it preserved by page_wf?
                self.frames@.value().contains_key(self.ptes@.value()[i].frame_pa as int)
        &&& forall |i: int| #[trigger] self.frames@.value().contains_key(i) ==>
                i < (PHYSICAL_BASE_ADDRESS() + SIZEOF_FRAME * MAX_FRAME_NUM) as int
        }
    }
}

pub tracked struct Tokens {
    pub tracked unused_addrs: Map<int, sub_page_table::SubPageTableStateMachine::unused_addrs>,
    pub tracked unused_pte_addrs: Map<
        int,
        sub_page_table::SubPageTableStateMachine::unused_pte_addrs,
    >,
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

#[verifier::external_body]
fn alloc_page_table_entries() -> (res: HashMap<
    usize,
    (PPtr<SimpleFrame>, Tracked<PointsTo<SimpleFrame>>),
>)
    ensures
        res@.dom().len() == MAX_FRAME_NUM,
        res@.len() == MAX_FRAME_NUM,
        res.len() == MAX_FRAME_NUM,
        forall|i: usize| 0 <= i < MAX_FRAME_NUM ==> { res@.dom().contains(i) },
        forall|i: usize| 0 <= i < MAX_FRAME_NUM ==> { res@.contains_key(i) },
        forall|i: usize| 0 <= i < MAX_FRAME_NUM ==> { (#[trigger] res@[i]).1@.pptr() == res@[i].0 },
        forall|i: usize|
            0 <= i < MAX_FRAME_NUM ==> {
                #[trigger] res@[i].1@.mem_contents() == MemContents::<SimpleFrame>::Uninit
            },
        forall|i: usize|
            0 <= i < MAX_FRAME_NUM ==> {
                #[trigger] (res@[i]).0.addr() == PHYSICAL_BASE_ADDRESS() as usize + i * SIZEOF_FRAME
            },
        res@.dom().finite(),
{
    let mut map = HashMap::<usize, (PPtr<SimpleFrame>, Tracked<PointsTo<SimpleFrame>>)>::new();
    // map.insert(0, (PPtr::from_addr(0), Tracked::assume_new()));
    let p = PHYSICAL_BASE_ADDRESS();
    for i in 0..MAX_FRAME_NUM {  // TODO: possible overflow for executable code
        map.insert(i, (PPtr::from_addr(p + i * SIZEOF_FRAME), Tracked::assume_new()));
    }
    map
}

#[verifier::external_body]
fn get_frame_from_index(
    index: usize,
    map: &HashMap<usize, (PPtr<SimpleFrame>, Tracked<PointsTo<SimpleFrame>>)>,
) -> (res: (PPtr<SimpleFrame>, Tracked<PointsTo<SimpleFrame>>))
    requires
        0 <= index < MAX_FRAME_NUM,
        map@.dom().contains(index),
        forall|i: usize| 0 <= i < MAX_FRAME_NUM ==> { map@.dom().contains(i) },
        forall|i: usize| 0 <= i < MAX_FRAME_NUM ==> { (#[trigger] map@[i]).1@.pptr() == map@[i].0 },
    ensures
        res.1@.pptr() == res.0,
        // NOTE: this is not true! && res.0.addr() == map@[index]@.0.addr()
        res.0 == map@[index].0,
        res.1 == map@[index].1,
        map@[index].1@.mem_contents() == res.1@.mem_contents(),
{
    let (p, Tracked(pt)) = map.get(&index).unwrap();
    (*p, Tracked(pt))
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
    SimplePageTableEntry)
    recommends
        spt.wf(),
{
    if (spt.ptes@.value().contains_key(addr as int)) {
        SimplePageTableEntry {
            pte_addr: addr as u64,
            frame_pa: spt.ptes@.value()[addr as int].frame_pa as u64,
            level: spt.ptes@.value()[addr as int].level as u8,
        }
    } else {
        SimplePageTableEntry { pte_addr: addr as u64, frame_pa: 0, level: 0 }
    }
}

#[verifier::external_body]
#[verifier::when_used_as_spec(get_pte_from_addr_spec)]
pub fn get_pte_from_addr(addr: usize, spt: &SubPageTable) -> (res: SimplePageTableEntry)
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
    let pte = PPtr::<SimplePageTableEntry>::from_addr(addr).read(Tracked::assume_new());  // TODO: permission violation
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
            let layout = Layout::new::<[SimplePageTableEntry; 4096]>();
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
