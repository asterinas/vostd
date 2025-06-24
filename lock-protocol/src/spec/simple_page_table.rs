#[allow(unused_imports)]
#[allow(unused)]
use builtin::*;
use builtin_macros::*;

use std::collections::HashMap;

use state_machines_macros::*;
use vstd::prelude::*;
use vstd::cell::*;
#[allow(unused_imports)]
use vstd::hash_map::*;
#[allow(unused_imports)]
use vstd::tokens::MapToken;
#[allow(unused_imports)]
use vstd::raw_ptr::*;
use vstd::simple_pptr::*;
use vstd::simple_pptr::PointsTo;

verus! {

type Paddr = usize;

type Vaddr = usize;

use crate::mm::NR_ENTRIES;
use crate::exec::SIZEOF_PAGETABLEENTRY;
use crate::exec::SIZEOF_FRAME;

#[derive(Clone, Copy)]
pub struct PteFlag;

#[derive(Clone, Copy)]
pub struct Frame {
    // pub pa: Paddr,
    pub ptes: [PageTableEntry; 512],
    // pub has_ptes: bool,
}

#[derive(Clone, Copy)]
pub struct PageTableEntry {
    pub frame_pa: Paddr,
    pub flags: PteFlag,
    pub level: usize,
}

pub ghost struct PageTableEntryView {
    pub frame_pa: int,
    pub flags: PteFlag,
    pub level: usize,
}

pub ghost struct FrameView {
    pub pa: int,
    // pub ptes: [PageTableEntry; 512],
    pub pte_addrs: Set<int>,
}

} // verus!
tokenized_state_machine! {
SimplePageTable {

    fields {
        #[sharding(variable)]
        pub frames: Map<int, FrameView>,

        #[sharding(set)]
        pub unused_addrs: Set<int>,

        #[sharding(variable)]
        pub ptes: Map<int, PageTableEntryView>,

        #[sharding(set)]
        pub unused_pte_addrs: Set<int>,
    }

    init!{
        initialize() {
            init frames = Map::empty();
            init unused_addrs = Set::full(); // TODO: P0 unused_addrs and unused_pte_addrs should be finite

            init ptes = Map::empty();
            init unused_pte_addrs = Set::full();
        }
    }

    transition! {
        // create a pte at a given address
        new_at(addr: int, newFrame: FrameView) {
            require addr == newFrame.pa;
            // require forall |i: int| 0 <= i < NR_ENTRIES ==> #[trigger] newFrame.ptes[i].frame_pa == 0;
            require newFrame.pte_addrs.len() == 0;
            // NOTE: wtf?! len() == 0 does not work and it does not mean empty
            require newFrame.pte_addrs == Set::<int>::empty();

            // no ptes for this frame
            require forall |i: int| 0 <= i < NR_ENTRIES ==>
                ! (#[trigger] pre.ptes.dom().contains(newFrame.pa + i * SIZEOF_PAGETABLEENTRY));

            // no others point to addr
            require forall |i: int| pre.ptes.contains_key(i) ==>
                (#[trigger] pre.ptes[i]).frame_pa != addr;

            remove unused_addrs -= set { addr };

            update frames = pre.frames.insert(addr, newFrame);
        }
    }

    transition! {
        // set child relationship
        set_child(parent: int, index: usize, child: int, level: usize) {
            require parent != child;
            require child != 0;
            require child as u64 != 0; // TODO: maybe add an axiom
            require pre.frames.contains_key(parent);
            require pre.frames.contains_key(child);
            // require pre.frames[parent].pa != pre.frames[child].pa;
            // require pre.frames[parent].pa == parent;

            // TODO: consider remapping? currently this is correct
            require !pre.frames[parent].pte_addrs.contains(parent + index * SIZEOF_PAGETABLEENTRY);

            // parent has valid ptes
            require forall |i: int| #[trigger] pre.frames[parent].pte_addrs.contains(i) ==>
                pre.ptes.dom().contains(i);

            // child has no ptes
            require pre.frames[child].pte_addrs.len() == 0;
            // NOTE: wtf?! len() == 0 does not work and it does not mean empty
            require pre.frames[child].pte_addrs == Set::<int>::empty();

            // others points to parent have a higher level
            require forall |i: int| #[trigger] pre.ptes.contains_key(i) ==>
                (#[trigger] pre.ptes[i]).frame_pa == parent ==> pre.ptes[i].level == level + 1;

            // parent has the same level ptes
            require forall |i: int| #[trigger] pre.frames[parent].pte_addrs.contains(i) ==>
                (#[trigger] pre.ptes[i]).frame_pa == parent ==> pre.ptes[i].level == level;

            // no others points to child
            require forall |i: int| pre.ptes.contains_key(i) ==>
                (#[trigger] pre.ptes[i]).frame_pa != child;

            // require pre.frames[child].pa == child;
            let pte_addr = parent + index * SIZEOF_PAGETABLEENTRY;
            // require !pre.frames[parent].pte_addrs.contains(pte_addr);
            // require !pre.ptes.dom().contains(pte_addr);

            remove unused_pte_addrs -= set { pte_addr };

            update frames = pre.frames.insert(parent, FrameView {
                pa: pre.frames[parent].pa,
                pte_addrs: pre.frames[parent].pte_addrs.insert(pte_addr),
            });

            update ptes = pre.ptes.insert(
                pte_addr,
                PageTableEntryView {
                    frame_pa: child,
                    flags: PteFlag,
                    level: level,
                }
            );
        }
    }

    transition! {
        // remove a pte at a given address
        remove_at(parent: int, pte_addr: int, child_addr: int) {
            require pre.frames.contains_key(parent); // TODO: weak?
            require pre.frames.contains_key(child_addr);

            // TODO: this could be incorrect
            // require pre.frames[child_addr].pte_addrs.len() == 0; // child has no ptes

            require pre.frames[parent].pte_addrs.contains(pte_addr); // parent has the pte

            // no others has the same pte
            require forall |i: int| pre.frames.contains_key(i) && i != parent ==>
                ! #[trigger] pre.frames[i].pte_addrs.contains(pte_addr);

            // pte is valid
            require pre.ptes.dom().contains(pte_addr);
            require pre.ptes[pte_addr].frame_pa == child_addr;

            // no others points to child
            require forall |i: int| pre.ptes.contains_key(i) && i != parent ==>
                (#[trigger] pre.ptes[i]).frame_pa != child_addr;

            // TODO: if child has ptes, we need to remove all of them, which in real world is done after unmapping
            update frames = pre.frames.insert(parent, FrameView {
                pa: pre.frames[parent].pa,
                pte_addrs: pre.frames[parent].pte_addrs.remove(pte_addr),
            });

            // TODO: remove child
            // TODO: this could cause memory leak
            // pre.frames.insert().remove(); TODO: this is not supported by verus

            update ptes = pre.ptes.remove(pte_addr);
            // add unused_addrs += set { child_addr };
            add unused_pte_addrs += set { pte_addr };
        }
    }

    #[inductive(remove_at)]
    pub fn tr_remove_at_invariant(pre: Self, post: Self, parent: int, pte_addr: int, child_addr: int) {
        assert(pre.frames.contains_key(parent));
        assert(pre.frames.contains_key(child_addr));
        // assert(pre.frames[child_addr].pte_addrs.len() == 0);
        assert(pre.frames[parent].pte_addrs.contains(pte_addr));
        assert(pre.ptes.dom().contains(pte_addr));
        assert(pre.ptes[pte_addr].frame_pa == child_addr);

        assert(post.frames.contains_key(parent));
        // assert(!post.frames.contains_key(child_addr)); // TODO
        assert(!post.frames[parent].pte_addrs.contains(pte_addr));
        assert(!post.ptes.dom().contains(pte_addr));

        // assert(post.unused_addrs.contains(child_addr));
        assert(post.unused_pte_addrs.contains(pte_addr));
        assert(forall |i: int| #[trigger] post.frames[parent].pte_addrs.contains(i) ==>
            post.ptes.dom().contains(i));
        assert(forall |i: int| #[trigger] post.frames[child_addr].pte_addrs.contains(i) ==>
            post.ptes.dom().contains(i));
    }

    #[inductive(set_child)]
    pub fn tr_set_child_invariant(pre: Self, post: Self, parent: int, index: usize, child: int, level: usize) {
        assert(pre.frames.contains_key(parent));
        assert(pre.frames.contains_key(child));
        assert(pre.frames[parent].pa != pre.frames[child].pa);
        assert(pre.frames[parent].pa == parent);
        assert(pre.frames[child].pa == child);
        assert(!pre.frames[parent].pte_addrs.contains(parent + index * SIZEOF_PAGETABLEENTRY));
        assert(pre.unused_pte_addrs.contains(parent + index * SIZEOF_PAGETABLEENTRY));
        assert(forall |i: int| #[trigger] pre.frames[parent].pte_addrs.contains(i) ==>
            pre.ptes.dom().contains(i));
        assert(forall |i: int| #[trigger] pre.frames[parent].pte_addrs.contains(i) ==>
            pre.frames[parent].pte_addrs.contains(i));

        assert(post.ptes.dom().contains(parent + index * SIZEOF_PAGETABLEENTRY));
        assert(post.frames.contains_key(parent));
        assert(post.frames[parent].pte_addrs.contains(parent + index * SIZEOF_PAGETABLEENTRY));
        assert(post.ptes[parent + index * SIZEOF_PAGETABLEENTRY].frame_pa == child);
        assert(forall |i: int| #[trigger] post.frames[parent].pte_addrs.contains(i) ==>
            post.ptes.dom().contains(i));
        assert(post.frames[child].pte_addrs.len() == 0);

        assert(forall |i: int| #[trigger] post.frames[parent].pte_addrs.contains(i) && i != (parent + index * SIZEOF_PAGETABLEENTRY) ==>
            pre.frames[parent].pte_addrs.contains(i));
        assert(forall |i: int| #[trigger] post.ptes.contains_key(i) ==>
                (#[trigger] post.ptes[i]).frame_pa == parent ==> post.ptes[i].level == level + 1);
        assert(forall |i: int| #[trigger] pre.ptes.contains_key(i) ==>
                (#[trigger] post.ptes[i]).frame_pa == child ==> post.ptes[i].level == level);
    }

    #[inductive(new_at)]
    pub fn tr_new_at_invariant(pre: Self, post: Self, addr: int, newFrame: FrameView) {
        assert(!pre.frames.contains_key(addr));
        assert(pre.unused_addrs.contains(addr));

        assert(post.frames.contains_key(addr));
        assert(post.frames[addr] == newFrame);
        assert(!post.unused_addrs.contains(addr));
        assert(post.frames[addr].pte_addrs.len() == 0);
        assert(pre.ptes == post.ptes);

        broadcast use vstd::set::group_set_axioms;
        assert(post.frames[addr].pte_addrs.len() == 0);
        assert(forall |pte_addr:int| #[trigger] post.frames[addr].pte_addrs.contains(pte_addr) ==>
            post.ptes.dom().contains(pte_addr));
    }

    #[inductive(initialize)]
    pub fn initialize_inductive(post: Self) { }

    #[invariant]
    pub spec fn page_wf(self) -> bool {
        &&& forall |addr: int| self.frames.dom().contains(addr) ==> {
            let frame = #[trigger] self.frames[addr];
            &&& frame.pa == addr
            &&& forall |pte_addr: int| frame.pte_addrs.contains(pte_addr) ==> {
                let pte = self.ptes[pte_addr];
                &&& self.ptes.dom().contains(pte_addr) // pte_addr is a valid pte address
                &&& pte.level > 1 ==> { // let's only care about ptes at level 2 or higher
                    &&& self.frames.dom().contains(pte.frame_pa) // pte points to a valid frame address
                    &&& self.frames[pte.frame_pa].pa == pte.frame_pa // pte points to a valid frame
                    &&& pte.frame_pa != addr // pte points to a different frame
                    &&& forall |child_pte_addr: int| self.frames[pte.frame_pa].pte_addrs.contains(child_pte_addr) ==> {
                        let child_pte = self.ptes[child_pte_addr];
                        &&& self.ptes.dom().contains(child_pte_addr) // pte_addr is a valid pte address
                        &&& self.frames.dom().contains(child_pte.frame_pa) // pte points to a valid frame address
                        &&& self.frames[child_pte.frame_pa].pa == child_pte.frame_pa // pte points to a valid frame
                        &&& self.ptes[child_pte_addr].level == pte.level - 1 // child level relation
                    }
                }
            }
        }
        &&& forall |pte_addr: int|
            #![trigger self.ptes[pte_addr]]
            self.ptes.dom().contains(pte_addr) ==> {
                &&& self.frames.dom().contains(self.ptes[pte_addr].frame_pa)
                &&& self.ptes[pte_addr].frame_pa != 0
                &&& self.ptes[pte_addr].frame_pa as u64 != 0
            }
    }

    #[invariant]
    pub closed spec fn unused_addrs_are_not_in_frames(&self) -> bool {
        &&& forall |addr: int|
            #![trigger self.unused_addrs.contains(addr)]
            #![trigger self.frames.dom().contains(addr)]
            self.unused_addrs.contains(addr)
              <==> !self.frames.dom().contains(addr)
        &&& forall |addr: int|
            #![trigger self.ptes.dom().contains(addr)]
            #![trigger self.unused_pte_addrs.contains(addr)]
            self.unused_pte_addrs.contains(addr)
              <==> !self.ptes.dom().contains(addr)
    }

}
} // tokenized_state_machine

verus! {

#[verifier::external_body]
fn alloc_page_table_entries() -> (res: HashMap<usize, (PPtr<Frame>, Tracked<PointsTo<Frame>>)>)
    ensures
        res@.dom().len() == NR_ENTRIES,
        res@.len() == NR_ENTRIES,
        res.len() == NR_ENTRIES,
        forall|i: usize| 0 <= i < NR_ENTRIES ==> { res@.dom().contains(i) },
        forall|i: usize| 0 <= i < NR_ENTRIES ==> { res@.contains_key(i) },
        forall|i: usize| 0 <= i < NR_ENTRIES ==> { (#[trigger] res@[i]).1@.pptr() == res@[i].0 },
        forall|i: usize|
            0 <= i < NR_ENTRIES ==> {
                #[trigger] res@[i].1@.mem_contents() == MemContents::<Frame>::Uninit
            },
        forall|i: usize, j: usize|
            0 <= i < j < NR_ENTRIES && i == j - 1 ==> {
                &&(#[trigger] res@[i]).0.addr() + SIZEOF_FRAME == (
                #[trigger] res@[j]).0.addr()  // pointers are adjacent

            },
        res@[0].0.addr() == PHYSICAL_BASE_ADDRESS_SPEC(),
        res@.dom().finite(),
{
    let mut map = HashMap::<usize, (PPtr<Frame>, Tracked<PointsTo<Frame>>)>::new();
    // map.insert(0, (PPtr::from_addr(0), Tracked::assume_new()));
    let p = PHYSICAL_BASE_ADDRESS();
    for i in 0..NR_ENTRIES {
        map.insert(i, (PPtr::from_addr(p + i * SIZEOF_FRAME), Tracked::assume_new()));
    }
    map
}

#[verifier::external_body]
fn get_from_index(
    index: usize,
    map: &HashMap<usize, (PPtr<Frame>, Tracked<PointsTo<Frame>>)>,
) -> (res: (PPtr<Frame>, Tracked<PointsTo<Frame>>))
    requires
        0 <= index < NR_ENTRIES,
        map@.dom().contains(index),
        forall|i: usize| 0 <= i < NR_ENTRIES ==> { map@.dom().contains(i) },
        forall|i: usize| 0 <= i < NR_ENTRIES ==> { (#[trigger] map@[i]).1@.pptr() == map@[i].0 },
    ensures
// res.0.addr() != 0,

        res.1@.pptr() == res.0,
        // NOTE: this is not true! && res.0.addr() == map@[index]@.0.addr()
        res.0 == map@[index].0,
        res.1 == map@[index].1,
{
    let (p, Tracked(pt)) = map.get(&index).unwrap();
    (*p, Tracked::assume_new())
}

pub open spec fn index_to_addr(index: usize) -> usize {
    (PHYSICAL_BASE_ADDRESS_SPEC() + index * SIZEOF_FRAME) as usize
}

// TODO: can we eliminate division
pub open spec fn addr_to_index(addr: usize) -> usize {
    ((addr - PHYSICAL_BASE_ADDRESS_SPEC()) / SIZEOF_FRAME as int) as usize
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
    unsafe {
        let layout = Layout::new::<[PageTableEntry; 4096]>();
        let mut ptr = alloc(layout);
        ptr as *mut u8 as usize
    }
}

#[verifier::external_body]
fn print_mem(mem: HashMap<usize, (PPtr<Frame>, Tracked<PointsTo<Frame>>)>) {
    println!("spec::simple_page_table::main_test start.");
    // print 1
    let (p, Tracked(mut pt)) = mem.get(&1).unwrap();
    let frame = p.read(Tracked(&mut pt));
    println!("Frame1: pa: {}", p.addr());

    println!("Frame1 10th pte points to: {}", frame.ptes[10].frame_pa);

    // print 2
    let (p, Tracked(mut pt)) = mem.get(&2).unwrap();
    let frame = p.read(Tracked(&mut pt));
    println!("Frame2: pa: {}", p.addr());

    // let's try to find frame2 by virtual address
    let va = 10;  // va is just the level since we only set one level of page table
    let (p, Tracked(mut pt)) = mem.get(&1).unwrap();  // let say root is 1
    let frame = p.read(Tracked(&mut pt));
    let pte = frame.ptes[va];
    let p2_addr = pte.frame_pa;
    let p2_index = (p2_addr - mem.get(&0).unwrap().0.addr()) / SIZEOF_FRAME as usize;
    let (p, Tracked(mut pt)) = mem.get(&p2_index).unwrap();
    let frame = p.read(Tracked(&mut pt));
    println!("Frame2: pa: {}", p.addr());

    println!("spec::simple_page_table::main_test end.");
    println!();
}

} // verus!
