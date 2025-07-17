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

use crate::mm::page_prop::{PageProperty, PageFlags, PrivilegedPageFlags, CachePolicy};

verus! {

type Paddr = usize;

type Vaddr = usize;

use crate::mm::NR_ENTRIES;
use crate::exec::SIZEOF_PAGETABLEENTRY;
use crate::exec::SIZEOF_FRAME;

#[derive(Clone, Copy)]
pub struct Frame {
    // pub pa: Paddr,
    pub ptes: [PageTableEntry; 512],
    // pub has_ptes: bool,
}

#[derive(Clone, Copy)]
pub struct PageTableEntry {
    pub frame_pa: Paddr,
    pub level: usize,
    pub prop: PageProperty,
}

pub ghost struct PageTableEntryView {
    pub frame_pa: int,
    pub level: usize,
    pub prop: PageProperty,
}

pub ghost struct FrameView {
    pub pa: int,
    // pub ptes: [PageTableEntry; 512],
    pub pte_addrs: Set<int>,
}

} // verus!
tokenized_state_machine! {

// A state machine for a sub-tree of a page table.
SubPageTableStateMachine {

    fields {
        /// Page table pages indexed by their physical address.
        #[sharding(variable)]
        pub frames: Map<int, FrameView>,

        /// Page table entries indexed by their physical address.
        #[sharding(variable)]
        pub ptes: Map<int, PageTableEntryView>,
    }

    init!{
        initialize() {
            init frames = Map::empty();
            init ptes = Map::empty();
        }
    }

    transition! {
        // acquire a sub-page-table at a given root node.
        new_at(root_frame: FrameView) {
            require root_frame.pte_addrs.len() == 0;
            require root_frame.pte_addrs == Set::<int>::empty();

            // no ptes for this frame
            require forall |i: int| 0 <= i < NR_ENTRIES ==>
                !(#[trigger] pre.ptes.dom().contains(root_frame.pa + i * SIZEOF_PAGETABLEENTRY));

            // the sub page table is empty
            require pre.frames.is_empty();
            require pre.ptes.is_empty();

            update frames = pre.frames.insert(root_frame.pa, root_frame);
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

            update frames = pre.frames.insert(parent, FrameView {
                pa: pre.frames[parent].pa,
                pte_addrs: pre.frames[parent].pte_addrs.insert(pte_addr),
            });

            update ptes = pre.ptes.insert(
                pte_addr,
                PageTableEntryView {
                    frame_pa: child,
                    level: level,
                    prop: PageProperty {
                        flags: PageFlags::R(),
                        cache: CachePolicy::Writeback,
                        priv_flags: PrivilegedPageFlags::empty(),
                    },
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
        }
    }

    #[inductive(new_at)]
    pub fn tr_new_at_invariant(pre: Self, post: Self, root_frame: FrameView) {
        assert(!pre.frames.contains_key(root_frame.pa));

        assert(post.frames.contains_key(root_frame.pa));
        assert(post.frames[root_frame.pa] == root_frame);
        assert(post.frames[root_frame.pa].pte_addrs.len() == 0);
        assert(pre.ptes == post.ptes);

        broadcast use vstd::set::group_set_axioms;
        assert(post.frames[root_frame.pa].pte_addrs.len() == 0);
        assert(forall |pte_addr:int| #[trigger] post.frames[root_frame.pa].pte_addrs.contains(pte_addr) ==>
            post.ptes.dom().contains(pte_addr));
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

    #[inductive(initialize)]
    pub fn initialize_inductive(post: Self) { }

    #[invariant]
    pub spec fn sub_pt_wf(self) -> bool {
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

}
} // tokenized_state_machine
