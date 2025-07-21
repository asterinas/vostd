use state_machines_macros::*;
use vstd::prelude::*;

use crate::mm::allocator::pa_is_valid_kernel_address;
use crate::mm::page_prop::{PageProperty, PageFlags, PrivilegedPageFlags, CachePolicy};

verus! {

type Paddr = usize;

type Vaddr = usize;

use super::{pa_is_valid_pt_address, index_is_in_range, level_is_in_range, index_pte_paddr};

pub ghost struct LeafPageTableEntryView {
    pub frame_pa: int,
    pub in_frame_index: int,
    pub map_to_pa: int,
    pub level: int,
    pub prop: PageProperty,
}

impl LeafPageTableEntryView {
    pub open spec fn wf(&self) -> bool {
        &&& pa_is_valid_pt_address(self.frame_pa)
        &&& index_is_in_range(self.in_frame_index)
        &&& pa_is_valid_kernel_address(
            self.map_to_pa,
        )
        // We assume that all level PTEs can be leaf. Thus they can map to huge pages.
        &&& level_is_in_range(self.level)
    }

    pub open spec fn entry_pa(&self) -> int {
        index_pte_paddr(self.frame_pa, self.in_frame_index)
    }
}

pub ghost struct IntermediatePageTableEntryView {
    pub frame_pa: int,
    pub in_frame_index: int,
    pub map_to_pa: int,
    pub level: int,
}

impl IntermediatePageTableEntryView {
    pub open spec fn wf(&self) -> bool {
        &&& pa_is_valid_pt_address(self.frame_pa)
        &&& index_is_in_range(self.in_frame_index)
        &&& pa_is_valid_pt_address(self.map_to_pa)
        &&& level_is_in_range(self.level)
        // No self-loop.
        &&& self.map_to_pa != self.frame_pa
    }

    pub open spec fn entry_pa(&self) -> int {
        index_pte_paddr(self.frame_pa, self.in_frame_index)
    }
}

pub ghost struct FrameView {
    pub pa: int,
    /// A map from the ancestor frame level to the PTE that the ancestor maps to its child.
    pub ancestor_chain: Map<int, IntermediatePageTableEntryView>,
    pub level: int,
}

impl FrameView {
    pub open spec fn wf(&self) -> bool {
        &&& pa_is_valid_pt_address(self.pa)
        &&& level_is_in_range(self.level)
        &&& forall|ancestor_level: int| #[trigger]
            self.ancestor_chain.contains_key(ancestor_level) ==> {
                &&& level_is_in_range(ancestor_level)
                &&& self.level < ancestor_level
                &&& self.ancestor_chain[ancestor_level].wf()
                &&& self.ancestor_chain[ancestor_level].level
                    == ancestor_level
                // No loops.
                &&& self.ancestor_chain[ancestor_level].frame_pa
                    != self.pa
                // The map-to-addresses actually forms a chain.
                &&& if ancestor_level == self.level + 1 {
                    self.ancestor_chain[ancestor_level].map_to_pa == self.pa
                } else {
                    &&& self.ancestor_chain.contains_key(ancestor_level - 1)
                    &&& self.ancestor_chain[ancestor_level].map_to_pa
                        == self.ancestor_chain[ancestor_level - 1].frame_pa
                }
                &&& if self.ancestor_chain.contains_key(ancestor_level + 1) {
                    self.ancestor_chain[ancestor_level + 1].map_to_pa
                        == self.ancestor_chain[ancestor_level].frame_pa
                } else {
                    true
                }
                // The ancestor is not duplicate.
                &&& forall|other_ancestor_level: int| #[trigger]
                    self.ancestor_chain.contains_key(other_ancestor_level) ==> {
                        ||| other_ancestor_level == ancestor_level
                        ||| self.ancestor_chain[other_ancestor_level]
                            != self.ancestor_chain[ancestor_level]
                    }
            }
    }
}

tokenized_state_machine! {
// A state machine for a sub-tree of a page table.
SubPageTableStateMachine {
    fields {
        /// The root of the sub-page-table.
        #[sharding(constant)]
        pub root: FrameView,

        /// Page table pages indexed by their physical address.
        #[sharding(variable)]
        pub frames: Map<int, FrameView>,

        /// Intermediate page table entries indexed by their physical address.
        #[sharding(variable)]
        pub i_ptes: Map<int, IntermediatePageTableEntryView>,

        /// Leaf page table entries indexed by their physical address.
        #[sharding(variable)]
        pub ptes: Map<int, LeafPageTableEntryView>,
    }

    #[invariant]
    pub open spec fn sub_pt_wf(self) -> bool {
        &&& self.root.ancestor_chain.is_empty()
        &&& self.root.wf()
        // Frame invariants.
        &&& forall |addr: int| self.frames.dom().contains(addr) ==> {
            let frame = #[trigger] self.frames[addr];
            &&& frame.wf()
            &&& frame.pa == addr
            // There must be ancestors all the way till the root.
            &&& forall |ancestor_level: int| {
                &&& frame.level < ancestor_level <= self.root.level ==>
                    #[trigger] frame.ancestor_chain.contains_key(ancestor_level)
                &&& ancestor_level <= frame.level || self.root.level < ancestor_level ==>
                    !(#[trigger] frame.ancestor_chain.contains_key(ancestor_level))
            }
            // The ultimate ancestor must be the root.
            &&& if addr != self.root.pa {
                &&& frame.level < self.root.level
                &&& frame.ancestor_chain[self.root.level].frame_pa == self.root.pa
            } else {
                true
            }
            // Properties for each ancestor. They must contain intermediate PTEs in the map.
            &&& forall |ancestor_level: int| #[trigger] frame.ancestor_chain.contains_key(ancestor_level) ==> {
                let ancestor = #[trigger] frame.ancestor_chain[ancestor_level];
                &&& ancestor_level <= self.root.level
                &&& self.frames.contains_key(ancestor.frame_pa)
                &&& self.frames[ancestor.frame_pa].level == ancestor_level
                &&& {
                    &&& self.i_ptes.contains_key(ancestor.entry_pa())
                    &&& self.i_ptes[ancestor.entry_pa()] == ancestor
                    &&& if ancestor_level == frame.level + 1 {
                        self.i_ptes[ancestor.entry_pa()].map_to_pa == frame.pa
                    } else {
                        self.i_ptes[ancestor.entry_pa()].map_to_pa == frame.ancestor_chain[ancestor_level - 1].frame_pa
                    }
                }
            }
        }
        // Intermediate PTE invariants.
        &&& forall |addr: int| self.i_ptes.dom().contains(addr) ==> {
            let i_pte = #[trigger] self.i_ptes[addr];
            &&& i_pte.wf()
            &&& i_pte.entry_pa() == addr
            &&& self.frames.contains_key(i_pte.frame_pa)
            &&& self.frames.contains_key(i_pte.map_to_pa)
            // PTEs must map to a lower level child frame.
            &&& self.frames[i_pte.map_to_pa].level == i_pte.level - 1
            // The ancestor chains of the child frame must be set correctly.
            &&& {
                let child_frame = self.frames[i_pte.map_to_pa];
                &&& child_frame.ancestor_chain.contains_key(i_pte.level)
                &&& child_frame.ancestor_chain[i_pte.level] == i_pte
            }
            // Intermediate PTEs can't overlap with leaf PTEs.
            &&& !self.ptes.contains_key(addr)
        }
        // Leaf PTE invariants.
        &&& forall |addr: int| self.ptes.dom().contains(addr) ==> {
            let pte = #[trigger] self.ptes[addr];
            &&& pte.wf()
            &&& pte.entry_pa() == addr
            // Leaf PTEs can't overlap with intermediate PTEs.
            &&& !self.i_ptes.contains_key(addr)
        }
    }

    init!{
        initialize(root_frame: FrameView) {
            require root_frame.wf();

            // The new frame has no ancestors.
            require root_frame.ancestor_chain.is_empty();

            init root = root_frame;
            init frames = Map::empty().insert(root_frame.pa, root_frame);
            init i_ptes = Map::empty();
            init ptes = Map::empty();
        }
    }

    #[inductive(initialize)]
    pub fn initialize_inductive(post: Self, root_frame: FrameView) {}

    transition! {
        // Sets a new child to the sub-page-table.
        set_child(i_pte: IntermediatePageTableEntryView) {
            let IntermediatePageTableEntryView {
                frame_pa,
                in_frame_index,
                map_to_pa,
                level,
            } = i_pte;

            require i_pte.wf();
            require level > 1;
            require level <= pre.root.level;
            require if level == pre.root.level {
                &&& frame_pa == pre.root.pa
            } else {
                &&& frame_pa != pre.root.pa
            };
            require if frame_pa == pre.root.pa {
                &&& level == pre.root.level
            } else {
                true
            };

            require pre.frames.contains_key(frame_pa);
            require !pre.frames.contains_key(map_to_pa);

            let parent_frame = pre.frames[frame_pa];

            require parent_frame.level == level;

            // No remapping for this transition.
            require !pre.i_ptes.contains_key(i_pte.entry_pa());
            require !pre.ptes.contains_key(i_pte.entry_pa());

            // Construct a child frame with proper ancestor chain.
            let ancestor_chain = parent_frame.ancestor_chain.insert(
                level,
                i_pte,
            );
            let child = FrameView {
                pa: map_to_pa,
                ancestor_chain,
                level: level - 1,
            };

            update frames = pre.frames.insert(child.pa, child);

            update i_ptes = pre.i_ptes.insert(
                i_pte.entry_pa(),
                i_pte,
            );
        }
    }

    #[inductive(set_child)]
    pub fn tr_set_child_invariant(pre: Self, post: Self, i_pte: IntermediatePageTableEntryView) {}

    transition! {
        // remove a pte at a given address
        remove_at(parent: int, index: int) {
            let pte_addr = index_pte_paddr(parent, index);

            require pre.i_ptes.contains_key(pte_addr);

            let child_frame_addr = pre.i_ptes[pte_addr].map_to_pa;
            let child_frame_level = pre.frames[child_frame_addr].level;

            require pre.frames.contains_key(parent);
            require pre.frames.contains_key(child_frame_addr);

            // The child is not an ancestor of any other frame.
            // TODO: this restriction may be uplifted in the future to allow child PTEs
            // to be cleared in the background after the PTE is overwritten.
            require forall |i: int| #[trigger] pre.frames.contains_key(i) ==> {
                ||| !pre.frames[i].ancestor_chain.contains_key(child_frame_level)
                ||| pre.frames[i].ancestor_chain[child_frame_level].frame_pa != child_frame_addr
            };

            update frames = pre.frames.remove(child_frame_addr);

            update i_ptes = pre.i_ptes.remove(pte_addr);
        }
    }

    #[inductive(remove_at)]
    pub fn tr_remove_at_invariant(pre: Self, post: Self, parent: int, index: int) {
        // We need to show that, if the frame is not an ancestor of any other
        // frame, then the parent PTE pointing to it shouldn't appear in any
        // ancestor chain.
        assert(forall |i: int| #[trigger] pre.frames.contains_key(i) ==> {
            let any_frame = #[trigger] pre.frames[i];
            // We write the contrapositive here.
            forall |frame_level: int, frame_addr: int| #[trigger] pa_is_valid_pt_address(frame_addr) && frame_level < any_frame.level ==> {
                (any_frame.ancestor_chain.contains_key(frame_level + 1)
                    && frame_addr == any_frame.ancestor_chain[frame_level + 1].map_to_pa)
                ==>
                (#[trigger] any_frame.ancestor_chain.contains_key(frame_level)
                    && frame_addr == any_frame.ancestor_chain[frame_level].frame_pa)
            }
        });
    }
} // SubPageTableStateMachine
}  // tokenized_state_machine!


} // verus!
