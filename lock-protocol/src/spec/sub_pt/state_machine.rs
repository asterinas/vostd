use std::marker::PhantomData;

use verus_state_machines_macros::*;
use vstd::prelude::*;

use crate::mm::allocator::pa_is_valid_kernel_address;
use crate::mm::page_prop::{PageProperty, PageFlags, PrivilegedPageFlags, CachePolicy};
use crate::mm::{page_size_spec, PageTableConfig, PagingLevel};

verus! {

type Paddr = usize;

type Vaddr = usize;

use super::{pa_is_valid_pt_address, index_is_in_range, level_is_in_range, index_pte_paddr};

pub ghost struct LeafPageTableEntryView<C: PageTableConfig> {
    pub map_va: int,
    pub frame_pa: int,
    pub in_frame_index: int,
    pub map_to_pa: int,
    pub level: PagingLevel,
    pub prop: PageProperty,
    pub phantom: PhantomData<C>,
}

impl<C: PageTableConfig> LeafPageTableEntryView<C> {
    pub open spec fn wf(&self) -> bool {
        &&& pa_is_valid_pt_address(self.frame_pa)
        &&& index_is_in_range(self.in_frame_index)
        &&& pa_is_valid_kernel_address(
            self.map_to_pa,
        )
        // We assume that all level PTEs can be leaf. Thus they can map to huge pages.
        &&& level_is_in_range::<C>(
            self.level as int,
        )
        // The corresponding virtual address must be aligned to the page size.
        &&& self.map_va % (page_size_spec::<C>(self.level) as int) == 0
    }

    pub open spec fn entry_pa(&self) -> int {
        index_pte_paddr(self.frame_pa, self.in_frame_index)
    }
}

pub ghost struct IntermediatePageTableEntryView<C: PageTableConfig> {
    pub map_va: int,
    pub frame_pa: int,
    pub in_frame_index: int,
    pub map_to_pa: int,
    pub level: PagingLevel,
    pub phantom: PhantomData<C>,
}

impl<C: PageTableConfig> IntermediatePageTableEntryView<C> {
    pub open spec fn wf(&self) -> bool {
        &&& pa_is_valid_pt_address(self.frame_pa)
        &&& index_is_in_range(self.in_frame_index)
        &&& pa_is_valid_pt_address(self.map_to_pa)
        &&& level_is_in_range::<C>(self.level as int)
        // No self-loop.
        &&& self.map_to_pa
            != self.frame_pa
        // The corresponding virtual address must be aligned to the page size.
        &&& self.map_va % (page_size_spec::<C>(self.level) as int) == 0
    }

    pub open spec fn entry_pa(&self) -> int {
        index_pte_paddr(self.frame_pa, self.in_frame_index)
    }
}

pub ghost struct FrameView<C: PageTableConfig> {
    pub map_va: int,
    pub pa: int,
    /// A map from the ancestor frame level to the PTE that the ancestor maps to its child.
    pub ancestor_chain: Map<int, IntermediatePageTableEntryView<C>>,
    pub level: PagingLevel,
    pub phantom: PhantomData<C>,
}

impl<C: PageTableConfig> FrameView<C> {
    pub open spec fn wf(&self) -> bool {
        &&& pa_is_valid_pt_address(self.pa)
        &&& level_is_in_range::<C>(
            self.level as int,
        )
        // The corresponding virtual address must be aligned to the upper-level page size.
        &&& self.map_va % (page_size_spec::<C>((self.level + 1) as PagingLevel) as int)
            == 0
        // Ancestor properties.
        &&& forall|ancestor_level: int| #[trigger]
            self.ancestor_chain.contains_key(ancestor_level) ==> {
                &&& level_is_in_range::<C>(ancestor_level)
                &&& self.level < ancestor_level
                &&& self.ancestor_chain[ancestor_level].wf()
                &&& self.ancestor_chain[ancestor_level].level
                    == ancestor_level
                // No loops.
                &&& #[trigger] self.ancestor_chain[ancestor_level].frame_pa
                    != self.pa
                // The map-to-addresses actually forms a chain.
                &&& if ancestor_level == self.level + 1 {
                    self.ancestor_chain[ancestor_level].map_to_pa == self.pa
                } else {
                    &&& self.ancestor_chain.contains_key(ancestor_level - 1)
                        ==> #[trigger] self.ancestor_chain[ancestor_level].map_to_pa
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

pub open spec fn frames_valid<C: PageTableConfig>(
    root: FrameView<C>,
    frames: &Map<int, FrameView<C>>,
    i_ptes: &Map<int, IntermediatePageTableEntryView<C>>,
) -> bool {
    // Frame invariants.
    &&& forall|addr: int|
        frames.dom().contains(addr) ==> {
            let frame = #[trigger] frames[addr];
            &&& frame.wf()
            &&& frame.pa
                == addr
            // There must be ancestors all the way till the root.
            &&& forall|ancestor_level: int|
                {
                    &&& frame.level < ancestor_level <= root.level
                        ==> #[trigger] frame.ancestor_chain.contains_key(ancestor_level)
                    &&& ancestor_level <= frame.level || root.level < ancestor_level ==> !(
                    #[trigger] frame.ancestor_chain.contains_key(ancestor_level))
                }
                // The ultimate ancestor must be the root.
            &&& if addr != root.pa {
                &&& frame.level < root.level
                &&& frame.ancestor_chain[root.level as int].frame_pa == root.pa
            } else {
                true
            }
            // Properties for each ancestor. They must contain intermediate PTEs in the map.
            &&& forall|ancestor_level: int| #[trigger]
                frame.ancestor_chain.contains_key(ancestor_level) ==> {
                    let ancestor = #[trigger] frame.ancestor_chain[ancestor_level];
                    &&& ancestor_level <= root.level
                    &&& frames.contains_key(ancestor.frame_pa)
                    &&& frames[ancestor.frame_pa].level == ancestor_level
                    &&& {
                        &&& i_ptes.contains_key(ancestor.entry_pa())
                        &&& i_ptes[ancestor.entry_pa()] == ancestor
                        &&& if ancestor_level == frame.level + 1 {
                            i_ptes[ancestor.entry_pa()].map_to_pa == frame.pa
                        } else {
                            i_ptes[ancestor.entry_pa()].map_to_pa
                                == frame.ancestor_chain[ancestor_level - 1].frame_pa
                        }
                    }
                }
        }
}

pub open spec fn ptes_frames_matches<C: PageTableConfig>(
    frames: &Map<int, FrameView<C>>,
    i_ptes: &Map<int, IntermediatePageTableEntryView<C>>,
    ptes: &Map<int, LeafPageTableEntryView<C>>,
) -> bool {
    // Intermediate PTE invariants.
    &&& forall|addr: int|
        i_ptes.dom().contains(addr) ==> {
            let i_pte = #[trigger] i_ptes[addr];
            &&& i_pte.wf()
            &&& i_pte.entry_pa() == addr
            &&& frames.contains_key(i_pte.frame_pa)
            &&& frames.contains_key(
                i_pte.map_to_pa,
            )
            // PTEs must map to a lower level child frame.
            &&& frames[i_pte.map_to_pa].level == i_pte.level
                - 1
            // The ancestor chains of the child frame must be set correctly.
            &&& {
                let child_frame = frames[i_pte.map_to_pa];
                &&& child_frame.ancestor_chain.contains_key(i_pte.level as int)
                &&& child_frame.ancestor_chain[i_pte.level as int] == i_pte
            }
            // Intermediate PTEs can't overlap with leaf PTEs.
            &&& !ptes.contains_key(addr)
        }
        // Leaf PTE invariants.
    &&& forall|addr: int|
        ptes.dom().contains(addr) ==> {
            let pte = #[trigger] ptes[addr];
            &&& pte.wf()
            &&& pte.entry_pa()
                == addr
            // Leaf PTEs can't overlap with intermediate PTEs.
            &&& !i_ptes.contains_key(addr)
        }
}

tokenized_state_machine! {
// A state machine for a sub-tree of a page table.
SubPageTableStateMachine<C: PageTableConfig> {
    fields {
        /// The root of the sub-page-table.
        #[sharding(constant)]
        pub root: FrameView<C>,

        /// Page table pages indexed by their physical address.
        #[sharding(variable)]
        pub frames: Map<int, FrameView<C>>,

        /// Intermediate page table entries indexed by their physical address.
        #[sharding(variable)]
        pub i_ptes: Map<int, IntermediatePageTableEntryView<C>>,

        /// Leaf page table entries indexed by their physical address.
        #[sharding(variable)]
        pub ptes: Map<int, LeafPageTableEntryView<C>>,
    }

    #[invariant]
    pub open spec fn sub_pt_wf(self) -> bool {
        &&& self.root.ancestor_chain.is_empty()
        &&& self.root.wf()
        &&& frames_valid(self.root, &self.frames, &self.i_ptes)
        &&& ptes_frames_matches(&self.frames, &self.i_ptes, &self.ptes)
    }

    init!{
        initialize(root_frame: FrameView<C>) {
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
    pub fn initialize_inductive(post: Self, root_frame: FrameView<C>) {}

    transition! {
        // Sets a new child to the sub-page-table.
        set_child(i_pte: IntermediatePageTableEntryView<C>) {
            let IntermediatePageTableEntryView {
                map_va,
                frame_pa,
                in_frame_index,
                map_to_pa,
                level,
                phantom: _,
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
                level as int,
                i_pte,
            );
            let child = FrameView::<C> {
                map_va,
                pa: map_to_pa,
                ancestor_chain,
                level: (level - 1) as PagingLevel,
                phantom: PhantomData,
            };

            update frames = pre.frames.insert(child.pa, child);

            update i_ptes = pre.i_ptes.insert(
                i_pte.entry_pa(),
                i_pte,
            );
        }
    }

    #[inductive(set_child)]
    pub fn tr_set_child_invariant(pre: Self, post: Self, i_pte: IntermediatePageTableEntryView<C>) {}

    transition! {
        // remove a pte at a given address
        remove_at(parent: int, index: int) {
            let pte_addr = index_pte_paddr(parent, index);

            require pre.i_ptes.contains_key(pte_addr);

            let child_frame_addr = pre.i_ptes[pte_addr].map_to_pa;
            let child_frame_level = pre.frames[child_frame_addr].level as int;

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
