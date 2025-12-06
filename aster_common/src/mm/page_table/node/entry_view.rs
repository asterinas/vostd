use vstd::prelude::*;

use std::marker::PhantomData;

use super::*;

verus! {

pub open spec fn level_is_in_range(level: int) -> bool {
    1 <= level <= NR_LEVELS() as int
}

pub open spec fn index_is_in_range(index: int) -> bool {
    0 <= index < NR_ENTRIES()
}

pub open spec fn pa_is_valid_pt_address(pa: int) -> bool {
    &&& pa_is_valid_kernel_address(pa as int)
    &&& pa % PAGE_SIZE() as int == 0
}

pub open spec fn PHYSICAL_BASE_ADDRESS_SPEC() -> usize {
    0
}

pub open spec fn pa_is_valid_kernel_address(pa: int) -> bool {
    PHYSICAL_BASE_ADDRESS_SPEC() <= pa < PHYSICAL_BASE_ADDRESS_SPEC() + PAGE_SIZE()
        * MAX_NR_PAGES() as int
}

pub ghost struct LeafPageTableEntryView<C: PageTableConfig> {
    pub map_va: int,
    pub frame_pa: int,
    pub in_frame_index: int,
    pub map_to_pa: int,
    pub level: PagingLevel,
    pub prop: PageProperty,
    pub phantom: PhantomData<C>,
}

impl<C: PageTableConfig> Inv for LeafPageTableEntryView<C> {
    open spec fn inv(self) -> bool {
        &&& pa_is_valid_pt_address(self.frame_pa)
        &&& index_is_in_range(self.in_frame_index)
        &&& pa_is_valid_kernel_address(
            self.map_to_pa,
        )
        // We assume that all level PTEs can be leaf. Thus they can map to huge pages.
        &&& level_is_in_range(
            self.level as int,
        )
        // The corresponding virtual address must be aligned to the page size.
        &&& self.map_va % (page_size_spec(self.level) as int) == 0
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

impl<C: PageTableConfig> Inv for IntermediatePageTableEntryView<C> {
    open spec fn inv(self) -> bool {
        &&& pa_is_valid_pt_address(self.frame_pa)
        &&& index_is_in_range(self.in_frame_index)
        &&& pa_is_valid_pt_address(self.map_to_pa)
        &&& level_is_in_range(self.level as int)
        // No self-loop.
        &&& self.map_to_pa
            != self.frame_pa
        // The corresponding virtual address must be aligned to the page size.
        &&& self.map_va % (page_size_spec(self.level) as int) == 0
    }
}

pub ghost struct FrameView<C: PageTableConfig> {
    /// A map from the ancestor frame level to the PTE that the ancestor maps to its child.
    pub ancestor_chain: Map<int, IntermediatePageTableEntryView<C>>,
    /// The view of the page table leaf entry
    pub leaf: LeafPageTableEntryView<C>,
}

impl<C: PageTableConfig> Inv for FrameView<C> {
    open spec fn inv(self) -> bool {
        &&& pa_is_valid_pt_address(self.leaf.map_to_pa)
        &&& level_is_in_range(
            self.leaf.level as int,
        )
        // The corresponding virtual address must be aligned to the upper-level page size.
        &&& self.leaf.map_va % (page_size_spec((self.leaf.level + 1) as PagingLevel) as int)
            == 0
        // Ancestor properties.
        &&& forall|ancestor_level: int| #[trigger]
            self.ancestor_chain.contains_key(ancestor_level) ==> {
                &&& level_is_in_range(ancestor_level)
                &&& self.leaf.level < ancestor_level
                &&& self.ancestor_chain[ancestor_level].inv()
                &&& self.ancestor_chain[ancestor_level].level
                    == ancestor_level
                // No loops.
                &&& #[trigger] self.ancestor_chain[ancestor_level].frame_pa
                    != self.leaf.map_to_pa
                // The map-to-addresses actually forms a chain.
                &&& if ancestor_level == self.leaf.level + 1 {
                    self.ancestor_chain[ancestor_level].map_to_pa == self.leaf.map_to_pa
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

impl<C: PageTableConfig> LeafPageTableEntryView<C> {
    pub open spec fn to_frame_view(
        self,
        ancestors: Map<int, IntermediatePageTableEntryView<C>>,
    ) -> FrameView<C> {
        FrameView { ancestor_chain: ancestors, leaf: self }
    }
}

pub ghost enum EntryView<C: PageTableConfig> {
    Leaf { leaf: LeafPageTableEntryView<C> },
    Intermediate { node: IntermediatePageTableEntryView<C> },
    LockedSubtree { views: Seq<FrameView<C>> },
    Absent,
}

impl<C: PageTableConfig> Inv for EntryView<C> {
    open spec fn inv(self) -> bool {
        match self {
            Self::Leaf { leaf: _ } => self->leaf.inv(),
            Self::Intermediate { node: _ } => self->node.inv(),
            Self::LockedSubtree { views: _ } => forall|i: int| #[trigger] self->views[i].inv(),
            Self::Absent => true,
        }
    }
}

} // verus!
