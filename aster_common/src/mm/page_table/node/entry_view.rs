use vstd::prelude::*;

use std::marker::PhantomData;

use super::*;

verus! {

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
        true/*        &&& pa_is_valid_pt_address(self.frame_pa)
        &&& index_is_in_range(self.in_frame_index)
        &&& pa_is_valid_kernel_address(
            self.map_to_pa,
        )
        // We assume that all level PTEs can be leaf. Thus they can map to huge pages.
        &&& level_is_in_range::<C>(
            self.level as int,
        )
        // The corresponding virtual address must be aligned to the page size.
        &&& self.map_va % (page_size_spec::<C>(self.level) as int) == 0 */

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
        true/*        &&& pa_is_valid_pt_address(self.frame_pa)
        &&& index_is_in_range(self.in_frame_index)
        &&& pa_is_valid_pt_address(self.map_to_pa)
        &&& level_is_in_range::<C>(self.level as int)
        // No self-loop.
        &&& self.map_to_pa
            != self.frame_pa
        // The corresponding virtual address must be aligned to the page size.
        &&& self.map_va % (page_size_spec::<C>(self.level) as int) == 0*/

    }
}

pub ghost enum EntryView<C: PageTableConfig> {
    Leaf(LeafPageTableEntryView<C>),
    Intermediate(IntermediatePageTableEntryView<C>),
}

impl<C: PageTableConfig> Inv for EntryView<C> {
    open spec fn inv(self) -> bool {
        match self {
            Self::Leaf(entry) => entry.inv(),
            Self::Intermediate(entry) => entry.inv(),
        }
    }
}

} // verus!
