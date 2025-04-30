use vstd::prelude::verus;

use crate::mm::{
    meta::AnyFrameMeta, MapTrackingStatus, PageTable, PageTableEntryTrait, PageTableLockTrait,
    PageTableMode, PagingConstsTrait, Vaddr,
};
use std::ops::Range;

use super::Cursor;

verus! {

#[verifier::external_body]
pub fn lock_range<
    'a,
    M: PageTableMode,
    // E: PageTableEntryTrait = PageTableEntry,
    E: PageTableEntryTrait,
    // C: PagingConstsTrait = PagingConsts,
    C: PagingConstsTrait,
    PTL: PageTableLockTrait<E, C>,
>(pt: &PageTable<M, E, C>, va: &Range<Vaddr>, new_pt_is_tracked: MapTrackingStatus) -> Cursor<
    'a,
    M,
    E,
    C,
    PTL,
> {
    // Placeholder implementation
    unimplemented!()
}

pub fn dfs_mark_astray<E: PageTableEntryTrait, C: PagingConstsTrait, PTL: PageTableLockTrait<E, C>>(
    mut sub_tree: PTL,
) -> (res: PTL)
    ensures
        res == sub_tree,
{
    sub_tree
}

} // verus!
