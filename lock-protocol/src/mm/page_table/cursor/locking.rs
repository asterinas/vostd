use vstd::prelude::verus;

use crate::mm::{
    meta::AnyFrameMeta, MapTrackingStatus, PageTable, PageTableEntryTrait, PageTableLockTrait,
    PageTableConfig, PagingConstsTrait, Vaddr,
};
use std::ops::Range;

use super::Cursor;

verus! {

#[verifier::external_body]
pub fn lock_range<'a, C: PageTableConfig, PTL: PageTableLockTrait<C>>(
    pt: &PageTable<C>,
    va: &Range<Vaddr>,
) -> Cursor<'a, C, PTL> {
    // Placeholder implementation
    unimplemented!()
}

pub fn dfs_mark_astray<C: PageTableConfig, PTL: PageTableLockTrait<C>>(mut sub_tree: PTL) -> (res:
    PTL)
    ensures
        res == sub_tree,
{
    sub_tree
}

} // verus!
