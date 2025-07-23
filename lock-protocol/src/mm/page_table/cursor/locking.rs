use vstd::prelude::verus;

use crate::mm::{
    meta::AnyFrameMeta, PageTable, PageTableConfig, PageTableEntryTrait, PageTableGuard,
    PagingConstsTrait, Vaddr,
};
use std::ops::Range;

use super::Cursor;

verus! {

#[verifier::external_body]
pub fn lock_range<'a, C: PageTableConfig>(pt: &PageTable<C>, va: &Range<Vaddr>) -> Cursor<'a, C> {
    // Placeholder implementation
    unimplemented!()
}

pub fn dfs_mark_astray<C: PageTableConfig>(mut sub_tree: PageTableGuard<C>) -> (res: PageTableGuard<
    C,
>)
    ensures
        res == sub_tree,
{
    sub_tree
}

} // verus!
