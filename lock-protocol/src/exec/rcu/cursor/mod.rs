pub mod locking;

use std::ops::Range;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::spec::{common::*, utils::*, rcu::*};
use super::{common::*, types::*, cpu::*};
use super::node::PageTableGuard;
use crate::mm::page_table::cursor::MAX_NR_LEVELS;

verus! {

pub struct Cursor<'rcu> {
    pub path: [Option<PageTableGuard<'rcu>>; MAX_NR_LEVELS],
    pub rcu_guard: &'rcu (),
    pub level: PagingLevel,
    pub guard_level: PagingLevel,
    pub va: Vaddr,
    pub barrier_va: Range<Vaddr>,
    pub inst: Tracked<SpecInstance>,
}

} // verus!
