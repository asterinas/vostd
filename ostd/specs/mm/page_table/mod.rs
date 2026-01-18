#![allow(hidden_glob_reexports)]

pub mod cursor;
pub mod node;
mod owners;
mod view;

pub use cursor::*;
pub use node::*;
pub use owners::*;
pub use view::*;

use vstd::prelude::*;
use vstd_extra::arithmetic::*;
use vstd_extra::ownership::*;

use crate::mm::page_table::page_size;
use crate::mm::page_table::PageTableConfig;
use crate::mm::{PagingLevel, Vaddr};
use crate::specs::arch::mm::{NR_ENTRIES, NR_LEVELS, PAGE_SIZE};

use align_ext::AlignExt;

verus! {

pub struct AbstractVaddr {
    pub offset: int,
    pub index: Map<int, int>,
}

impl Inv for AbstractVaddr {
    open spec fn inv(self) -> bool {
        &&& 0 <= self.offset < PAGE_SIZE()
        &&& forall |i: int|
            #![trigger self.index.contains_key(i)]
        0 <= i < NR_LEVELS() ==> {
            &&& self.index.contains_key(i)
            &&& 0 <= self.index[i]
            &&& self.index[i] < NR_ENTRIES()
        }
    }
}

impl AbstractVaddr {
    pub uninterp spec fn from_vaddr(va: Vaddr) -> Self;

    pub axiom fn from_vaddr_wf(va: Vaddr)
        ensures
            AbstractVaddr::from_vaddr(va).inv();

    pub uninterp spec fn to_vaddr(self) -> Vaddr;

    pub uninterp spec fn reflect(self, va: Vaddr) -> bool;

    pub broadcast axiom fn reflect_prop(self, va: Vaddr)
        requires
            self.inv(),
            self.reflect(va),
        ensures
            #[trigger] self.to_vaddr() == va,
            #[trigger] Self::from_vaddr(va) == self;

    pub broadcast axiom fn reflect_from_vaddr(va: Vaddr)
        ensures
            #[trigger] Self::from_vaddr(va).reflect(va),
            #[trigger] Self::from_vaddr(va).inv();

    pub broadcast axiom fn reflect_to_vaddr(self)
        requires
            self.inv(),
        ensures
            #[trigger] self.reflect(self.to_vaddr());

    pub broadcast axiom fn reflect_eq(self, other: Self, va: Vaddr)
        requires
            self.reflect(va),
            other.reflect(va),
        ensures
            #![auto] (self == other);

    pub open spec fn align_down(self, level: int) -> Self
        decreases level when level >= 1
    {
        if level == 1 {
            AbstractVaddr {
                offset: 0,
                index: self.index,
            }
        } else {
            let tmp = self.align_down(level - 1);
            AbstractVaddr {
                index: tmp.index.insert(level - 2, 0),
                ..tmp
            }
        }
    }

    pub proof fn align_down_inv(self, level: int)
        requires
            1 <= level < NR_LEVELS(),
            self.inv(),
        ensures
            self.align_down(level).inv(),
            forall |i: int| level <= i < NR_LEVELS() ==> #[trigger] self.index[i - 1] == self.align_down(level).index[i - 1],
        decreases level
    {
        if level == 1 {
            assert(self.inv());
        } else {
            let tmp = self.align_down(level - 1);
            self.align_down_inv(level - 1);
        }
    }

    pub axiom fn align_down_concrete(self, level: int)
        requires
            1 <= level <= NR_LEVELS(),
        ensures
            self.align_down(level).reflect(nat_align_down(self.to_vaddr() as nat, page_size(level as PagingLevel) as nat) as Vaddr);

    pub open spec fn align_up(self, level: int) -> Self {
        let lower_aligned = self.align_down(level - 1);
        lower_aligned.next_index(level)
    }

    pub axiom fn align_up_concrete(self, level: int)
        requires
            1 <= level <= NR_LEVELS(),
        ensures
            self.align_up(level).reflect(nat_align_up(self.to_vaddr() as nat, page_size(level as PagingLevel) as nat) as Vaddr);

    pub axiom fn align_diff(self, level: int)
        requires
            1 <= level <= NR_LEVELS(),
        ensures
            nat_align_up(self.to_vaddr() as nat, page_size(level as PagingLevel) as nat) ==
            nat_align_down(self.to_vaddr() as nat, page_size(level as PagingLevel) as nat) + page_size(level as PagingLevel),
            nat_align_up(self.to_vaddr() as nat, page_size(level as PagingLevel) as nat) < usize::MAX;

    pub open spec fn next_index(self, level: int) -> Self
        decreases NR_LEVELS() - level when 1 <= level <= NR_LEVELS()
    {
        let index = self.index[level - 1];
        let next_index = index + 1;
        if next_index == NR_ENTRIES() && level < NR_LEVELS() {
            let next_va = Self {
                offset: self.offset,
                index: self.index.insert(level - 1, 0),
            };
            next_va.next_index(level + 1)
        } else if next_index == NR_ENTRIES() && level == NR_LEVELS() {
            Self {
                offset: self.offset,
                index: self.index.insert(level - 1, 0),
            }
        } else {
            Self {
                offset: self.offset,
                index: self.index.insert(level - 1, next_index),
            }
        }
    }

    pub open spec fn wrapped(self, start_level: int, level: int) -> bool
        decreases NR_LEVELS() - level when 1 <= start_level <= level <= NR_LEVELS()
    {
        &&& self.next_index(start_level).index[level - 1] == 0 ==> {
            &&& self.index[level - 1] + 1 == NR_ENTRIES()
            &&& if level < NR_LEVELS() {
                self.wrapped(start_level, level + 1)
            } else {
                true
            }
        }
        &&& self.next_index(start_level).index[level - 1] != 0 ==>
            self.index[level - 1] + 1 < NR_ENTRIES()
    }

    pub proof fn use_wrapped(self, start_level: int, level: int)
        requires
            1 <= start_level <= level < NR_LEVELS(),
            self.wrapped(start_level, level),
            self.next_index(start_level).index[level - 1] == 0
        ensures
            self.index[level - 1] + 1 == NR_ENTRIES()
    { }

    pub proof fn wrapped_unwrap(self, start_level: int, level: int)
        requires
            1 <= start_level <= level < NR_LEVELS(),
            self.wrapped(start_level, level),
            self.next_index(start_level).index[level - 1] == 0,
        ensures
            self.wrapped(start_level, level + 1)
    { }

    pub proof fn next_index_wrap_condition(self, level: int)
        requires
            self.inv(),
            1 <= level <= NR_LEVELS(),
        ensures
            self.wrapped(level, level)
    { admit() }
}

}
