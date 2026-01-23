use vstd::prelude::*;

use vstd_extra::ownership::*;
use vstd_extra::prelude::TreePath;

use crate::mm::page_table::*;
use crate::mm::{Paddr, PagingConstsTrait, PagingLevel, Vaddr};
use crate::specs::arch::mm::{NR_ENTRIES, NR_LEVELS, PAGE_SIZE};
use crate::specs::arch::paging_consts::PagingConsts;
use crate::specs::mm::page_table::cursor::owners::*;
use crate::specs::mm::page_table::*;

use core::ops::Range;

verus! {

impl<C: PageTableConfig> PageTableOwner<C> {
    pub uninterp spec fn new_cursor_owner_spec<'rcu>(self) -> (Self, CursorOwner<'rcu, C>);
}

impl<C: PageTableConfig> CursorView<C> {
    /* A `CursorView` is not aware that the underlying structure of the page table is a tree.
       It is concerned with the elements that can be reached by moving forward (the `rear` of the structure)
       and, to a lesser degree, those that have already been traversed (the `fore`).

       It also tracks a `cur_va` and a `step`. Even in an "empty" view (one in which none of the subtree is mapped)
       `move_forward` can update `cur_va` by adding `step` to it. `push_level` and `pop_level` decrease and increase
       `step`, respectively. If the new virtual address would be aligned to `step`, `move_forward` additionally increases
       `step` until it is no longer aligned, if possible. Functions that remove entries from the page table entirely
       remove them in `step`-sized chunks.
    */

    pub uninterp spec fn push_level_spec(self) -> Self;
    /* {
        Self {
            cur_va: self.cur_va,
            scope: Self::push_size(self.scope),
            fore: self.fore,
            rear: self.rear,
        }
    }*/

    pub uninterp spec fn pop_level_spec(self) -> Self;
    /* {
        Self {
            cur_va: self.cur_va,
            va_range: self.va_range
            scope: Self::pop_size(self.scope),
            fore: self.fore,
            rear: self.rear,
        }
    }*/

    pub uninterp spec fn pop_to_alignment(va: usize, scope: usize) -> usize;

    pub uninterp spec fn take_until(max_va: int, list: Seq<EntryView<C>>) -> (Seq<EntryView<C>>, Seq<EntryView<C>>);

    pub uninterp spec fn move_forward_spec(self) -> Self;/* {
        let new_va = self.cur_va + page_size(level);
        let scope = Self::pop_to_alignment(self.cur_va, self.scope);
        let (taken, rear) = Self::take_until(va, self.rear_local);
        Self { cur_va: va as usize, scope: scope, fore_local: self.fore_local.add(taken), rear_local: rear }
    }*/

    pub open spec fn present(self) -> bool {
        let entry = self.rear_local[0]->leaf;
        self.cur_va == entry.map_va
    }

    pub open spec fn query_item_spec(self) -> C::Item
        recommends
            self.present(),
    {
        let entry = self.rear_local[0]->leaf;
        C::item_from_raw(entry.map_to_pa as usize, entry.level, entry.prop)
    }

    pub open spec fn find_next_spec(self, len: usize) -> Option<Vaddr> {
        if self.rear_local.len() > 0 && self.rear_local[0]->leaf.va_end() < self.cur_va + len {
            Some(self.rear_local[0]->leaf.map_va as usize)
        } else {
            None
        }
    }

    pub uninterp spec fn jump(self, va: usize) -> Self;

    /*    #[rustc_allow_incoherent_impl]
    pub open spec fn cur_entry_spec(self) -> FrameView<C> {
        let end_va = self.cur_va.
        let (taken, rear) = Self::take_until(self.cur_va, self.rear[0]
    }*/
    pub open spec fn cur_va_range_spec(self) -> Range<Vaddr> {
        self.cur_va..(self.cur_va + page_size(self.level)) as usize
    }

    pub open spec fn replace_cur_entry_spec(self, replacement: EntryView<C>) -> (Seq<EntryView<C>>, Self) {
        let va = self.cur_va + page_size(self.level);
        let (taken, rear) = Self::take_until(va, self.rear_local);
        let view = Self {
            cur_va: va as usize,
            level: self.level,
            va_range: self.va_range,
            fore_higher: self.fore_higher,
            fore_local: self.fore_local,
            rear_local: rear,
            rear_higher: self.rear_higher,
        };
        (taken, view)
    }

    pub uninterp spec fn map_spec(
        self,
        item: C::Item,
    ) -> Self;

    /*
    pub open spec fn pop_level_spec(self) -> Self {
        let (tail, popped) = self.path.pop_tail();
        Self {
            path: popped,
            ..self
        }
    }

    pub open spec fn inc_pop_aligned_rec(path: TreePath<CONST_NR_ENTRIES>) -> TreePath<CONST_NR_ENTRIES>
        decreases path.len(),
    {
        if path.len() == 0 {
            path
        } else {
            let n = path.len();
            let val = path.0[n - 1];
            let new_path = path.0.update(n - 1, (val + 1) as usize);

            if new_path[n - 1] % NR_ENTRIES() == 0 {
                let (tail, popped) = path.pop_tail();
                Self::inc_pop_aligned_rec(popped)
            } else {
                path
            }
        }
    }

    pub open spec fn move_forward_spec(self) -> Self {
        Self {
            path: Self::inc_pop_aligned_rec(self.path),
            ..self
        }
    }*/

}

impl<'rcu, C: PageTableConfig> CursorOwner<'rcu, C> {

    pub proof fn present_frame(self)
        ensures
            self.cur_entry_owner().is_frame() ==> {
                &&& self@.present()
                &&& self.cur_entry_owner().frame.unwrap().mapped_pa == self@.rear_local[0]->leaf.map_to_pa
                &&& self.cur_entry_owner().frame.unwrap().prop == self@.rear_local[0]->leaf.prop
                &&& self@.rear_local[0]->leaf.level == self.level
            },
    {
        admit()
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn present_not_absent(self)
        ensures
            self.cur_entry_owner().is_absent() ==> !self@.present(),
    {
        admit()
    }

}

} // verus!
