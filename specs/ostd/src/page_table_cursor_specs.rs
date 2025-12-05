use vstd::prelude::*;

use vstd_extra::ownership::*;
use vstd_extra::prelude::TreePath;

use aster_common::prelude::page_table::*;
use aster_common::prelude::*;

use core::ops::Range;

verus! {

impl<'rcu, C: PageTableConfig> PageTableOwner<'rcu, C> {
    #[rustc_allow_incoherent_impl]
    pub closed spec fn new_spec(self) -> (Self, CursorOwner<'rcu, C>);
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

    #[rustc_allow_incoherent_impl]
    pub closed spec fn push_size(size: usize) -> usize;

    #[rustc_allow_incoherent_impl]
    pub closed spec fn pop_size(size: usize) -> usize;

    #[rustc_allow_incoherent_impl]
    pub open spec fn push_level_spec(self) -> Self {
        Self {
            cur_va: self.cur_va,
            scope: Self::push_size(self.scope),
            fore: self.fore,
            rear: self.rear
        }
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn pop_level_spec(self) -> Self {
        Self {
            cur_va: self.cur_va,
            scope: Self::pop_size(self.scope),
            fore: self.fore,
            rear: self.rear
        }
    }

    #[rustc_allow_incoherent_impl]
    pub closed spec fn pop_to_alignment(va: usize, scope: usize) -> usize;

    #[rustc_allow_incoherent_impl]
    pub closed spec fn take_until(max_va: int, list: Seq<FrameView<C>>) -> (Seq<FrameView<C>>, Seq<FrameView<C>>);

    #[rustc_allow_incoherent_impl]
    pub open spec fn move_forward_spec(self) -> Self {
        let va = self.cur_va + self.scope;
        let scope = Self::pop_to_alignment(self.cur_va, self.scope);
        let (taken, rear) = Self::take_until(va, self.rear);
        Self {
            cur_va: va as usize,
            scope: scope,
            fore: self.fore.add(taken),
            rear: rear
        }
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn query_item_spec(self) -> Option<C::Item> {
        let entry = self.rear[0];
        if self.cur_va == entry.leaf.map_va {
            Some(C::item_from_raw(entry.leaf.map_to_pa as usize, entry.leaf.level, entry.leaf.prop))
        } else {
            None
        }
    }

    #[rustc_allow_incoherent_impl]
    pub closed spec fn find_next_spec(self) -> Option<Vaddr>;

    #[rustc_allow_incoherent_impl]
    pub closed spec fn jump(self, va: usize) -> Self;

/*    #[rustc_allow_incoherent_impl]
    pub open spec fn cur_entry_spec(self) -> FrameView<C> {
        let end_va = self.cur_va.
        let (taken, rear) = Self::take_until(self.cur_va, self.rear[0]
    }*/

    #[rustc_allow_incoherent_impl]
    pub open spec fn cur_va_range_spec(self) -> Range<Vaddr> {
        self.cur_va .. (self.cur_va+self.scope) as usize
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn replace_cur_entry_spec(self, replacement: FrameView<C>) -> (Seq<FrameView<C>>, Self) {
        let va = self.cur_va + self.scope;
        let (taken, rear) = Self::take_until(va, self.rear);
        let view = Self {
            cur_va: va as usize,
            scope: self.scope,
            fore: self.fore.insert(self.fore.len() as int, replacement),
            rear: rear
        };
        (taken, view)
    }

    #[rustc_allow_incoherent_impl]
    pub closed spec fn map_spec(self, item: C::Item) -> Self;


/*    #[rustc_allow_incoherent_impl]
    pub open spec fn push_level_spec(self) -> Self {
        Self {
            path: self.path.push_tail(0 as usize),
            ..self
        }
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn pop_level_spec(self) -> Self {
        let (tail, popped) = self.path.pop_tail();
        Self {
            path: popped,
            ..self
        }
    }

    #[rustc_allow_incoherent_impl]
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

    #[rustc_allow_incoherent_impl]
    pub open spec fn move_forward_spec(self) -> Self {
        Self {
            path: Self::inc_pop_aligned_rec(self.path),
            ..self
        }
    }*/

}

} // verus!
