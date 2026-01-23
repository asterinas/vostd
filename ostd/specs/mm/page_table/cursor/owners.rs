use vstd::prelude::*;

use vstd_extra::ownership::*;
use vstd_extra::prelude::TreePath;

use crate::mm::page_table::*;

use core::marker::PhantomData;
use core::ops::Range;

use crate::mm::{Paddr, PagingConstsTrait, PagingLevel, Vaddr};
use crate::specs::arch::mm::{NR_ENTRIES, NR_LEVELS, PAGE_SIZE};
use crate::specs::arch::paging_consts::PagingConsts;
use crate::specs::mm::page_table::owners::*;
use crate::specs::mm::page_table::AbstractVaddr;
use crate::specs::task::InAtomicMode;
use crate::specs::mm::page_table::node::GuardPerm;

verus! {

pub tracked struct CursorContinuation<'rcu, C: PageTableConfig> {
    pub entry_own: EntryOwner<'rcu, C>,
    pub idx: usize,
    pub base_va: Vaddr,
    pub bound_va: Vaddr,
    pub level: nat,
    pub tree_level: nat,
    pub children: Seq<Option<OwnerSubtree<'rcu, C>>>,
    pub guard_perm: GuardPerm<'rcu, C>,
}

impl<'rcu, C: PageTableConfig> CursorContinuation<'rcu, C> {

    pub open spec fn take_child_spec(self) -> (OwnerSubtree<'rcu, C>, Self) {
        let child = self.children[self.idx as int].unwrap();
        let cont = Self {
            children: self.children.remove(self.idx as int).insert(self.idx as int, None),
            ..self
        };
        (child, cont)
    }

    #[verifier::returns(proof)]
    pub proof fn take_child(tracked &mut self) -> (res: OwnerSubtree<'rcu, C>)
        requires
            old(self).idx < old(self).children.len(),
            old(self).children[old(self).idx as int] is Some,
        ensures
            res == old(self).take_child_spec().0,
            self == old(self).take_child_spec().1,
    {
        let tracked child = self.children.tracked_remove(old(self).idx as int).tracked_unwrap();
        self.children.tracked_insert(old(self).idx as int, None);
        child
    }

    pub open spec fn put_child_spec(self, child: OwnerSubtree<'rcu, C>) -> Self {
        Self {
            children: self.children.remove(self.idx as int).insert(self.idx as int, Some(child)),
            ..self
        }
    }

    #[verifier::returns(proof)]
    pub proof fn put_child(tracked &mut self, tracked child: OwnerSubtree<'rcu, C>)
        requires
            old(self).idx < old(self).children.len(),
            old(self).children[old(self).idx as int] is None,
        ensures
            self == old(self).put_child_spec(child)
    {
        let _ = self.children.tracked_remove(old(self).idx as int);
        self.children.tracked_insert(old(self).idx as int, Some(child));
    }

    pub proof fn take_put_child(self)
        requires
            self.idx < self.children.len(),
            self.children[self.idx as int] is Some,
        ensures
            self.take_child_spec().1.put_child_spec(self.take_child_spec().0) == self,
    {
        let child = self.take_child_spec().0;
        let cont = self.take_child_spec().1;
        assert(cont.put_child_spec(child).children == self.children);
    }

    pub open spec fn make_cont_spec(self, idx: usize, guard_perm: GuardPerm<'rcu, C>) -> (Self, Self) {
        let child = Self {
            base_va: (self.base_va + self.idx * page_size((self.level - 1) as u8)) as usize,
            bound_va: (self.base_va + page_size(self.level as u8)) as usize,
            entry_own: self.children[self.idx as int].unwrap().value,
            level: (self.level - 1) as nat,
            tree_level: (self.tree_level + 1) as nat,
            idx: idx,
            children: self.children[self.idx as int].unwrap().children,
            guard_perm: guard_perm,
        };
        let cont = Self {
            children: self.children.update(self.idx as int, None),
            ..self
        };
        (child, cont)
    }

    #[verifier::returns(proof)]
    pub axiom fn make_cont(tracked &mut self, idx: usize, tracked guard_perm: Tracked<GuardPerm<'rcu, C>>) -> (res: Self)
        requires
            old(self).all_some(),
            old(self).idx < NR_ENTRIES(),
            idx < NR_ENTRIES(),
        ensures
            res == old(self).make_cont_spec(idx, guard_perm@).0,
            self == old(self).make_cont_spec(idx, guard_perm@).1,
    ;

    pub open spec fn restore_spec(self, child: Self) -> (Self, GuardPerm<'rcu, C>) {
        let child_node = OwnerSubtree {
            value: child.entry_own,
            level: child.tree_level,
            children: child.children,
        };
        (Self { children: self.children.update(self.idx as int, Some(child_node)), ..self }, self.guard_perm)
    }

    #[verifier::returns(proof)]
    pub axiom fn restore(tracked &mut self, tracked child: Self) -> (tracked guard_perm: Tracked<GuardPerm<'rcu, C>>)
        ensures
            self == old(self).restore_spec(child).0,
            guard_perm@ == old(self).restore_spec(child).1,
    ;

    pub open spec fn prev_views(self) -> Seq<EntryView<C>> {
        self.children.take(self.idx as int).flat_map(
            |child: Option<OwnerSubtree<'rcu, C>>|
                match child {
                    Some(child) => child@,
                    None => Seq::empty(),
                },
        )
    }

    pub open spec fn next_views(self) -> Seq<EntryView<C>> {
        self.children.skip(self.idx as int).flat_map(
            |child: Option<OwnerSubtree<'rcu, C>>|
                match child {
                    Some(child) => child@,
                    None => Seq::empty(),
                },
        )
    }

    pub open spec fn inv(self) -> bool {
        &&& self.children.len() == NR_ENTRIES()
        &&& 0 <= self.idx < NR_ENTRIES()
        &&& forall|i: int|
            #![trigger self.children[i]]
            0 <= i < NR_ENTRIES() ==> self.children[i] is Some ==> {
                &&& self.children[i].unwrap().inv()
                &&& self.children[i].unwrap().level == self.tree_level + 1
                &&& self.tree_level == INC_LEVELS() - self.level
            }
        &&& self.entry_own.is_node()
        &&& self.entry_own.inv()
        &&& self.tree_level == INC_LEVELS() - self.level
        &&& self.tree_level < INC_LEVELS() - 1
    }

    pub open spec fn all_some(self) -> bool {
        forall|i: int| 0 <= i < NR_ENTRIES() ==> self.children[i] is Some
    }

    pub open spec fn all_but_index_some(self) -> bool {
        &&& forall|i: int| 0 <= i < self.idx ==> self.children[i] is Some
        &&& forall|i: int| self.idx < i < NR_ENTRIES() ==> self.children[i] is Some
        &&& self.children[self.idx as int] is None
    }

    pub open spec fn inc_index(self) -> Self {
        Self {
            idx: (self.idx + 1) as usize,
            ..self
        }
    }

    pub proof fn do_inc_index(tracked &mut self)
        requires
            old(self).idx + 1 < NR_ENTRIES(),
        ensures
            self == old(self).inc_index(),
    {
        self.idx = (self.idx + 1) as usize;
    }
}

#[rustc_has_incoherent_inherent_impls]
pub tracked struct CursorOwner<'rcu, C: PageTableConfig> {
    pub level: PagingLevel,
    pub continuations: Map<int, CursorContinuation<'rcu, C>>,
    pub va: AbstractVaddr,
    pub guard_level: PagingLevel,
    pub prefix: AbstractVaddr,
}

impl<'rcu, C: PageTableConfig> Inv for CursorOwner<'rcu, C> {
    open spec fn inv(self) -> bool {
        &&& self.va.inv()
        &&& 1 <= self.level <= NR_LEVELS()
        &&& self.continuations[self.level - 1].all_some()
        &&& forall|i: int| self.level <= i < NR_LEVELS() ==> {
            (#[trigger] self.continuations[i]).all_but_index_some()
        }
        &&& self.prefix.inv()
        &&& forall|i: int| i < self.guard_level ==> self.prefix.index[i] == 0
        &&& self.level <= 4 ==> {
            &&& self.continuations.contains_key(3)
            &&& self.continuations[3].inv()
            &&& self.continuations[3].level == 4
            &&& self.continuations[3].entry_own.is_node()
            &&& self.va.index[3] == self.continuations[3].idx
        }
        &&& self.level <= 3 ==> {
            &&& self.continuations.contains_key(2)
            &&& self.continuations[2].inv()
            &&& self.continuations[2].level == 3
            &&& self.continuations[2].entry_own.is_node()
            &&& self.va.index[2] == self.continuations[2].idx
        }
        &&& self.level <= 2 ==> {
            &&& self.continuations.contains_key(1)
            &&& self.continuations[1].inv()
            &&& self.continuations[1].level == 2
            &&& self.continuations[1].entry_own.is_node()
            &&& self.va.index[1] == self.continuations[1].idx
        }
        &&& self.level == 1 ==> {
            &&& self.continuations.contains_key(0)
            &&& self.continuations[0].inv()
            &&& self.continuations[0].level == 1
            &&& self.continuations[0].entry_own.is_node()
            &&& self.va.index[0] == self.continuations[0].idx
        }
    }
}

impl<'rcu, C: PageTableConfig> CursorOwner<'rcu, C> {

    pub open spec fn index(self) -> usize {
        self.continuations[self.level - 1].idx
    }

    pub open spec fn inc_index(self) -> Self {
        Self {
            continuations: self.continuations.insert(self.level - 1, self.continuations[self.level - 1].inc_index()),
            va: AbstractVaddr {
                offset: self.va.offset,
                index: self.va.index.insert(self.level - 1, self.continuations[self.level - 1].inc_index().idx as int)
            },
            ..self
        }
    }

    pub proof fn do_inc_index(tracked &mut self)
        requires
            old(self).inv(),
            old(self).continuations[old(self).level - 1].idx + 1 < NR_ENTRIES(),
        ensures
            self.inv(),
            self == old(self).inc_index(),
    {
        let tracked mut cont = self.continuations.tracked_remove(self.level - 1);
        cont.do_inc_index();
        self.va.index.tracked_insert(self.level - 1, cont.idx as int);
        self.continuations.tracked_insert(self.level - 1, cont);
        assert(self.continuations == old(self).continuations.insert(self.level - 1, cont));
    }

    pub proof fn inc_index_increases_va(self)
        requires
            self.inv()
        ensures
            self.inc_index().va.to_vaddr() > self.va.to_vaddr(),
    { admit() }

    pub open spec fn cur_va(self) -> Vaddr {
        (self.continuations[self.level - 1].base_va + self.index() * page_size(self.level as u8)) as usize
    }

    pub proof fn inv_continuation(self, i: int)
        requires
            self.inv(),
            self.level - 1 <= i <= NR_LEVELS() - 1,
        ensures
            self.continuations.contains_key(i),
            self.continuations[i].inv(),
            self.continuations[i].children.len() == NR_ENTRIES(),
    {
        assert(self.continuations.contains_key(i));
    }

    pub open spec fn prev_views_rec(self, i: int) -> Seq<EntryView<C>>
        decreases i,
        when self.level > 0
    {
        if i < self.level {
            Seq::empty()
        } else {
            self.prev_views_rec(i - 1).add(self.continuations[i - 1].prev_views())
        }
    }

    pub open spec fn next_views_rec(self, i: int) -> Seq<EntryView<C>>
        decreases i,
        when self.level > 0
    {
        if i < self.level {
            Seq::empty()
        } else {
            self.continuations[i - 1].next_views().add(self.next_views_rec(i - 1))
        }
    }

    pub open spec fn cur_entry_owner(self) -> EntryOwner<'rcu, C> {
        self.continuations[self.level - 1].children[self.index() as int].unwrap().value
    }

    pub open spec fn locked_range(self) -> Range<Vaddr> {
        let start = self.prefix.align_down(self.guard_level as int).to_vaddr();
        let end = self.prefix.align_up(self.guard_level as int).to_vaddr();
        Range { start, end }
    }

    pub open spec fn in_locked_range(self) -> bool {
        self.locked_range().start <= self.va.to_vaddr() < self.locked_range().end
    }

    pub proof fn prefix_in_locked_range(self)
        requires
            forall|i:int| i >= self.guard_level ==> self.va.index[i] == self.prefix.index[i],
        ensures
            self.in_locked_range(),
    { admit() }
}

pub tracked struct CursorView<C: PageTableConfig> {
    pub cur_va: Vaddr,
    pub level: PagingLevel,
    pub va_range: Range<Vaddr>,
    pub fore_higher: Seq<EntryView<C>>,
    pub fore_local: Seq<EntryView<C>>,
    pub rear_local: Seq<EntryView<C>>,
    pub rear_higher: Seq<EntryView<C>>,
}

impl<C: PageTableConfig> CursorView<C> {
    pub open spec fn descendants(self) -> Seq<EntryView<C>> {
        self.fore_local.add(self.rear_local)
    }
}

impl<C: PageTableConfig> Inv for CursorView<C> {
    open spec fn inv(self) -> bool {
        &&& forall |view| #[trigger] self.descendants().contains(view) ==>
            self.va_range.start <= view->leaf.map_va < self.va_range.end
        &&& forall |view| #[trigger] self.fore_higher.contains(view) ==>
            view->leaf.map_va < self.va_range.start
        &&& forall |view| #[trigger] self.rear_higher.contains(view) ==>
            self.va_range.end <= view->leaf.map_va
    }
}

impl<'rcu, C: PageTableConfig> View for CursorOwner<'rcu, C> {
    type V = CursorView<C>;

    open spec fn view(&self) -> Self::V {
        CursorView {
            cur_va: self.cur_va(),
            level: self.level,
            va_range: Range { start: self.continuations[self.level - 1].base_va,
                end: self.continuations[self.level - 1].bound_va },
            fore_higher: self.prev_views_rec(NR_LEVELS() as int),
            fore_local: self.continuations[self.level - 1].prev_views(),
            rear_local: self.continuations[self.level - 1].next_views(),
            rear_higher: self.next_views_rec(NR_LEVELS() as int),
        }
    }
}


impl<'rcu, C: PageTableConfig> InvView for CursorOwner<'rcu, C> {
    proof fn view_preserves_inv(self) {
        assert(self@.inv()) by { admit() };
    }
}

impl<'rcu, C: PageTableConfig, A: InAtomicMode> Inv for Cursor<'rcu, C, A> {
    open spec fn inv(self) -> bool {
        &&& 1 <= self.level <= NR_LEVELS()
        &&& self.level <= self.guard_level <= NR_LEVELS()
//        &&& forall|i: int| 0 <= i < self.guard_level - self.level ==> self.path[i] is Some
    }
}

impl<'rcu, C: PageTableConfig, A: InAtomicMode> OwnerOf for Cursor<'rcu, C, A> {
    type Owner = CursorOwner<'rcu, C>;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& owner.va.reflect(self.va)
        &&& self.level == owner.level
//        &&& owner.index() == self.va % page_size(self.level)
        &&& self.level <= 4 ==> {
            &&& self.path[3] is Some
            &&& owner.continuations.contains_key(3)
            &&& owner.continuations[3].guard_perm.pptr() == self.path[3].unwrap()
        }
        &&& self.level <= 3 ==> {
            &&& self.path[2] is Some
            &&& owner.continuations.contains_key(2)
            &&& owner.continuations[2].guard_perm.pptr() == self.path[2].unwrap()
        }
        &&& self.level <= 2 ==> {
            &&& self.path[1] is Some
            &&& owner.continuations.contains_key(1)
            &&& owner.continuations[1].guard_perm.pptr() == self.path[1].unwrap()
        }
        &&& self.level == 1 ==> {
            &&& self.path[0] is Some
            &&& owner.continuations.contains_key(0)
            &&& owner.continuations[0].guard_perm.pptr() == self.path[0].unwrap()
        }
        &&& self.barrier_va.start == owner.locked_range().start
        &&& self.barrier_va.end == owner.locked_range().end
    }
}

impl<'rcu, C: PageTableConfig, A: InAtomicMode> ModelOf for Cursor<'rcu, C, A> {

}

} // verus!
