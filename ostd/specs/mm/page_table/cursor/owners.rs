use vstd::prelude::*;
use vstd::simple_pptr::*;

use vstd_extra::ownership::*;
use vstd_extra::prelude::TreePath;

use crate::mm::page_table::*;

use core::marker::PhantomData;
use core::ops::Range;

use crate::aster_common::*;

verus! {


/// The state of virtual pages represented by a page table.
///
/// This is the return type of the [`Cursor::query`] method.
pub type PagesState<C> = (Range<Vaddr>, Option<<C as PageTableConfig>::Item>);


pub tracked struct CursorContinuation<'rcu, C: PageTableConfig> {
    pub entry_own: EntryOwner<'rcu, C>,
    pub idx: usize,
    pub level: nat,
    pub tree_level: nat,
    pub children: Seq<Option<OwnerSubtree<'rcu, C>>>,
}

impl<'rcu, C: PageTableConfig> CursorContinuation<'rcu, C> {
    #[verifier::returns(proof)]
    pub proof fn take_child(tracked &mut self, idx: usize) -> (res: OwnerSubtree<'rcu, C>)
        requires
            0 <= idx < old(self).children.len(),
            old(self).children[idx as int] is Some,
        ensures
            self.children.len() == old(self).children.len(),
            res == old(self).children[idx as int].unwrap(),
            forall|i: int| 0 <= i < idx ==> self.children[i] == old(self).children[i],
            self.children[idx as int] is None,
            forall|i: int|
                idx < i < old(self).children.len() ==> self.children[i] == old(self).children[i],
            self.level == old(self).level,
            self.tree_level == old(self).tree_level,
            self.idx == old(self).idx,
            self.entry_own == old(self).entry_own,
    {
        let tracked child = self.children.tracked_remove(idx as int).tracked_unwrap();
        self.children.tracked_insert(idx as int, None);
        child
    }

    #[verifier::returns(proof)]
    pub proof fn put_child(tracked &mut self, idx: usize, tracked child: OwnerSubtree<'rcu, C>)
        requires
            0 <= idx < old(self).children.len(),
            old(self).children[idx as int] is None,
        ensures
            self.children.len() == old(self).children.len(),
            forall|i: int| 0 <= i < idx ==> self.children[i] == old(self).children[i],
            self.children[idx as int] == Some(child),
            forall|i: int|
                idx < i < old(self).children.len() ==> self.children[i] == old(self).children[i],
            self.level == old(self).level,
            self.tree_level == old(self).tree_level,
            self.idx == old(self).idx,
            self.entry_own == old(self).entry_own,
    {
        let _ = self.children.tracked_remove(idx as int);
        self.children.tracked_insert(idx as int, Some(child));
    }

    pub open spec fn make_cont_spec(self, idx: usize) -> (Self, Self) {
        let child = Self {
            entry_own: self.children[idx as int].unwrap().value,
            level: (self.level - 1) as nat,
            tree_level: (self.tree_level + 1) as nat,
            idx: idx,
            children: self.children[idx as int].unwrap().children,
        };
        let cont = Self {
            entry_own: self.entry_own,
            level: self.level,
            tree_level: self.tree_level,
            idx: self.idx,
            children: self.children.update(idx as int, None),
        };
        (child, cont)
    }

    #[verifier::returns(proof)]
    pub axiom fn make_cont(tracked &mut self, idx: usize) -> (res: Self)
        requires
            0 <= idx < NR_ENTRIES(),
        ensures
            res == old(self).make_cont_spec(idx).0,
            self == old(self).make_cont_spec(idx).1,
    ;

    pub open spec fn restore_spec(self, child: Self) -> Self {
        let child_node = OwnerSubtree {
            value: child.entry_own,
            level: child.level,
            children: child.children,
        };
        Self { children: self.children.update(self.idx as int, Some(child_node)), ..self }
    }

    pub axiom fn restore(&mut self, child: Self)
        ensures
            self == old(self).restore_spec(child),
    ;

    pub proof fn cont_property(self, idx: usize)
        requires
            0 <= idx < NR_ENTRIES(),
            self.children[idx as int] is Some,
        ensures
            self.make_cont_spec(idx).1.restore_spec(self.make_cont_spec(idx).0) == self,
    {
        admit()
    }

    pub open spec fn prev_views(self) -> Seq<FrameView<C>> {
        self.children.take(self.idx as int).flat_map(
            |child: Option<OwnerSubtree<'rcu, C>>|
                match child {
                    Some(child) => OwnerAsTreeNode::view_rec(child, self.level as int),
                    None => Seq::empty(),
                },
        )
    }

    pub open spec fn next_views(self) -> Seq<FrameView<C>> {
        self.children.skip(self.idx as int).flat_map(
            |child: Option<OwnerSubtree<'rcu, C>>|
                match child {
                    Some(child) => OwnerAsTreeNode::view_rec(child, self.level as int),
                    None => Seq::empty(),
                },
        )
    }

    pub open spec fn inv(self) -> bool {
        &&& self.children.len() == NR_ENTRIES()
        &&& 0 <= self.idx < NR_ENTRIES()
        &&& forall|i: int|
            0 <= i < NR_ENTRIES() ==> self.children[i] is Some ==> {
                &&& self.children[i].unwrap().inv()
                &&& self.children[i].unwrap().level == self.tree_level
                &&& self.tree_level == INC_LEVELS() - self.level
                &&& self.children[i].unwrap().value.relate_parent_guard_perm(
                    self.entry_own.node.unwrap().guard_perm,
                )
            }
        &&& self.entry_own.is_node()
        &&& self.entry_own.inv()
    }

    pub open spec fn all_some(self) -> bool {
        forall|i: int| 0 <= i < NR_ENTRIES() ==> self.children[i] is Some
    }
}

#[rustc_has_incoherent_inherent_impls]
pub tracked struct CursorOwner<'rcu, C: PageTableConfig> {
    pub path: TreePath<CONST_NR_ENTRIES>,
    pub level: PagingLevel,
    pub index: usize,
    pub continuations: Map<int, CursorContinuation<'rcu, C>>,
}

impl<'rcu, C: PageTableConfig> Inv for CursorOwner<'rcu, C> {
    open spec fn inv(self) -> bool {
        &&& 0 <= self.index < NR_ENTRIES()
        &&& 1 <= self.level <= NR_LEVELS()
        &&& forall|i: int|
            self.level - 1 <= i <= NR_LEVELS() - 1 ==> self.continuations.contains_key(i)
        &&& forall|i: int|
            self.level - 1 <= i <= NR_LEVELS() - 1 ==> {
                &&& self.continuations[i].inv()
                &&& self.continuations[i].level == i
            }
        &&& self.continuations[self.level
            - 1].all_some()
    }
}

impl<'rcu, C: PageTableConfig> CursorOwner<'rcu, C> {
    /// The number of steps it will take to walk through every node of a full
    /// page table at level `level`
    pub open spec fn max_steps_subtree(level: usize) -> usize
        decreases level,
    {
        if level <= 1 {
            NR_ENTRIES()
        } else {
            (NR_ENTRIES() * (Self::max_steps_subtree((level - 1) as usize)
                + 1)) as usize  // One step to push down a level, then the number for that subtree

        }
    }

    pub open spec fn max_steps_partial(self, level: usize) -> usize
        decreases NR_LEVELS() - level,
        when level <= NR_LEVELS()
    {
        if level == NR_LEVELS() {
            0
        } else {
            let cont = self.continuations[level as int];
            (Self::max_steps_subtree(level) * (NR_ENTRIES() - cont.idx) + self.max_steps_partial(
                (level + 1) as usize,
            )) as usize
        }
    }

    pub open spec fn max_steps(self) -> usize {
        self.max_steps_partial((self.level - 1) as usize)
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

    pub open spec fn prev_views_rec(self, i: int) -> Seq<FrameView<C>>
        decreases i,
        when self.level > 0
    {
        if i < self.level {
            Seq::empty()
        } else {
            self.prev_views_rec(i - 1).add(self.continuations[i - 1].prev_views())
        }
    }

    pub open spec fn next_views_rec(self, i: int) -> Seq<FrameView<C>>
        decreases i,
        when self.level > 0
    {
        if i < self.level {
            Seq::empty()
        } else {
            self.continuations[i - 1].next_views().add(self.next_views_rec(i - 1))
        }
    }

    pub open spec fn cur_at_level(self, lv: u8) -> Option<EntryOwner<'rcu, C>> {
        if lv > self.level {
            Some(self.continuations[self.level - 2].entry_own)
        } else if lv == self.level && self.continuations[self.level
            - 1].children[self.index as int] is Some {
            Some(self.continuations[self.level - 1].children[self.index as int].unwrap().value)
        } else {
            None
        }
    }

    pub open spec fn cur_entry_owner(self) -> Option<EntryOwner<'rcu, C>> {
        self.cur_at_level(self.level)
    }
}

#[rustc_has_incoherent_inherent_impls]
pub tracked struct CursorView<C: PageTableConfig> {
    pub cur_va: usize,
    pub scope: usize,
    pub fore: Seq<FrameView<C>>,
    pub rear: Seq<FrameView<C>>,
}

impl<C: PageTableConfig> Inv for CursorView<C> {
    open spec fn inv(self) -> bool {
        true
    }
}

impl<'rcu, C: PageTableConfig> View for CursorOwner<'rcu, C> {
    type V = CursorView<C>;

    open spec fn view(&self) -> Self::V {
        CursorView {
            cur_va: vaddr(self.path),
            scope: page_size(self.level as u8),
            fore: self.prev_views_rec(NR_LEVELS() as int),
            rear: self.next_views_rec(NR_LEVELS() as int),
        }
    }
}

impl<'rcu, C: PageTableConfig> InvView for CursorOwner<'rcu, C> {
    proof fn view_preserves_inv(self) {
    }
}

impl<'rcu, C: PageTableConfig, A: InAtomicMode> OwnerOf for Cursor<'rcu, C, A> {
    type Owner = CursorOwner<'rcu, C>;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& self.level == owner.level
        &&& owner.index == self.va % page_size(self.level)
        &&& self.level <= 4 ==> {
            &&& self.path[3] is Some
            &&& owner.continuations.contains_key(3)
            &&& owner.continuations[3].entry_own.node.unwrap().guard_perm.pptr()
                == self.path[3].unwrap()
        }
        &&& self.level <= 3 ==> {
            &&& self.path[2] is Some
            &&& owner.continuations.contains_key(2)
            &&& owner.continuations[2].entry_own.node.unwrap().guard_perm.pptr()
                == self.path[2].unwrap()
            &&& owner.continuations[3].entry_own.node.unwrap().guard_perm.addr()
                == owner.continuations[2].entry_own.guard_addr
        }
        &&& self.level <= 2 ==> {
            &&& self.path[1] is Some
            &&& owner.continuations.contains_key(1)
            &&& owner.continuations[1].entry_own.node.unwrap().guard_perm.pptr()
                == self.path[1].unwrap()
            &&& owner.continuations[2].entry_own.node.unwrap().guard_perm.addr()
                == owner.continuations[1].entry_own.guard_addr
        }
        &&& self.level == 1 ==> {
            &&& self.path[0] is Some
            &&& owner.continuations.contains_key(0)
            &&& owner.continuations[0].entry_own.node.unwrap().guard_perm.pptr()
                == self.path[0].unwrap()
            &&& owner.continuations[1].entry_own.node.unwrap().guard_perm.addr()
                == owner.continuations[0].entry_own.guard_addr
        }
    }
}

impl<'rcu, C: PageTableConfig, A: InAtomicMode> ModelOf for Cursor<'rcu, C, A> {

}

} // verus!

