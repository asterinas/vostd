use vstd::prelude::*;

use vstd_extra::ownership::*;
use vstd_extra::ghost_tree::TreePath;
use vstd_extra::undroppable::*;

use crate::mm::page_table::*;

use core::marker::PhantomData;
use core::ops::Range;

use crate::mm::{Paddr, PagingConstsTrait, PagingLevel, Vaddr};
use crate::mm::page_prop::PageProperty;
use crate::specs::arch::mm::{CONST_NR_ENTRIES, NR_ENTRIES, NR_LEVELS, PAGE_SIZE};
use crate::specs::arch::paging_consts::PagingConsts;
use crate::specs::arch::mm::MAX_USERSPACE_VADDR;
use crate::specs::mm::page_table::node::GuardPerm;
use crate::specs::mm::page_table::owners::*;
use crate::specs::mm::page_table::AbstractVaddr;
use crate::specs::mm::page_table::Guards;
use crate::specs::mm::page_table::Mapping;
use crate::specs::mm::page_table::view::PageTableView;
use crate::specs::task::InAtomicMode;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;

verus! {

pub tracked struct CursorContinuation<'rcu, C: PageTableConfig> {
    pub entry_own: EntryOwner<C>,
    pub idx: usize,
    pub tree_level: nat,
    pub children: Seq<Option<OwnerSubtree<C>>>,
    pub guard_perm: GuardPerm<'rcu, C>,
}

impl<'rcu, C: PageTableConfig> CursorContinuation<'rcu, C> {
    pub open spec fn path(self) -> TreePath<CONST_NR_ENTRIES> {
        self.entry_own.node.unwrap().path
    }

    pub open spec fn child(self) -> OwnerSubtree<C> {
        self.children[self.idx as int].unwrap()
    }

    pub open spec fn take_child_spec(self) -> (OwnerSubtree<C>, Self) {
        let child = self.children[self.idx as int].unwrap();
        let cont = Self {
            children: self.children.remove(self.idx as int).insert(self.idx as int, None),
            ..self
        };
        (child, cont)
    }

    #[verifier::returns(proof)]
    pub proof fn take_child(tracked &mut self) -> (res: OwnerSubtree<C>)
        requires
            old(self).idx < old(self).children.len(),
            old(self).children[old(self).idx as int] is Some,
        ensures
            res == old(self).take_child_spec().0,
            *self == old(self).take_child_spec().1,
    {
        let tracked child = self.children.tracked_remove(old(self).idx as int).tracked_unwrap();
        self.children.tracked_insert(old(self).idx as int, None);
        child
    }

    pub open spec fn put_child_spec(self, child: OwnerSubtree<C>) -> Self {
        Self {
            children: self.children.remove(self.idx as int).insert(self.idx as int, Some(child)),
            ..self
        }
    }

    #[verifier::returns(proof)]
    pub proof fn put_child(tracked &mut self, tracked child: OwnerSubtree<C>)
        requires
            old(self).idx < old(self).children.len(),
            old(self).children[old(self).idx as int] is None,
        ensures
            *self == old(self).put_child_spec(child)
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
            entry_own: self.children[self.idx as int].unwrap().value,
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
            *self == old(self).make_cont_spec(idx, guard_perm@).1,
    ;

    pub open spec fn restore_spec(self, child: Self) -> (Self, GuardPerm<'rcu, C>) {
        let child_node = OwnerSubtree {
            value: child.entry_own,
            level: child.tree_level,
            children: child.children,
        };
        (Self { children: self.children.update(self.idx as int, Some(child_node)), ..self }, child.guard_perm)
    }

    #[verifier::returns(proof)]
    pub axiom fn restore(tracked &mut self, tracked child: Self) -> (tracked guard_perm: Tracked<GuardPerm<'rcu, C>>)
        ensures
            self == old(self).restore_spec(child).0,
            guard_perm@ == old(self).restore_spec(child).1,
    ;

    pub open spec fn map_children(self, f: spec_fn(EntryOwner<C>, TreePath<CONST_NR_ENTRIES>) -> bool) -> bool {
        forall |i: int| 0 <= i < self.children.len() ==>
            self.children[i] is Some ==>
            self.children[i].unwrap().tree_predicate_map(self.path().push_tail(i as usize), f)
    }

    pub open spec fn level(self) -> PagingLevel {
        self.entry_own.node.unwrap().level
    }

    pub open spec fn inv(self) -> bool {
        &&& self.children.len() == NR_ENTRIES()
        &&& 0 <= self.idx < NR_ENTRIES()
        &&& forall|i: int|
            #![trigger self.children[i]]
            0 <= i < NR_ENTRIES() ==> 
            self.children[i] is Some ==> {
                &&& self.children[i].unwrap().value.parent_path == self.path()
                &&& self.children[i].unwrap().value.parent_level == self.level()
                &&& self.children[i].unwrap().inv()
                &&& self.children[i].unwrap().level == self.tree_level + 1
            }
        &&& self.entry_own.is_node()
        &&& self.entry_own.inv()
        &&& self.entry_own.node.unwrap().relate_guard_perm(self.guard_perm)
        &&& self.tree_level == INC_LEVELS() - self.level()
        &&& self.tree_level < INC_LEVELS() - 1
        &&& self.path().len() == self.tree_level
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
            *self == old(self).inc_index(),
    {
        self.idx = (self.idx + 1) as usize;
    }

    /*
    pub proof fn never_drop_preserves_children_not_locked(
        self,
        guard: PageTableGuard<'rcu, C>,
        guards0: Guards<'rcu, C>,
        guards1: Guards<'rcu, C>)
        requires
            self.inv(),
            self.children_not_locked(guards0),
            <PageTableGuard<'rcu, C> as Undroppable>::constructor_requires(guard,guards0),
            <PageTableGuard<'rcu, C> as Undroppable>::constructor_ensures(guard, guards0, guards1),
        ensures
            self.children_not_locked(guards1),
    {
        admit();
        /*
        assert forall|i: int| 0 <= i < self.children.len() && self.children[i] is Some ==>
            PageTableOwner::unlocked(self.children[i].unwrap(), self.path, guards1) by {
            PageTableOwner::map_implies(self.children[i].unwrap(), self.path,
                |owner: EntryOwner<C>, path: TreePath<CONST_NR_ENTRIES>|
                    guards0.unlocked(owner.node.unwrap().meta_perm.addr()),
                |owner: EntryOwner<C>, path: TreePath<CONST_NR_ENTRIES>|
                    guards1.unlocked(owner.node.unwrap().meta_perm.addr()));
        }
        */
    }
    */

    pub open spec fn node_locked(self, guards: Guards<'rcu, C>) -> bool {
        guards.lock_held(self.guard_perm.value().inner.inner@.ptr.addr())
    }

    pub open spec fn relate_region(self, regions: MetaRegionOwners) -> bool {
        &&& self.entry_own.node.unwrap().relate_region(regions)
        &&& forall|i: int| 0 <= i < self.children.len() && self.children[i] is Some ==>
            PageTableOwner(self.children[i].unwrap()).relate_region_rec(self.path().push_tail(i as usize), regions)
    }

    pub open spec fn view_mappings(self) -> Set<Mapping> {
        Set::new(
            |m: Mapping| exists|i:int| 0 <= i < self.children.len() &&
                self.children[i] is Some &&
                PageTableOwner(self.children[i].unwrap()).view_rec(self.path().push_tail(i as usize)).contains(m)
        )
    }

    pub open spec fn view_mappings_take_child_spec(self) -> Set<Mapping> {
        PageTableOwner(self.children[self.idx as int].unwrap()).view_rec(self.path().push_tail(self.idx as usize))
    }

    pub proof fn view_mappings_take_child(self)
        requires
            self.inv(),
            self.all_some(),
        ensures
            self.take_child_spec().1.view_mappings() == self.view_mappings() - self.view_mappings_take_child_spec()
    {
        let def = self.take_child_spec().1.view_mappings();
        let diff = self.view_mappings() - self.view_mappings_take_child_spec();
        assert forall |m: Mapping| diff.contains(m) implies def.contains(m) by {
            let i = choose|i: int| 0 <= i < self.children.len() && self.children[i] is Some &&
                PageTableOwner(self.children[i].unwrap()).view_rec(self.path().push_tail(i as usize)).contains(m);
            assert(i != self.idx);
            assert(self.take_child_spec().1.children[i] is Some);
        };
        assert forall |m: Mapping| def.contains(m) implies diff.contains(m) by {
            let left = self.take_child_spec().1;
            assert(left.view_mappings().contains(m));
            if self.view_mappings_take_child_spec().contains(m) {
                assert(PageTableOwner(self.children[self.idx as int].unwrap()).view_rec(self.path().push_tail(self.idx as usize)).contains(m));
                let i = choose|i: int| 0 <= i < left.children.len() && left.children[i] is Some &&
                    PageTableOwner(left.children[i].unwrap()).view_rec(left.path().push_tail(i as usize)).contains(m);
                assert(i != self.idx);
                assert(PageTableOwner(left.children[i as int].unwrap()).view_rec(left.path().push_tail(i as usize)).contains(m));

                PageTableOwner(self.children[self.idx as int].unwrap()).view_rec_vaddr_range(self.path().push_tail(self.idx as usize), m);
                PageTableOwner(left.children[i as int].unwrap()).view_rec_vaddr_range(left.path().push_tail(i as usize), m);

                let size = page_size(self.path().push_tail(self.idx as usize).len() as PagingLevel);

                // TODO: arithmetic property of vaddr()
                assert(vaddr(self.path().push_tail(self.idx as usize)) + size <= vaddr(left.path().push_tail(i as usize)) ||
                    vaddr(left.path().push_tail(i as usize)) + size <= vaddr(self.path().push_tail(self.idx as usize))) by { admit() };

            }
        };
    }

    pub proof fn view_mappings_put_child(self, child: OwnerSubtree<C>)
        requires
            self.inv(),
            child.inv(),
            self.all_but_index_some(),
        ensures
            self.put_child_spec(child).view_mappings() == self.view_mappings() + PageTableOwner(child).view_rec(self.path().push_tail(self.idx as usize))
    {
        let def = self.put_child_spec(child).view_mappings();
        let sum = self.view_mappings() + PageTableOwner(child).view_rec(self.path().push_tail(self.idx as usize));
        assert forall |m: Mapping| sum.contains(m) implies def.contains(m) by {
            if self.view_mappings().contains(m) {
                let i = choose|i: int| 0 <= i < self.children.len() && self.children[i] is Some &&
                    PageTableOwner(self.children[i].unwrap()).view_rec(self.path().push_tail(i as usize)).contains(m);
                assert(i != self.idx);
                assert(self.put_child_spec(child).children[i] == self.children[i]);
            } else {
                assert(PageTableOwner(child).view_rec(self.path().push_tail(self.idx as usize)).contains(m));
                assert(self.put_child_spec(child).children[self.idx as int] == Some(child));
            }
        };
    }

    pub proof fn new_child(tracked &self, paddr: Paddr, prop: PageProperty) -> (tracked res: OwnerSubtree<C>)
        requires
            self.inv(),
        ensures
            res.value == EntryOwner::<C>::new_frame_spec(paddr, self.path(), self.level(), prop),
            res.inv(),
            res.level == self.tree_level + 1
    {
        let tracked owner = EntryOwner::<C>::new_frame(paddr, self.path(), self.level(), prop);
        OwnerSubtree::new_val_tracked(owner, self.tree_level + 1)
    }
}

#[rustc_has_incoherent_inherent_impls]
pub tracked struct CursorOwner<'rcu, C: PageTableConfig> {
    pub level: PagingLevel,
    pub continuations: Map<int, CursorContinuation<'rcu, C>>,
    pub va: AbstractVaddr,
    pub guard_level: PagingLevel,
    pub prefix: AbstractVaddr,
    pub popped_too_high: bool,
}

impl<'rcu, C: PageTableConfig> Inv for CursorOwner<'rcu, C> {
    open spec fn inv(self) -> bool {
        &&& self.va.inv()
        &&& 1 <= self.level <= NR_LEVELS()
        &&& self.guard_level <= NR_LEVELS()
        // The cursor is allowed to pop out of the guard range only when it reaches the end of the locked range.
        // This allows the user to reason solely about the current vaddr and not keep track of the cursor's level.
        &&& self.popped_too_high ==> self.level >= self.guard_level && self.in_locked_range()
        &&& !self.popped_too_high ==> self.level < self.guard_level || self.above_locked_range()
        &&& self.continuations[self.level - 1].all_some()
        &&& forall|i: int| self.level <= i < NR_LEVELS() ==> {
            (#[trigger] self.continuations[i]).all_but_index_some()
        }
        &&& self.prefix.inv()
        &&& forall|i: int| i < self.guard_level ==> self.prefix.index[i] == 0
        &&& self.level <= 4 ==> {
            &&& self.continuations.contains_key(3)
            &&& self.continuations[3].inv()
            &&& self.continuations[3].level() == 4
            // Obviously there is no level 5 pt, but that would be the level of the parent of the root pt.
            &&& self.continuations[3].entry_own.parent_level == 5
            &&& self.va.index[3] == self.continuations[3].idx
        }
        &&& self.level <= 3 ==> {
            &&& self.continuations.contains_key(2)
            &&& self.continuations[2].inv()
            &&& self.continuations[2].level() == 3
            &&& self.continuations[2].entry_own.parent_level == 4
            &&& self.va.index[2] == self.continuations[2].idx
            &&& self.continuations[2].guard_perm.value().inner.inner@.ptr.addr() !=
                self.continuations[3].guard_perm.value().inner.inner@.ptr.addr()
        }
        &&& self.level <= 2 ==> {
            &&& self.continuations.contains_key(1)
            &&& self.continuations[1].inv()
            &&& self.continuations[1].level() == 2
            &&& self.continuations[1].entry_own.parent_level == 3
            &&& self.va.index[1] == self.continuations[1].idx
            &&& self.continuations[1].guard_perm.value().inner.inner@.ptr.addr() !=
                self.continuations[2].guard_perm.value().inner.inner@.ptr.addr()
            &&& self.continuations[1].guard_perm.value().inner.inner@.ptr.addr() !=
                self.continuations[3].guard_perm.value().inner.inner@.ptr.addr()
        }
        &&& self.level == 1 ==> {
            &&& self.continuations.contains_key(0)
            &&& self.continuations[0].inv()
            &&& self.continuations[0].level() == 1
            &&& self.continuations[0].entry_own.parent_level == 2
            &&& self.va.index[0] == self.continuations[0].idx
            &&& self.continuations[0].guard_perm.value().inner.inner@.ptr.addr() !=
                self.continuations[1].guard_perm.value().inner.inner@.ptr.addr()
            &&& self.continuations[0].guard_perm.value().inner.inner@.ptr.addr() !=
                self.continuations[2].guard_perm.value().inner.inner@.ptr.addr()
            &&& self.continuations[0].guard_perm.value().inner.inner@.ptr.addr() !=
                self.continuations[3].guard_perm.value().inner.inner@.ptr.addr()
        }
    }
}

impl<'rcu, C: PageTableConfig> CursorOwner<'rcu, C> {

    pub open spec fn node_unlocked(guards: Guards<'rcu, C>) ->
        (spec_fn(EntryOwner<C>, TreePath<CONST_NR_ENTRIES>) -> bool) {
        |owner: EntryOwner<C>, path: TreePath<CONST_NR_ENTRIES>|
            owner.is_node() ==>
            guards.unlocked(owner.node.unwrap().meta_perm.addr())
    }

    pub open spec fn node_unlocked_except(guards: Guards<'rcu, C>, addr: usize) ->
        (spec_fn(EntryOwner<C>, TreePath<CONST_NR_ENTRIES>) -> bool) {
        |owner: EntryOwner<C>, path: TreePath<CONST_NR_ENTRIES>|
            owner.is_node() ==>
            owner.node.unwrap().meta_perm.addr() != addr ==>
            guards.unlocked(owner.node.unwrap().meta_perm.addr())
    }

    pub open spec fn children_not_locked(self, guards: Guards<'rcu, C>) -> bool {
        forall|i: int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS() ==> {
                self.continuations[i].map_children(Self::node_unlocked(guards))
            }
    }

    pub open spec fn only_current_locked(self, guards: Guards<'rcu, C>) -> bool {
        forall|i: int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS() ==>
            self.continuations[i].map_children(Self::node_unlocked_except(guards, self.cur_entry_owner().node.unwrap().meta_perm.addr()))
    }

    pub proof fn never_drop_preserves_nodes_locked(
        self,
        guard: PageTableGuard<'rcu, C>,
        guards0: Guards<'rcu, C>,
        guards1: Guards<'rcu, C>)
        requires
            self.inv(),
            self.nodes_locked(guards0),
            <PageTableGuard<'rcu, C> as Undroppable>::constructor_requires(guard, guards0),
            <PageTableGuard<'rcu, C> as Undroppable>::constructor_ensures(guard, guards0, guards1),
            forall|i: int| self.level - 1 <= i < NR_LEVELS() ==>
                self.continuations[i].guard_perm.value().inner.inner@.ptr.addr() != 
                    guard.inner.inner@.ptr.addr(),
        ensures
            self.nodes_locked(guards1),
    { admit() }

    pub proof fn never_drop_preserves_children_not_locked(
        self,
        guard: PageTableGuard<'rcu, C>,
        guards0: Guards<'rcu, C>,
        guards1: Guards<'rcu, C>)
    requires
        self.inv(),
        self.children_not_locked(guards0),
        <PageTableGuard<'rcu, C> as Undroppable>::constructor_requires(guard, guards0),
        <PageTableGuard<'rcu, C> as Undroppable>::constructor_ensures(guard, guards0, guards1),
    ensures
        self.children_not_locked(guards1),
    {
        admit()
    }

    pub proof fn map_children_implies(
        self,
        f: spec_fn(EntryOwner<C>, TreePath<CONST_NR_ENTRIES>) -> bool,
        g: spec_fn(EntryOwner<C>, TreePath<CONST_NR_ENTRIES>) -> bool,
    )
    requires
        self.inv(),
        OwnerSubtree::implies(f, g),
        forall|i: int| self.level - 1 <= i < NR_LEVELS() ==>
            self.continuations[i].map_children(f),
    ensures
        forall|i: int| self.level - 1 <= i < NR_LEVELS() ==>
            self.continuations[i].map_children(g),
    {
        assert forall|i: int| self.level - 1 <= i < NR_LEVELS() implies self.continuations[i].map_children(g) by {
            let cont = self.continuations[i];
            assert forall|j: int| 0 <= j < cont.children.len() && cont.children[j] is Some
                implies cont.children[j].unwrap().tree_predicate_map(cont.path().push_tail(j as usize), g) by {
                OwnerSubtree::map_implies(cont.children[j].unwrap(), cont.path().push_tail(j as usize), f, g);
            }
        }
    }

    pub open spec fn nodes_locked(self, guards: Guards<'rcu, C>) -> bool {
        forall|i: int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS() ==> {
                self.continuations[i].node_locked(guards)
            }
    }

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
            popped_too_high: false,
            ..self
        }
    }

    pub open spec fn zero_below_level_rec(self, level: PagingLevel) -> Self
        decreases self.level - level
    {
        if self.level <= level {
            self
        } else {
            Self {
                va: AbstractVaddr {
                    offset: self.va.offset,
                    index: self.va.index.insert(level - 1, 0)
                },
                ..self.zero_below_level_rec((level + 1) as u8)
            }
        }
    }

    pub open spec fn zero_below_level(self) -> Self {
        self.zero_below_level_rec(1u8)
    }

    pub proof fn zero_below_level_rec_preserves_above(self, level: PagingLevel)
        ensures
            forall |lv: int| lv >= self.level ==> self.zero_below_level_rec(level).va.index[lv] == self.va.index[lv],
        decreases self.level - level,
    {
        if self.level > level {
            self.zero_below_level_rec_preserves_above((level + 1) as u8);
        }
    }

    pub proof fn zero_preserves_above(self)
        ensures
            forall |lv: int| lv >= self.level ==> self.zero_below_level().va.index[lv] == self.va.index[lv],
    {
        self.zero_below_level_rec_preserves_above(1u8);
    }

    pub axiom fn do_zero_below_level(tracked &mut self)
        requires
            old(self).inv(),
        ensures
            *self == old(self).zero_below_level();

    pub proof fn do_inc_index(tracked &mut self)
        requires
            old(self).inv(),
            old(self).continuations[old(self).level - 1].idx + 1 < NR_ENTRIES(),
            old(self).in_locked_range(),
        ensures
            self.inv(),
            *self == old(self).inc_index(),
    {
        self.popped_too_high = false;
        let tracked mut cont = self.continuations.tracked_remove(self.level - 1);
        if self.level >= self.guard_level {
            let ghost size = self.locked_range().end - self.locked_range().start;
            let ghost new_va = AbstractVaddr {
                offset: self.va.offset,
                index: self.va.index.insert(self.level - 1, cont.idx + 1)
            };
            assert(new_va.to_vaddr() == self.va.to_vaddr() + size) by { admit() };
        }

        cont.do_inc_index();
        self.va.index.tracked_insert(self.level - 1, cont.idx as int);
        self.continuations.tracked_insert(self.level - 1, cont);
        assert(self.continuations == old(self).continuations.insert(self.level - 1, cont));
    }

    pub proof fn inc_and_zero_increases_va(self)
        requires
            self.inv()
        ensures
            self.inc_index().zero_below_level().va.to_vaddr() > self.va.to_vaddr(),
    {
        admit()
    }

    pub proof fn zero_rec_preserves_all_but_va(self, level: PagingLevel)
        ensures
            self.zero_below_level_rec(level).level == self.level,
            self.zero_below_level_rec(level).continuations == self.continuations,
            self.zero_below_level_rec(level).guard_level == self.guard_level,
            self.zero_below_level_rec(level).prefix == self.prefix,
            self.zero_below_level_rec(level).popped_too_high == self.popped_too_high,
        decreases self.level - level,
    {
        if self.level > level {
            self.zero_rec_preserves_all_but_va((level + 1) as u8);
        }
    }

    pub proof fn zero_preserves_all_but_va(self)
        ensures
            self.zero_below_level().level == self.level,
            self.zero_below_level().continuations == self.continuations,
            self.zero_below_level().guard_level == self.guard_level,
            self.zero_below_level().prefix == self.prefix,
            self.zero_below_level().popped_too_high == self.popped_too_high,
    {
        self.zero_rec_preserves_all_but_va(1u8);
    }

    pub open spec fn cur_va(self) -> Vaddr {
        self.va.to_vaddr()
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

    pub open spec fn view_mappings(self) -> Set<Mapping>
    {
        Set::new(
            |m: Mapping| exists|i:int| self.level - 1 <= i < NR_LEVELS() - 1 && self.continuations[i].view_mappings().contains(m)
        )
    }

    pub proof fn view_mappings_remove(self, new: Self, i: int)
        requires
            self.inv(),
            self.continuations.contains_key(i),
            new.continuations == self.continuations.remove(i),
        ensures
            new.view_mappings() == self.view_mappings() - self.continuations[i].view_mappings(),
    { admit() }

    pub proof fn view_mappings_insert(self, new: Self, i: int, cont: CursorContinuation<C>)
        requires
            self.inv(),
            cont.inv(),
            new.continuations == self.continuations.insert(i, cont),
        ensures
            new.view_mappings() == self.view_mappings() + cont.view_mappings(),
    { admit() }

    pub proof fn view_mappings_replace(self, new: Self, i: int, cont: CursorContinuation<C>, f: spec_fn(Set<Mapping>) -> Set<Mapping>)
        requires
            self.inv(),
            cont.inv(),
            new.continuations == self.continuations.remove(i).insert(i, cont),
            f(self.continuations[i].view_mappings()) == cont.view_mappings(),
        ensures
            new.view_mappings() == f(self.view_mappings()),
    {
        assert forall |m: Mapping| new.view_mappings().contains(m) implies f(self.view_mappings()).contains(m) by {
            admit()
        };
        assert forall |m: Mapping| f(self.view_mappings()).contains(m) implies new.view_mappings().contains(m) by {
            admit()
        };
    }

    pub open spec fn cur_entry_owner(self) -> EntryOwner<C> {
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

    pub open spec fn above_locked_range(self) -> bool {
        self.va.to_vaddr() >= self.locked_range().end
    }

    pub proof fn prefix_in_locked_range(self)
        requires
            forall|i:int| i >= self.guard_level ==> self.va.index[i] == self.prefix.index[i],
        ensures
            self.in_locked_range(),
    { admit() }

    pub open spec fn relate_region(self, regions: MetaRegionOwners) -> bool
    {
        let f = |owner: EntryOwner<C>, path: TreePath<CONST_NR_ENTRIES>|
            owner.is_node() ==> owner.node.unwrap().relate_region(regions);
        forall|i: int| self.level - 1 <= i < NR_LEVELS() ==> self.continuations[i].map_children(f)
    }
}

pub tracked struct CursorView<C: PageTableConfig> {
    pub cur_va: Vaddr,
    pub mappings: Set<Mapping>,
    pub phantom: PhantomData<C>,
}

impl<'rcu, C: PageTableConfig> View for CursorOwner<'rcu, C> {
    type V = CursorView<C>;

    open spec fn view(&self) -> Self::V {
        CursorView {
            cur_va: self.cur_va(),
            mappings: self.into_pt_owner_rec().view().mappings,
            phantom: PhantomData,
        }
    }
}

impl<C: PageTableConfig> Inv for CursorView<C> {
    open spec fn inv(self) -> bool {
        &&& self.cur_va < MAX_USERSPACE_VADDR()
        &&& forall|m: Mapping| #![auto] self.mappings.contains(m) ==> m.inv()
        &&& forall|m: Mapping, n: Mapping| #![auto]
            self.mappings.contains(m) ==>
            self.mappings.contains(n) ==>
            m != n ==>
            m.va_range.end <= n.va_range.start || n.va_range.end <= m.va_range.start
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
        &&& owner.guard_level == self.guard_level
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
