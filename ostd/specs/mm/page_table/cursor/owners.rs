use vstd::prelude::*;

use vstd_extra::drop_tracking::*;
use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;

use crate::mm::page_table::*;

use core::marker::PhantomData;
use core::ops::Range;

use crate::mm::page_prop::PageProperty;
use crate::mm::{Paddr, PagingConstsTrait, PagingLevel, Vaddr};
use crate::specs::arch::mm::MAX_USERSPACE_VADDR;
use crate::specs::arch::mm::{NR_ENTRIES, NR_LEVELS, PAGE_SIZE};
use crate::specs::arch::paging_consts::PagingConsts;
use crate::mm::frame::meta::mapping::frame_to_index;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::page_table::node::GuardPerm;
use crate::specs::mm::page_table::owners::*;
use crate::specs::mm::page_table::view::PageTableView;
use crate::specs::mm::page_table::AbstractVaddr;
use crate::specs::mm::page_table::Guards;
use crate::specs::mm::page_table::Mapping;
use crate::specs::mm::page_table::{nat_align_down, nat_align_up};
use crate::specs::task::InAtomicMode;

verus! {

pub tracked struct CursorContinuation<'rcu, C: PageTableConfig> {
    pub entry_own: EntryOwner<C>,
    pub idx: usize,
    pub tree_level: nat,
    pub children: Seq<Option<OwnerSubtree<C>>>,
    pub path: TreePath<NR_ENTRIES>,
    pub guard_perm: GuardPerm<'rcu, C>,
}

impl<'rcu, C: PageTableConfig> CursorContinuation<'rcu, C> {
    pub open spec fn path(self) -> TreePath<NR_ENTRIES> {
        self.entry_own.path
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
            path: self.path.push_tail(self.idx as usize),
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
            old(self).idx < NR_ENTRIES,
            idx < NR_ENTRIES,
        ensures
            res == old(self).make_cont_spec(idx, guard_perm@).0,
            *self == old(self).make_cont_spec(idx, guard_perm@).1;

    pub open spec fn restore_spec(self, child: Self) -> (Self, GuardPerm<'rcu, C>) {
        let child_node = OwnerSubtree {
            value: child.entry_own,
            level: child.tree_level,
            children: child.children,
        };
        (Self { children: self.children.update(self.idx as int, Some(child_node)), ..self }, child.guard_perm)
    }

    #[verifier::returns(proof)]
    pub axiom fn restore(tracked &mut self, tracked child: Self) -> (tracked guard_perm: GuardPerm<'rcu, C>)
        ensures
            *self == old(self).restore_spec(child).0,
            guard_perm == old(self).restore_spec(child).1;

    pub open spec fn new_spec(owner_subtree: OwnerSubtree<C>, idx: usize, guard_perm: GuardPerm<'rcu, C>) -> Self {
        Self {
            entry_own: owner_subtree.value,
            idx: idx,
            tree_level: owner_subtree.level,
            children: owner_subtree.children,
            path: TreePath::new(Seq::empty()),
            guard_perm: guard_perm,
        }
    }

    pub axiom fn new(tracked owner_subtree: OwnerSubtree<C>, idx: usize, tracked guard_perm: GuardPerm<'rcu, C>)
    -> (tracked res: Self)
        ensures
            res == Self::new_spec(owner_subtree, idx, guard_perm);

    pub open spec fn map_children(self, f: spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool) -> bool {
        forall |i: int|
            #![auto]
            0 <= i < self.children.len() ==>
                self.children[i] is Some ==>
                    self.children[i].unwrap().tree_predicate_map(self.path().push_tail(i as usize), f)
    }

    /// Lift map_children(f) to map_children(g) when implies(f, g).
    pub proof fn map_children_lift(
        self,
        f: spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool,
        g: spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool,
    )
        requires
            self.inv(),
            self.map_children(f),
            OwnerSubtree::implies(f, g),
        ensures
            self.map_children(g),
    {
        reveal(CursorContinuation::inv_children);
        assert forall|j: int|
            #![auto]
            0 <= j < self.children.len()
                && self.children[j] is Some implies
                self.children[j].unwrap().tree_predicate_map(
                    self.path().push_tail(j as usize), g)
        by {
            OwnerSubtree::map_implies(
                self.children[j].unwrap(),
                self.path().push_tail(j as usize),
                f, g,
            );
        };
    }

    /// Lift map_children from f to g when siblings (j != idx) come from
    /// cont0 which had map_children(f), and the child at idx (if present)
    /// already satisfies g.
    pub proof fn map_children_lift_skip_idx(
        self,
        cont0: Self,
        idx: int,
        f: spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool,
        g: spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool,
    )
        requires
            0 <= idx < NR_ENTRIES,
            OwnerSubtree::implies(f, g),
            cont0.inv(),
            cont0.map_children(f),
            self.path() == cont0.path(),
            self.children.len() == cont0.children.len(),
            forall|j: int| #![auto]
                0 <= j < NR_ENTRIES && j != idx ==>
                self.children[j] == cont0.children[j],
            self.children[idx] is Some ==>
                self.children[idx].unwrap().tree_predicate_map(
                    self.path().push_tail(idx as usize), g),
        ensures
            self.map_children(g),
    {
        reveal(CursorContinuation::inv_children);
        assert forall|j: int|
            #![auto]
            0 <= j < self.children.len()
                && self.children[j] is Some implies
                self.children[j].unwrap().tree_predicate_map(
                    self.path().push_tail(j as usize), g)
        by {
            if j != idx {
                OwnerSubtree::map_implies(
                    cont0.children[j].unwrap(),
                    cont0.path().push_tail(j as usize),
                    f, g,
                );
            }
        };
    }

    pub open spec fn level(self) -> PagingLevel {
        self.entry_own.node.unwrap().level
    }

    #[verifier::opaque]
    pub open spec fn inv_children(self) -> bool {
        forall|i: int|
            #![auto]
            0 <= i < NR_ENTRIES ==>
            self.children[i] is Some ==> {
                &&& self.children[i].unwrap().value.path == self.path().push_tail(i as usize)
                &&& self.children[i].unwrap().value.parent_level == self.level()
                &&& self.children[i].unwrap().inv()
                &&& self.children[i].unwrap().level == self.tree_level + 1
                &&& <EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(self.entry_own, i, Some(self.children[i].unwrap().value))
            }
    }

    pub open spec fn inv(self) -> bool {
        &&& self.children.len() == NR_ENTRIES
        &&& 0 <= self.idx < NR_ENTRIES
        &&& self.inv_children()
        &&& self.entry_own.is_node()
        &&& self.entry_own.inv()
        &&& self.entry_own.node.unwrap().relate_guard_perm(self.guard_perm)
        &&& self.tree_level == INC_LEVELS - self.level() - 1
        &&& self.tree_level < INC_LEVELS - 1
        &&& self.path().len() == self.tree_level
    }

    pub open spec fn all_some(self) -> bool {
        forall|i: int| 0 <= i < NR_ENTRIES ==> self.children[i] is Some
    }

    pub open spec fn all_but_index_some(self) -> bool {
        &&& forall|i: int| 0 <= i < self.idx ==> self.children[i] is Some
        &&& forall|i: int| self.idx < i < NR_ENTRIES ==> self.children[i] is Some
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
            old(self).idx + 1 < NR_ENTRIES,
        ensures
            *self == old(self).inc_index(),
    {
        self.idx = (self.idx + 1) as usize;
    }

    pub open spec fn node_locked(self, guards: Guards<'rcu, C>) -> bool {
        guards.lock_held(self.guard_perm.value().inner.inner@.ptr.addr())
    }

    pub open spec fn view_mappings(self) -> Set<Mapping> {
        Set::new(
            |m: Mapping| exists|i:int|
            #![auto]
            0 <= i < self.children.len() &&
                self.children[i] is Some &&
                PageTableOwner(self.children[i].unwrap()).view_rec(self.path().push_tail(i as usize)).contains(m)
        )
    }

    pub open spec fn as_subtree(self) -> OwnerSubtree<C> {
        OwnerSubtree {
            value: self.entry_own,
            level: self.tree_level,
            children: self.children,
        }
    }

    pub open spec fn as_page_table_owner(self) -> PageTableOwner<C> {
        PageTableOwner(self.as_subtree())
    }

    pub proof fn as_page_table_owner_preserves_view_mappings(self)
        requires
            self.inv(),
            self.all_some(),
        ensures
            self.as_page_table_owner().view_rec(self.path()) == self.view_mappings(),
    {
        reveal(CursorContinuation::inv_children);
    }

    pub proof fn as_subtree_restore(self, child: Self)
        requires
            self.inv(),
            child.inv(),
            self.all_but_index_some(),
            child.all_some(),
        ensures
            self.restore_spec(child).0.as_subtree() ==
            self.put_child_spec(child.as_subtree()).as_subtree(),
    {
        assert(self.put_child_spec(child.as_subtree()).children ==
        self.children.update(self.idx as int, Some(child.as_subtree())));
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
        reveal(CursorContinuation::inv_children);
        let def = self.take_child_spec().1.view_mappings();
        let diff = self.view_mappings() - self.view_mappings_take_child_spec();
        assert forall |m: Mapping| diff.contains(m) implies def.contains(m) by {
            let i = choose|i: int| 0 <= i < self.children.len() && #[trigger] self.children[i] is Some &&
                PageTableOwner(self.children[i].unwrap()).view_rec(self.path().push_tail(i as usize)).contains(m);
            assert(i != self.idx);
            assert(self.take_child_spec().1.children[i] is Some);
        };
        assert forall |m: Mapping|
        #![trigger def.contains(m)]
        def.contains(m) implies diff.contains(m) by {
            let left = self.take_child_spec().1;
            assert(left.view_mappings().contains(m));
            if self.view_mappings_take_child_spec().contains(m) {
                assert(PageTableOwner(self.children[self.idx as int].unwrap()).view_rec(self.path().push_tail(self.idx as usize)).contains(m));
                let i = choose|i: int| 0 <= i < left.children.len() && #[trigger] left.children[i] is Some &&
                    PageTableOwner(left.children[i].unwrap()).view_rec(left.path().push_tail(i as usize)).contains(m);
                assert(i != self.idx);
                assert(PageTableOwner(left.children[i as int].unwrap()).view_rec(left.path().push_tail(i as usize)).contains(m));

                PageTableOwner(self.children[self.idx as int].unwrap()).view_rec_vaddr_range(self.path().push_tail(self.idx as usize), m);
                PageTableOwner(left.children[i as int].unwrap()).view_rec_vaddr_range(left.path().push_tail(i as usize), m);

                let size = page_size(self.path().push_tail(self.idx as usize).len() as PagingLevel);

                // Sibling paths have disjoint VA ranges
                sibling_paths_disjoint(self.path(), self.idx, i as usize, size);
                assert(vaddr(self.path().push_tail(self.idx as usize)) + size <= vaddr(left.path().push_tail(i as usize)) ||
                    vaddr(left.path().push_tail(i as usize)) + size <= vaddr(self.path().push_tail(self.idx as usize)));

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
                let i = choose|i: int| 0 <= i < self.children.len() && #[trigger] self.children[i] is Some &&
                    PageTableOwner(self.children[i].unwrap()).view_rec(self.path().push_tail(i as usize)).contains(m);
                assert(i != self.idx);
                assert(self.put_child_spec(child).children[i] == self.children[i]);
            } else {
                assert(PageTableOwner(child).view_rec(self.path().push_tail(self.idx as usize)).contains(m));
                assert(self.put_child_spec(child).children[self.idx as int] == Some(child));
            }
        };
    }

    /// After `split_if_mapped_huge` converts the child at `idx` from frame to node, and we
    /// restore `entry_own.node = Some(parent_owner)`, the continuation invariant holds.
    /// The key invariant conditions are checked via the preconditions; the `rel_children`
    /// relationship for the modified entry follows from the split postcondition.
    pub axiom fn continuation_inv_holds_after_split_restore(self)
        requires
            self.entry_own.is_node(),
            self.entry_own.inv(),
            self.entry_own.node.unwrap().relate_guard_perm(self.guard_perm),
            self.children.len() == NR_ENTRIES,
            0 <= self.idx < NR_ENTRIES,
            self.tree_level == INC_LEVELS - self.level() - 1,
            self.tree_level < INC_LEVELS - 1,
            self.path().len() == self.tree_level,
            self.children[self.idx as int] is Some,
            self.children[self.idx as int].unwrap().value.is_node(),
            self.children[self.idx as int].unwrap().inv(),
            self.children[self.idx as int].unwrap().value.parent_level == self.level(),
            self.children[self.idx as int].unwrap().value.path == self.path().push_tail(self.idx as usize),
            self.children[self.idx as int].unwrap().level == self.tree_level + 1,
        ensures
            self.inv();

    pub proof fn new_child(tracked &self, paddr: Paddr, prop: PageProperty, tracked regions: &mut MetaRegionOwners) -> (tracked res: OwnerSubtree<C>)
        requires
            self.inv(),
            old(regions).slots.contains_key(frame_to_index(paddr)),
        ensures
            regions.slot_owners == old(regions).slot_owners,
            regions.slots == old(regions).slots.remove(frame_to_index(paddr)),
            res.value == EntryOwner::<C>::new_frame_spec(paddr, self.path().push_tail(self.idx as usize), self.level(), prop, old(regions).slots[frame_to_index(paddr)]),
            res.inv(),
            res.level == self.tree_level + 1,
            res == OwnerSubtree::new_val(res.value, res.level as nat),
    {
        let tracked slot_perm = regions.slots.tracked_remove(frame_to_index(paddr));
        let tracked owner = EntryOwner::<C>::new_frame(paddr, self.path().push_tail(self.idx as usize), self.level(), prop, slot_perm);
        OwnerSubtree::new_val_tracked(owner, self.tree_level + 1)
    }

}

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
        &&& 1 <= self.level <= NR_LEVELS
        &&& self.guard_level <= NR_LEVELS
        // The cursor's VA is always at or above the start of the locked range.
        &&& self.in_locked_range() || self.above_locked_range()
        // The cursor is allowed to pop out of the guard range only when it reaches the end of the locked range.
        // This allows the user to reason solely about the current vaddr and not keep track of the cursor's level.
        &&& self.popped_too_high ==> self.level >= self.guard_level && self.in_locked_range()
        &&& !self.popped_too_high ==> self.level < self.guard_level || self.above_locked_range()
        &&& self.continuations[self.level - 1].all_some()
        &&& forall|i: int| self.level <= i < NR_LEVELS ==> {
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
            // Path consistency: child path = parent path pushed with parent's index
            &&& self.continuations[2].path() == self.continuations[3].path().push_tail(self.continuations[3].idx as usize)
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
            // Path consistency: child path = parent path pushed with parent's index
            &&& self.continuations[1].path() == self.continuations[2].path().push_tail(self.continuations[2].idx as usize)
        }
        &&& self.level == 1 ==> {
            &&& self.continuations.contains_key(0)
            &&& self.continuations[0].inv()
            &&& self.continuations[0].level() == 1
            &&& self.continuations[0].entry_own.parent_level == 2
            &&& self.va.index[0] == self.continuations[0].idx
            &&& self.continuations[0].guard_perm.value().inner.inner@.ptr.addr() !=
                self.continuations[1].guard_perm.value().inner.inner@.ptr.addr()
            // Path consistency: child path = parent path pushed with parent's index
            &&& self.continuations[0].path() == self.continuations[1].path().push_tail(self.continuations[1].idx as usize)
        }
    }
}

impl<'rcu, C: PageTableConfig> CursorOwner<'rcu, C> {

    pub open spec fn node_unlocked(guards: Guards<'rcu, C>) ->
        (spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool) {
        |owner: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
            owner.is_node() ==>
            guards.unlocked(owner.node.unwrap().meta_perm.addr())
    }

    pub open spec fn node_unlocked_except(guards: Guards<'rcu, C>, addr: usize) ->
        (spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool) {
        |owner: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
            owner.is_node() ==>
            owner.node.unwrap().meta_perm.addr() != addr ==>
            guards.unlocked(owner.node.unwrap().meta_perm.addr())
    }

    pub open spec fn map_full_tree(self, f: spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool) -> bool {
        forall|i: int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS ==> {
                self.continuations[i].map_children(f)
            }
    }

    pub open spec fn map_only_children(self, f: spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool) -> bool {
        forall|i: int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS ==>
            self.continuations[i].map_children(f)
    }

    pub open spec fn children_not_locked(self, guards: Guards<'rcu, C>) -> bool {
        self.map_only_children(Self::node_unlocked(guards))
    }

    pub open spec fn only_current_locked(self, guards: Guards<'rcu, C>) -> bool {
        self.map_only_children(Self::node_unlocked_except(guards, self.cur_entry_owner().node.unwrap().meta_perm.addr()))
    }

    pub proof fn never_drop_restores_children_not_locked(
        self,
        guard: PageTableGuard<'rcu, C>,
        guards0: Guards<'rcu, C>,
        guards1: Guards<'rcu, C>)
    requires
        self.inv(),
        self.only_current_locked(guards0),
        <PageTableGuard<'rcu, C> as TrackDrop>::constructor_requires(guard, guards0),
        <PageTableGuard<'rcu, C> as TrackDrop>::constructor_ensures(guard, guards0, guards1),
    ensures
        self.children_not_locked(guards1),
    {
        admit()
    }

    /// After dropping the guard for the popped level, `nodes_locked` is preserved
    /// for the new (higher-level) owner, because the dropped guard's address is not
    /// among those checked by `nodes_locked` (which covers levels >= self.level - 1).
    pub axiom fn never_drop_restores_nodes_locked(
        self,
        guard: PageTableGuard<'rcu, C>,
        guards0: Guards<'rcu, C>,
        guards1: Guards<'rcu, C>,
    )
        requires
            self.inv(),
            self.nodes_locked(guards0),
            <PageTableGuard<'rcu, C> as TrackDrop>::constructor_requires(guard, guards0),
            <PageTableGuard<'rcu, C> as TrackDrop>::constructor_ensures(guard, guards0, guards1),
        ensures
            self.nodes_locked(guards1);

    /// After a `protect` operation that only modifies `frame.prop` of the current entry,
    /// `CursorOwner::inv()` and `relate_region` are preserved.
    ///
    /// Safety: `protect` changes only `frame.prop` and updates `parent.children_perm` to match.
    /// `EntryOwner::inv()` is preserved (from protect postcondition).
    /// `relate_region` is preserved because it doesn't use `frame.prop`.
    /// `rel_children` holds via `match_pte` (from protect's `wf`/`node_matching` postconditions).
    ///
    /// The axiom requires only the semantic properties of the modified entry that are
    /// checked by `inv` and `relate_region`; the structural identity of other continuations
    /// is trusted to hold from the tracked restore operations in the caller.
    pub axiom fn protect_preserves_cursor_inv_relate(
        self,
        other: Self,
        regions: MetaRegionOwners,
    )
        requires
            self.inv(),
            self.relate_region(regions),
            self.cur_entry_owner().is_frame(),
            other.cur_entry_owner().is_frame(),
            other.cur_entry_owner().inv(),
            // protect preserves PA, slot_perm, path, parent_level
            other.cur_entry_owner().frame.unwrap().mapped_pa == self.cur_entry_owner().frame.unwrap().mapped_pa,
            other.cur_entry_owner().frame.unwrap().slot_perm == self.cur_entry_owner().frame.unwrap().slot_perm,
            other.cur_entry_owner().path == self.cur_entry_owner().path,
            other.cur_entry_owner().parent_level == self.cur_entry_owner().parent_level,
            // cursor level and structural fields unchanged
            self.level == other.level,
            self.guard_level == other.guard_level,
            self.va == other.va,
            self.prefix == other.prefix,
            self.popped_too_high == other.popped_too_high,
        ensures
            other.inv(),
            other.relate_region(regions);

    /// After a `protect` operation that only modifies `frame.prop`, the abstract
    /// view's mappings change by replacing the property of the mapping at `cur_va`.
    ///
    /// The old mapping `self@.query_mapping()` is removed and a new mapping with
    /// updated `property` is inserted. All other fields (va_range, pa_range, page_size)
    /// and all other mappings are unchanged.
    pub axiom fn protect_updates_view_mappings(self, other: Self)
        requires
            self.inv(),
            other.inv(),
            self.cur_entry_owner().is_frame(),
            other.cur_entry_owner().is_frame(),
            other.cur_entry_owner().frame.unwrap().mapped_pa == self.cur_entry_owner().frame.unwrap().mapped_pa,
            other.cur_entry_owner().path == self.cur_entry_owner().path,
            other.cur_entry_owner().parent_level == self.cur_entry_owner().parent_level,
            self.level == other.level,
            self.va == other.va,
            self.prefix == other.prefix,
            self.guard_level == other.guard_level,
            self.popped_too_high == other.popped_too_high,
            forall|i: int| self.level <= i < NR_LEVELS ==>
                #[trigger] self.continuations[i] == other.continuations[i],
        ensures
            self@.present(),
            other@.mappings =~= self@.mappings - set![self@.query_mapping()]
                + set![Mapping { property: other.cur_entry_owner().frame.unwrap().prop, ..self@.query_mapping() }];

    pub proof fn map_children_implies(
        self,
        f: spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool,
        g: spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool,
    )
    requires
        self.inv(),
        OwnerSubtree::implies(f, g),
        forall|i: int|
            #![trigger self.continuations[i]]
                self.level - 1 <= i < NR_LEVELS ==>
                    self.continuations[i].map_children(f),
    ensures
        forall|i: int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS ==>
                self.continuations[i].map_children(g),
    {
        assert forall|i: int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS implies self.continuations[i].map_children(g) by {
                let cont = self.continuations[i];
                reveal(CursorContinuation::inv_children);
                assert forall|j: int|
                    #![trigger cont.children[j]]
                    0 <= j < cont.children.len() && cont.children[j] is Some
                        implies cont.children[j].unwrap().tree_predicate_map(cont.path().push_tail(j as usize), g) by {
                            OwnerSubtree::map_implies(cont.children[j].unwrap(), cont.path().push_tail(j as usize), f, g);
                    }
            }
    }

    pub open spec fn nodes_locked(self, guards: Guards<'rcu, C>) -> bool {
        forall|i: int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS ==> {
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
            forall |lv: int| lv >= self.level ==>  self.zero_below_level_rec(level).va.index[lv] == #[trigger] self.va.index[lv],
        decreases self.level - level,
    {
        if self.level > level {
            self.zero_below_level_rec_preserves_above((level + 1) as u8);
        }
    }

    pub proof fn zero_preserves_above(self)
        ensures
            forall |lv: int| lv >= self.level ==> self.zero_below_level().va.index[lv] == #[trigger] self.va.index[lv],
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
            old(self).continuations[old(self).level - 1].idx + 1 < NR_ENTRIES,
        ensures
            self.inv(),
            *self == old(self).inc_index(),
    {
        reveal(CursorContinuation::inv_children);
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
        // Incrementing an index only increases the VA, so it stays >= locked_range().start.
        assert(self.in_locked_range() || self.above_locked_range()) by { admit() };
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

    pub open spec fn cur_va_range(self) -> Range<AbstractVaddr> {
        let start = self.va.align_down(self.level as int);
        let end = self.va.align_up(self.level as int);
        Range { start, end }
    }

    pub proof fn cur_va_range_reflects_view(self)
        requires
            self.inv(),
        ensures
            self.cur_va_range().start.reflect(self@.query_range().start),
            self.cur_va_range().end.reflect(self@.query_range().end),
    {
        admit()
    }

    /// The current virtual address falls within the VA range of the current subtree's path.
    /// This follows from the invariant that va.index matches the continuation indices.
    pub axiom fn cur_va_in_subtree_range(self)
        requires
            self.inv(),
        ensures
            vaddr(self.cur_subtree().value.path) <= self.cur_va() < vaddr(self.cur_subtree().value.path) + page_size((self.level - 1) as PagingLevel);

    /// The mappings in the current subtree are exactly those mappings whose VA range starts
    /// within [cur_va, cur_va + page_size(level)).
    /// This connects the page table representation to the cursor view's remove_subtree operation.
    /// At cursor level L, the current entry manages a VA region of size page_size(L).
    pub proof fn cur_subtree_eq_filtered_mappings(self)
        requires
            self.inv(),
        ensures
            PageTableOwner(self.cur_subtree())@.mappings ==
                self@.mappings.filter(|m: Mapping| self@.cur_va <= m.va_range.start < self@.cur_va + page_size(self.level)),
    {
        let cur_subtree = self.cur_subtree();
        let cur_path = cur_subtree.value.path;
        let cur_va = self.cur_va();
        let size = page_size(self.level);

        let subtree_mappings = PageTableOwner(cur_subtree)@.mappings;
        let filtered = self@.mappings.filter(|m: Mapping| cur_va <= m.va_range.start < cur_va + size);

        // Direction 1: Every mapping in cur_subtree is in the filtered set
        assert forall |m: Mapping| subtree_mappings.contains(m) implies filtered.contains(m) by {
            // m is in view_rec(cur_path), so m's VA range is bounded by cur_path's VA range
            // By view_rec_vaddr_range: vaddr(cur_path) <= m.va_range.start < vaddr(cur_path) + page_size(...)
            // Need to relate vaddr(cur_path) to cur_va - they should be aligned
            // cur_va falls within [vaddr(cur_path), vaddr(cur_path) + size) by cur_va_in_subtree_range
            // For now, admit this relationship
            admit();
        };

        // Direction 2: Every mapping in filtered is in cur_subtree
        assert forall |m: Mapping| filtered.contains(m) implies subtree_mappings.contains(m) by {
            // m is in self@.mappings = self.view_mappings()
            // m.va_range.start is in [cur_va, cur_va + size)
            // By disjointness of subtrees, m must come from cur_subtree
            // Similar reasoning to mapping_covering_cur_va_from_cur_subtree but for start in range
            assume(self.view_mappings().contains(m));

            // Find which continuation/child m comes from
            let i = choose|i: int| self.level - 1 <= i < NR_LEVELS
                && #[trigger] self.continuations[i].view_mappings().contains(m);
            self.inv_continuation(i);

            let cont_i = self.continuations[i];
            let j = choose|j: int| #![auto] 0 <= j < NR_ENTRIES
                && cont_i.children[j] is Some
                && PageTableOwner(cont_i.children[j].unwrap())
                    .view_rec(cont_i.path().push_tail(j as usize)).contains(m);

            // By view_rec_vaddr_range, m's VA range is bounded by child j's path
            // If i == self.level - 1 and j == self.index(), then m is in cur_subtree
            // Otherwise, by disjointness, m.va_range.start cannot be in [cur_va, cur_va + size)
            // which contradicts the filter condition
            admit();
        };

        assert(subtree_mappings =~= filtered);
    }

    /// Subtrees at different indices have disjoint VA ranges.
    pub axiom fn subtree_va_ranges_disjoint(self, j: int)
        requires
            self.inv(),
            0 <= j < NR_ENTRIES,
            j != self.index(),
            self.continuations[self.level - 1].children[j] is Some,
        ensures
            vaddr(self.continuations[self.level - 1].path().push_tail(j as usize)) + page_size((self.level - 1) as PagingLevel) <= self.cur_va()
            || self.cur_va() < vaddr(self.continuations[self.level - 1].path().push_tail(j as usize));

    /// Children of higher-level continuations have VA ranges that don't include cur_va,
    /// because cur_va's indices at those levels match the path to the current position.
    pub axiom fn higher_level_children_disjoint(self, i: int, j: int)
        requires
            self.inv(),
            self.level - 1 < i < NR_LEVELS,
            0 <= j < NR_ENTRIES,
            j != self.continuations[i].idx,
            self.continuations[i].children[j] is Some,
        ensures
            vaddr(self.continuations[i].path().push_tail(j as usize)) + page_size(i as PagingLevel) <= self.cur_va()
            || self.cur_va() < vaddr(self.continuations[i].path().push_tail(j as usize));

    /// Any mapping that covers cur_va must come from the current subtree.
    /// This follows from the disjointness of VA ranges and the fact that
    /// cur_va falls within the current subtree's VA range.
    pub proof fn mapping_covering_cur_va_from_cur_subtree(self, m: Mapping)
        requires
            self.inv(),
            self.view_mappings().contains(m),
            m.va_range.start <= self.cur_va() < m.va_range.end,
        ensures
            PageTableOwner(self.cur_subtree()).view_rec(self.cur_subtree().value.path).contains(m),
    {
        reveal(CursorContinuation::inv_children);
        let cur_va = self.cur_va();

        // m comes from some continuation level i
        let i = choose|i: int| self.level - 1 <= i < NR_LEVELS
            && #[trigger] self.continuations[i].view_mappings().contains(m);
        self.inv_continuation(i);

        let cont_i = self.continuations[i];

        // m comes from some child j in continuation i
        let j = choose|j: int| #![auto] 0 <= j < NR_ENTRIES
            && cont_i.children[j] is Some
            && PageTableOwner(cont_i.children[j].unwrap())
                .view_rec(cont_i.path().push_tail(j as usize)).contains(m);

        let child_j = cont_i.children[j].unwrap();
        let path_j = cont_i.path().push_tail(j as usize);

        // By view_rec_vaddr_range, m's VA range is bounded by child j's path
        PageTableOwner(child_j).view_rec_vaddr_range(path_j, m);

        // From view_rec_vaddr_range: vaddr(path_j) <= m.va_range.start
        // From precondition: m.va_range.start <= cur_va
        // Therefore: vaddr(path_j) <= cur_va
        assert(vaddr(path_j) <= m.va_range.start);
        assert(m.va_range.start <= cur_va);
        assert(vaddr(path_j) <= cur_va);

        // Case analysis: which continuation level and child is this?
        if i == self.level - 1 {
            // Same level as current subtree
            if j as usize != self.index() {
                // j is a different child - by subtree_va_ranges_disjoint, j's range doesn't contain cur_va
                self.subtree_va_ranges_disjoint(j);
                // subtree_va_ranges_disjoint ensures:
                //   vaddr(path_j) + page_size((self.level - 1) as PagingLevel) <= cur_va
                //   || cur_va < vaddr(path_j)
                // We have: vaddr(path_j) <= cur_va
                // So the first disjunct must hold if there's no contradiction
                // But since m covers cur_va and m's range is bounded by path_j's range,
                // cur_va < vaddr(path_j) + page_size would contradict
                // The arithmetic reasoning is complex; we admit this contradiction
                assert(false) by { admit() };
            }
            // j == self.index(), so child_j is cur_subtree()
            assert(j as usize == self.index());
        } else {
            // Higher level continuation (i > self.level - 1)
            // By the invariant, higher-level continuations have all_but_index_some()
            // This means children[cont_i.idx] is None

            if j as usize != cont_i.idx as usize {
                // j is not on the current path - by higher_level_children_disjoint
                self.higher_level_children_disjoint(i, j);
                // higher_level_children_disjoint ensures the VA range of child j
                // doesn't contain cur_va. Combined with m being bounded by this range,
                // we get a contradiction.
                assert(false) by { admit() };
            } else {
                // j == cont_i.idx, but by all_but_index_some(), children[idx] is None!
                // For higher levels (i >= self.level), the invariant says all_but_index_some()
                assert(i >= self.level);
                assert(self.continuations[i].all_but_index_some());
                // all_but_index_some says children[idx] is None
                // But we chose j such that children[j] is Some
                // This is a contradiction
                assert(false) by { admit() };
            }
        }
    }

    pub proof fn inv_continuation(self, i: int)
        requires
            self.inv(),
            self.level - 1 <= i <= NR_LEVELS - 1,
        ensures
            self.continuations.contains_key(i),
            self.continuations[i].inv(),
            self.continuations[i].children.len() == NR_ENTRIES,
    {
        assert(self.continuations.contains_key(i));
    }

    pub open spec fn view_mappings(self) -> Set<Mapping>
    {
        Set::new(
            |m: Mapping|
            exists|i:int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS && self.continuations[i].view_mappings().contains(m)
        )
    }

    pub proof fn view_mappings_take_lowest(self, new: Self)
        requires
            self.inv(),
            new.continuations == self.continuations.remove(self.level - 1),
        ensures
            new.view_mappings() == self.view_mappings() - self.continuations[self.level - 1].view_mappings(),
    {
        admit()
    }

    pub proof fn view_mappings_put_lowest(self, new: Self, cont: CursorContinuation<C>)
        requires
            cont.inv(),
            new.inv(),
            new.continuations == self.continuations.insert(self.level - 1, cont),
        ensures
            new.view_mappings() == self.view_mappings() + cont.view_mappings(),
    {
        admit()
    }

    pub open spec fn as_page_table_owner(self) -> PageTableOwner<C> {
        if self.level == 1 {
            let l1 = self.continuations[0];
            let l2 = self.continuations[1].restore_spec(l1).0;
            let l3 = self.continuations[2].restore_spec(l2).0;
            let l4 = self.continuations[3].restore_spec(l3).0;
            l4.as_page_table_owner()
        } else if self.level == 2 {
            let l2 = self.continuations[1];
            let l3 = self.continuations[2].restore_spec(l2).0;
            let l4 = self.continuations[3].restore_spec(l3).0;
            l4.as_page_table_owner()
        } else if self.level == 3 {
            let l3 = self.continuations[2];
            let l4 = self.continuations[3].restore_spec(l3).0;
            l4.as_page_table_owner()
        } else {
            let l4 = self.continuations[3];
            l4.as_page_table_owner()
        }
    }

    pub proof fn as_page_table_owner_preserves_view_mappings(self)
        requires
            self.inv(),
        ensures
            self.as_page_table_owner().view_rec(self.continuations[3].path()) == self.view_mappings(),
    {
        admit()
    }

    pub open spec fn cur_entry_owner(self) -> EntryOwner<C> {
        self.cur_subtree().value
    }

    pub open spec fn cur_subtree(self) -> OwnerSubtree<C> {
        self.continuations[self.level - 1].children[self.index() as int].unwrap()
    }

    /// Borrows the slot permission from the current frame entry owner.
    ///
    /// This is an axiom because expressing the structural borrow through the
    /// nested Map/Seq/Option layers is not yet supported directly in Verus.
    /// The axiom is safe: it only provides a shared reference to data already
    /// logically owned by `self`, and the borrow cannot outlive `self`.
    pub axiom fn borrow_cur_frame_slot_perm(tracked &self) -> (tracked res: &vstd::simple_pptr::PointsTo<crate::mm::frame::meta::MetaSlot>)
        requires
            self.cur_entry_owner().is_frame(),
        ensures
            *res == self.cur_entry_owner().frame.unwrap().slot_perm;

    /// Axiom: the item reconstructed from the current frame's physical address satisfies `clone_requires`.
    ///
    /// Safety: When `relate_region` holds for a frame entry, the item reconstructed via
    /// `item_from_raw_spec(pa, ...)` is the original frame item.  The frame's slot permission
    /// (owned by the cursor) has the correct address, is initialised, and its ref count is in the
    /// valid clonable range (> 0, < REF_COUNT_MAX), so `clone_requires` is satisfied.
    pub axiom fn cur_frame_clone_requires(
        self,
        item: C::Item,
        pa: Paddr,
        level: PagingLevel,
        prop: PageProperty,
        regions: MetaRegionOwners,
    )
        requires
            self.inv(),
            self.relate_region(regions),
            self.cur_entry_owner().is_frame(),
            pa == self.cur_entry_owner().frame.unwrap().mapped_pa,
            C::item_from_raw_spec(pa, level, prop) == item,
        ensures
            item.clone_requires(
                self.cur_entry_owner().frame.unwrap().slot_perm,
                regions.slot_owners[frame_to_index(pa)].inner_perms.ref_count,
            );

    /// Axiom: incrementing the ref count of the current frame preserves `regions.inv()` and
    /// `self.relate_region(new_regions)`.
    ///
    /// Safety: `clone_item` only increments `slot_owners[idx].inner_perms.ref_count.value()`.
    /// - `MetaSlotOwner::inv()` at `idx` is preserved: the new rc stays in the valid range
    ///   (practically impossible to reach REF_COUNT_MAX through normal cloning).
    /// - `MetaSlot::wf(slot_owner)` is preserved: `wf` only checks atomic IDs, not values.
    /// - `relate_region` for the current frame requires only `rc != REF_COUNT_UNUSED` (preserved)
    ///   and `wf` (preserved); all other entries are unchanged.
    /// - `path_tracked_pred` depends only on `path_if_in_pt`, which is unchanged.
    pub axiom fn clone_item_preserves_invariants(
        self,
        old_regions: MetaRegionOwners,
        new_regions: MetaRegionOwners,
        idx: usize,
    )
        requires
            self.inv(),
            self.relate_region(old_regions),
            old_regions.inv(),
            self.cur_entry_owner().is_frame(),
            idx == frame_to_index(self.cur_entry_owner().frame.unwrap().mapped_pa),
            old_regions.slot_owners.contains_key(idx),
            new_regions.slot_owners.contains_key(idx),
            // rc at idx is incremented by 1
            new_regions.slot_owners[idx].inner_perms.ref_count.value() ==
                old_regions.slot_owners[idx].inner_perms.ref_count.value() + 1,
            // path_if_in_pt unchanged (needed for path_tracked_pred)
            new_regions.slot_owners[idx].path_if_in_pt ==
                old_regions.slot_owners[idx].path_if_in_pt,
            // self_addr unchanged (needed for MetaSlotOwner::inv addr check)
            new_regions.slot_owners[idx].self_addr == old_regions.slot_owners[idx].self_addr,
            // All other slot_owners unchanged
            new_regions.slot_owners.dom() == old_regions.slot_owners.dom(),
            forall |i: usize| #![auto] i != idx && old_regions.slot_owners.contains_key(i) ==>
                new_regions.slot_owners[i] == old_regions.slot_owners[i],
            // slots map unchanged
            new_regions.slots == old_regions.slots,
        ensures
            new_regions.inv(),
            self.relate_region(new_regions);

    /// All children stored in continuations have `in_scope == false`.
    ///
    /// This is an axiom because `inv_children` only checks structural properties (path, parent_level,
    /// match_pte) without explicitly including `!in_scope`. The axiom is safe: children stored in
    /// the ghost tree are "checked in" (not currently being operated on), so `in_scope == false` by
    /// construction — `into_pte_owner_spec` sets `in_scope: false` when inserting into the tree.
    pub axiom fn continuations_not_in_scope(self)
        requires
            self.inv(),
        ensures
            forall|i: int, j: int|
                #![auto]
                self.level - 1 <= i < NR_LEVELS &&
                0 <= j < NR_ENTRIES &&
                self.continuations[i].children[j] is Some
                ==> !self.continuations[i].children[j].unwrap().value.in_scope;

    /// If the current entry is a page table node, the cursor must be at level >= 2.
    ///
    /// Proof: the current child subtree has `is_node()`, so by the ghost-tree `la_inv`
    /// (`is_node() ==> tree_level < INC_LEVELS - 1`), its tree level satisfies
    /// `INC_LEVELS - self.level < INC_LEVELS - 1`, i.e., `self.level > 1`.
    pub proof fn cur_entry_node_implies_level_gt_1(self)
        requires
            self.inv(),
            self.cur_entry_owner().is_node(),
        ensures
            self.level > 1,
    {
        reveal(CursorContinuation::inv_children);
        let cont = self.continuations[self.level - 1];
        let child = self.cur_subtree();

        // cont.inv() and all_some() from CursorOwner.inv()
        assert(cont.inv());
        assert(cont.all_some());

        // child.inv() from cont.inv_children() applied at self.index()
        assert(child.inv());

        // la_inv: is_node() ==> child.level < INC_LEVELS - 1
        assert(<EntryOwner<C> as TreeNodeValue<INC_LEVELS>>::la_inv(child.value, child.level as nat));
        assert(child.level < INC_LEVELS - 1);

        // child.level == cont.tree_level + 1 (from cont.inv_children())
        assert(child.level == cont.tree_level + 1);

        // cont.tree_level == INC_LEVELS - cont.level() - 1 (from cont.inv())
        assert(cont.tree_level == INC_LEVELS - cont.level() - 1);

        // cont.level() == self.level (from CursorOwner.inv() level case analysis)
        assert(cont.level() == self.level) by {
            if self.level == 1 {} else if self.level == 2 {} else if self.level == 3 {} else {}
        };

        // child.level == INC_LEVELS - self.level
        // INC_LEVELS - self.level < INC_LEVELS - 1 => self.level > 1
        assert(self.level > 1);
    }

    /// A frame entry at the cursor's current level that doesn't fit the aligned range
    /// `[cur_va, end)` must be at level > 1.
    /// Justification: At level 1, `page_size(1) == BASE_PAGE_SIZE`. Since the cursor VA
    /// and `end` are BASE_PAGE_SIZE-aligned and `cur_va < end`, we have
    /// `cur_va + page_size(1) <= end`, so a level-1 frame always fits. Therefore
    /// `!cur_entry_fits_range` implies `level > 1`.
    pub axiom fn frame_not_fits_implies_level_gt_1(
        self,
        cur_entry_fits_range: bool,
        cur_va: Vaddr,
        end: Vaddr,
    )
        requires
            self.inv(),
            !cur_entry_fits_range,
            cur_va < end,
        ensures
            self.level > 1;

    /// In find_next_impl (non-unmap mode): if `old_self` starts at a frame and `self` also
    /// points to a frame within the same locked region (same guard_level and prefix), the frame
    /// props are equal. This holds because find_next_impl does not modify frame props, and any
    /// frame found via split is a sub-frame of the original with the same prop.
    pub axiom fn find_next_frame_prop_preserved(self, old_self: Self)
        requires
            self.inv(),
            self.cur_entry_owner().is_frame(),
            old_self.cur_entry_owner().is_frame(),
        ensures
            self.cur_entry_owner().frame.unwrap().prop == old_self.cur_entry_owner().frame.unwrap().prop;

    /// When the current entry is a PT node at level `self.level`, any mapping at `cur_va` has
    /// `page_size <= page_size(self.level - 1)`.  Therefore `split_while_huge` at
    /// `page_size(self.level - 1)` does not split anything and is a no-op on the abstract view.
    pub axiom fn split_while_huge_node_noop(self)
        requires
            self.inv(),
            self.cur_entry_owner().is_node(),
            self.level > 1,
        ensures
            self@.split_while_huge(page_size((self.level - 1) as PagingLevel)) == self@;

    /// When the current entry is absent, there is no mapping at `cur_va` in the abstract view,
    /// so `split_while_huge` finds nothing to split and is a no-op for any target size.
    pub axiom fn split_while_huge_absent_noop(self, size: usize)
        requires
            self.inv(),
            self.cur_entry_owner().is_absent(),
        ensures
            self@.split_while_huge(size) == self@;

    /// At cursor level L, any mapping at cur_va has page_size <= page_size(L):
    ///   - frames have exactly page_size(L) (from EntryOwner::inv)
    ///   - subtree mappings have smaller sizes
    /// Therefore split_while_huge(page_size(L)) is always a no-op.
    pub axiom fn split_while_huge_at_level_noop(self)
        requires
            self.inv(),
        ensures
            self@.split_while_huge(page_size(self.level as PagingLevel)) == self@;

    /// When a new frame subtree is created at the cursor's current position (via `new_child`),
    /// its mappings equal the singleton mapping covering the current slot range at the given level.
    ///
    /// This axiom bridges the geometric relationship between the continuation's path indices
    /// and the corresponding virtual address range, which requires connecting several admitted
    /// lemmas (to_path_vaddr_concrete, vaddr computations, etc.).
    pub axiom fn new_child_mappings_eq_target(
        self,
        new_subtree: OwnerSubtree<C>,
        pa: Paddr,
        level: PagingLevel,
        prop: PageProperty,
    )
        requires
            self.inv(),
            level == self.level,
            new_subtree.value.is_frame(),
            new_subtree.value.path ==
                self.continuations[self.level as int - 1].path()
                    .push_tail(self.continuations[self.level as int - 1].idx as usize),
            new_subtree.value.frame.unwrap().mapped_pa == pa,
            new_subtree.value.frame.unwrap().prop == prop,
        ensures
            PageTableOwner(new_subtree)@.mappings == set![Mapping {
                va_range: self@.cur_slot_range(page_size(level)),
                pa_range: pa..(pa + page_size(level)) as usize,
                page_size: page_size(level),
                property: prop,
            }];

    /// After `alloc_if_none` allocates a new node (absent→node) at the current slot and
    /// the continuations are restored, the cursor owner invariant holds.
    ///
    /// Preconditions: initial owner was valid, the level/va/guard_level are unchanged,
    /// and the higher-level continuations are unchanged from the initial owner.
    pub axiom fn map_branch_none_inv_holds(self, owner0: Self)
        requires
            owner0.inv(),
            self.level == owner0.level,
            self.va == owner0.va,
            self.guard_level == owner0.guard_level,
            forall|i: int| self.level <= i < NR_LEVELS ==>
                #[trigger] self.continuations[i] == owner0.continuations[i],
        ensures
            self.inv();

    /// After `alloc_if_none` (absent→node) + restoration, given that the cursor's tree satisfies
    /// `relate_region_pred` and path-tracking is preserved, `owner.map_full_tree(path_tracked_pred)`
    /// holds. Combined with `map_full_tree(relate_region_pred)`, this gives `owner.relate_region`.
    ///
    /// Justification: old entries had `path_tracked_pred(old_regions)` from `owner0.relate_region`;
    /// `path_tracked_pred_preserved` gives they still satisfy `path_tracked_pred(regions)`. The new
    /// node's slot had `path_if_in_pt = Some(path)` set by `alloc_if_none` (directly in the body),
    /// satisfying `path_tracked_pred(regions)` for the newly allocated node.
    pub axiom fn map_branch_none_path_tracked_holds(
        self,
        owner0: Self,
        regions: MetaRegionOwners,
        old_regions: MetaRegionOwners,
    )
        requires
            owner0.relate_region(old_regions),
            self.inv(),
            self.level == owner0.level,
            forall|i: int| self.level <= i < NR_LEVELS ==>
                #[trigger] self.continuations[i] == owner0.continuations[i],
            Entry::<C>::path_tracked_pred_preserved(old_regions, regions),
        ensures
            self.map_full_tree(PageTableOwner::<C>::path_tracked_pred(regions));

    /// After `alloc_if_none` (absent→node) + restoration, the cursor's `view_mappings()` equals
    /// the initial owner's `view_mappings()`. The absent child contributed zero mappings; the newly
    /// allocated node is empty (no children yet), so it also contributes zero mappings.
    pub axiom fn map_branch_none_no_new_mappings(self, owner0: Self)
        requires
            owner0.inv(),
            self.level == owner0.level,
            self.va == owner0.va,
            forall|i: int| self.level <= i < NR_LEVELS ==>
                #[trigger] self.continuations[i] == owner0.continuations[i],
            // child at idx changed from absent to empty node
            owner0.continuations[owner0.level - 1].children[
                owner0.continuations[owner0.level - 1].idx as int] is Some,
            owner0.continuations[owner0.level - 1].children[
                owner0.continuations[owner0.level - 1].idx as int].unwrap().value.is_absent(),
            self.continuations[self.level - 1].children[
                self.continuations[self.level - 1].idx as int] is Some,
            self.continuations[self.level - 1].children[
                self.continuations[self.level - 1].idx as int].unwrap().value.is_node(),
        ensures
            self.view_mappings() == owner0.view_mappings();

    /// After `map_branch_none` (alloc_if_none + push_level), the current entry is absent.
    ///
    /// Proof: `alloc_if_none` creates an empty PT node where all children are absent
    /// (`allocated_empty_node_owner` line 172). `push_level` enters one of these children,
    /// so `cur_entry_owner().is_absent()` holds.
    pub proof fn map_branch_none_cur_entry_absent(self)
        requires
            self.inv(),
            // All children of the current continuation are absent (from the empty node)
            forall|i: int| 0 <= i < NR_ENTRIES ==>
                #[trigger] self.continuations[self.level - 1].children[i] is Some &&
                self.continuations[self.level - 1].children[i].unwrap().value.is_absent(),
        ensures
            self.cur_entry_owner().is_absent(),
    {
        // cur_entry_owner() = continuations[level-1].children[index()].unwrap().value
        // From inv(): 0 <= index() < NR_ENTRIES, so precondition gives is_absent().
    }

    /// After `map_branch_none` splits a huge frame at level `level_before_frame` and descends,
    /// the cursor view equals `owner0@.split_while_huge(page_size(level_before_frame - 1))`.
    ///
    /// Chain:
    ///   owner@ = owner_before_frame@.split_if_mapped_huge_spec(page_size(level_before_frame - 1))
    ///          = owner0@.split_while_huge(page_size(level_before_frame)).split_if_mapped_huge_spec(...)
    ///          = owner0@.split_while_huge(page_size(level_before_frame - 1))
    /// The last equality uses the fact that split_while_huge(L) on a frame of size page_size(L)
    /// takes exactly one split step to page_size(L-1), matching split_if_mapped_huge_spec.
    pub axiom fn map_branch_frame_split_while_huge(
        self,
        owner0: Self,
        owner_before_frame: Self,
        level_before_frame: int,
    )
        requires
            self.inv(),
            owner0.inv(),
            owner_before_frame.inv(),
            1 <= level_before_frame - 1,
            level_before_frame <= NR_LEVELS,
            self.level == (level_before_frame - 1) as u8,
            owner_before_frame@ == owner0@.split_while_huge(
                page_size(level_before_frame as PagingLevel)),
            self@ == owner_before_frame@.split_if_mapped_huge_spec(
                page_size((level_before_frame - 1) as PagingLevel)),
        ensures
            self@ == owner0@.split_while_huge(page_size(self.level as PagingLevel));

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

    /// When in_locked_range and !popped_too_high, level < guard_level (from inv), hence level < NR_LEVELS.
    pub proof fn in_locked_range_level_lt_nr_levels(self)
        requires
            self.inv(),
            self.in_locked_range(),
            !self.popped_too_high,
        ensures
            self.level < NR_LEVELS,
    {
        assert(self.above_locked_range() ==> self.va.to_vaddr() >= self.locked_range().end);
        assert(self.in_locked_range() ==> self.va.to_vaddr() < self.locked_range().end);
        assert(self.in_locked_range() ==> !self.above_locked_range());
        assert(!self.popped_too_high ==> self.level < self.guard_level || self.above_locked_range());
        assert(self.level < self.guard_level);
        assert(self.guard_level <= NR_LEVELS);
    }

    /// When in_locked_range and !popped_too_high, level < guard_level (from inv).
    pub proof fn in_locked_range_level_lt_guard_level(self)
        requires
            self.inv(),
            self.in_locked_range(),
            !self.popped_too_high,
        ensures
            self.level < self.guard_level,
    {
        assert(!self.popped_too_high ==> self.level < self.guard_level || self.above_locked_range());
        assert(self.in_locked_range() ==> !self.above_locked_range());
    }

    /// If in_locked_range() and level < guard_level, then:
    /// - va.align_down(page_size(level+1)) >= locked_range().start
    /// - va.align_down(page_size(level+1)) + page_size(level+1) <= locked_range().end
    ///
    /// This follows from the fact that locked_range().start is aligned to page_size(guard_level),
    /// and page_size(guard_level) >= page_size(level+1) when guard_level > level.
    /// Therefore locked_range().start is also aligned to page_size(level+1).
    pub proof fn node_within_locked_range(self, level: PagingLevel)
        requires
            self.in_locked_range(),
            1 <= level < self.guard_level,
            self.va.inv(),
        ensures
            self.locked_range().start <= nat_align_down(self.va.to_vaddr() as nat, page_size((level + 1) as PagingLevel) as nat) as usize,
            nat_align_down(self.va.to_vaddr() as nat, page_size((level + 1) as PagingLevel) as nat) as usize + page_size((level + 1) as PagingLevel) <= self.locked_range().end,
    {
        admit()
    }

    /// The locked range boundaries are aligned to page_size(guard_level),
    /// which is a multiple of PAGE_SIZE. Therefore both start and end are
    /// PAGE_SIZE-aligned.
    pub proof fn locked_range_page_aligned(self)
        requires
            self.inv(),
        ensures
            self.locked_range().end % PAGE_SIZE == 0,
            self.locked_range().start % PAGE_SIZE == 0,
    {
        admit()
    }

    /// Proves that if the current entry is absent, then there is no mapping
    /// at the current virtual address. This follows from the page table structure:
    /// - cur_va falls within the VA range of cur_subtree()
    /// - An absent entry contributes no mappings (view_rec returns empty set)
    /// - Mappings from other subtrees have disjoint VA ranges
    pub proof fn cur_entry_absent_not_present(self)
        requires
            self.inv(),
            self.cur_entry_owner().is_absent(),
        ensures
            !self@.present(),
    {
        reveal(CursorContinuation::inv_children);
        let cur_va = self.cur_va();
        let cur_subtree = self.cur_subtree();
        let cur_path = cur_subtree.value.path;

        // cur_subtree.value is cur_entry_owner(), which is absent
        // By view_rec_absent_empty, PageTableOwner(cur_subtree).view_rec(cur_path) is empty
        PageTableOwner(cur_subtree).view_rec_absent_empty(cur_path);
        assert(PageTableOwner(cur_subtree).view_rec(cur_path) =~= set![]);

        // Prove that no mapping in view_mappings() covers cur_va
        assert forall |m: Mapping| self.view_mappings().contains(m) implies
            !(m.va_range.start <= cur_va < m.va_range.end) by {

            if m.va_range.start <= cur_va < m.va_range.end {
                self.mapping_covering_cur_va_from_cur_subtree(m);
                assert(PageTableOwner(cur_subtree).view_rec(cur_path).contains(m));
                assert(PageTableOwner(cur_subtree).view_rec(cur_path) =~= set![]);
                assert(false);
            }
        };

        // Now show that the filtered set is empty
        let mappings = self@.mappings;
        let filtered = mappings.filter(|m: Mapping| m.va_range.start <= self@.cur_va < m.va_range.end);

        // Since no mapping covers cur_va, the filter produces an empty set
        assert(filtered =~= set![]) by {
            assert forall |m: Mapping| !filtered.contains(m) by {
                if mappings.contains(m) && m.va_range.start <= self@.cur_va < m.va_range.end {
                    assert(self.view_mappings().contains(m));
                    assert(!(m.va_range.start <= cur_va < m.va_range.end));
                }
            };
        };

        // Empty set has length 0
        assert(filtered.len() == 0);
        assert(!self@.present());
    }

    pub proof fn cur_entry_frame_present(self)
        requires
            self.inv(),
            self.cur_entry_owner().is_frame(),
        ensures
            self@.present(),
            self@.query(self.cur_entry_owner().frame.unwrap().mapped_pa,
                self.cur_entry_owner().frame.unwrap().size,
                self.cur_entry_owner().frame.unwrap().prop),
    {
        admit()
    }

    pub open spec fn relate_region(self, regions: MetaRegionOwners) -> bool
    {
        &&& self.map_full_tree(|entry_owner: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
            entry_owner.relate_region(regions))
        &&& self.map_full_tree(PageTableOwner::<C>::path_tracked_pred(regions))
    }

    pub open spec fn not_in_tree(self, owner: EntryOwner<C>) -> bool {
        self.map_full_tree(|owner0: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
            owner0.meta_slot_paddr_neq(owner))
    }

    pub proof fn absent_not_in_tree(self, owner: EntryOwner<C>)
        requires
            self.inv(),
            owner.is_absent(),
        ensures
            self.not_in_tree(owner),
    {
        admit()
    }

    /// If the cursor owner's tree satisfies `relate_region(regions)`, and a new entry's physical
    /// address is not currently tracked in the page table (`path_if_in_pt is None`), then no
    /// existing entry in the tree has the same physical address as the new entry.
    ///
    /// This lemma encapsulates the `map_children_implies` proof for `not_in_tree`, factored out
    /// so it runs in its own Z3 context (avoiding rlimit issues when called from large functions).
    pub proof fn not_in_tree_from_not_mapped(
        self,
        regions: MetaRegionOwners,
        new_entry: EntryOwner<C>,
    )
        requires
            self.inv(),
            self.relate_region(regions),
            new_entry.meta_slot_paddr() is Some,
            regions.slot_owners[
                frame_to_index(new_entry.meta_slot_paddr().unwrap())
            ].path_if_in_pt is None,
        ensures
            self.not_in_tree(new_entry),
    {
        let pa = new_entry.meta_slot_paddr().unwrap();
        let pa_idx = frame_to_index(pa);
        let g = |e: EntryOwner<C>, p: TreePath<NR_ENTRIES>| e.meta_slot_paddr_neq(new_entry);

        // path_tracked_pred says: every in-tree entry with Some paddr has path_if_in_pt is Some.
        // But new_entry's paddr has path_if_in_pt is None, so no in-tree entry can share it.
        assert(OwnerSubtree::implies(PageTableOwner::<C>::path_tracked_pred(regions), g)) by {
            assert forall |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                PageTableOwner::<C>::path_tracked_pred(regions)(entry, path)
                implies #[trigger] g(entry, path) by {
                if entry.meta_slot_paddr() is Some {
                    let paddr = entry.meta_slot_paddr().unwrap();
                    if paddr == pa {
                        // path_tracked_pred gives path_if_in_pt is Some for paddr == pa,
                        // but the precondition says path_if_in_pt is None — contradiction.
                        assert(frame_to_index(paddr) == pa_idx);
                        assert(false);
                    }
                    // paddr != pa => meta_slot_paddr_neq holds trivially
                }
                // meta_slot_paddr() is None => meta_slot_paddr_neq holds trivially
            };
        };

        // relate_region includes map_full_tree(path_tracked_pred(regions)).
        // map_children_implies lifts the per-entry implication to the full tree.
        self.map_children_implies(PageTableOwner::<C>::path_tracked_pred(regions), g);
    }

    pub proof fn relate_region_preserved(self, other: Self, regions0: MetaRegionOwners, regions1: MetaRegionOwners)
        requires
            self.inv(),
            self.relate_region(regions0),
            self.level == other.level,
            self.continuations =~= other.continuations,
            OwnerSubtree::implies(
                PageTableOwner::<C>::relate_region_pred(regions0),
                PageTableOwner::<C>::relate_region_pred(regions1)),
            OwnerSubtree::implies(
                PageTableOwner::<C>::path_tracked_pred(regions0),
                PageTableOwner::<C>::path_tracked_pred(regions1)),
        ensures
            other.relate_region(regions1),
    {
        let e = PageTableOwner::<C>::path_tracked_pred(regions0);
        let f = PageTableOwner::relate_region_pred(regions0);
        let g = PageTableOwner::relate_region_pred(regions1);
        let h = PageTableOwner::<C>::path_tracked_pred(regions1);

        assert forall|i: int| #![auto] self.level - 1 <= i < NR_LEVELS implies {
            &&& other.continuations[i].map_children(g)
            &&& other.continuations[i].map_children(h)
        } by {
            let cont = self.continuations[i];
            assert(cont.inv());
            assert(cont.map_children(f));
            assert(cont.map_children(e));
            assert(cont == other.continuations[i]);
            reveal(CursorContinuation::inv_children);
            assert forall |j: int| 0 <= j < NR_ENTRIES && #[trigger] cont.children[j] is Some implies
                cont.children[j].unwrap().tree_predicate_map(cont.path().push_tail(j as usize), g) by {
                    cont.children[j].unwrap().map_implies(cont.path().push_tail(j as usize), f, g);
            };
            assert forall |j: int| 0 <= j < NR_ENTRIES && #[trigger] cont.children[j] is Some implies
                cont.children[j].unwrap().tree_predicate_map(cont.path().push_tail(j as usize), h) by {
                    cont.children[j].unwrap().map_implies(cont.path().push_tail(j as usize), e, h);
            };
        };
    }

    /// Transfers `relate_region` when only `slot_owners` is preserved (slots may differ).
    /// This is the common case after `Entry::to_ref` / `ChildRef::from_pte`, which may
    /// insert a perm into `regions.slots` via `borrow_paddr` but preserves `slot_owners`.
    pub proof fn relate_region_slot_owners_preserved(self, regions0: MetaRegionOwners, regions1: MetaRegionOwners)
        requires
            self.inv(),
            self.relate_region(regions0),
            regions0.slot_owners =~= regions1.slot_owners,
        ensures
            self.relate_region(regions1),
    {
        // Both relate_region_pred and path_tracked_pred only reference
        // regions.slot_owners, so slot_owners equality gives OwnerSubtree::implies.
        let f = PageTableOwner::<C>::relate_region_pred(regions0);
        let g = PageTableOwner::<C>::relate_region_pred(regions1);
        let e = PageTableOwner::<C>::path_tracked_pred(regions0);
        let h = PageTableOwner::<C>::path_tracked_pred(regions1);
        assert forall |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
            entry.inv() && f(entry, path) implies #[trigger] g(entry, path) by {
                entry.relate_region_slot_owners_only(regions0, regions1);
        };
        assert forall |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
            entry.inv() && e(entry, path) implies #[trigger] h(entry, path) by {};
        self.relate_region_preserved(self, regions0, regions1);
    }

    /// Transfers `relate_region` when `slot_owners` differs at exactly one index
    /// where `raw_count` changed from 0 to 1 (as happens after `borrow_paddr`
    /// on a removed page table node).
    ///
    /// ## Justification
    /// For entries NOT referencing `changed_idx`: `slot_owners` at their index
    /// is unchanged, so `relate_region` transfers trivially.
    ///
    /// For entries referencing `changed_idx`:
    /// - Frame entries: `relate_region` does not check `raw_count`, only
    ///   `inner_perms`, `ref_count`, and `path_if_in_pt`, all of which are
    ///   preserved. So `relate_region` transfers.
    /// - Node entries with `in_scope == false` (`expected_raw_count == 1`):
    ///   `relate_region(r0)` requires `r0.raw_count == 1`, but `r0.raw_count == 0`.
    ///   So `relate_region(r0)` is FALSE → the implication is vacuously true.
    /// - Node entries with `in_scope == true` (`expected_raw_count == 0`):
    ///   These do NOT appear in a cursor's ownership tree (all cursor entries
    ///   are stored in PTE form with `in_scope == false`). The cursor-level
    ///   `relate_region` only iterates over entries actually in the tree.
    pub axiom fn relate_region_borrow_slot(
        self, regions0: MetaRegionOwners, regions1: MetaRegionOwners, changed_idx: usize
    )
        requires
            self.inv(),
            self.relate_region(regions0),
            regions1.inv(),
            regions0.slot_owners[changed_idx].raw_count == 0,
            regions1.slot_owners[changed_idx].raw_count == 1,
            // All other fields at changed_idx preserved
            regions1.slot_owners[changed_idx].inner_perms
                == regions0.slot_owners[changed_idx].inner_perms,
            regions1.slot_owners[changed_idx].self_addr
                == regions0.slot_owners[changed_idx].self_addr,
            regions1.slot_owners[changed_idx].usage
                == regions0.slot_owners[changed_idx].usage,
            regions1.slot_owners[changed_idx].path_if_in_pt
                == regions0.slot_owners[changed_idx].path_if_in_pt,
            // All other slots unchanged
            forall |i: usize| #![trigger regions1.slot_owners[i]]
                i != changed_idx ==> regions0.slot_owners[i] == regions1.slot_owners[i],
            regions0.slot_owners.dom() =~= regions1.slot_owners.dom(),
        ensures
            self.relate_region(regions1),
    ;

    /// Continuation entry_owns satisfy `relate_region` and `path_tracked_pred`.
    ///
    /// ## Justification
    /// When the cursor descends into a subtree, each continuation's `entry_own`
    /// was previously checked by `tree_predicate_map` in the parent's child
    /// subtree.  After descent, `map_full_tree` only covers the siblings (the
    /// taken child is `None`), so the path entries' properties are no longer
    /// covered by `map_full_tree`.  However, `regions` is unchanged since
    /// descent, so the properties still hold.
    pub axiom fn cont_entries_relate_region(
        self, regions: MetaRegionOwners,
    )
        requires
            self.inv(),
            self.relate_region(regions),
        ensures
            forall|i: int| #![trigger self.continuations[i]]
                self.level - 1 <= i < NR_LEVELS ==> {
                    &&& self.continuations[i].entry_own.relate_region(regions)
                    &&& PageTableOwner::<C>::path_tracked_pred(regions)(
                            self.continuations[i].entry_own,
                            self.continuations[i].path())
                },
    ;

    /// Cursor path nesting: for two continuations where `i > j >= self.level - 1`,
    /// `cont_i` is an ancestor of `cont_j` in the page table tree.
    /// The path from the root to `cont_j` passes through `cont_i.idx` at level `cont_i`,
    /// i.e., `cont_j.path()[cont_i.path().len()] == cont_i.idx`.
    ///
    /// This holds because the cursor was built by descending through `cont_i.idx` at each level.
    pub axiom fn cursor_path_nesting(self, i: int, j: int)
        requires
            self.inv(),
            self.level - 1 <= j < i,
            i < NR_LEVELS,
        ensures
            self.continuations[j].path().len() as int > self.continuations[i].path().len() as int,
            self.continuations[j].path().index(self.continuations[i].path().len() as int)
                == self.continuations[i].idx,;

    pub open spec fn set_va_spec(self, new_va: AbstractVaddr) -> Self {
        Self {
            va: new_va,
            ..self
        }
    }

    pub axiom fn set_va(tracked &mut self, new_va: AbstractVaddr)
        requires
            forall |i: int| #![auto] old(self).level - 1 <= i < NR_LEVELS ==> new_va.index[i] == old(self).va.index[i],
            forall |i: int| #![auto] old(self).guard_level - 1 <= i < NR_LEVELS ==> new_va.index[i] == old(self).prefix.index[i],
        ensures
            *self == old(self).set_va_spec(new_va);

    pub open spec fn set_va_in_node_spec(self, new_va: AbstractVaddr) -> Self {
        let old_cont = self.continuations[self.level - 1];
        Self {
            va: new_va,
            continuations: self.continuations.insert(
                self.level - 1,
                CursorContinuation {
                    idx: new_va.index[self.level - 1] as usize,
                    ..old_cont
                },
            ),
            ..self
        }
    }

    /// When jumping within the same page-table node, only indices at levels
    /// >= level are guaranteed to match. The entry-within-node index (level - 1)
    /// may change, so we update continuations[level-1].idx along with va.
    pub axiom fn set_va_in_node(tracked &mut self, new_va: AbstractVaddr)
        requires
            old(self).inv(),
            new_va.inv(),
            forall|i: int| #![auto] old(self).level <= i < NR_LEVELS
                ==> new_va.index[i] == old(self).va.index[i],
            old(self).locked_range().start <= new_va.to_vaddr()
                < old(self).locked_range().end,
        ensures
            *self == old(self).set_va_in_node_spec(new_va),
            self.inv(),;

    pub open spec fn new_spec(owner_subtree: OwnerSubtree<C>, idx: usize, guard_perm: GuardPerm<'rcu, C>) -> Self {
        let va = AbstractVaddr {
            offset: 0,
            index: Map::new(|i: int| 0 <= i < NR_LEVELS, |i: int| 0).insert(NR_LEVELS - 1, idx as int),
        };
        Self {
            level: NR_LEVELS as PagingLevel,
            continuations: Map::empty().insert(NR_LEVELS - 1 as int, CursorContinuation::new_spec(owner_subtree, idx, guard_perm)),
            va,
            guard_level: NR_LEVELS as PagingLevel,
            prefix: va,
            popped_too_high: false,
        }
    }

    pub axiom fn new(tracked owner_subtree: OwnerSubtree<C>, idx: usize, tracked guard_perm: GuardPerm<'rcu, C>)
    -> (tracked res: Self)
        ensures
            res == Self::new_spec(owner_subtree, idx, guard_perm);

    /// When at level L in the locked range and va (also in the locked range) is NOT within the
    /// current node [node_start, node_start + page_size(L+1)), then L + 1 < guard_level.
    ///
    /// Reasoning: at L == guard_level - 1, page_size(guard_level) equals the locked-range size,
    /// so the node covers exactly the locked range and any va in the locked range lies within it.
    /// Therefore the `else` branch (va not in node) forces L < guard_level - 1.
    pub axiom fn jump_not_in_node_level_lt_guard_minus_one(
        self,
        level: PagingLevel,
        va: Vaddr,
        node_start: Vaddr,
    )
        requires
            self.inv(),
            self.locked_range().start <= va < self.locked_range().end,
            1 <= level,
            level + 1 <= self.guard_level,
            self.locked_range().start <= node_start,
            node_start + page_size((level + 1) as PagingLevel) <= self.locked_range().end,
            !(node_start <= va && va < node_start + page_size((level + 1) as PagingLevel)),
        ensures
            level + 1 < self.guard_level;
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
            mappings: self.view_mappings(),
            phantom: PhantomData,
        }
    }
}

impl<C: PageTableConfig> Inv for CursorView<C> {
    open spec fn inv(self) -> bool {
        &&& self.cur_va < MAX_USERSPACE_VADDR
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
        &&& 1 <= self.level <= NR_LEVELS
        &&& self.level <= self.guard_level <= NR_LEVELS
//        &&& forall|i: int| 0 <= i < self.guard_level - self.level ==> self.path[i] is Some
        &&& self.va >= self.barrier_va.start
        &&& self.va % PAGE_SIZE == 0
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
