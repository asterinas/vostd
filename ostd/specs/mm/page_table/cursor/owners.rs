use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::set::{axiom_set_choose_len, axiom_set_contains_len, axiom_set_intersect_finite};

use vstd_extra::arithmetic::{
    lemma_nat_align_down_monotone, lemma_nat_align_down_sound, lemma_nat_align_down_within_block,
    lemma_nat_align_up_sound,
};
use vstd_extra::drop_tracking::*;
use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;
use vstd_extra::seq_extra::{forall_seq, lemma_forall_seq_index};

use core::marker::PhantomData;
use core::ops::Range;

use crate::mm::frame::meta::mapping::frame_to_index;
use crate::mm::page_table::*;
use crate::mm::page_prop::PageProperty;
use crate::mm::{nr_subpage_per_huge, Paddr, PagingConstsTrait, PagingLevel, Vaddr};
use crate::specs::arch::mm::{MAX_PADDR, MAX_USERSPACE_VADDR, NR_ENTRIES, NR_LEVELS, PAGE_SIZE};
use crate::specs::mm::frame::meta_owners::{REF_COUNT_MAX, REF_COUNT_UNUSED};
use crate::specs::mm::page_table::cursor::page_size_lemmas::{
    lemma_page_size_divides, lemma_page_size_ge_page_size, lemma_page_size_spec_level1,
};
use crate::specs::arch::paging_consts::PagingConsts;
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
            old(self).inv(),
            old(self).idx < old(self).children.len(),
            old(self).children[old(self).idx as int] is Some,
        ensures
            res == old(self).take_child_spec().0,
            *final(self) == old(self).take_child_spec().1,
            res.inv()
    {
        self.inv_children_unroll(self.idx as int);
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
            *final(self) == old(self).put_child_spec(child)
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
            *final(self) == old(self).make_cont_spec(idx, guard_perm@).1;

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
            *final(self) == old(self).restore_spec(child).0,
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
        assert forall|j: int|
            #![auto]
            0 <= j < self.children.len()
                && self.children[j] is Some implies
                self.children[j].unwrap().tree_predicate_map(
                    self.path().push_tail(j as usize), g)
        by {
            self.inv_children_unroll(j);
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
        assert forall|j: int|
            #![auto]
            0 <= j < self.children.len()
                && self.children[j] is Some implies
                self.children[j].unwrap().tree_predicate_map(
                    self.path().push_tail(j as usize), g)
        by {
            if j != idx {
                cont0.inv_children_unroll(j);
                OwnerSubtree::map_implies(
                    cont0.children[j].unwrap(),
                    cont0.path().push_tail(j as usize), f, g);
            }
        };
    }

    pub open spec fn level(self) -> PagingLevel {
        self.entry_own.node.unwrap().level
    }

    pub open spec fn inv_children(self) -> bool {
        self.children.all(
            |child: Option<OwnerSubtree<C>>|
            child is Some ==> child.unwrap().inv()
        )
    }

    pub proof fn inv_children_unroll(self, i:int)
        requires
            self.inv_children(),
            0 <= i < self.children.len(),
            self.children[i] is Some
        ensures
            self.children[i].unwrap().inv()
    {
        let pred = |child: Option<OwnerSubtree<C>>| child is Some ==> child.unwrap().inv();
        assert(pred(self.children[i]));
    }

    pub proof fn inv_children_unroll_all(self)
        requires
            self.inv_children()
        ensures
            forall |i:int|
                #![auto]
                0 <= i < self.children.len() ==>
                self.children[i] is Some ==>
                self.children[i].unwrap().inv()
    {
        let pred = |child: Option<OwnerSubtree<C>>| child is Some ==> child.unwrap().inv();
        assert forall |i:int| 0 <= i < self.children.len() && #[trigger] self.children[i] is Some implies
            self.children[i].unwrap().inv()
        by {
            self.inv_children_unroll(i)
        }
    }

    pub open spec fn inv_children_rel_pred(self) -> spec_fn(int, Option<OwnerSubtree<C>>) -> bool {
        |i: int, child: Option<OwnerSubtree<C>>| {
            child is Some ==> {
                &&& child.unwrap().value.parent_level == self.level()
                &&& child.unwrap().level == self.tree_level + 1
                &&& !child.unwrap().value.in_scope
                &&& <EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(self.entry_own, i, Some(child.unwrap().value))
                &&& child.unwrap().value.path == self.path().push_tail(i as usize)
            }
        }
    }

    pub open spec fn inv_children_rel(self) -> bool {
        forall_seq(self.children, self.inv_children_rel_pred())
    }

    pub proof fn inv_children_rel_unroll(self, i: int)
        requires
            self.inv_children_rel(),
            0 <= i < self.children.len(),
            self.children[i] is Some,
        ensures
            self.children[i].unwrap().value.parent_level == self.level(),
            self.children[i].unwrap().level == self.tree_level + 1,
            !self.children[i].unwrap().value.in_scope,
            <EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(self.entry_own, i, Some(self.children[i].unwrap().value)),
            self.children[i].unwrap().value.path == self.path().push_tail(i as usize),
    {
        lemma_forall_seq_index(
            self.children, self.inv_children_rel_pred(), i);
    }

    pub open spec fn inv(self) -> bool {
        &&& self.children.len() == NR_ENTRIES
        &&& 0 <= self.idx < NR_ENTRIES
        &&& self.inv_children()
        &&& self.inv_children_rel()
        &&& self.entry_own.is_node()
        &&& self.entry_own.inv()
        &&& !self.entry_own.in_scope
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
            *final(self) == old(self).inc_index(),
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

    /// Proves `rel_children` for a child that was taken from the continuation, modified
    /// (by protect, alloc_if_none, or split_if_mapped_huge), and placed back at the same index.
    ///
    /// The key inputs are:
    /// - `node_matching` from the operation's postcondition (provides `match_pte`)
    /// - The child's path and path length (preserved by the operation)
    /// - The entry's path (unchanged through the reconstruction)
    /// Proves `rel_children` from `node_matching`. After taking a child from a continuation,
    /// modifying it (protect/alloc/split), and restoring `entry_own.node = Some(parent_owner)`,
    /// `rel_children` holds for any `entry_own` that has `node == Some(parent_owner)` and the
    /// correct `path`.
    pub proof fn rel_children_from_node_matching(
        entry: &Entry<'rcu, C>,
        child_value: EntryOwner<C>,
        parent_owner: NodeOwner<C>,
        guard_perm: GuardPerm<'rcu, C>,
        entry_own: EntryOwner<C>,
        idx: usize,
    )
        requires
            entry.node_matching(child_value, parent_owner, guard_perm),
            entry.idx == idx,
            entry_own.node == Some(parent_owner),
            child_value.path == entry_own.path.push_tail(idx),
            child_value.path.len() == parent_owner.tree_level + 1,
        ensures
            <EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(
                entry_own,
                idx as int,
                Some(child_value)),
    { }

    /// After restoring `entry_own.node = Some(parent_owner)` and putting the child back
    /// at `idx`, the continuation invariant holds. The child at `idx` may have been modified
    /// (e.g., by `split_if_mapped_huge` or `protect`) but must satisfy `inv()`, have the
    /// correct path/parent_level/level, satisfy `rel_children`, and have `!in_scope`.
    pub axiom fn continuation_inv_holds_after_child_restore(self)
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
            self.children[self.idx as int].unwrap().inv(),
            self.children[self.idx as int].unwrap().value.parent_level == self.level(),
            self.children[self.idx as int].unwrap().value.path == self.path().push_tail(self.idx as usize),
            self.children[self.idx as int].unwrap().level == self.tree_level + 1,
            <EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(
                self.entry_own, self.idx as int, Some(self.children[self.idx as int].unwrap().value)),
            !self.children[self.idx as int].unwrap().value.in_scope,
        ensures
            self.inv();

    pub proof fn new_child(tracked &self, paddr: Paddr, prop: PageProperty, tracked regions: &mut MetaRegionOwners) -> (tracked res: OwnerSubtree<C>)
        requires
            self.inv(),
            old(regions).slots.contains_key(frame_to_index(paddr)),
            paddr % PAGE_SIZE == 0,
            paddr < MAX_PADDR,
            paddr % page_size(self.level()) == 0,
            paddr + page_size(self.level()) <= MAX_PADDR,
            self.path().push_tail(self.idx as usize).inv(),
        ensures
            final(regions).slot_owners == old(regions).slot_owners,
            final(regions).slots == old(regions).slots,
            res.value == EntryOwner::<C>::new_frame_spec(paddr, self.path().push_tail(self.idx as usize), self.level(), prop).set_in_scope(false),
            res.inv(),
            res.level == self.tree_level + 1,
            res == OwnerSubtree::new_val(res.value, res.level as nat),
    {
        let tracked mut owner = EntryOwner::<C>::new_frame(paddr, self.path().push_tail(self.idx as usize), self.level(), prop);
        owner.in_scope = false;
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
        &&& self.va.offset == 0
        &&& 1 <= self.level <= NR_LEVELS
        &&& 1 <= self.guard_level <= NR_LEVELS
        // The top-level index of the cursor's VA must be within the page table config's
        // managed range. This ensures cursors for UserPtConfig and KernelPtConfig operate
        // on disjoint portions of the virtual address space.
        &&& C::TOP_LEVEL_INDEX_RANGE_spec().start <= self.va.index[NR_LEVELS - 1]
        &&& self.va.index[NR_LEVELS - 1] < C::TOP_LEVEL_INDEX_RANGE_spec().end
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
        // The cursor's VA shares upper indices with the prefix as long as
        // the cursor hasn't popped above guard_level.
        &&& !self.popped_too_high ==> forall|i: int| self.guard_level <= i < NR_LEVELS ==>
            self.va.index[i] == self.prefix.index[i]
        &&& !self.popped_too_high && self.guard_level >= 1 && self.level < self.guard_level ==>
            self.va.index[self.guard_level - 1] == 0
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
            // PTE consistency: child entry matches parent's PTE at parent's index
            &&& <EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(
                    self.continuations[3].entry_own, self.continuations[3].idx as int,
                    Some(self.continuations[2].entry_own))
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
            // PTE consistency: child entry matches parent's PTE at parent's index
            &&& <EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(
                    self.continuations[2].entry_own, self.continuations[2].idx as int,
                    Some(self.continuations[1].entry_own))
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
            // Path consistency: child path = parent path pushed with parent's index
            &&& self.continuations[0].path() == self.continuations[1].path().push_tail(self.continuations[1].idx as usize)
            // PTE consistency: child entry matches parent's PTE at parent's index
            &&& <EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(
                    self.continuations[1].entry_own, self.continuations[1].idx as int,
                    Some(self.continuations[0].entry_own))
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
            forall|i: int| #![trigger self.continuations[i]]
                self.level - 1 <= i < NR_LEVELS ==>
                    self.continuations[i].guard_perm.value().inner.inner@.ptr.addr()
                        != guard.inner.inner@.ptr.addr(),
        ensures
            self.nodes_locked(guards1);

    /// After a `protect` operation that only modifies `frame.prop` of the current entry,
    /// `CursorOwner::inv()` and `metaregion_sound`/`metaregion_correct` are preserved.
    ///
    /// Safety: `protect` changes only `frame.prop` and updates `parent.children_perm` to match.
    /// `EntryOwner::inv()` is preserved (from protect postcondition).
    /// `metaregion_sound` is preserved because it doesn't use `frame.prop`.
    /// `rel_children` holds via `match_pte` (from protect's `wf`/`node_matching` postconditions).
    ///
    /// The axiom requires only the semantic properties of the modified entry that are
    /// checked by `inv` and `metaregion_sound`; the structural identity of other continuations
    /// is trusted to hold from the tracked restore operations in the caller.
    pub proof fn protect_preserves_cursor_inv_metaregion(
        self,
        other: Self,
        regions: MetaRegionOwners,
    )
        requires
            self.inv(),
            self.metaregion_sound(regions),
            self.cur_entry_owner().is_frame(),
            other.cur_entry_owner().is_frame(),
            other.cur_entry_owner().inv(),
            // protect preserves PA, path, parent_level
            other.cur_entry_owner().frame.unwrap().mapped_pa == self.cur_entry_owner().frame.unwrap().mapped_pa,
            other.cur_entry_owner().path == self.cur_entry_owner().path,
            other.cur_entry_owner().parent_level == self.cur_entry_owner().parent_level,
            // cursor level and structural fields unchanged
            self.level == other.level,
            self.guard_level == other.guard_level,
            self.va == other.va,
            self.prefix == other.prefix,
            self.popped_too_high == other.popped_too_high,
            // higher-level continuations unchanged
            forall|i: int| self.level <= i < NR_LEVELS ==>
                #[trigger] self.continuations[i] == other.continuations[i],
            // bottom continuation well-formed after protect
            other.continuations[self.level - 1].inv(),
            other.continuations[self.level - 1].all_some(),
        ensures
            other.inv(),
            other.metaregion_sound(regions),
            self.metaregion_correct(regions) ==> other.metaregion_correct(regions),
    { admit() }

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
                            cont.inv_children_unroll(j);
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

    pub open spec fn zero_below_level(self) -> Self
        recommends 1 <= self.level <= NR_LEVELS,
    {
        Self { va: self.va.align_down(self.level as int), ..self }
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

    /// Unfolds zero_below_level to expose the VA as align_down(level).
    pub proof fn zero_below_level_va(self)
        requires
            1 <= self.level <= NR_LEVELS,
        ensures
            self.zero_below_level().va == self.va.align_down(self.level as int),
    {}

    pub proof fn zero_preserves_above(self)
        requires
            self.va.inv(),
            1 <= self.level <= NR_LEVELS,
        ensures
            forall |lv: int| self.level <= lv < NR_LEVELS ==> self.zero_below_level().va.index[lv] == #[trigger] self.va.index[lv],
    {
        self.va.align_down_shape(self.level as int);
    }

    pub axiom fn do_zero_below_level(tracked &mut self)
        requires
            old(self).inv(),
        ensures
            *final(self) == old(self).zero_below_level(),
            final(self).inv();

    pub proof fn do_inc_index(tracked &mut self)
        requires
            old(self).inv(),
            old(self).level <= old(self).guard_level,
            old(self).continuations[old(self).level - 1].idx + 1 < NR_ENTRIES,
            old(self).level == NR_LEVELS ==>
                (old(self).continuations[old(self).level - 1].idx + 1) < C::TOP_LEVEL_INDEX_RANGE_spec().end,
        ensures
            final(self).inv(),
            *final(self) == old(self).inc_index(),
    {
        reveal(CursorContinuation::inv_children);
        self.popped_too_high = false;
        let tracked mut cont = self.continuations.tracked_remove(self.level - 1);
        cont.do_inc_index();
        self.va.index.tracked_insert(self.level - 1, cont.idx as int);
        self.continuations.tracked_insert(self.level - 1, cont);
        assert(self.continuations == old(self).continuations.insert(self.level - 1, cont));

        old(self).va.index_increment_adds_page_size(old(self).level as int);
        lemma_page_size_ge_page_size(old(self).level as PagingLevel);

        if self.level >= self.guard_level {
            if !old(self).above_locked_range() {
                Self::inc_at_guard_level_above_locked_range(
                    old(self).va, old(self).prefix,
                    old(self).guard_level, old(self).level,
                    self.va.to_vaddr());
            }
        }
        if old(self).popped_too_high { old(self).in_locked_range_prefix_match(); }
        assert(self.va.index[self.level as int - 1] == self.continuations[self.level as int - 1].idx);
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
    pub proof fn cur_va_in_subtree_range(self)
        requires
            self.inv(),
        ensures
            vaddr(self.cur_subtree().value.path) <= self.cur_va() < vaddr(self.cur_subtree().value.path) + page_size(self.level as PagingLevel)
    {
        let L = self.level as int;
        let cont = self.continuations[L - 1];
        let subtree_path = cont.path().push_tail(cont.idx as usize);
        let va_path = self.va.to_path(L - 1);

        self.va.to_path_len(L - 1);
        cont.path().push_tail_property_len(cont.idx as usize);
        assert(cont.level() == self.level) by {
            if L == 1 {} else if L == 2 {} else if L == 3 {} else {}
        };

        assert forall|i: int| 0 <= i < subtree_path.len() implies
            subtree_path.index(i) == va_path.index(i) by {
            self.va.to_path_index(L - 1, i);
            if L == 4 {
                cont.path().push_tail_property_index(cont.idx as usize);
            } else if L == 3 {
                cont.path().push_tail_property_index(cont.idx as usize);
                self.continuations[3].path().push_tail_property_index(self.continuations[3].idx as usize);
            } else if L == 2 {
                cont.path().push_tail_property_index(cont.idx as usize);
                self.continuations[2].path().push_tail_property_index(self.continuations[2].idx as usize);
                self.continuations[3].path().push_tail_property_index(self.continuations[3].idx as usize);
            } else {
                cont.path().push_tail_property_index(cont.idx as usize);
                self.continuations[1].path().push_tail_property_index(self.continuations[1].idx as usize);
                self.continuations[2].path().push_tail_property_index(self.continuations[2].idx as usize);
                self.continuations[3].path().push_tail_property_index(self.continuations[3].idx as usize);
            }
        };

        self.va.to_path_inv(L - 1);
        self.cur_subtree_inv();
        AbstractVaddr::rec_vaddr_eq_if_indices_eq(subtree_path, va_path, 0);
        self.va.vaddr_range_from_path(L - 1);
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

    pub open spec fn cur_entry_owner(self) -> EntryOwner<C> {
        self.cur_subtree().value
    }

    pub open spec fn cur_subtree(self) -> OwnerSubtree<C> {
        self.continuations[self.level - 1].children[self.index() as int].unwrap()
    }

    /// Axiom: the item reconstructed from the current frame's physical address satisfies `clone_requires`.
    ///
    /// Safety: When `metaregion_sound` holds for a frame entry, the item reconstructed via
    /// `item_from_raw_spec(pa, ...)` is the original frame item.  The frame's slot permission
    /// (owned by the cursor) has the correct address, is initialised, and its ref count is in the
    /// valid clonable range (> 0, < REF_COUNT_MAX), so `clone_requires` is satisfied.
    pub proof fn cur_frame_clone_requires(
        self,
        item: C::Item,
        pa: Paddr,
        level: PagingLevel,
        prop: PageProperty,
        regions: MetaRegionOwners,
    )
        requires
            self.inv(),
            self.metaregion_sound(regions),
            self.cur_entry_owner().is_frame(),
            pa == self.cur_entry_owner().frame.unwrap().mapped_pa,
            C::item_from_raw_spec(pa, level, prop) == item,
        ensures
            item.clone_requires(
                regions.slots[frame_to_index(pa)],
                regions.slot_owners[frame_to_index(pa)].inner_perms.ref_count,
            )
    { admit() }

    /// Incrementing the ref count of the current frame preserves `regions.inv()` and
    /// `self.metaregion_sound(new_regions) && self.metaregion_correct(new_regions)`.
    pub proof fn clone_item_preserves_invariants(
        self,
        old_regions: MetaRegionOwners,
        new_regions: MetaRegionOwners,
        idx: usize,
    )
        requires
            self.inv(),
            self.metaregion_sound(old_regions),
            old_regions.inv(),
            self.cur_entry_owner().is_frame(),
            idx == frame_to_index(self.cur_entry_owner().frame.unwrap().mapped_pa),
            old_regions.slot_owners.contains_key(idx),
            new_regions.slot_owners.contains_key(idx),
            // rc at idx is incremented by 1
            new_regions.slot_owners[idx].inner_perms.ref_count.value() ==
                old_regions.slot_owners[idx].inner_perms.ref_count.value() + 1,
            // All other inner_perms fields at idx are identical (same tracked object)
            new_regions.slot_owners[idx].inner_perms.ref_count.id() ==
                old_regions.slot_owners[idx].inner_perms.ref_count.id(),
            new_regions.slot_owners[idx].inner_perms.storage ==
                old_regions.slot_owners[idx].inner_perms.storage,
            new_regions.slot_owners[idx].inner_perms.vtable_ptr ==
                old_regions.slot_owners[idx].inner_perms.vtable_ptr,
            new_regions.slot_owners[idx].inner_perms.in_list ==
                old_regions.slot_owners[idx].inner_perms.in_list,
            // Other MetaSlotOwner fields at idx unchanged
            new_regions.slot_owners[idx].path_if_in_pt ==
                old_regions.slot_owners[idx].path_if_in_pt,
            new_regions.slot_owners[idx].self_addr == old_regions.slot_owners[idx].self_addr,
            new_regions.slot_owners[idx].raw_count == old_regions.slot_owners[idx].raw_count,
            new_regions.slot_owners[idx].usage == old_regions.slot_owners[idx].usage,
            // All other slot_owners unchanged
            new_regions.slot_owners.dom() == old_regions.slot_owners.dom(),
            forall |i: usize| #![trigger new_regions.slot_owners[i]]
                i != idx && old_regions.slot_owners.contains_key(i) ==>
                new_regions.slot_owners[i] == old_regions.slot_owners[i],
            // slots map unchanged
            new_regions.slots == old_regions.slots,
            // rc overflow guard: old rc is a normal shared count; rc+1 stays below REF_COUNT_MAX.
            0 < old_regions.slot_owners[idx].inner_perms.ref_count.value(),
            old_regions.slot_owners[idx].inner_perms.ref_count.value() + 1 < REF_COUNT_MAX,
        ensures
            new_regions.inv(),
            self.metaregion_sound(new_regions),
            self.metaregion_correct(old_regions) ==> self.metaregion_correct(new_regions),
    {
        self.cont_entries_metaregion(old_regions);
        assert(new_regions.slot_owners[idx].inv());
        assert(new_regions.inv()) by {
            assert forall |i: usize| #[trigger] new_regions.slots.contains_key(i) implies {
                &&& new_regions.slot_owners.contains_key(i)
                &&& new_regions.slot_owners[i].inv()
                &&& new_regions.slots[i].is_init()
                &&& new_regions.slots[i].value().wf(new_regions.slot_owners[i])
                &&& new_regions.slot_owners[i].self_addr == new_regions.slots[i].addr()
            } by { assert(old_regions.slots.contains_key(i)); };
            assert forall |i: usize| #[trigger] new_regions.slot_owners.contains_key(i) implies
                new_regions.slot_owners[i].inv() by {};
        };
        self.metaregion_slot_owners_rc_increment(old_regions, new_regions, idx);
    }

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
        self.cur_subtree_inv();
        let cont = self.continuations[self.level - 1];
        let child = self.cur_subtree();
        assert(child.level < INC_LEVELS - 1);
        assert(cont.level() == self.level) by {
            if self.level == 1 {} else if self.level == 2 {} else if self.level == 3 {} else {}
        };
    }

    /// A frame entry at the cursor's current level that doesn't fit the aligned range
    /// `[cur_va, end)` must be at level > 1.
    /// Justification: At level 1, `page_size(1) == BASE_PAGE_SIZE`. Since the cursor VA
    /// and `end` are BASE_PAGE_SIZE-aligned and `cur_va < end`, we have
    /// `cur_va + page_size(1) <= end`, so a level-1 frame always fits. Therefore
    /// `!cur_entry_fits_range` implies `level > 1`.
    pub proof fn frame_not_fits_implies_level_gt_1(
        self,
        cur_entry_fits_range: bool,
        cur_va: Vaddr,
        end: Vaddr,
    )
        requires
            self.inv(),
            self.cur_entry_owner().is_frame(),
            !cur_entry_fits_range,
            cur_va < end,
            // Definition: cur_entry_fits_range iff cur_va is at start of entry AND entry end <= end.
            cur_entry_fits_range == (
                cur_va == self.cur_va_range().start.to_vaddr()
                && self.cur_va_range().end.to_vaddr() <= end),
            // cur_va and end are PAGE_SIZE-aligned
            cur_va as nat % PAGE_SIZE as nat == 0,
            end as nat % PAGE_SIZE as nat == 0,
        ensures
            self.level > 1
    { admit() }

    /// A new frame subtree at the current position has mappings equal to the singleton
    /// mapping covering the current slot range.
    pub proof fn new_child_mappings_eq_target(
        self,
        new_subtree: OwnerSubtree<C>,
        pa: Paddr,
        level: PagingLevel,
        prop: PageProperty,
    )
        requires
            self.inv(),
            level == self.level,
            new_subtree.inv(),
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
            }]
    {
        let path = new_subtree.value.path;
        let ps = page_size(level);
        let pt_level = INC_LEVELS - path.len();
        let cont = self.continuations[self.level as int - 1];

        cont.path().push_tail_property_len(cont.idx as usize);
        assert(cont.level() == self.level) by {
            if self.level == 1 {} else if self.level == 2 {} else if self.level == 3 {} else {}
        };
        assert(pt_level == self.level);

        // Reuse cur_va_in_subtree_range's vaddr equality + to_path_vaddr_concrete.
        self.cur_va_in_subtree_range();
        assert(vaddr(path) == nat_align_down(self@.cur_va as nat, ps as nat) as Vaddr) by {
            self.va.to_path_vaddr_concrete(self.level as int - 1);
            let va_path = self.va.to_path(self.level as int - 1);
            self.va.to_path_len(self.level as int - 1);
            self.va.to_path_inv(self.level as int - 1);
            self.cur_subtree_inv();
            assert forall|i: int| 0 <= i < path.len() implies path.index(i) == va_path.index(i) by {
                self.va.to_path_index(self.level as int - 1, i);
                if self.level == 4 {
                    cont.path().push_tail_property_index(cont.idx as usize);
                } else if self.level == 3 {
                    cont.path().push_tail_property_index(cont.idx as usize);
                    self.continuations[3].path().push_tail_property_index(self.continuations[3].idx as usize);
                } else if self.level == 2 {
                    cont.path().push_tail_property_index(cont.idx as usize);
                    self.continuations[2].path().push_tail_property_index(self.continuations[2].idx as usize);
                    self.continuations[3].path().push_tail_property_index(self.continuations[3].idx as usize);
                } else {
                    cont.path().push_tail_property_index(cont.idx as usize);
                    self.continuations[1].path().push_tail_property_index(self.continuations[1].idx as usize);
                    self.continuations[2].path().push_tail_property_index(self.continuations[2].idx as usize);
                    self.continuations[3].path().push_tail_property_index(self.continuations[3].idx as usize);
                }
            };
            AbstractVaddr::rec_vaddr_eq_if_indices_eq(path, va_path, 0);
        };
    }

    /// After alloc_if_none (absent→node) + restore, the cursor invariant holds.
    pub proof fn map_branch_none_inv_holds(self, owner0: Self)
        requires
            owner0.inv(),
            self.level == owner0.level,
            self.va == owner0.va,
            self.guard_level == owner0.guard_level,
            self.prefix == owner0.prefix,
            self.popped_too_high == owner0.popped_too_high,
            // Higher-level continuations unchanged
            forall|i: int| self.level <= i < NR_LEVELS ==>
                #[trigger] self.continuations[i] == owner0.continuations[i],
            // Bottom continuation is well-formed
            self.continuations[self.level - 1].inv(),
            self.continuations[self.level - 1].all_some(),
            self.continuations[self.level - 1].idx == owner0.continuations[owner0.level - 1].idx,
            self.continuations[self.level - 1].entry_own.parent_level
                == owner0.continuations[owner0.level - 1].entry_own.parent_level,
            // Guard address preserved (from parent_perms_preserved).
            self.continuations[self.level - 1].guard_perm.value().inner.inner@.ptr.addr()
                == owner0.continuations[owner0.level - 1].guard_perm.value().inner.inner@.ptr.addr(),
            self.continuations[self.level - 1].path()
                == owner0.continuations[owner0.level - 1].path(),
            self.va.index[self.level - 1] == self.continuations[self.level - 1].idx,
            // Domain preserved: same keys as owner0.
            self.continuations.dom() =~= owner0.continuations.dom(),
        ensures
            self.inv()
    {
        let L = self.level as int;
        assert(self.continuations[L - 1].level() == self.level) by {
            assert(self.continuations[L - 1].path() == owner0.continuations[L - 1].path());
            if L == 1 {} else if L == 2 {} else if L == 3 {} else {}
        };
        assert(self.continuations.contains_key(L - 1)) by {
            if L == 1 {} else if L == 2 {} else if L == 3 {} else {}
        };
    }

    /// After alloc_if_none (absent→node), `path_tracked_pred` transfers via `map_children_lift`.
    pub proof fn map_branch_none_path_tracked_holds(
        self,
        owner0: Self,
        regions: MetaRegionOwners,
        old_regions: MetaRegionOwners,
    )
        requires
            owner0.metaregion_sound(old_regions) && owner0.metaregion_correct(old_regions),
            self.inv(),
            self.level == owner0.level,
            forall|i: int| self.level <= i < NR_LEVELS ==>
                #[trigger] self.continuations[i] == owner0.continuations[i],
            Entry::<C>::path_tracked_pred_preserved(old_regions, regions),
            // Bottom continuation's children satisfy ptp(regions).
            self.continuations[self.level - 1].map_children(
                PageTableOwner::<C>::path_tracked_pred(regions)),
        ensures
            self.map_full_tree(PageTableOwner::<C>::path_tracked_pred(regions))
    {
        let ptp_old = PageTableOwner::<C>::path_tracked_pred(old_regions);
        let ptp_new = PageTableOwner::<C>::path_tracked_pred(regions);
        assert forall|i: int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS implies
                self.continuations[i].map_children(ptp_new)
        by {
            if i >= self.level as int {
                let cont = owner0.continuations[i];
                assert(cont.map_children(ptp_old));
                cont.map_children_lift(ptp_old, ptp_new);
            }
        };
    }

    /// After alloc_if_none (absent→node), `view_mappings` is unchanged (both contribute zero mappings).
    pub proof fn map_branch_none_no_new_mappings(self, owner0: Self)
        requires
            owner0.inv(),
            self.inv(),
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
            // Non-idx children and path preserved
            self.continuations[self.level - 1].path()
                == owner0.continuations[owner0.level - 1].path(),
            forall|j: int| 0 <= j < NR_ENTRIES
                && j != owner0.continuations[owner0.level - 1].idx as int ==>
                #[trigger] self.continuations[self.level - 1].children[j]
                    == owner0.continuations[owner0.level - 1].children[j],
            // The new node's subtree has empty view_rec (from alloc_if_none postcondition)
            PageTableOwner(self.continuations[self.level - 1].children[
                self.continuations[self.level - 1].idx as int].unwrap())
                .view_rec(self.continuations[self.level - 1].path()
                    .push_tail(self.continuations[self.level - 1].idx as usize))
                =~= Set::<Mapping>::empty(),
        ensures
            self.view_mappings() =~= owner0.view_mappings()
    {
        let L = self.level as int;
        let cont = self.continuations[L - 1];
        let cont0 = owner0.continuations[L - 1];
        let idx = cont0.idx as int;

        assert(cont.view_mappings() =~= cont0.view_mappings()) by {
            cont0.inv_children_unroll(idx);
            PageTableOwner(cont0.children[idx].unwrap())
                .view_rec_absent_empty(cont0.path().push_tail(idx as usize));
            assert forall |m: Mapping| cont.view_mappings().contains(m)
                implies cont0.view_mappings().contains(m) by {
                let j = choose|j:int| 0 <= j < cont.children.len()
                    && #[trigger] cont.children[j] is Some
                    && PageTableOwner(cont.children[j].unwrap())
                        .view_rec(cont.path().push_tail(j as usize)).contains(m);
                if j != idx { assert(cont.children[j] == cont0.children[j]); }
            };
            assert forall |m: Mapping| cont0.view_mappings().contains(m)
                implies cont.view_mappings().contains(m) by {
                let j = choose|j:int| 0 <= j < cont0.children.len()
                    && #[trigger] cont0.children[j] is Some
                    && PageTableOwner(cont0.children[j].unwrap())
                        .view_rec(cont0.path().push_tail(j as usize)).contains(m);
                if j != idx { assert(cont0.children[j] == cont.children[j]); }
            };
        };
    }

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

    /// After incrementing at guard_level, the new VA >= locked_range.end.
    pub proof fn inc_at_guard_level_above_locked_range(
        old_va: AbstractVaddr, prefix: AbstractVaddr,
        guard_level: u8, level: u8, new_va_val: Vaddr,
    )
        requires
            old_va.inv(), prefix.inv(),
            1 <= guard_level <= NR_LEVELS, level == guard_level,
            new_va_val == old_va.to_vaddr() + page_size(level as PagingLevel),
            prefix.align_down(guard_level as int).to_vaddr() <= old_va.to_vaddr(),
            old_va.to_vaddr() < prefix.align_up(guard_level as int).to_vaddr(),
        ensures
            new_va_val >= prefix.align_up(guard_level as int).to_vaddr(),
    {
        let ps_gl = page_size(guard_level as PagingLevel);
        lemma_page_size_ge_page_size(guard_level as PagingLevel);
        prefix.align_diff(guard_level as int);
        prefix.align_down_concrete(guard_level as int);
        prefix.align_up_concrete(guard_level as int);
        prefix.align_down_shape(guard_level as int);
        prefix.align_down(guard_level as int).reflect_prop(
            nat_align_down(prefix.to_vaddr() as nat, ps_gl as nat) as Vaddr);
        prefix.align_up(guard_level as int).reflect_prop(
            nat_align_up(prefix.to_vaddr() as nat, ps_gl as nat) as Vaddr);
    }

    pub proof fn prefix_in_locked_range(self)
        requires
            self.inv(),
            !self.popped_too_high,
            self.level < self.guard_level,
        ensures
            self.in_locked_range(),
    {
        let gl = self.guard_level;
        // From inv: !popped_too_high && level < guard_level && gl >= 1 ==> va.index[gl - 1] == 0
        // From inv: prefix.index[i] == 0 for i < gl, so prefix.index[gl - 1] == 0
        // Combined: va.index[i] == prefix.index[i] for ALL i >= gl - 1
        // align_down_to_vaddr_eq_if_upper_indices_eq(va, prefix, gl):
        //   va.align_down(gl).to_vaddr() == prefix.align_down(gl).to_vaddr() = locked_range.start
        // nat_align_down: start <= va < start + page_size(gl) = end
        if gl >= 1 && gl <= NR_LEVELS {
            // Establish match at gl - 1
            assert(self.va.index[gl as int - 1] == self.prefix.index[gl as int - 1]) by {
                assert(self.va.index[gl as int - 1] == 0);
                assert(self.prefix.index[gl as int - 1] == 0);
            };
            self.va.align_down_to_vaddr_eq_if_upper_indices_eq(self.prefix, gl as int);
            self.va.align_down_concrete(gl as int);
            self.prefix.align_down_concrete(gl as int);
            self.prefix.align_diff(gl as int);
            AbstractVaddr::from_vaddr_to_vaddr_roundtrip(
                nat_align_down(self.va.to_vaddr() as nat, page_size(gl as PagingLevel) as nat) as Vaddr);
            AbstractVaddr::from_vaddr_to_vaddr_roundtrip(
                nat_align_down(self.prefix.to_vaddr() as nat, page_size(gl as PagingLevel) as nat) as Vaddr);
            AbstractVaddr::from_vaddr_to_vaddr_roundtrip(
                nat_align_up(self.prefix.to_vaddr() as nat, page_size(gl as PagingLevel) as nat) as Vaddr);
            lemma_page_size_ge_page_size(gl as PagingLevel);
            lemma_nat_align_down_sound(self.va.to_vaddr() as nat, page_size(gl as PagingLevel) as nat);

            let ps = page_size(gl as PagingLevel) as nat;
            let va_val = self.va.to_vaddr() as nat;
            let prefix_val = self.prefix.to_vaddr() as nat;

            // Chain: locked_range.start == prefix.align_down(gl).to_vaddr()
            //   == nat_align_down(prefix_val, ps)  [from align_down_concrete + roundtrip]
            //   == nat_align_down(va_val, ps)       [from align_down_to_vaddr_eq]
            //   <= va_val                            [from lemma_nat_align_down_sound]
            // And: va_val < nat_align_down(va_val, ps) + ps
            //   == nat_align_down(prefix_val, ps) + ps
            //   == nat_align_up(prefix_val, ps)      [from align_diff]
            //   == locked_range.end                  [from align_up_concrete + roundtrip]
            // Connect locked_range to nat_align via reflect_prop
            self.prefix.align_down_shape(gl as int);
            self.prefix.align_down(gl as int).reflect_prop(
                nat_align_down(prefix_val, ps) as Vaddr);
            self.prefix.align_up_concrete(gl as int);
            self.prefix.align_up(gl as int).reflect_prop(
                nat_align_up(prefix_val, ps) as Vaddr);

            assert(self.locked_range().start == nat_align_down(prefix_val, ps) as usize);
            assert(self.locked_range().end == nat_align_up(prefix_val, ps) as usize);
            assert(nat_align_down(va_val, ps) == nat_align_down(prefix_val, ps));
            assert(nat_align_down(va_val, ps) as usize <= self.va.to_vaddr());
            assert(self.va.to_vaddr() < (nat_align_down(va_val, ps) + ps) as usize);
        }
    }

    /// Reverse of prefix_in_locked_range: if va is in the locked range,
    /// then va shares upper indices with prefix.
    pub proof fn in_locked_range_prefix_match(self)
        requires
            self.inv(),
            self.prefix.inv(),
            1 <= self.guard_level <= NR_LEVELS,
            self.in_locked_range(),
        ensures
            forall|i:int| self.guard_level <= i < NR_LEVELS ==> self.va.index[i] == self.prefix.index[i],
    {
        let gl = self.guard_level;
        let start = self.prefix.align_down(gl as int).to_vaddr();

        // prefix is in its own locked range
        self.prefix.align_down_shape(gl as int);
        let prefix_ad = self.prefix.align_down(gl as int);

        // align_down(gl).to_vaddr() is page_size(gl)-aligned
        self.prefix.align_down_concrete(gl as int);
        AbstractVaddr::from_vaddr_to_vaddr_roundtrip(nat_align_down(
            self.prefix.to_vaddr() as nat, page_size(gl as PagingLevel) as nat) as Vaddr);
        lemma_page_size_ge_page_size(gl as PagingLevel);
        lemma_nat_align_down_sound(self.prefix.to_vaddr() as nat, page_size(gl as PagingLevel) as nat);

        // prefix.to_vaddr() is in [start, start + page_size(gl))
        self.prefix.align_diff(gl as int);

        if gl as int >= 2 && (gl as int) < NR_LEVELS as int {
            // Connect locked_range.end == start + page_size(gl)
            self.prefix.align_up_concrete(gl as int);
            AbstractVaddr::from_vaddr_to_vaddr_roundtrip(
                nat_align_up(self.prefix.to_vaddr() as nat, page_size(gl as PagingLevel) as nat) as Vaddr);

            // Both va and prefix are in [start, start + page_size(gl)).
            // same_node_indices_match with level = gl - 1 >= 1
            AbstractVaddr::same_node_indices_match(
                self.va.to_vaddr(),
                self.prefix.to_vaddr(),
                start,
                (gl - 1) as PagingLevel,
            );
            // from_vaddr(va) == va (since va.inv())
            AbstractVaddr::to_vaddr_from_vaddr_roundtrip(self.va);
            AbstractVaddr::to_vaddr_from_vaddr_roundtrip(self.prefix);
        } else if gl as int == 1 {
            // gl == 1: both va and prefix are in [start, start + page_size(1)) where
            // start = nat_align_down(prefix.to_vaddr(), page_size(1)).
            // Use same_node_indices_match at level=1 with base = align_down(prefix, page_size(2)).
            let ps1 = page_size(1 as PagingLevel) as nat;
            let ps2 = page_size(2 as PagingLevel) as nat;
            let pv = self.prefix.to_vaddr() as nat;
            let cv = self.va.to_vaddr() as nat;
            let node_start = nat_align_down(pv, ps2) as usize;

            lemma_page_size_ge_page_size(1 as PagingLevel);
            lemma_page_size_ge_page_size(2 as PagingLevel);
            page_size_monotonic(1 as PagingLevel, 2 as PagingLevel);
            lemma_page_size_divides(1 as PagingLevel, 2 as PagingLevel);
            lemma_nat_align_down_sound(pv, ps2);
            lemma_nat_align_down_sound(pv, ps1);

            // locked_range.end = start_4k + ps1 where start_4k = align_down(prefix, ps1)
            self.prefix.align_up_concrete(1);
            self.prefix.align_diff(1);
            AbstractVaddr::from_vaddr_to_vaddr_roundtrip(nat_align_up(pv, ps1) as Vaddr);

            // prefix is in [node_start, node_start + ps2) (from align_down(prefix, ps2) = node_start)
            // va is in [start_4k, start_4k + ps1) from in_locked_range.
            // start_4k = align_down(prefix, ps1) >= align_down(prefix, ps2) = node_start (monotone)
            lemma_nat_align_down_monotone(pv, ps1, ps2);
            // start_4k < node_start + ps2 (since start_4k <= prefix < node_start + ps2)
            // start_4k + ps1 <= node_start + ps2 (from within_block: start_4k is ps1-aligned
            //   in the ps2-block, and ps1 | ps2, so last ps1-block ends at node_start + ps2)
            lemma_nat_align_down_within_block(pv, ps1, ps2);
            // So va < start_4k + ps1 <= node_start + ps2.
            // And va >= start_4k >= node_start.

            AbstractVaddr::same_node_indices_match(
                self.va.to_vaddr(),
                self.prefix.to_vaddr(),
                node_start,
                1 as PagingLevel,
            );
            AbstractVaddr::to_vaddr_from_vaddr_roundtrip(self.va);
            AbstractVaddr::to_vaddr_from_vaddr_roundtrip(self.prefix);
        } else {
            // gl == NR_LEVELS: forall i >= NR_LEVELS is vacuous
        }
    }

    pub proof fn in_locked_range_level_lt_nr_levels(self)
        requires self.inv(), self.in_locked_range(), !self.popped_too_high,
        ensures self.level < NR_LEVELS,
    {
        self.in_locked_range_level_lt_guard_level();
    }

    pub proof fn in_locked_range_level_lt_guard_level(self)
        requires self.inv(), self.in_locked_range(), !self.popped_too_high,
        ensures self.level < self.guard_level,
    {
        assert(self.in_locked_range() ==> !self.above_locked_range());
    }

    /// The node at `level+1` containing `va` fits within the locked range.
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

    pub proof fn locked_range_page_aligned(self)
        requires
            self.inv(),
        ensures
            self.locked_range().end % PAGE_SIZE == 0,
            self.locked_range().start % PAGE_SIZE == 0,
    {
        let gl = self.guard_level;
        // From inv(): 1 <= guard_level <= NR_LEVELS.
        assert(1 <= gl <= NR_LEVELS);
        let pv = self.prefix.to_vaddr() as nat;
        let ps = page_size(gl as PagingLevel) as nat;
        lemma_page_size_ge_page_size(gl as PagingLevel);
        lemma_page_size_divides(1u8, gl as PagingLevel);
        lemma_page_size_spec_level1();
        lemma_nat_align_down_sound(pv, ps);
        lemma_nat_align_up_sound(pv, ps);
        let start_va = nat_align_down(pv, ps);
        let end_va = nat_align_up(pv, ps);
        vstd::arithmetic::div_mod::lemma_mod_mod(start_va as int, PAGE_SIZE as int, ps as int / PAGE_SIZE as int);
        vstd::arithmetic::div_mod::lemma_mod_mod(end_va as int, PAGE_SIZE as int, ps as int / PAGE_SIZE as int);
        self.prefix.align_down_concrete(gl as int);
        self.prefix.align_up_concrete(gl as int);

        // Prove the nat values fit in Vaddr (usize), so the `as Vaddr` cast doesn't truncate.
        self.prefix.to_vaddr_bounded();
        self.prefix.to_vaddr_indices_gap_bound(0);
        // to_vaddr_indices_gap_bound(0): to_vaddr_indices(0) + 2^12 <= 2^48.
        // to_vaddr_bounded: to_vaddr() = offset + to_vaddr_indices(0), offset < 2^12.
        // Therefore pv < 2^48.
        vstd::arithmetic::power2::lemma2_to64();
        let bound = pow2(48nat) as nat;
        assert(pv < bound);
        // page_size(gl) = PAGE_SIZE * pow2(9*(gl-1)).
        // gl <= NR_LEVELS = 4, so 9*(gl-1) <= 27, so page_size(gl) <= 2^39.
        // ps <= 2^39 < 2^48 = bound.
        crate::specs::arch::paging_consts::lemma_nr_subpage_per_huge_eq_nr_entries();
        vstd_extra::external::ilog2::lemma_usize_ilog2_to32();
        lemma_page_size_ge_page_size(gl as PagingLevel);
        assert(ps <= page_size(NR_LEVELS as PagingLevel) as nat) by {
            page_size_monotonic(gl as PagingLevel, NR_LEVELS as PagingLevel);
        };
        // page_size(4) = PAGE_SIZE * pow2(9*3) = 4096 * pow2(27) = pow2(12) * pow2(27) = pow2(39).
        vstd::arithmetic::power2::lemma_pow2_adds(12nat, 27nat);
        vstd::arithmetic::power2::lemma2_to64_rest();
        assert(pow2(39nat) < pow2(48nat)) by {
            vstd_extra::external::ilog2::lemma_pow2_increases(39nat, 48nat);
        };
        assert(page_size(NR_LEVELS as PagingLevel) == pow2(39nat)) by {
            assert(nr_subpage_per_huge::<PagingConsts>().ilog2() * ((NR_LEVELS - 1) as nat) == 27nat);
        };
        assert(ps < bound);
        assert(end_va < pv + ps);
        assert(pv + ps < 2 * bound);
        // 2 * 2^48 = 2^49 < 2^64 = usize::MAX + 1.
        vstd::arithmetic::power2::lemma_pow2_adds(1nat, 48nat);
        assert(2 * bound == pow2(49nat) as nat);
        assert(pow2(49nat) <= pow2(64nat)) by {
            vstd_extra::external::ilog2::lemma_pow2_increases(49nat, 64nat);
        };
        assert(end_va < usize::MAX as nat);
        assert(start_va < usize::MAX as nat);

        AbstractVaddr::from_vaddr_to_vaddr_roundtrip(start_va as Vaddr);
        AbstractVaddr::from_vaddr_to_vaddr_roundtrip(end_va as Vaddr);

        self.prefix.align_down(gl as int).reflect_prop(start_va as Vaddr);
        self.prefix.align_up(gl as int).reflect_prop(end_va as Vaddr);
    }

    pub proof fn cur_subtree_inv(self)
        requires
            self.inv()
        ensures
            self.cur_subtree().inv()
    {
        let cont = self.continuations[self.level - 1];
        cont.inv_children_unroll(cont.idx as int)
    }

    /// If the current entry is absent, `!self@.present()`.
    pub proof fn cur_entry_absent_not_present(self)
        requires self.inv(), self.cur_entry_owner().is_absent(),
        ensures !self@.present(),
    {
        self.cur_subtree_inv();
        let cur_va = self.cur_va();
        let cur_subtree = self.cur_subtree();
        let cur_path = cur_subtree.value.path;
        PageTableOwner(cur_subtree).view_rec_absent_empty(cur_path);

        assert forall |m: Mapping| self.view_mappings().contains(m) implies
            !(m.va_range.start <= cur_va < m.va_range.end) by {
            if m.va_range.start <= cur_va < m.va_range.end {
                self.mapping_covering_cur_va_from_cur_subtree(m);
            }
        };

        let filtered = self@.mappings.filter(
            |m: Mapping| m.va_range.start <= self@.cur_va < m.va_range.end);
        assert(filtered =~= set![]) by {
            assert forall |m: Mapping| !filtered.contains(m) by {
                if self@.mappings.contains(m) && m.va_range.start <= self@.cur_va < m.va_range.end {
                    assert(self.view_mappings().contains(m));
                }
            };
        };
    }

    /// Generalises `cur_entry_absent_not_present` to any empty subtree.
    pub proof fn cur_subtree_empty_not_present(self)
        requires
            self.inv(),
            PageTableOwner(self.cur_subtree()).view_rec(self.cur_subtree().value.path) =~= set![],
        ensures !self@.present(),
    {
        let cur_va = self.cur_va();

        assert forall |m: Mapping| self.view_mappings().contains(m) implies
            !(m.va_range.start <= cur_va < m.va_range.end) by {
            if m.va_range.start <= cur_va < m.va_range.end {
                self.mapping_covering_cur_va_from_cur_subtree(m);
            }
        };

        let filtered = self@.mappings.filter(
            |m: Mapping| m.va_range.start <= self@.cur_va < m.va_range.end);
        assert(filtered =~= set![]) by {
            assert forall |m: Mapping| !filtered.contains(m) by {
                if self@.mappings.contains(m) && m.va_range.start <= self@.cur_va < m.va_range.end {
                    assert(self.view_mappings().contains(m));
                }
            };
        };
        assert(filtered.len() == 0);
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
        self.cur_subtree_inv();
        self.cur_va_in_subtree_range();
        self.view_preserves_inv();
        let subtree = self.cur_subtree();
        let path = subtree.value.path;
        let frame = self.cur_entry_owner().frame.unwrap();
        let pt_level = INC_LEVELS - path.len();
        let cont = self.continuations[self.level - 1];

        cont.path().push_tail_property_len(cont.idx as usize);
        assert(cont.level() == self.level) by {
            if self.level == 1 {} else if self.level == 2 {} else if self.level == 3 {} else {}
        };
        assert(pt_level == self.level);

        let m = Mapping {
            va_range: Range { start: vaddr(path), end: (vaddr(path) + page_size(pt_level as PagingLevel)) as Vaddr },
            pa_range: Range { start: frame.mapped_pa, end: (frame.mapped_pa + page_size(pt_level as PagingLevel)) as Paddr },
            page_size: page_size(pt_level as PagingLevel),
            property: frame.prop,
        };
        assert(PageTableOwner(subtree).view_rec(path) =~= set![m]);
        assert(self.view_mappings().contains(m));
        assert(m.inv());

        assert(m.va_range.start <= self@.cur_va < m.va_range.end) by {
            self.cur_va_in_subtree_range();
        };
        let filtered = self@.mappings.filter(|m2: Mapping| m2.va_range.start <= self@.cur_va < m2.va_range.end);
        assert(filtered.contains(m));
        axiom_set_intersect_finite::<Mapping>(
            self@.mappings, Set::new(|m2: Mapping| m2.va_range.start <= self@.cur_va < m2.va_range.end));
        axiom_set_contains_len(filtered, m);
    }

    /// The entry_own at each continuation level satisfies `metaregion_sound`.
    pub open spec fn path_metaregion_sound(self, regions: MetaRegionOwners) -> bool {
        forall|i: int| #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS ==>
                self.continuations[i].entry_own.metaregion_sound(regions)
    }

    /// The entry_own at each continuation level satisfies `path_tracked_pred`.
    pub open spec fn path_metaregion_correct(self, regions: MetaRegionOwners) -> bool {
        forall|i: int| #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS ==>
                PageTableOwner::<C>::path_tracked_pred(regions)(
                    self.continuations[i].entry_own,
                    self.continuations[i].path())
    }

    pub open spec fn metaregion_sound(self, regions: MetaRegionOwners) -> bool
    {
        &&& self.map_full_tree(|entry_owner: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
            entry_owner.metaregion_sound(regions))
        &&& self.path_metaregion_sound(regions)
    }

    pub open spec fn metaregion_correct(self, regions: MetaRegionOwners) -> bool
    {
        &&& self.map_full_tree(PageTableOwner::<C>::path_tracked_pred(regions))
        &&& self.path_metaregion_correct(regions)
    }

    pub open spec fn not_in_tree(self, owner: EntryOwner<C>) -> bool {
        self.map_full_tree(|owner0: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
            owner0.meta_slot_paddr_neq(owner))
    }

    pub proof fn absent_not_in_tree(self, owner: EntryOwner<C>)
        requires
            self.inv(),
            owner.inv(),
            owner.is_absent(),
        ensures
            self.not_in_tree(owner),
    {
        let g = |e: EntryOwner<C>, p: TreePath<NR_ENTRIES>| e.meta_slot_paddr_neq(owner);
        let nsp = PageTableOwner::<C>::not_in_scope_pred();
        assert(OwnerSubtree::implies(nsp, g)) by {
            assert forall |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                entry.inv() && !entry.in_scope implies #[trigger] g(entry, path) by {};
        };
        assert forall |i: int| #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS implies self.continuations[i].map_children(g)
        by {
            let cont = self.continuations[i];
            reveal(CursorContinuation::inv_children);
            assert forall |j: int| 0 <= j < NR_ENTRIES
                && #[trigger] cont.children[j] is Some implies
                cont.children[j].unwrap().tree_predicate_map(cont.path().push_tail(j as usize), g)
            by {
                cont.inv_children_unroll(j);
                PageTableOwner::tree_not_in_scope(cont.children[j].unwrap(), cont.path().push_tail(j as usize));
                cont.children[j].unwrap().map_implies(cont.path().push_tail(j as usize), nsp, g);
            };
        };
    }

    /// If the cursor owner's tree satisfies `metaregion_correct(regions)`, and a new entry's
    /// physical address is not currently tracked in the page table (`path_if_in_pt is None`),
    /// then no existing entry in the tree has the same physical address as the new entry.
    ///
    /// This lemma encapsulates the `map_children_implies` proof for `not_in_tree`, factored out
    /// so it runs in its own Z3 context (avoiding rlimit issues when called from large functions).
    /// If `path_if_in_pt is None` at the new entry's slot, then no NODE in the tree
    /// has the same paddr (node metaregion_sound requires path_if_in_pt == Some).
    /// Frames CAN share paddrs (they don't track path_if_in_pt).
    pub proof fn not_in_tree_from_not_mapped(
        self,
        regions: MetaRegionOwners,
        new_entry: EntryOwner<C>,
    )
        requires
            self.inv(),
            self.metaregion_correct(regions),
            new_entry.meta_slot_paddr() is Some,
            regions.slot_owners[
                frame_to_index(new_entry.meta_slot_paddr().unwrap())
            ].path_if_in_pt is None,
        ensures
            // Only guarantees paddr_neq for node entries (frames can share paddrs).
            self.map_full_tree(|e: EntryOwner<C>, p: TreePath<NR_ENTRIES>|
                e.is_node() ==> e.meta_slot_paddr_neq(new_entry)),
    {
        let pa = new_entry.meta_slot_paddr().unwrap();
        let g = |e: EntryOwner<C>, p: TreePath<NR_ENTRIES>|
            e.is_node() ==> e.meta_slot_paddr_neq(new_entry);
        assert(OwnerSubtree::implies(PageTableOwner::<C>::path_tracked_pred(regions), g)) by {
            assert forall |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                PageTableOwner::<C>::path_tracked_pred(regions)(entry, path)
                implies #[trigger] g(entry, path) by {
                if entry.is_node() && entry.meta_slot_paddr() is Some
                    && entry.meta_slot_paddr().unwrap() == pa {
                    // Node: path_tracked_pred gives path_if_in_pt == Some(entry.path).
                    // But precondition says path_if_in_pt is None. Contradiction.
                    assert(false);
                }
            };
        };
        self.map_children_implies(PageTableOwner::<C>::path_tracked_pred(regions), g);
    }

    pub proof fn metaregion_preserved(self, other: Self, regions0: MetaRegionOwners, regions1: MetaRegionOwners)
        requires
            self.inv(),
            self.metaregion_sound(regions0),
            self.level == other.level,
            self.continuations =~= other.continuations,
            OwnerSubtree::implies(
                PageTableOwner::<C>::metaregion_sound_pred(regions0),
                PageTableOwner::<C>::metaregion_sound_pred(regions1)),
            OwnerSubtree::implies(
                PageTableOwner::<C>::path_tracked_pred(regions0),
                PageTableOwner::<C>::path_tracked_pred(regions1)),
        ensures
            other.metaregion_sound(regions1),
            self.metaregion_correct(regions0) ==> other.metaregion_correct(regions1),
    {
        let e = PageTableOwner::<C>::path_tracked_pred(regions0);
        let f = PageTableOwner::metaregion_sound_pred(regions0);
        let g = PageTableOwner::metaregion_sound_pred(regions1);
        let h = PageTableOwner::<C>::path_tracked_pred(regions1);

        assert forall|i: int| #![auto] self.level - 1 <= i < NR_LEVELS implies {
            other.continuations[i].map_children(g)
        } by {
            let cont = self.continuations[i];
            assert(cont.inv());
            assert(cont.map_children(f));
            assert(cont == other.continuations[i]);
            reveal(CursorContinuation::inv_children);
            assert forall |j: int| 0 <= j < NR_ENTRIES && #[trigger] cont.children[j] is Some implies
                cont.children[j].unwrap().tree_predicate_map(cont.path().push_tail(j as usize), g) by {
                    cont.inv_children_unroll(j);
                    cont.children[j].unwrap().map_implies(cont.path().push_tail(j as usize), f, g);
            };
        };
        // Path entries: transfer via implies(f, g) + entry_own.inv().
        assert(other.path_metaregion_sound(regions1)) by {
            assert forall|i: int| #![trigger other.continuations[i]]
                self.level - 1 <= i < NR_LEVELS implies
                    other.continuations[i].entry_own.metaregion_sound(regions1) by {
                self.inv_continuation(i);
                let eo = self.continuations[i].entry_own;
                assert(eo.inv());
                assert(eo.metaregion_sound(regions0));
                // implies(f, g): eo.inv() && f(eo, _) ==> g(eo, _)
                assert(g(eo, self.continuations[i].path()));
            };
        };
        if self.metaregion_correct(regions0) {
            assert forall|i: int| #![auto] self.level - 1 <= i < NR_LEVELS implies {
                other.continuations[i].map_children(h)
            } by {
                let cont = self.continuations[i];
                assert(cont.inv());
                assert(cont.map_children(e));
                assert(cont == other.continuations[i]);
                reveal(CursorContinuation::inv_children);
                assert forall |j: int| 0 <= j < NR_ENTRIES && #[trigger] cont.children[j] is Some implies
                    cont.children[j].unwrap().tree_predicate_map(cont.path().push_tail(j as usize), h) by {
                        cont.inv_children_unroll(j);
                        cont.children[j].unwrap().map_implies(cont.path().push_tail(j as usize), e, h);
                };
            };
            // Path entries: transfer via implies(e, h).
            assert(other.path_metaregion_correct(regions1)) by {
                assert forall|i: int| #![trigger other.continuations[i]]
                    self.level - 1 <= i < NR_LEVELS implies
                        PageTableOwner::<C>::path_tracked_pred(regions1)(
                            other.continuations[i].entry_own,
                            other.continuations[i].path()) by {
                    self.inv_continuation(i);
                    let eo = self.continuations[i].entry_own;
                    assert(eo.inv());
                };
            };
        }
    }

    /// Transfers `metaregion_sound`+`metaregion_correct` when `slot_owners` is preserved.
    pub proof fn metaregion_slot_owners_preserved(self, regions0: MetaRegionOwners, regions1: MetaRegionOwners)
        requires
            self.inv(),
            self.metaregion_sound(regions0),
            regions0.slot_owners =~= regions1.slot_owners,
            forall |k: usize| regions0.slots.contains_key(k) ==> #[trigger] regions1.slots.contains_key(k),
            forall |k: usize| regions0.slots.contains_key(k) ==> regions0.slots[k] == #[trigger] regions1.slots[k],
        ensures
            self.metaregion_sound(regions1),
            self.metaregion_correct(regions0) ==> self.metaregion_correct(regions1),
    {
        let f = PageTableOwner::<C>::metaregion_sound_pred(regions0);
        let g = PageTableOwner::<C>::metaregion_sound_pred(regions1);
        let e = PageTableOwner::<C>::path_tracked_pred(regions0);
        let h = PageTableOwner::<C>::path_tracked_pred(regions1);
        assert forall |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
            entry.inv() && f(entry, path) implies #[trigger] g(entry, path) by {
                entry.metaregion_sound_slot_owners_only(regions0, regions1);
        };
        assert forall |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
            entry.inv() && e(entry, path) implies #[trigger] h(entry, path) by {};
        self.metaregion_preserved(self, regions0, regions1);
    }

    pub proof fn metaregion_slot_owners_rc_increment(
        self, regions0: MetaRegionOwners, regions1: MetaRegionOwners, idx: usize)
        requires
            self.inv(),
            self.metaregion_sound(regions0),
            regions0.inv(),
            regions1.slots == regions0.slots,
            regions1.slot_owners.dom() == regions0.slot_owners.dom(),
            regions1.slot_owners[idx].inner_perms.ref_count.value() ==
                regions0.slot_owners[idx].inner_perms.ref_count.value() + 1,
            regions1.slot_owners[idx].inner_perms.ref_count.id() ==
                regions0.slot_owners[idx].inner_perms.ref_count.id(),
            regions1.slot_owners[idx].inner_perms.storage ==
                regions0.slot_owners[idx].inner_perms.storage,
            regions1.slot_owners[idx].inner_perms.vtable_ptr ==
                regions0.slot_owners[idx].inner_perms.vtable_ptr,
            regions1.slot_owners[idx].inner_perms.in_list ==
                regions0.slot_owners[idx].inner_perms.in_list,
            regions1.slot_owners[idx].path_if_in_pt == regions0.slot_owners[idx].path_if_in_pt,
            regions1.slot_owners[idx].self_addr == regions0.slot_owners[idx].self_addr,
            regions1.slot_owners[idx].raw_count == regions0.slot_owners[idx].raw_count,
            regions1.slot_owners[idx].usage == regions0.slot_owners[idx].usage,
            regions1.slot_owners[idx].inner_perms.ref_count.value()
                != REF_COUNT_UNUSED,
            forall |i: usize| #![trigger regions1.slot_owners[i]]
                i != idx && regions0.slot_owners.contains_key(i) ==>
                regions1.slot_owners[i] == regions0.slot_owners[i],
        ensures
            self.metaregion_sound(regions1),
            self.metaregion_correct(regions0) ==> self.metaregion_correct(regions1),
    {
        let f = PageTableOwner::<C>::metaregion_sound_pred(regions0);
        let g = PageTableOwner::<C>::metaregion_sound_pred(regions1);
        let e = PageTableOwner::<C>::path_tracked_pred(regions0);
        let h = PageTableOwner::<C>::path_tracked_pred(regions1);
        assert(OwnerSubtree::implies(f, g)) by {
            assert forall |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                entry.inv() && f(entry, path) implies #[trigger] g(entry, path) by {
                if entry.meta_slot_paddr() is Some {
                    let eidx = frame_to_index(entry.meta_slot_paddr().unwrap());
                    if eidx != idx {} else { entry.metaregion_sound_rc_value_changed(regions0, regions1); }
                }
            };
        };
        assert(OwnerSubtree::implies(e, h)) by {
            assert forall |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                entry.inv() && e(entry, path) implies #[trigger] h(entry, path) by {
                if entry.meta_slot_paddr() is Some { let eidx = frame_to_index(entry.meta_slot_paddr().unwrap()); if eidx != idx {} }
            };
        };
        self.metaregion_preserved(self, regions0, regions1);
    }

    /// Transfers `metaregion_sound`+`metaregion_correct` when `raw_count` changed from 0 to 1 at one index.
    /// Uses `map_implies_and` with `not_in_scope_pred` since tree entries have `!in_scope`.
    pub proof fn metaregion_borrow_slot(
        self, regions0: MetaRegionOwners, regions1: MetaRegionOwners, changed_idx: usize
    )
        requires
            self.inv(),
            self.metaregion_sound(regions0),
            regions1.inv(),
            forall |k: usize| regions0.slots.contains_key(k) ==> #[trigger] regions1.slots.contains_key(k),
            forall |k: usize| regions0.slots.contains_key(k) && k != changed_idx
                ==> regions0.slots[k] == #[trigger] regions1.slots[k],
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
            self.metaregion_sound(regions1),
            self.metaregion_correct(regions0) ==> self.metaregion_correct(regions1),
    {
        let f = PageTableOwner::<C>::metaregion_sound_pred(regions0);
        let g = PageTableOwner::<C>::metaregion_sound_pred(regions1);
        let e = PageTableOwner::<C>::path_tracked_pred(regions0);
        let h = PageTableOwner::<C>::path_tracked_pred(regions1);
        let nsp = PageTableOwner::<C>::not_in_scope_pred();

        // implies(f && nsp, g):
        // - Nodes at changed_idx: expected_raw_count==1 but r0.raw_count==0, so f is false → vacuous.
        // - Frames at changed_idx: regions1.inv() provides all slot properties from regions1.slots.
        // - Other entries: slot_owners and slots unchanged at their index.
        assert(OwnerSubtree::implies(
            |v: EntryOwner<C>, p: TreePath<NR_ENTRIES>| f(v, p) && nsp(v, p), g)) by {
            assert forall |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                entry.inv() && f(entry, path) && nsp(entry, path)
                implies #[trigger] g(entry, path) by {
                if entry.meta_slot_paddr() is Some {
                    let eidx = frame_to_index(entry.meta_slot_paddr().unwrap());
                    if eidx != changed_idx {
                        assert(regions0.slot_owners[eidx] == regions1.slot_owners[eidx]);
                    } else if entry.is_frame() {
                        // Frame at changed_idx: use regions1.inv() to get slot properties.
                        assert(regions1.slots.contains_key(eidx));
                        // regions1.inv() => slots[eidx].addr() == meta_addr(eidx) etc.
                        // ref_count preserved from inner_perms equality.
                    }
                    // Node at changed_idx with !in_scope: expected_raw_count==1 != r0.raw_count==0 → f is false.
                }
            };
        };

        assert forall |i: int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS implies {
                self.continuations[i].map_children(g)
            }
        by {
            let cont = self.continuations[i];
            assert(cont.map_children(f));
            reveal(CursorContinuation::inv_children);
            assert forall |j: int| 0 <= j < NR_ENTRIES
                && #[trigger] cont.children[j] is Some implies
                cont.children[j].unwrap().tree_predicate_map(cont.path().push_tail(j as usize), nsp)
            by {
                cont.inv_children_unroll(j);
                PageTableOwner::tree_not_in_scope(cont.children[j].unwrap(), cont.path().push_tail(j as usize));
            };
            assert forall |j: int| 0 <= j < NR_ENTRIES
                && #[trigger] cont.children[j] is Some implies
                cont.children[j].unwrap().tree_predicate_map(cont.path().push_tail(j as usize), g)
            by {
                cont.inv_children_unroll(j);
                cont.children[j].unwrap().map_implies_and(cont.path().push_tail(j as usize), f, nsp, g);
            };
        };

        assert(self.path_metaregion_sound(regions1)) by {
            assert forall|i: int| #![trigger self.continuations[i]]
                self.level - 1 <= i < NR_LEVELS implies
                    self.continuations[i].entry_own.metaregion_sound(regions1) by {
                self.inv_continuation(i);
                let eo = self.continuations[i].entry_own;
                assert(eo.inv() && eo.is_node() && !eo.in_scope);
                if eo.meta_slot_paddr() is Some {
                    let eidx = frame_to_index(eo.meta_slot_paddr().unwrap());
                    if eidx != changed_idx {
                        assert(regions0.slot_owners[eidx] == regions1.slot_owners[eidx]);
                    }
                }
            };
        };
        if self.metaregion_correct(regions0) {
            // implies(e && nsp, h): path_if_in_pt unchanged.
            assert(OwnerSubtree::implies(
                |v: EntryOwner<C>, p: TreePath<NR_ENTRIES>| e(v, p) && nsp(v, p), h)) by {
                assert forall |entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                    entry.inv() && e(entry, path) && nsp(entry, path)
                    implies #[trigger] h(entry, path) by {
                    if entry.meta_slot_paddr() is Some {
                        let eidx = frame_to_index(entry.meta_slot_paddr().unwrap());
                        if eidx != changed_idx {}
                    }
                };
            };

            assert forall |i: int|
                #![trigger self.continuations[i]]
                self.level - 1 <= i < NR_LEVELS implies {
                    self.continuations[i].map_children(h)
                }
            by {
                let cont = self.continuations[i];
                assert(cont.map_children(e));
                reveal(CursorContinuation::inv_children);
                assert forall |j: int| 0 <= j < NR_ENTRIES
                    && #[trigger] cont.children[j] is Some implies
                    cont.children[j].unwrap().tree_predicate_map(cont.path().push_tail(j as usize), nsp)
                by {
                    cont.inv_children_unroll(j);
                    PageTableOwner::tree_not_in_scope(cont.children[j].unwrap(), cont.path().push_tail(j as usize));
                };
                assert forall |j: int| 0 <= j < NR_ENTRIES
                    && #[trigger] cont.children[j] is Some implies
                    cont.children[j].unwrap().tree_predicate_map(cont.path().push_tail(j as usize), h)
                by {
                    cont.inv_children_unroll(j);
                    cont.children[j].unwrap().map_implies_and(cont.path().push_tail(j as usize), e, nsp, h);
                };
            };
            // Path entries: path_if_in_pt unchanged at all indices.
            assert(self.path_metaregion_correct(regions1)) by {
                assert forall|i: int| #![trigger self.continuations[i]]
                    self.level - 1 <= i < NR_LEVELS implies
                        PageTableOwner::<C>::path_tracked_pred(regions1)(
                            self.continuations[i].entry_own,
                            self.continuations[i].path()) by {
                    self.inv_continuation(i);
                    let eo = self.continuations[i].entry_own;
                    if eo.meta_slot_paddr() is Some {
                        let eidx = frame_to_index(eo.meta_slot_paddr().unwrap());
                        if eidx != changed_idx {}
                    }
                };
            };
        }
    }

    /// Continuation entry_owns satisfy `metaregion_sound` and `path_tracked_pred`.
    ///
    /// ## Justification
    /// When the cursor descends into a subtree, each continuation's `entry_own`
    /// was previously checked by `tree_predicate_map` in the parent's child
    /// subtree.  After descent, `map_full_tree` only covers the siblings (the
    /// taken child is `None`), so the path entries' properties are no longer
    /// covered by `map_full_tree`.  However, `regions` is unchanged since
    /// descent, so the properties still hold.
    pub proof fn cont_entries_metaregion(
        self, regions: MetaRegionOwners,
    )
        requires
            self.inv(),
            self.metaregion_sound(regions),
        ensures
            forall|i: int| #![trigger self.continuations[i]]
                self.level - 1 <= i < NR_LEVELS ==>
                    self.continuations[i].entry_own.metaregion_sound(regions),
            self.metaregion_correct(regions) ==>
                forall|i: int| #![trigger self.continuations[i]]
                    self.level - 1 <= i < NR_LEVELS ==>
                        PageTableOwner::<C>::path_tracked_pred(regions)(
                            self.continuations[i].entry_own,
                            self.continuations[i].path()),
    {
        // Follows directly from path_metaregion_sound / path_metaregion_correct,
        // which are now part of metaregion_sound / metaregion_correct.
    }

    /// Cursor path nesting: for two continuations where `i > j >= self.level - 1`,
    /// `cont_i` is an ancestor of `cont_j` in the page table tree.
    /// The path from the root to `cont_j` passes through `cont_i.idx` at level `cont_i`,
    /// i.e., `cont_j.path()[cont_i.path().len()] == cont_i.idx`.
    ///
    /// This holds because the cursor was built by descending through `cont_i.idx` at each level.
    pub proof fn cursor_path_nesting(self, i: int, j: int)
        requires
            self.inv(),
            self.level - 1 <= j < i,
            i < NR_LEVELS,
        ensures
            self.continuations[j].path().len() as int > self.continuations[i].path().len() as int,
            self.continuations[j].path().index(self.continuations[i].path().len() as int)
                == self.continuations[i].idx,
    {
        if i == 3 && j == 2 {
            self.continuations[3].path().push_tail_property_index(self.continuations[3].idx as usize);
            self.continuations[3].path().push_tail_property_len(self.continuations[3].idx as usize);
        } else if i == 3 && j == 1 {
            let p3 = self.continuations[3].path();
            let p2 = self.continuations[2].path();
            let idx3 = self.continuations[3].idx as usize;
            let idx2 = self.continuations[2].idx as usize;
            p3.push_tail_property_index(idx3);
            p3.push_tail_property_len(idx3);
            p2.push_tail_property_index(idx2);
            p2.push_tail_property_len(idx2);
            assert(p3.len() < p2.len());
            assert(self.continuations[1].path() == p2.push_tail(idx2));
            assert(p2.push_tail(idx2).index(p3.len() as int) == p2.index(p3.len() as int));
        } else if i == 3 && j == 0 {
            let p3 = self.continuations[3].path();
            let p2 = self.continuations[2].path();
            let p1 = self.continuations[1].path();
            let idx3 = self.continuations[3].idx as usize;
            let idx2 = self.continuations[2].idx as usize;
            let idx1 = self.continuations[1].idx as usize;
            p3.push_tail_property_index(idx3);
            p3.push_tail_property_len(idx3);
            p2.push_tail_property_index(idx2);
            p2.push_tail_property_len(idx2);
            p1.push_tail_property_index(idx1);
            p1.push_tail_property_len(idx1);
            assert(p3.len() < p2.len());
            assert(p3.len() < p1.len());
            assert(p1.push_tail(idx1).index(p3.len() as int) == p1.index(p3.len() as int));
            assert(p2.push_tail(idx2).index(p3.len() as int) == p2.index(p3.len() as int));
        } else if i == 2 && j == 1 {
            self.continuations[2].path().push_tail_property_index(self.continuations[2].idx as usize);
            self.continuations[2].path().push_tail_property_len(self.continuations[2].idx as usize);
        } else if i == 2 && j == 0 {
            let p2 = self.continuations[2].path();
            let p1 = self.continuations[1].path();
            let idx2 = self.continuations[2].idx as usize;
            let idx1 = self.continuations[1].idx as usize;
            p2.push_tail_property_index(idx2);
            p2.push_tail_property_len(idx2);
            p1.push_tail_property_index(idx1);
            p1.push_tail_property_len(idx1);
            assert(p2.len() < p1.len());
            assert(self.continuations[0].path() == p1.push_tail(idx1));
            assert(p1.push_tail(idx1).index(p2.len() as int) == p1.index(p2.len() as int));
            assert(p1 == p2.push_tail(idx2));
            assert(p2.push_tail(idx2).index(p2.len() as int) == idx2);
        } else if i == 1 && j == 0 {
            self.continuations[1].path().push_tail_property_index(self.continuations[1].idx as usize);
            self.continuations[1].path().push_tail_property_len(self.continuations[1].idx as usize);
        }
    }

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
            *final(self) == old(self).set_va_spec(new_va);

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
            *final(self) == old(self).set_va_in_node_spec(new_va),
            final(self).inv(),;

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

    pub proof fn jump_above_locked_range_va_in_node(
        self,
        va: Vaddr,
        node_start: Vaddr,
    )
        requires
            self.inv(),
            self.level == self.guard_level,
            self.above_locked_range(),
            self.locked_range().start <= va < self.locked_range().end,
            node_start == nat_align_down(self.va.to_vaddr() as nat,
                page_size((self.level + 1) as PagingLevel) as nat) as usize,
        ensures
            node_start <= va,
            va < node_start + page_size((self.level + 1) as PagingLevel),
    {
        let gl = self.guard_level;
        let ps_gl = page_size_spec(gl as PagingLevel) as nat;
        let ps_gl1 = page_size_spec((gl + 1) as PagingLevel) as nat;
        let pv = self.prefix.to_vaddr() as nat;
        let cv = self.va.to_vaddr() as nat;
        lemma_page_size_ge_page_size(gl as PagingLevel);
        lemma_page_size_ge_page_size((gl + 1) as PagingLevel);
        lemma_nat_align_down_sound(pv, ps_gl);
        lemma_nat_align_up_sound(pv, ps_gl);
        lemma_nat_align_down_sound(cv, ps_gl1);

        lemma_page_size_divides(gl as PagingLevel, (gl + 1) as PagingLevel);
        self.prefix.align_down_concrete(gl as int);
        AbstractVaddr::from_vaddr_to_vaddr_roundtrip(nat_align_down(pv, ps_gl) as Vaddr);
        self.prefix.align_up_concrete(gl as int);
        AbstractVaddr::from_vaddr_to_vaddr_roundtrip(nat_align_up(pv, ps_gl) as Vaddr);
        self.prefix.align_diff(gl as int);

        if gl < NR_LEVELS {
            self.va.align_down_to_vaddr_eq_if_upper_indices_eq(self.prefix, (gl + 1) as int);
            self.va.align_down_concrete((gl + 1) as int);
            AbstractVaddr::from_vaddr_to_vaddr_roundtrip(nat_align_down(cv, ps_gl1) as Vaddr);
            self.prefix.align_down_concrete((gl + 1) as int);
            AbstractVaddr::from_vaddr_to_vaddr_roundtrip(nat_align_down(pv, ps_gl1) as Vaddr);
            lemma_page_size_ge_page_size(gl as PagingLevel);
            lemma_page_size_ge_page_size((gl + 1) as PagingLevel);
            lemma_nat_align_down_monotone(pv, ps_gl, ps_gl1);
            lemma_nat_align_down_within_block(pv, ps_gl, ps_gl1);
        } else {
            // guard_level == NR_LEVELS: ps_gl1 covers the entire VA space.
            crate::specs::arch::paging_consts::lemma_nr_subpage_per_huge_eq_nr_entries();
            vstd_extra::external::ilog2::lemma_usize_ilog2_to32();
            vstd::arithmetic::power2::lemma2_to64();
            vstd::arithmetic::power2::lemma2_to64_rest();
            assert(page_size_spec(5) == pow2(48nat) as usize) by {
                vstd::arithmetic::power2::lemma_pow2_adds(12nat, 36nat);
            };
            self.va.to_vaddr_bounded();
            self.va.to_vaddr_indices_gap_bound(0);
            assert(node_start == 0) by {
                if nat_align_down(cv, ps_gl1) != 0 {
                    vstd::arithmetic::div_mod::lemma_small_mod(
                        nat_align_down(cv, ps_gl1),
                        ps_gl1,
                    );
                }
            };
            self.prefix.to_vaddr_indices_gap_bound(0);
        }
    }

    pub proof fn jump_not_in_node_level_lt_guard_minus_one(
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
            level + 1 < self.guard_level,
    {
        if level + 1 == self.guard_level {
            let pv = self.prefix.to_vaddr() as nat;
            let ps = page_size(self.guard_level as PagingLevel) as nat;
            self.prefix.align_down_concrete(self.guard_level as int);
            self.prefix.align_up_concrete(self.guard_level as int);
            self.prefix.align_diff(self.guard_level as int);
            AbstractVaddr::from_vaddr_to_vaddr_roundtrip(nat_align_down(pv, ps) as Vaddr);
            AbstractVaddr::from_vaddr_to_vaddr_roundtrip(nat_align_up(pv, ps) as Vaddr);
        }
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
            mappings: self.view_mappings(),
            phantom: PhantomData,
        }
    }
}

impl<C: PageTableConfig> Inv for CursorView<C> {
    open spec fn inv(self) -> bool {
        &&& self.cur_va < MAX_USERSPACE_VADDR
        &&& self.mappings.finite()
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
