use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::set::{lemma_set_choose_len, lemma_set_contains_len};

use vstd_extra::arithmetic::{
    lemma_nat_align_down_monotone, lemma_nat_align_down_sound, lemma_nat_align_down_within_block,
    lemma_nat_align_up_sound,
};
use vstd_extra::drop_tracking::*;
use vstd_extra::ghost_tree::*;
use vstd_extra::ownership::*;
use vstd_extra::panic::may_panic;
use vstd_extra::seq_extra::{forall_seq, lemma_forall_seq_index};

use core::marker::PhantomData;
use core::ops::Range;

use crate::arch::mm::PagingConsts;
use crate::mm::frame::meta::{REF_COUNT_MAX, REF_COUNT_UNIQUE, REF_COUNT_UNUSED};
use crate::mm::page_prop::PageProperty;
use crate::mm::page_table::*;
use crate::mm::{
    MAX_USERSPACE_VADDR, Paddr, PagingConstsTrait, PagingLevel, Vaddr, nr_subpage_per_huge,
    page_size,
};
use crate::specs::arch::{MAX_PADDR, NR_ENTRIES, NR_LEVELS, PAGE_SIZE, has_safe_slot};
use crate::specs::mm::frame::mapping::frame_to_index;
use crate::specs::mm::page_table::cursor::page_size_lemmas::{
    lemma_page_size_divides, lemma_page_size_ge_page_size, lemma_page_size_spec_level1,
};
use crate::specs::mm::page_table::owners::*;
use crate::specs::mm::page_table::view::PageTableView;
use crate::specs::mm::page_table::{nat_align_down, nat_align_up};
use crate::specs::mm::{
    frame::{mapping::meta_addr, meta_region_owners::MetaRegionOwners},
    page_table::{AbstractVaddr, Guards, Mapping},
};
use crate::specs::task::InAtomicMode;

verus! {

pub tracked struct CursorContinuation<'rcu, C: PageTableConfig> {
    pub entry_own: EntryOwner<C>,
    pub idx: usize,
    pub tree_level: nat,
    pub children: Seq<Option<OwnerSubtree<C>>>,
    pub path: TreePath<NR_ENTRIES>,
    pub guard: PageTableGuard<'rcu, C>,
}

impl<'rcu, C: PageTableConfig> CursorContinuation<'rcu, C> {
    pub open spec fn path(self) -> TreePath<NR_ENTRIES> {
        self.entry_own.path
    }

    pub open spec fn child(self) -> OwnerSubtree<C> {
        self.children[self.idx as int]->0
    }

    pub open spec fn take_child(self) -> (OwnerSubtree<C>, Self) {
        let child = self.children[self.idx as int]->0;
        let cont = Self {
            children: self.children.remove(self.idx as int).insert(self.idx as int, None),
            ..self
        };
        (child, cont)
    }

    pub proof fn tracked_take_child(tracked &mut self) -> (tracked res: OwnerSubtree<C>)
        requires
            old(self).inv(),
            old(self).idx < old(self).children.len(),
            old(self).children[old(self).idx as int] is Some,
        ensures
            res == old(self).take_child().0,
            *final(self) == old(self).take_child().1,
            res.inv(),
    {
        self.inv_children_unroll(self.idx as int);
        let tracked child = self.children.tracked_remove(old(self).idx as int).tracked_unwrap();
        self.children.tracked_insert(old(self).idx as int, None);
        child
    }

    pub open spec fn put_child(self, child: OwnerSubtree<C>) -> Self {
        Self {
            children: self.children.remove(self.idx as int).insert(self.idx as int, Some(child)),
            ..self
        }
    }

    pub proof fn tracked_put_child(tracked &mut self, tracked child: OwnerSubtree<C>)
        requires
            old(self).idx < old(self).children.len(),
            old(self).children[old(self).idx as int] is None,
        ensures
            *final(self) == old(self).put_child(child),
    {
        let _ = self.children.tracked_remove(old(self).idx as int);
        self.children.tracked_insert(old(self).idx as int, Some(child));
    }

    pub proof fn take_put_child(self)
        requires
            self.idx < self.children.len(),
            self.children[self.idx as int] is Some,
        ensures
            self.take_child().1.put_child(self.take_child().0) == self,
    {
        let child = self.take_child().0;
        let cont = self.take_child().1;
        assert(cont.put_child(child).children == self.children);
    }

    pub open spec fn make_cont(self, idx: usize, guard: PageTableGuard<'rcu, C>) -> (Self, Self) {
        let child = Self {
            entry_own: self.children[self.idx as int]->0.value,
            tree_level: (self.tree_level + 1) as nat,
            idx: idx,
            children: self.children[self.idx as int]->0.children,
            path: self.path.push_tail(self.idx as usize),
            guard: guard,
        };
        let cont = Self { children: self.children.update(self.idx as int, None), ..self };
        (child, cont)
    }

    pub axiom fn tracked_make_cont(
        tracked &mut self,
        idx: usize,
        guard: PageTableGuard<'rcu, C>,
    ) -> (tracked res: Self)
        requires
            old(self).all_some(),
            old(self).idx < NR_ENTRIES,
            idx < NR_ENTRIES,
        ensures
            res == old(self).make_cont(idx, guard).0,
            *final(self) == old(self).make_cont(idx, guard).1,
    ;

    pub open spec fn restore(self, child: Self) -> (Self, PageTableGuard<'rcu, C>) {
        let child_node = OwnerSubtree {
            value: child.entry_own,
            level: child.tree_level,
            children: child.children,
        };
        (
            Self { children: self.children.update(self.idx as int, Some(child_node)), ..self },
            child.guard,
        )
    }

    pub axiom fn tracked_restore(tracked &mut self, tracked child: Self) -> (tracked guard:
        PageTableGuard<'rcu, C>)
        ensures
            *final(self) == old(self).restore(child).0,
            guard == old(self).restore(child).1,
    ;

    pub open spec fn new(
        owner_subtree: OwnerSubtree<C>,
        idx: usize,
        guard: PageTableGuard<'rcu, C>,
    ) -> Self {
        Self {
            entry_own: owner_subtree.value,
            idx: idx,
            tree_level: owner_subtree.level,
            children: owner_subtree.children,
            path: TreePath::new(Seq::empty()),
            guard: guard,
        }
    }

    pub axiom fn tracked_new(
        tracked owner_subtree: OwnerSubtree<C>,
        idx: usize,
        guard: PageTableGuard<'rcu, C>,
    ) -> (tracked res: Self)
        ensures
            res == Self::new(owner_subtree, idx, guard),
    ;

    pub open spec fn map_children(
        self,
        f: spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool,
    ) -> bool {
        forall|i: int|
            #![trigger(self.children[i])]
            0 <= i < self.children.len() ==> self.children[i] is Some
                ==> self.children[i]->0.tree_predicate_map(self.path().push_tail(i as usize), f)
    }

    // map_children_lift, map_children_lift_skip_idx, as_subtree_restore
    // have been moved to tree_lemmas.rs.
    pub open spec fn level(self) -> PagingLevel {
        self.entry_own.node().level
    }

    pub open spec fn inv_children(self) -> bool {
        self.children.all(|child: Option<OwnerSubtree<C>>| child is Some ==> child->0.inv())
    }

    pub proof fn inv_children_unroll(self, i: int)
        requires
            self.inv_children(),
            0 <= i < self.children.len(),
            self.children[i] is Some,
        ensures
            self.children[i]->0.inv(),
    {
        let pred = |child: Option<OwnerSubtree<C>>| child is Some ==> child.unwrap().inv();
        assert(pred(self.children[i]));
    }

    pub proof fn inv_children_unroll_all(self)
        requires
            self.inv_children(),
        ensures
            forall|i: int|
                #![auto]
                0 <= i < self.children.len() ==> self.children[i] is Some
                    ==> self.children[i]->0.inv(),
    {
        let pred = |child: Option<OwnerSubtree<C>>| child is Some ==> child.unwrap().inv();
        assert forall|i: int|
            0 <= i < self.children.len()
                && #[trigger] self.children[i] is Some implies self.children[i].unwrap().inv() by {
            self.inv_children_unroll(i)
        }
    }

    pub open spec fn inv_children_rel_pred(self) -> spec_fn(int, Option<OwnerSubtree<C>>) -> bool {
        |i: int, child: Option<OwnerSubtree<C>>|
            {
                child is Some ==> {
                    &&& child->0.value.parent_level == self.level()
                    &&& child->0.level == self.tree_level + 1
                    &&& child->0.value.path.len() == self.entry_own.node().tree_level + 1
                    &&& child->0.value.match_pte(
                        self.entry_own.node().children_perm.value()[i],
                        self.entry_own.node().level,
                    )
                    &&& child->0.value.path == self.path().push_tail(i as usize)
                }
            }
    }

    pub open spec fn inv_children_rel(self) -> bool {
        forall_seq(self.children, self.inv_children_rel_pred())
    }

    pub open spec fn pt_inv_children_pred() -> spec_fn(int, Option<OwnerSubtree<C>>) -> bool {
        |i: int, child: Option<OwnerSubtree<C>>| child is Some ==> PageTableOwner(child->0).pt_inv()
    }

    pub open spec fn pt_inv_children(self) -> bool {
        forall_seq(self.children, Self::pt_inv_children_pred())
    }

    pub proof fn pt_inv_children_unroll(self, i: int)
        requires
            self.pt_inv_children(),
            0 <= i < self.children.len(),
            self.children[i] is Some,
        ensures
            PageTableOwner(self.children[i]->0).pt_inv(),
    {
        lemma_forall_seq_index(self.children, Self::pt_inv_children_pred(), i);
    }

    pub proof fn inv_children_rel_unroll(self, i: int)
        requires
            self.inv_children_rel(),
            0 <= i < self.children.len(),
            self.children[i] is Some,
        ensures
            self.children[i]->0.value.parent_level == self.level(),
            self.children[i]->0.level == self.tree_level + 1,
            self.children[i]->0.value.path.len() == self.entry_own.node().tree_level + 1,
            self.children[i]->0.value.match_pte(
                self.entry_own.node().children_perm.value()[i],
                self.entry_own.node().level,
            ),
            self.children[i]->0.value.path == self.path().push_tail(i as usize),
    {
        lemma_forall_seq_index(self.children, self.inv_children_rel_pred(), i);
    }

    pub open spec fn inv(self) -> bool {
        &&& self.children.len() == NR_ENTRIES
        &&& 0 <= self.idx < NR_ENTRIES
        &&& self.inv_children()
        &&& self.inv_children_rel()
        &&& self.pt_inv_children()
        &&& self.entry_own.is_node()
        &&& self.entry_own.inv()
        &&& self.entry_own.node().relate_guard(self.guard)
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
        Self { idx: (self.idx + 1) as usize, ..self }
    }

    pub proof fn do_inc_index(tracked &mut self)
        requires
            old(self).idx + 1 < NR_ENTRIES,
        ensures
            *final(self) == old(self).inc_index(),
    {
        self.idx = (self.idx + 1) as usize;
    }

    pub open spec fn node_locked(self, guards: Guards<'rcu>) -> bool {
        guards.lock_held(self.guard.inner.inner@.ptr.addr())
    }

    pub open spec fn view_mappings(self) -> Set<Mapping> {
        self.children.map(
            |i, child: Option<OwnerSubtree<C>>|
                if child is Some {
                    PageTableOwner(child->0).view_rec(self.path().push_tail(i as usize))
                } else {
                    Set::empty()
                },
        ).to_set().flatten()
    }

    pub broadcast proof fn lemma_view_mappings_contains(self)
        ensures
            #![trigger self.view_mappings()]
            forall|m: Mapping| #[trigger]
                self.view_mappings().contains(m) ==> exists|i: int|
                    #![trigger self.children[i]]
                    0 <= i < self.children.len() && self.children[i] is Some && PageTableOwner(
                        self.children[i]->0,
                    ).view_rec(self.path().push_tail(i as usize)).contains(m),
    {
        broadcast use vstd::seq_lib::group_seq_properties;

        assert forall|m: Mapping| self.view_mappings().contains(m) implies exists|i: int|
            #![trigger self.children[i]]
            0 <= i < self.children.len() && self.children[i] is Some && PageTableOwner(
                self.children[i]->0,
            ).view_rec(self.path().push_tail(i as usize)).contains(m) by {
            let mapped = self.children.map(
                |i, child: Option<OwnerSubtree<C>>|
                    if child is Some {
                        PageTableOwner(child->0).view_rec(self.path().push_tail(i as usize))
                    } else {
                        Set::empty()
                    },
            );
            mapped.to_set().lemma_flatten_contains(m);
            let elem_s = choose|elem_s: Set<Mapping>| #[trigger]
                mapped.to_set().contains(elem_s) && elem_s.contains(m);
            mapped.to_set_ensures();
            assert(mapped.contains(elem_s));
            let i = mapped.lemma_contains_to_index(elem_s);
            assert(0 <= i < self.children.len());
            if self.children[i] is Some {
                assert(mapped[i] == PageTableOwner(self.children[i]->0).view_rec(
                    self.path().push_tail(i as usize),
                ));
            } else {
                assert(mapped[i] == Set::<Mapping>::empty());
                assert(false);
            }
        }
    }

    pub broadcast proof fn lemma_view_mappings_intro(self, m: Mapping, i: int)
        requires
            0 <= i < self.children.len(),
            self.children[i] is Some,
            #[trigger] PageTableOwner(self.children[i]->0).view_rec(
                self.path().push_tail(i as usize),
            ).contains(m),
        ensures
            self.view_mappings().contains(m),
    {
        broadcast use vstd::seq_lib::group_seq_properties;

        let mapped = self.children.map(
            |i, child: Option<OwnerSubtree<C>>|
                if child is Some {
                    PageTableOwner(child->0).view_rec(self.path().push_tail(i as usize))
                } else {
                    Set::empty()
                },
        );
        assert(mapped[i].contains(m));
        mapped.to_set_ensures();
        assert(mapped.to_set().contains(mapped[i]));
        mapped.to_set().lemma_flatten_contains(m);
    }

    pub open spec fn as_subtree(self) -> OwnerSubtree<C> {
        OwnerSubtree { value: self.entry_own, level: self.tree_level, children: self.children }
    }

    pub open spec fn as_page_table_owner(self) -> PageTableOwner<C> {
        PageTableOwner(self.as_subtree())
    }

    pub open spec fn view_mappings_take_child_spec(self) -> Set<Mapping> {
        PageTableOwner(self.children[self.idx as int]->0).view_rec(
            self.path().push_tail(self.idx as usize),
        )
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
        entry: &Entry<'_, 'rcu, C>,
        child_value: EntryOwner<C>,
        parent_owner: NodeOwner<C>,
        guard: PageTableGuard<'rcu, C>,
        entry_own: EntryOwner<C>,
        idx: usize,
    )
        requires
            entry.node_matching(child_value, parent_owner, guard),
            entry.idx == idx,
            entry_own.is_node(),
            entry_own.node() == parent_owner,
            child_value.path == entry_own.path.push_tail(idx),
            child_value.path.len() == parent_owner.tree_level + 1,
        ensures
            child_value.path.len() == parent_owner.tree_level + 1,
            child_value.match_pte(
                parent_owner.children_perm.value()[idx as int],
                parent_owner.level,
            ),
            child_value.path == entry_own.path.push_tail(idx),
            child_value.parent_level == parent_owner.level,
    {
    }

    /// After restoring `entry_own.node = Some(parent_owner)` and putting the child back
    /// at `idx`, the continuation invariant holds.
    ///
    /// Caller passes the pre-modification continuation `cont_old` and its
    /// parent_owner `parent_old` so we can recover the per-`j != idx`
    /// `inv_children_rel`/`pt_inv_children` facts from `cont_old.inv()`.
    /// Operations that take/restore (alloc_if_none, split_if_mapped_huge,
    /// protect, replace) all preserve the parent's other PTEs and the
    /// children at `j != idx`.
    pub proof fn continuation_inv_holds_after_child_restore(
        self,
        cont_old: Self,
        parent_old: NodeOwner<C>,
    )
        requires
    // Old continuation was inv with parent_old wired in

            cont_old.inv(),
            cont_old.entry_own.is_node(),
            cont_old.entry_own.node() == parent_old,
            // Frozen fields shared with cont_old
            self.children.len() == cont_old.children.len(),
            self.idx == cont_old.idx,
            self.tree_level == cont_old.tree_level,
            self.guard == cont_old.guard,
            self.path == cont_old.path,
            // entry_own changed only by the Node payload and otherwise keeps
            // the surrounding owner metadata.
            self.entry_own.is_absent() == cont_old.entry_own.is_absent(),
            self.entry_own.path == cont_old.entry_own.path,
            self.entry_own.parent_level == cont_old.entry_own.parent_level,
            // entry_own's new parent is well-formed and structurally matches the old
            self.entry_own.is_node(),
            self.entry_own.inv(),
            self.entry_own.node().relate_guard(self.guard),
            self.entry_own.node().level == parent_old.level,
            self.entry_own.node().tree_level == parent_old.tree_level,
            // Other PTEs preserved (operation only touched the entry at idx)
            forall|j: int|
                0 <= j < NR_ENTRIES && j != self.idx as int
                    ==> #[trigger] self.entry_own.node().children_perm.value()[j]
                    == parent_old.children_perm.value()[j],
            // Children at j != idx untouched
            forall|j: int|
                0 <= j < NR_ENTRIES && j != self.idx as int ==> #[trigger] self.children[j]
                    == cont_old.children[j],
            // Standard size/index facts (also implied by cont_old.inv()
            // + frozen fields, but stated directly to avoid extra unrolls).
            self.children.len() == NR_ENTRIES,
            0 <= self.idx < NR_ENTRIES,
            self.tree_level == INC_LEVELS - self.level() - 1,
            self.tree_level < INC_LEVELS - 1,
            self.path().len() == self.tree_level,
            // The new child at idx is well-formed
            self.children[self.idx as int] is Some,
            self.children[self.idx as int]->0.inv(),
            self.children[self.idx as int]->0.value.parent_level == self.level(),
            self.children[self.idx as int]->0.value.path == self.path().push_tail(
                self.idx as usize,
            ),
            self.children[self.idx as int]->0.level == self.tree_level + 1,
            self.children[self.idx as int]->0.value.path.len() == self.entry_own.node().tree_level
                + 1,
            self.children[self.idx as int]->0.value.match_pte(
                self.entry_own.node().children_perm.value()[self.idx as int],
                self.entry_own.node().level,
            ),
            // The new child satisfies the PT-specific tree invariant. This is
            // operation-specific (alloc_if_none/protect/split_if_mapped_huge/
            // replace each establish it differently) so it's lifted to a
            // precondition rather than discharged here.
            PageTableOwner(self.children[self.idx as int]->0).pt_inv(),
        ensures
            self.inv(),
    {
        let cont_idx = self.idx as int;
        let new_parent = self.entry_own.node();
        let new_child = self.children[cont_idx].unwrap();

        // (1) inv_children: every Some child is inv.
        assert(self.inv_children()) by {
            let pred = |child: Option<OwnerSubtree<C>>| child is Some ==> child.unwrap().inv();
            assert forall|i: int| 0 <= i < self.children.len() implies #[trigger] pred(
                self.children[i],
            ) by {
                if i != cont_idx {
                    if self.children[i] is Some {
                        assert(self.children[i] == cont_old.children[i]);
                        cont_old.inv_children_unroll(i);
                    }
                }
            };
            assert(self.children.all(pred));
        };

        // (2) inv_children_rel: each Some child satisfies the structural
        // predicate against entry_own.node = new_parent.
        assert(self.inv_children_rel()) by {
            let pred = self.inv_children_rel_pred();
            assert forall|i: int| 0 <= i < self.children.len() implies #[trigger] pred(
                i,
                self.children[i],
            ) by {
                if i != cont_idx {
                    if self.children[i] is Some {
                        cont_old.inv_children_rel_unroll(i);
                        assert(self.children[i] == cont_old.children[i]);
                    }
                }
            };
        };

        // (3) pt_inv_children: each Some child has PageTableOwner(child).pt_inv().
        // For j != idx, transferred from cont_old's pt_inv_children. For
        // j == idx, supplied by the caller as a precondition since `pt_inv`
        // is operation-specific.
        assert(self.pt_inv_children()) by {
            let pred = Self::pt_inv_children_pred();
            assert forall|i: int| 0 <= i < self.children.len() implies #[trigger] pred(
                i,
                self.children[i],
            ) by {
                if i == cont_idx {
                    assert(PageTableOwner(self.children[cont_idx].unwrap()).pt_inv());
                } else {
                    if self.children[i] is Some {
                        cont_old.pt_inv_children_unroll(i);
                        assert(self.children[i] == cont_old.children[i]);
                    }
                }
            };
        };
    }

    pub proof fn new_child(
        tracked &self,
        paddr: Paddr,
        prop: PageProperty,
        is_tracked: bool,
        tracked regions: &mut MetaRegionOwners,
    ) -> (tracked res: OwnerSubtree<C>)
        requires
            self.inv(),
            self.level() < NR_LEVELS,
            old(regions).slots.contains_key(frame_to_index(paddr)),
            paddr % PAGE_SIZE == 0,
            paddr < MAX_PADDR,
            paddr % page_size(self.level()) == 0,
            paddr + page_size(self.level()) <= MAX_PADDR,
            self.path().push_tail(self.idx as usize).inv(),
        ensures
            final(regions).slot_owners == old(regions).slot_owners,
            final(regions).slots == old(regions).slots,
            // Allocating a child doesn't touch the segment obligation ledger.
            res.value == EntryOwner::<C>::new_frame(
                paddr,
                self.path().push_tail(self.idx as usize),
                self.level(),
                prop,
                is_tracked,
            ),
            res.inv(),
            res.level == self.tree_level + 1,
            res == OwnerSubtree::new_val(res.value, res.level as nat),
    {
        let tracked mut owner = EntryOwner::<C>::tracked_new_frame(
            paddr,
            self.path().push_tail(self.idx as usize),
            self.level(),
            prop,
            is_tracked,
        );
        OwnerSubtree::new_val_tracked(owner, self.tree_level + 1)
    }

    pub broadcast group group_lemmas {
        CursorContinuation::lemma_view_mappings_contains,
        CursorContinuation::lemma_view_mappings_intro,
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
        &&& 1 <= self.guard_level
            <= NR_LEVELS
        // The top-level index of the cursor's VA must be within the page table config's
        // managed range. This ensures cursors for UserPtConfig and KernelPtConfig operate
        // on disjoint portions of the virtual address space.
        &&& C::TOP_LEVEL_INDEX_RANGE_spec().start <= self.va.index[NR_LEVELS
            - 1]
        // The top index may equal TOP_LEVEL_INDEX_RANGE.end as a "one-past-end"
        // sentinel meaning the cursor has been advanced past the very last in-range
        // top-level slot. In this state the cursor is `above_locked_range`.
        &&& self.va.index[NR_LEVELS - 1]
            <= C::TOP_LEVEL_INDEX_RANGE_spec().end
        // The cursor's VA is always at or above the start of the locked range.
        &&& self.in_locked_range()
            || self.above_locked_range()
        // The cursor is allowed to pop out of the guard range only when it reaches the end of the locked range.
        // This allows the user to reason solely about the current vaddr and not keep track of the cursor's level.
        &&& self.popped_too_high ==> self.level >= self.guard_level
        &&& !self.popped_too_high ==> self.level <= self.guard_level || self.above_locked_range()
        &&& self.continuations[self.level - 1].all_some()
        &&& forall|i: int|
            self.level <= i < NR_LEVELS ==> {
                (#[trigger] self.continuations[i]).all_but_index_some()
            }
            // Root-continuation top-level index stays within the config range, and
            //  (b) its top-level children OUTSIDE the config range are `borrowed`
            //      OR `absent` — they share another config's sub-tree (user PT's
            //      kernel half = borrowed) or are unmapped (kernel PT's user half =
            //      absent), and either way contribute NOTHING to `view_rec`.
            //      Preserved across cursor ops; makes both the user
            //      (`lemma_view_in_vaddr_range_user`) and kernel
            //      (`lemma_view_in_vaddr_range_kernel`) view bounds provable.
        &&& self.level <= NR_LEVELS - 1 ==> {
            &&& C::TOP_LEVEL_INDEX_RANGE_spec().start <= self.continuations[NR_LEVELS - 1].idx
            &&& self.continuations[NR_LEVELS - 1].idx < C::TOP_LEVEL_INDEX_RANGE_spec().end
        }
        &&& forall|j: int|
            #![trigger self.continuations[NR_LEVELS - 1].children[j]]
            0 <= j < NR_ENTRIES && !(C::TOP_LEVEL_INDEX_RANGE_spec().start <= j
                < C::TOP_LEVEL_INDEX_RANGE_spec().end) ==> self.continuations[NR_LEVELS
                - 1].children[j] is Some ==> (self.continuations[NR_LEVELS
                - 1].children[j].unwrap().value.is_borrowed() || self.continuations[NR_LEVELS
                - 1].children[j].unwrap().value.is_absent())
        &&& self.prefix.inv()
        &&& self.prefix.offset == 0
        &&& forall|i: int|
            i < self.guard_level ==> self.prefix.index[i]
                == 0
            // The prefix's top-level index is within the configured page-table range.
            // This is established at construction (when prefix == va, which itself starts
            // strictly in-range) and preserved by all cursor operations (none touch prefix).
        &&& self.prefix.index[NR_LEVELS - 1]
            < C::TOP_LEVEL_INDEX_RANGE_spec().end
        // Top-of-address-space sentinel reservation: none of our `PtConfig`s actually use
        // the very last index. The first half of the address space
        &&& self.prefix.index[NR_LEVELS - 1] + 1
            < NR_ENTRIES
        // Locked range stays within the config's managed VA space. Established at
        // cursor construction (barrier_va == *va with is_valid_range_spec(va)) and
        // preserved by all cursor operations since they don't modify prefix/guard_level.
        &&& self.locked_range().end as int <= crate::mm::page_table::vaddr_range_bounds_spec::<
            C,
        >().1 as int
            + 1
        // Per-config tightening: e.g. `KernelPtConfig` overrides this to
        // `FRAME_METADATA_BASE_VADDR`, which the kvirt allocator enforces and
        // is what `move_forward` uses to prove `prefix.idx[NR_LEVELS-1] + 1
        // < NR_ENTRIES` at the wrap-pop boundary. Default is trivial.
        &&& self.locked_range().end as int
            <= C::LOCKED_END_BOUND_spec()
        // The cursor stays within the same canonical half of the address
        // space as its prefix — so `leading_bits` agrees throughout traversal.
        &&& self.va.leading_bits
            == self.prefix.leading_bits
        // Established at construction (new initializes both va and
        // prefix with LEADING_BITS_spec()) and preserved by cursor ops.
        &&& self.prefix.leading_bits
            == C::LEADING_BITS_spec() as int
        // The cursor's VA shares upper indices with the prefix when the
        // cursor hasn't popped above guard_level AND is either in_locked_range
        // OR strictly below guard_level. The wrap branch of
        // `move_forward_owner_spec` (level == guard_level && idx+1 ==
        // NR_ENTRIES) advances `va` past the prefix's chunk; that state has
        // `level == guard_level` and `above_locked_range`, and is excluded
        // from this clause.
        &&& !self.popped_too_high && (self.in_locked_range() || self.level < self.guard_level)
            ==> forall|i: int|
            self.guard_level <= i < NR_LEVELS ==> self.va.index[i] == self.prefix.index[i]
        &&& !self.popped_too_high && self.guard_level >= 1 && self.level < self.guard_level
            ==> self.va.index[self.guard_level - 1] == self.prefix.index[self.guard_level - 1]
        &&& self.level <= 4 ==> {
            &&& self.continuations.contains_key(3)
            &&& self.continuations[3].inv()
            &&& self.continuations[3].level()
                == 4
            // Obviously there is no level 5 pt, but that would be the level of the parent of the root pt.
            &&& self.continuations[3].entry_own.parent_level
                == 5
            // `va.index[i] == cont[i].idx` is meaningful only while the
            // cursor is in_locked_range. Above-locked-range cursors keep
            // their continuations as-is (stale w.r.t. the wrapped va) and
            // never read from them.
            &&& self.in_locked_range() ==> self.va.index[3] == self.continuations[3].idx
        }
        &&& self.level <= 3 ==> {
            &&& self.continuations.contains_key(2)
            &&& self.continuations[2].inv()
            &&& self.continuations[2].level() == 3
            &&& self.continuations[2].entry_own.parent_level == 4
            &&& self.in_locked_range() ==> self.va.index[2] == self.continuations[2].idx
            &&& self.continuations[2].guard.inner.inner@.ptr.addr()
                != self.continuations[3].guard.inner.inner@.ptr.addr()
            // Path consistency: child path = parent path pushed with parent's index
            &&& self.continuations[2].path() == self.continuations[3].path().push_tail(
                self.continuations[3].idx as usize,
            )
            // PTE consistency
            &&& self.continuations[2].entry_own.path.len()
                == self.continuations[3].entry_own.node().tree_level + 1
            &&& self.continuations[2].entry_own.match_pte(
                self.continuations[3].entry_own.node().children_perm.value()[self.continuations[3].idx as int],
                self.continuations[3].entry_own.node().level,
            )
            &&& self.continuations[2].entry_own.parent_level
                == self.continuations[3].entry_own.node().level
        }
        &&& self.level <= 2 ==> {
            &&& self.continuations.contains_key(1)
            &&& self.continuations[1].inv()
            &&& self.continuations[1].level() == 2
            &&& self.continuations[1].entry_own.parent_level == 3
            &&& self.in_locked_range() ==> self.va.index[1] == self.continuations[1].idx
            &&& self.continuations[1].guard.inner.inner@.ptr.addr()
                != self.continuations[2].guard.inner.inner@.ptr.addr()
            &&& self.continuations[1].guard.inner.inner@.ptr.addr()
                != self.continuations[3].guard.inner.inner@.ptr.addr()
            // Path consistency: child path = parent path pushed with parent's index
            &&& self.continuations[1].path() == self.continuations[2].path().push_tail(
                self.continuations[2].idx as usize,
            )
            // PTE consistency
            &&& self.continuations[1].entry_own.path.len()
                == self.continuations[2].entry_own.node().tree_level + 1
            &&& self.continuations[1].entry_own.match_pte(
                self.continuations[2].entry_own.node().children_perm.value()[self.continuations[2].idx as int],
                self.continuations[2].entry_own.node().level,
            )
            &&& self.continuations[1].entry_own.parent_level
                == self.continuations[2].entry_own.node().level
        }
        &&& self.level == 1 ==> {
            &&& self.continuations.contains_key(0)
            &&& self.continuations[0].inv()
            &&& self.continuations[0].level() == 1
            &&& self.continuations[0].entry_own.parent_level == 2
            &&& self.in_locked_range() ==> self.va.index[0] == self.continuations[0].idx
            &&& self.continuations[0].guard.inner.inner@.ptr.addr()
                != self.continuations[1].guard.inner.inner@.ptr.addr()
            &&& self.continuations[0].guard.inner.inner@.ptr.addr()
                != self.continuations[2].guard.inner.inner@.ptr.addr()
            &&& self.continuations[0].guard.inner.inner@.ptr.addr()
                != self.continuations[3].guard.inner.inner@.ptr.addr()
            // Path consistency: child path = parent path pushed with parent's index
            &&& self.continuations[0].path() == self.continuations[1].path().push_tail(
                self.continuations[1].idx as usize,
            )
            // PTE consistency
            &&& self.continuations[0].entry_own.path.len()
                == self.continuations[1].entry_own.node().tree_level + 1
            &&& self.continuations[0].entry_own.match_pte(
                self.continuations[1].entry_own.node().children_perm.value()[self.continuations[1].idx as int],
                self.continuations[1].entry_own.node().level,
            )
            &&& self.continuations[0].entry_own.parent_level
                == self.continuations[1].entry_own.node().level
        }
    }
}

impl<'rcu, C: PageTableConfig> CursorOwner<'rcu, C> {
    pub open spec fn node_unlocked(guards: Guards<'rcu>) -> (spec_fn(
        EntryOwner<C>,
        TreePath<NR_ENTRIES>,
    ) -> bool) {
        |owner: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
            owner.is_node() ==> guards.unlocked(owner.node().meta_addr_self())
    }

    pub open spec fn node_unlocked_except(guards: Guards<'rcu>, addr: usize) -> (spec_fn(
        EntryOwner<C>,
        TreePath<NR_ENTRIES>,
    ) -> bool) {
        |owner: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
            owner.is_node() ==> owner.node().meta_addr_self() != addr ==> guards.unlocked(
                owner.node().meta_addr_self(),
            )
    }

    pub open spec fn map_full_tree(
        self,
        f: spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool,
    ) -> bool {
        forall|i: int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS ==> { self.continuations[i].map_children(f) }
    }

    pub open spec fn map_only_children(
        self,
        f: spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool,
    ) -> bool {
        forall|i: int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS ==> self.continuations[i].map_children(f)
    }

    pub open spec fn children_not_locked(self, guards: Guards<'rcu>) -> bool {
        self.map_only_children(Self::node_unlocked(guards))
    }

    pub open spec fn only_current_locked(self, guards: Guards<'rcu>) -> bool {
        self.map_only_children(
            Self::node_unlocked_except(guards, self.cur_entry_owner().node().meta_addr_self()),
        )
    }

    pub proof fn never_drop_restores_children_not_locked(
        self,
        guard: PageTableGuard<'rcu, C>,
        guards0: Guards<'rcu>,
        guards1: Guards<'rcu>,
        obl_key: usize,
    )
        requires
            self.inv(),
            self.only_current_locked(guards0),
            <PageTableGuard<'rcu, C> as TrackDrop>::constructor_requires(guard, guards0),
            <PageTableGuard<'rcu, C> as TrackDrop>::constructor_ensures(
                guard,
                guards0,
                guards1,
                obl_key,
            ),
            // The dropped guard is for the current entry's node (from pop_level).
            self.cur_entry_owner().is_node(),
            guard.inner.inner@.ptr.addr() == self.cur_entry_owner().node().meta_addr_self(),
        ensures
            self.children_not_locked(guards1),
    {
        let current_addr = self.cur_entry_owner().node().meta_addr_self();
        let f = Self::node_unlocked_except(guards0, current_addr);
        let g = Self::node_unlocked(guards1);
        assert(OwnerSubtree::implies(f, g));
        self.map_children_implies(f, g);
    }

    /// After dropping the guard for the popped level, `nodes_locked` is preserved
    /// for the new (higher-level) owner, because the dropped guard's address is not
    /// among those checked by `nodes_locked` (which covers levels >= self.level - 1).
    pub axiom fn never_drop_restores_nodes_locked(
        self,
        guard: PageTableGuard<'rcu, C>,
        guards0: Guards<'rcu>,
        guards1: Guards<'rcu>,
        obl_key: usize,
    )
        requires
            self.inv(),
            self.nodes_locked(guards0),
            <PageTableGuard<'rcu, C> as TrackDrop>::constructor_requires(guard, guards0),
            <PageTableGuard<'rcu, C> as TrackDrop>::constructor_ensures(
                guard,
                guards0,
                guards1,
                obl_key,
            ),
            forall|i: int|
                #![trigger self.continuations[i]]
                self.level - 1 <= i < NR_LEVELS
                    ==> self.continuations[i].guard.inner.inner@.ptr.addr()
                    != guard.inner.inner@.ptr.addr(),
        ensures
            self.nodes_locked(guards1),
    ;

    /// After a `protect` operation that only modifies `frame.prop` of the current entry,
    /// `CursorOwner::inv()` and `metaregion_sound` are preserved.
    ///
    /// Safety: `protect` changes only `frame.prop` and updates `parent.children_perm` to match.
    /// `EntryOwner::inv()` is preserved (from protect postcondition).
    /// `metaregion_sound` is preserved because it doesn't use `frame.prop`.
    /// `rel_children` holds via `match_pte` (from protect's `wf`/`node_matching` postconditions).
    ///
    /// The axiom requires only the semantic properties of the modified entry that are
    /// checked by `inv` and `metaregion_sound`; the structural identity of other continuations
    /// is trusted to hold from the tracked restore operations in the caller.
    // protect_preserves_cursor_inv_metaregion moved to cursor_fn_lemmas.rs.
    // map_children_implies moved to tree_lemmas.rs.
    pub open spec fn nodes_locked(self, guards: Guards<'rcu>) -> bool {
        // Only the subtree rooted at `guard_level` and its descendants down to
        // `level` are actually locked (see `locking.rs`). The ghost
        // `continuations` chain extends above `guard_level` to the root, but
        // those ancestor nodes are NOT lock-held, so the upper bound is
        // `guard_level`, not `NR_LEVELS`.
        forall|i: int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i < self.guard_level ==> { self.continuations[i].node_locked(guards) }
    }

    pub open spec fn index(self) -> usize {
        self.continuations[self.level - 1].idx
    }

    pub open spec fn inc_index(self) -> Self {
        Self {
            continuations: self.continuations.insert(
                self.level - 1,
                self.continuations[self.level - 1].inc_index(),
            ),
            va: AbstractVaddr {
                index: self.va.index.insert(
                    self.level - 1,
                    self.continuations[self.level - 1].inc_index().idx as int,
                ),
                ..self.va
            },
            popped_too_high: false,
            ..self
        }
    }

    #[verifier::spinoff_prover]
    pub proof fn do_inc_index(tracked &mut self)
        requires
            old(self).inv(),
            old(self).level <= old(self).guard_level,
            old(self).in_locked_range(),
            old(self).continuations[old(self).level - 1].idx + 1 < NR_ENTRIES,
            old(self).level == NR_LEVELS ==> (old(self).continuations[old(self).level - 1].idx + 1)
                <= C::TOP_LEVEL_INDEX_RANGE_spec().end,
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
        assert(self.va.index.dom() == Set::<int>::range(0, NR_LEVELS as int));

        old(self).va.index_increment_adds_page_size(old(self).level as int);
        lemma_page_size_ge_page_size(old(self).level as PagingLevel);

        if self.level >= self.guard_level {
            if !old(self).above_locked_range() {
                Self::inc_at_guard_level_above_locked_range(
                    old(self).va,
                    old(self).prefix,
                    old(self).guard_level,
                    old(self).level,
                    self.va.to_vaddr(),
                );
            }
        }
        if old(self).popped_too_high {
            old(self).in_locked_range_prefix_match();
        }
        assert(self.va.index[self.level as int - 1] == self.continuations[self.level as int
            - 1].idx);
        assert(self.prefix == old(self).prefix);
        assert(self.prefix.index[NR_LEVELS - 1] < C::TOP_LEVEL_INDEX_RANGE_spec().end);
        // inc_index doesn't change children, so pt_inv_children transfers.
        assert(cont.children == old(self).continuations[self.level - 1].children);
        assert(cont.pt_inv_children());
        assert(self.va.inv());
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

    pub open spec fn view_mappings(self) -> Set<Mapping> {
        self.continuations.filter_keys(|k| self.level - 1 <= k < NR_LEVELS).map_values(
            |cont: CursorContinuation<'rcu, C>| cont.view_mappings(),
        ).values().flatten()
    }

    pub broadcast proof fn lemma_view_mappings_contains(self)
        requires
            1 <= self.level <= NR_LEVELS,
        ensures
            #![trigger self.view_mappings()]
            forall|m: Mapping| #[trigger]
                self.view_mappings().contains(m) ==> exists|i: int|
                    #![trigger self.continuations[i]]
                    self.level - 1 <= i < NR_LEVELS
                        && self.continuations[i].view_mappings().contains(m),
    {
        broadcast use vstd::map_lib::group_map_properties;

        assert forall|m: Mapping| #[trigger] self.view_mappings().contains(m) implies exists|i: int|

            #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS && self.continuations[i].view_mappings().contains(
                m,
            ) by {
            let filtered = self.continuations.filter_keys(|k| self.level - 1 <= k < NR_LEVELS);
            let mapped = filtered.map_values(
                |cont: CursorContinuation<'rcu, C>| cont.view_mappings(),
            );
            let values = mapped.values();
            values.lemma_flatten_contains(m);
            let elem_s = choose|elem_s: Set<Mapping>| #[trigger]
                values.contains(elem_s) && elem_s.contains(m);
            assert(exists|i: int| #[trigger] mapped.dom().contains(i) && mapped[i] == elem_s);
            let i = choose|i: int| #[trigger] mapped.dom().contains(i) && mapped[i] == elem_s;
            assert(filtered.dom().contains(i));
            assert(self.level - 1 <= i < NR_LEVELS);
            assert(filtered[i] == self.continuations[i]);
            assert(mapped[i] == self.continuations[i].view_mappings());
        }
    }

    pub broadcast proof fn lemma_view_mappings_intro(self, m: Mapping, i: int)
        requires
            1 <= self.level <= NR_LEVELS,
            self.level - 1 <= i < NR_LEVELS,
            self.continuations.contains_key(i),
            #[trigger] self.continuations[i].view_mappings().contains(m),
        ensures
            self.view_mappings().contains(m),
    {
        broadcast use vstd::map_lib::group_map_properties;

        let filtered = self.continuations.filter_keys(|k| self.level - 1 <= k < NR_LEVELS);
        let mapped = filtered.map_values(|cont: CursorContinuation<'rcu, C>| cont.view_mappings());
        let values = mapped.values();
        assert(filtered.dom().contains(i));
        assert(filtered[i] == self.continuations[i]);
        assert(mapped.dom().contains(i));
        assert(mapped[i] == self.continuations[i].view_mappings());
        assert(values.contains(mapped[i]));
        values.lemma_flatten_contains(m);
    }

    pub open spec fn as_page_table_owner(self) -> PageTableOwner<C> {
        if self.level == 1 {
            let l1 = self.continuations[0];
            let l2 = self.continuations[1].restore(l1).0;
            let l3 = self.continuations[2].restore(l2).0;
            let l4 = self.continuations[3].restore(l3).0;
            l4.as_page_table_owner()
        } else if self.level == 2 {
            let l2 = self.continuations[1];
            let l3 = self.continuations[2].restore(l2).0;
            let l4 = self.continuations[3].restore(l3).0;
            l4.as_page_table_owner()
        } else if self.level == 3 {
            let l3 = self.continuations[2];
            let l4 = self.continuations[3].restore(l3).0;
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
        self.continuations[self.level - 1].children[self.index() as int]->0
    }

    /// Axiom: the item reconstructed from the current frame's physical address satisfies
    /// `clone_requires`.
    ///
    /// Safety: When `metaregion_sound` holds for a frame entry, the item reconstructed via
    /// `item_from_raw_spec(pa, ...)` is the original frame item.  The frame's slot permission
    /// (owned by the cursor) has the correct address, is initialised, and its ref count is in the
    /// valid clonable range (> 0, < REF_COUNT_MAX), so `clone_requires` is satisfied.
    ///
    /// This is a *trait-level* axiom: `C::Item::clone_requires` is fully generic in the
    /// `PageTableConfig` trait, so the postcondition cannot be discharged without knowing
    /// the concrete item type.  It holds for every `PageTableConfig` used in `ostd` because
    /// `item_from_raw_spec` always returns a freshly-constructed `Frame<M>` handle whose
    /// `Frame::<M>::clone_requires` unfolds to slot-address equality, initialisation, and a
    /// bounded ref-count — all delivered by `metaregion_sound` for frame entries.
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
            regions.inv(),
            self.metaregion_sound(regions),
            self.cur_entry_owner().is_frame(),
            pa == self.cur_entry_owner().frame().mapped_pa,
            C::item_from_raw_spec(pa, level, prop) == item,
            has_safe_slot(pa),
            // The recorded entry trackedness matches the item being cloned.
            C::tracked(item) == self.cur_entry_owner().frame().is_tracked,
            // Saturation aborts (Arc-style) via `inc_ref_count`'s diverging panic.
            C::tracked(item) ==> (regions.slot_owners[frame_to_index(
                pa,
            )].inner_perms.ref_count.value() < REF_COUNT_MAX || may_panic()),
        ensures
            item.clone_requires(regions),
    {
        broadcast use crate::specs::mm::frame::meta_owners::axiom_mmio_usage_iff_mmio_paddr;
        // Extract the frame-slot facts from metaregion_sound via path_metaregion_sound.

        assert(self.path_metaregion_sound(regions));
        assert(self.cur_entry_owner().metaregion_sound(regions));
        let entry = self.cur_entry_owner();
        let idx = frame_to_index(pa);
        // Bridge `C::tracked(item)` to `usage != MMIO`: the entry's `is_tracked`
        // is connected to its paddr's MMIO-ness by `axiom_frame_is_tracked_iff_not_mmio`,
        // and `usage == MMIO` to the paddr by `axiom_mmio_usage_iff_mmio_paddr`.
        EntryOwner::<C>::axiom_frame_is_tracked_iff_not_mmio(entry);
        assert(regions.slot_owners[idx].slot_vaddr == crate::specs::mm::frame::mapping::meta_addr(
            idx,
        ));
        if C::tracked(item) {
            assert(!crate::specs::mm::frame::meta_owners::is_mmio_paddr(pa));
            assert(regions.slot_owners[idx].usage !is MMIO);
            assert(regions.slot_owners[idx].inner_perms.ref_count.value() > 0);
            assert(regions.slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED);
        }
        // Now all preconditions of `C::clone_requires_concrete` are in scope.

        C::clone_requires_concrete(item, pa, level, prop, regions);
    }

    /// Incrementing the ref count of the current frame preserves `regions.inv()` and
    /// `self.metaregion_sound(new_regions)`.
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
            idx == frame_to_index(self.cur_entry_owner().frame().mapped_pa),
            old_regions.slot_owners.contains_key(idx),
            new_regions.slot_owners.contains_key(idx),
            // rc at idx is incremented by 1
            new_regions.slot_owners[idx].inner_perms.ref_count.value()
                == old_regions.slot_owners[idx].inner_perms.ref_count.value() + 1,
            // All other inner_perms fields at idx are identical (same tracked object)
            new_regions.slot_owners[idx].inner_perms.ref_count.id()
                == old_regions.slot_owners[idx].inner_perms.ref_count.id(),
            new_regions.slot_owners[idx].inner_perms.storage
                == old_regions.slot_owners[idx].inner_perms.storage,
            new_regions.slot_owners[idx].inner_perms.vtable_ptr
                == old_regions.slot_owners[idx].inner_perms.vtable_ptr,
            new_regions.slot_owners[idx].inner_perms.in_list
                == old_regions.slot_owners[idx].inner_perms.in_list,
            // Other MetaSlotOwner fields at idx unchanged
            new_regions.slot_owners[idx].paths_in_pt == old_regions.slot_owners[idx].paths_in_pt,
            new_regions.slot_owners[idx].slot_vaddr == old_regions.slot_owners[idx].slot_vaddr,
            new_regions.slot_owners[idx].usage == old_regions.slot_owners[idx].usage,
            // All other slot_owners unchanged
            new_regions.slot_owners.dom() == old_regions.slot_owners.dom(),
            forall|i: usize|
                #![trigger new_regions.slot_owners[i]]
                i != idx && old_regions.slot_owners.contains_key(i) ==> new_regions.slot_owners[i]
                    == old_regions.slot_owners[i],
            // slots map unchanged
            new_regions.slots == old_regions.slots,
            // obligation ledger unchanged (clone bumps a ref count only)
            // rc overflow guard: old rc is a normal shared count; the bumped rc fits
            // in the valid `[1, REF_COUNT_MAX]` range. The `<=` form (vs strict `<`)
            // matches what callers actually have: post-`clone_item`, the new rc is
            // bounded by the slot's `inv()` (which permits `rc == REF_COUNT_MAX`).
            0 < old_regions.slot_owners[idx].inner_perms.ref_count.value(),
            old_regions.slot_owners[idx].inner_perms.ref_count.value() + 1 <= REF_COUNT_MAX,
        ensures
            new_regions.inv(),
            self.metaregion_sound(new_regions),
    {
        self.cont_entries_metaregion(old_regions);
        assert(new_regions.slot_owners[idx].inv());
        assert(new_regions.inv()) by {
            assert forall|i: usize| #[trigger] new_regions.slots.contains_key(i) implies {
                &&& new_regions.slot_owners.contains_key(i)
                &&& new_regions.slot_owners[i].inv()
                &&& new_regions.slots[i].is_init()
                &&& new_regions.slots[i].value().wf(new_regions.slot_owners[i])
                &&& new_regions.slot_owners[i].slot_vaddr == new_regions.slots[i].addr()
            } by {
                assert(old_regions.slots.contains_key(i));
            };
            assert forall|i: usize| #[trigger]
                new_regions.slot_owners.contains_key(
                    i,
                ) implies new_regions.slot_owners[i].inv() by {};
        };
        self.metaregion_slot_owners_rc_increment(old_regions, new_regions, idx);
    }

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
            self.in_locked_range(),
            level == self.level,
            new_subtree.inv(),
            new_subtree.value.is_frame(),
            new_subtree.value.path == self.continuations[self.level as int - 1].path().push_tail(
                self.continuations[self.level as int - 1].idx as usize,
            ),
            new_subtree.value.frame().mapped_pa == pa,
            new_subtree.value.frame().prop == prop,
        ensures
            PageTableOwner(new_subtree)@.mappings
                == set![Mapping {
                va_range: self@.cur_slot_range(page_size(level)),
                pa_range: pa..(pa + page_size(level)) as usize,
                page_size: page_size(level),
                property: prop,
            }],
    {
        let path = new_subtree.value.path;
        let ps = page_size(level);
        let cont = self.continuations[self.level as int - 1];

        cont.path().push_tail_property_len(cont.idx as usize);

        // Bridge `nat_align_down(cur_va, ps) == vaddr_of::<C>(path) as Vaddr`:
        //   to_path_vaddr_concrete: vaddr(path) + va.leading_bits * 2^48 == nat_align_down(cur_va, ps)
        //   lemma_vaddr_of_eq_int : vaddr_of::<C>(path) == vaddr(path) + LEADING_BITS_spec * 2^48
        //   cursor inv            : va.leading_bits == LEADING_BITS_spec
        self.cur_va_in_subtree_range();
        assert(vaddr_of::<C>(path) == nat_align_down(self@.cur_va as nat, ps as nat) as Vaddr) by {
            self.va.to_path_vaddr_concrete(self.level as int - 1);
            crate::specs::mm::page_table::owners::lemma_vaddr_of_eq_int::<C>(path);
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
                    self.continuations[3].path().push_tail_property_index(
                        self.continuations[3].idx as usize,
                    );
                } else if self.level == 2 {
                    cont.path().push_tail_property_index(cont.idx as usize);
                    self.continuations[2].path().push_tail_property_index(
                        self.continuations[2].idx as usize,
                    );
                    self.continuations[3].path().push_tail_property_index(
                        self.continuations[3].idx as usize,
                    );
                } else {
                    cont.path().push_tail_property_index(cont.idx as usize);
                    self.continuations[1].path().push_tail_property_index(
                        self.continuations[1].idx as usize,
                    );
                    self.continuations[2].path().push_tail_property_index(
                        self.continuations[2].idx as usize,
                    );
                    self.continuations[3].path().push_tail_property_index(
                        self.continuations[3].idx as usize,
                    );
                }
            };
            AbstractVaddr::rec_vaddr_eq_if_indices_eq(path, va_path, 0);
        };
        // Show the singleton equality. view_rec at a frame produces a
        // singleton with va_range built from vaddr_of(path). cur_slot_range
        // produces start..start+ps with start = nat_align_down(cur_va, ps).
        // The bridge above identifies the two starts.
        let target = Mapping {
            va_range: self@.cur_slot_range(page_size(level)),
            pa_range: pa..(pa + page_size(level)) as usize,
            page_size: page_size(level),
            property: prop,
        };
        let from_view = Mapping {
            va_range: Range {
                start: vaddr_of::<C>(path) as int,
                end: vaddr_of::<C>(path) as int + ps as int,
            },
            pa_range: pa..(pa + ps) as usize,
            page_size: ps,
            property: prop,
        };
        // The bridge gave `vaddr_of::<C>(path) == nat_align_down(...) as Vaddr`
        // (both usize). Cast both to int to compare.
        let nad = nat_align_down(self@.cur_va as nat, ps as nat);
        assert(nad <= self@.cur_va as nat) by {
            vstd_extra::arithmetic::lemma_nat_align_down_sound(self@.cur_va as nat, ps as nat);
        };
        assert(target.va_range.start == nad as int);
        assert(target == from_view);
        assert(PageTableOwner(new_subtree).view_rec(path) == set![from_view]);
        assert(PageTableOwner(new_subtree)@.mappings == set![target]);
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
        old_va: AbstractVaddr,
        prefix: AbstractVaddr,
        guard_level: u8,
        level: u8,
        new_va_val: Vaddr,
    )
        requires
            old_va.inv(),
            prefix.inv(),
            1 <= guard_level <= NR_LEVELS,
            level == guard_level,
            new_va_val == old_va.to_vaddr() + page_size(level as PagingLevel),
            prefix.align_down(guard_level as int).to_vaddr() <= old_va.to_vaddr(),
            old_va.to_vaddr() < prefix.align_up(guard_level as int).to_vaddr(),
            // Overflow bound needed for `aligned_align_up_advances` on align_down(gl).
            prefix.align_down(guard_level as int).to_vaddr() + page_size(guard_level as PagingLevel)
                <= usize::MAX,
        ensures
            new_va_val >= prefix.align_up(guard_level as int).to_vaddr(),
    {
        let ps_gl = page_size(guard_level as PagingLevel);
        lemma_page_size_ge_page_size(guard_level as PagingLevel);
        let aligned = prefix.align_down(guard_level as int);
        prefix.align_down_concrete(guard_level as int);
        prefix.align_down_shape(guard_level as int);

        // `aligned = prefix.align_down(gl)` is ps_gl-aligned (align_down_shape gives
        // offset == 0, indices [0, gl-1) all 0 — note index[gl-1] is preserved from prefix).
        // Wait: align_down_shape only gives indices [0, gl-2) == 0 (i.e., 0..level-1 in
        // the 0-indexed array). For ps_gl-alignment we need offset = 0 AND index[0..gl-2] = 0.
        // align_down_shape gives both. So aligned is ps_gl-aligned.
        assert(aligned.to_vaddr() as nat % ps_gl as nat == 0) by {
            vstd_extra::arithmetic::lemma_nat_align_down_sound(
                prefix.to_vaddr() as nat,
                ps_gl as nat,
            );
            prefix.to_vaddr_bounded();
            aligned.to_vaddr_bounded();
            aligned.reflect_prop(nat_align_down(prefix.to_vaddr() as nat, ps_gl as nat) as Vaddr);
        };
        // aligned.align_up(gl).to_vaddr() == aligned.to_vaddr() + ps_gl.
        aligned.aligned_align_up_advances(guard_level as int);
        // Bridge: aligned.align_up(gl) == prefix.align_up(gl), since prefix.align_up(gl)
        // is defined as prefix.align_down(gl).next_index(gl) == aligned.next_index(gl),
        // and aligned.align_up(gl) == aligned.align_down(gl).next_index(gl) == aligned.next_index(gl)
        // (aligned_align_down_is_self makes aligned.align_down(gl) == aligned).
        aligned.aligned_align_down_is_self(guard_level as int);
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
        if gl >= 1 && gl <= NR_LEVELS {
            // va.index[gl-1] == prefix.index[gl-1] from invariant (level < guard_level)
            // Combined with line 488 (upper indices match), all indices at gl-1
            // and above are equal, so align_down(gl) matches.
            self.va.align_down_to_vaddr_eq_if_upper_indices_eq(self.prefix, gl as int);
            self.va.align_down_concrete(gl as int);
            self.prefix.align_down_concrete(gl as int);
            AbstractVaddr::from_vaddr_to_vaddr_roundtrip(
                nat_align_down(
                    self.va.to_vaddr() as nat,
                    page_size(gl as PagingLevel) as nat,
                ) as Vaddr,
            );
            AbstractVaddr::from_vaddr_to_vaddr_roundtrip(
                nat_align_down(
                    self.prefix.to_vaddr() as nat,
                    page_size(gl as PagingLevel) as nat,
                ) as Vaddr,
            );
            lemma_page_size_ge_page_size(gl as PagingLevel);
            lemma_nat_align_down_sound(
                self.va.to_vaddr() as nat,
                page_size(gl as PagingLevel) as nat,
            );

            let ps = page_size(gl as PagingLevel) as nat;
            let prefix_val = self.prefix.to_vaddr() as nat;

            self.prefix.align_down_shape(gl as int);
            self.prefix.align_down(gl as int).reflect_prop(nat_align_down(prefix_val, ps) as Vaddr);
            // Use sound aligned_align_up_advances via helpers instead of unsound axioms.
            self.prefix_aligned_to_guard_level();
            self.prefix_plus_ps_no_overflow();
            self.prefix.aligned_align_up_advances(gl as int);
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
            forall|i: int|
                self.guard_level <= i < NR_LEVELS ==> self.va.index[i] == self.prefix.index[i],
    {
        let gl = self.guard_level;
        let start = self.prefix.align_down(gl as int).to_vaddr();

        // prefix is in its own locked range
        self.prefix.align_down_shape(gl as int);
        let prefix_ad = self.prefix.align_down(gl as int);

        // align_down(gl).to_vaddr() is page_size(gl)-aligned
        self.prefix.align_down_concrete(gl as int);
        AbstractVaddr::from_vaddr_to_vaddr_roundtrip(
            nat_align_down(
                self.prefix.to_vaddr() as nat,
                page_size(gl as PagingLevel) as nat,
            ) as Vaddr,
        );
        lemma_page_size_ge_page_size(gl as PagingLevel);
        lemma_nat_align_down_sound(
            self.prefix.to_vaddr() as nat,
            page_size(gl as PagingLevel) as nat,
        );

        // prefix.to_vaddr() is in [start, start + page_size(gl)) via aligned_align_up_advances.
        self.prefix_aligned_to_guard_level();
        self.prefix_plus_ps_no_overflow();
        self.prefix.aligned_align_up_advances(gl as int);

        if gl as int >= 2 && (gl as int) < NR_LEVELS as int {
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

            lemma_nat_align_down_monotone(pv, ps1, ps2);
            lemma_nat_align_down_within_block(pv, ps1, ps2);

            AbstractVaddr::same_node_indices_match(
                self.va.to_vaddr(),
                self.prefix.to_vaddr(),
                node_start,
                1 as PagingLevel,
            );
            AbstractVaddr::to_vaddr_from_vaddr_roundtrip(self.va);
            AbstractVaddr::to_vaddr_from_vaddr_roundtrip(self.prefix);
        }
    }

    /// When the cursor is in the locked range, va.index[guard_level - 1]
    /// matches prefix.index[guard_level - 1]. This is because both va and
    /// prefix are within the same page_size(guard_level)-aligned block.
    #[verifier::rlimit(2000)]
    pub proof fn in_locked_range_guard_index_eq_prefix(self)
        requires
            self.inv(),
            self.prefix.inv(),
            1 <= self.guard_level <= NR_LEVELS,
            self.in_locked_range(),
        ensures
            self.va.index[self.guard_level - 1] == self.prefix.index[self.guard_level - 1],
    {
        let gl = self.guard_level;
        let start = self.prefix.align_down(gl as int).to_vaddr();

        self.prefix.align_down_shape(gl as int);
        self.prefix.align_down_concrete(gl as int);
        // Use sound aligned_align_up_advances via helpers instead of the
        // axiomatic align_up_concrete/align_diff (now removed).
        self.prefix_aligned_to_guard_level();
        self.prefix_plus_ps_no_overflow();
        self.prefix.aligned_align_up_advances(gl as int);
        AbstractVaddr::from_vaddr_to_vaddr_roundtrip(
            nat_align_down(
                self.prefix.to_vaddr() as nat,
                page_size(gl as PagingLevel) as nat,
            ) as Vaddr,
        );
        lemma_page_size_ge_page_size(gl as PagingLevel);
        lemma_nat_align_down_sound(
            self.prefix.to_vaddr() as nat,
            page_size(gl as PagingLevel) as nat,
        );

        self.prefix.align_down(gl as int).reflect_prop(
            nat_align_down(
                self.prefix.to_vaddr() as nat,
                page_size(gl as PagingLevel) as nat,
            ) as Vaddr,
        );

        // Both va and prefix are in [start, start + page_size(gl)).
        // Since they're in the same page_size(gl)-aligned block:
        // va / page_size(gl) == prefix / page_size(gl), hence
        // pte_index(va, gl) == pte_index(prefix, gl), hence
        // va.index[gl-1] == prefix.index[gl-1].
        //
        // Use pte_index postcondition to connect to AbstractVaddr.index.
        let ps = page_size(gl as PagingLevel);
        let va_val = self.va.to_vaddr();
        let pf_val = self.prefix.to_vaddr();
        // va and prefix are in [start, start + ps), so va/ps == prefix/ps == start/ps
        // start is ps-aligned (from align_down), so start/ps = start/ps and (start+ps-1)/ps = start/ps.
        let k = start as int / ps as int;
        assert(start as int == k * ps as int) by {
            lemma_nat_align_down_sound(self.prefix.to_vaddr() as nat, ps as nat);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(start as int, ps as int);
        };
        // va in [start, start + ps) means va = k*ps + r for 0 <= r < ps, so va/ps = k.
        assert(va_val as int / ps as int == k) by {
            let r = va_val as int - start as int;
            assert(0 <= r);
            assert(r < ps as int);
            assert(va_val as int == k * ps as int + r) by (nonlinear_arith)
                requires
                    va_val as int == start as int + r,
                    start as int == k * ps as int,
            ;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                va_val as int,
                ps as int,
                k,
                r,
            );
        };
        assert(pf_val as int / ps as int == k) by {
            let r = pf_val as int - start as int;
            assert(0 <= r);
            assert(r < ps as int);
            assert(pf_val as int == k * ps as int + r) by (nonlinear_arith)
                requires
                    pf_val as int == start as int + r,
                    start as int == k * ps as int,
            ;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                pf_val as int,
                ps as int,
                k,
                r,
            );
        };
        // pte_index gives index[gl-1] == from_vaddr(va).index[gl-1]
        // Since va/ps == prefix/ps, their pte_index at level gl must be equal.
        // pte_index(va, gl) = (va >> bit_offset(gl)) & (NR_ENTRIES - 1)
        // For VAs in the same ps-aligned block, this is the same.
        // from_vaddr(va).index[gl-1] == (va / ps) % NR_ENTRIES (from pte_index spec).
        // Since va/ps == pf/ps (proved above), (va/ps) % NR_ENTRIES == (pf/ps) % NR_ENTRIES,
        // hence the indices are equal.
        //
        // Connection: pte_index(va, gl) == from_vaddr(va).index[gl-1] (pte_index ensures)
        // and pte_index(va, gl) is (va >> bit_offset(gl)) & (NR_ENTRIES-1).
        // Since va/ps = va >> bit_offset(gl) (ps is a power of 2),
        // pte_index(va, gl) = (va/ps) % NR_ENTRIES.
        //
        // same_node_indices_match provides this but its auto trigger doesn't fire.
        // from_vaddr(v).index[i] == ((v / pow2((12 + 9*i) as nat) as usize) % NR_ENTRIES) as int.
        // ps == page_size(gl) == pow2((12 + 9*(gl-1)) as nat) as usize.
        // So from_vaddr(v).index[gl-1] == ((v / ps) % NR_ENTRIES) as int.
        // Since va_val / ps == pf_val / ps == k, the indices are equal.
        use crate::specs::mm::page_table::cursor::page_size_lemmas::*;
        lemma_page_size_spec_values();
        // page_size(gl) == pow2(12 + 9*(gl-1)) for gl in 1..=4.
        // Use concrete values from lemma_page_size_spec_values + lemma2_to64.
        vstd::arithmetic::power2::lemma2_to64();
        vstd::arithmetic::power2::lemma2_to64_rest();
        assert(ps as int == pow2((12 + 9 * (gl - 1)) as nat) as int);
        // Now from_vaddr unfolds: index[gl-1] = ((va / pow2(...)) % NR_ENTRIES) = ((va / ps) % NR_ENTRIES)
        assert(AbstractVaddr::from_vaddr(va_val).index[gl - 1] == ((va_val as usize / ps)
            % NR_ENTRIES) as int);
        assert(AbstractVaddr::from_vaddr(pf_val).index[gl - 1] == ((pf_val as usize / ps)
            % NR_ENTRIES) as int);
        // va_val / ps == pf_val / ps (already proved as k)
        AbstractVaddr::to_vaddr_from_vaddr_roundtrip(self.va);
        AbstractVaddr::to_vaddr_from_vaddr_roundtrip(self.prefix);
    }

    pub proof fn in_locked_range_level_le_nr_levels(self)
        requires
            self.inv(),
            self.in_locked_range(),
            !self.popped_too_high,
        ensures
            self.level <= NR_LEVELS,
    {
        self.in_locked_range_level_le_guard_level();
    }

    /// When the cursor is in the locked range and not popped, its top-level
    /// index is strictly less than `TOP_LEVEL_INDEX_RANGE.end` (the relaxed inv
    /// only allows `<=`, but the operational state is strict).
    pub proof fn in_locked_range_top_index_lt_top_end(self)
        requires
            self.inv(),
            self.in_locked_range(),
            !self.popped_too_high,
        ensures
            self.va.index[NR_LEVELS - 1] < C::TOP_LEVEL_INDEX_RANGE_spec().end,
    {
        self.in_locked_range_level_le_guard_level();
        if self.guard_level as int == NR_LEVELS as int {
            if self.level < self.guard_level {
                // va.index[guard_level-1] == prefix.index[guard_level-1] < TOP_LEVEL_INDEX_RANGE.end
                assert(self.va.index[NR_LEVELS - 1] == self.prefix.index[NR_LEVELS - 1]);
            } else {
                // level == guard_level == NR_LEVELS:
                // va.index[NR_LEVELS-1] <= TOP_LEVEL_INDEX_RANGE.end (from inv).
                // in_locked_range means va < locked_range.end = prefix.align_up(gl).
                // If va.index[NR_LEVELS-1] == TOP_LEVEL_INDEX_RANGE.end, the cursor
                // would be above_locked_range (the one-past-end sentinel), contradicting
                // in_locked_range. So strict < holds.
                // Since prefix.index[NR_LEVELS-1] < TOP_LEVEL_INDEX_RANGE.end (line 482)
                // and locked_range.end = prefix.align_up(NR_LEVELS), which has
                // index[NR_LEVELS-1] at most prefix.index[NR_LEVELS-1] + 1, any VA
                // at the top_end sentinel overshoots.
                self.in_locked_range_guard_index_eq_prefix();
                assert(self.va.index[NR_LEVELS - 1] == self.prefix.index[NR_LEVELS - 1]);
            }
        } else {
            assert(self.va.index[NR_LEVELS - 1] == self.prefix.index[NR_LEVELS - 1]);
        }
    }

    pub proof fn in_locked_range_level_le_guard_level(self)
        requires
            self.inv(),
            self.in_locked_range(),
            !self.popped_too_high,
        ensures
            self.level <= self.guard_level,
    {
        assert(self.in_locked_range() ==> !self.above_locked_range());
    }

    /// At `level == guard_level == NR_LEVELS`, the cursor's index strictly
    /// satisfies `idx + 1 < NR_ENTRIES`. This rules out the spec corner where
    /// `move_forward_owner_spec` falls into its third branch (returning self
    /// unchanged) — without this fact several `move_forward_*` lemmas have
    /// genuinely-false postconditions.
    ///
    /// **UserPtConfig**: `TOP_LEVEL_INDEX_RANGE.end == 256 < NR_ENTRIES`, so
    /// `in_locked_range_top_index_lt_top_end` already gives strict < NR_ENTRIES.
    ///
    /// **KernelPtConfig**: `TOP_LEVEL_INDEX_RANGE.end == NR_ENTRIES`, but
    /// `LOCKED_END_BOUND_spec() == FRAME_METADATA_BASE_VADDR + PAGE_SIZE ==
    /// 0xffff_e000_0000_1000`. Combined with `leading_bits == 0xFFFF`, the
    /// cursor inv `locked_range().end <= LOCKED_END_BOUND_spec()` forces
    /// `prefix.index[NR_LEVELS - 1] + 1 <= 0x1c0 < NR_ENTRIES`. The full
    /// arithmetic chain through `align_up` is encapsulated in this lemma.
    pub proof fn cursor_top_idx_strict_lt_nr_entries(self)
        requires
            self.inv(),
            self.in_locked_range(),
            !self.popped_too_high,
            self.level == NR_LEVELS,
            self.guard_level == NR_LEVELS,
        ensures
            self.continuations[self.level - 1].idx + 1 < NR_ENTRIES,
    {
        self.in_locked_range_top_index_lt_top_end();
        self.in_locked_range_guard_index_eq_prefix();
        let top_end = C::TOP_LEVEL_INDEX_RANGE_spec().end as int;
        if top_end >= NR_ENTRIES as int {
            assert(self.continuations[self.level - 1].idx + 1 < NR_ENTRIES);
        }
    }

    /// The locked range spans exactly one guard-level node:
    /// `end - start == page_size(guard_level)`. Surfaces the arithmetic
    /// that `node_within_locked_range` / `in_node_holds_at_top` derive
    /// internally (`locked_range().start == nat_align_down(prefix, ps_gl)`,
    /// `end == start + ps_gl`), so callers can turn `node ⊆ locked_range`
    /// (at `level == guard - 1`, where the node size equals the span) into
    /// `node == locked_range`.
    pub proof fn locked_range_span(self)
        requires
            self.inv(),
        ensures
            self.locked_range().start as nat == nat_align_down(
                self.prefix.to_vaddr() as nat,
                page_size(self.guard_level as PagingLevel) as nat,
            ),
            self.locked_range().start as nat % page_size(self.guard_level as PagingLevel) as nat
                == 0,
            self.locked_range().end - self.locked_range().start == page_size(
                self.guard_level as PagingLevel,
            ),
    {
        let gl = self.guard_level;
        let ps_gl = page_size(gl as PagingLevel) as nat;
        let pv = self.prefix.to_vaddr() as nat;

        lemma_page_size_ge_page_size(gl as PagingLevel);
        self.prefix.align_down_concrete(gl as int);
        self.prefix_aligned_to_guard_level();
        self.prefix_plus_ps_no_overflow();
        self.prefix.aligned_align_up_advances(gl as int);
        AbstractVaddr::from_vaddr_to_vaddr_roundtrip(nat_align_down(pv, ps_gl) as Vaddr);
        vstd_extra::arithmetic::lemma_nat_align_down_sound(pv, ps_gl);
    }

    /// The whole locked range (which contains `va`) lies in the single
    /// guard-level-parent node (`page_size(guard_level + 1)`) that holds the
    /// cursor's own VA — `in_node_holds_at_top` generalized from `NR_LEVELS`
    /// to an arbitrary `guard_level`. The locked range is
    /// `page_size(guard_level)`-aligned and -sized (`locked_range_span`) and
    /// `page_size(guard_level)` divides `page_size(guard_level + 1)`, so it
    /// never straddles a `page_size(guard_level + 1)` boundary.
    pub proof fn in_node_holds_at_guard(self, self_va: Vaddr, va: Vaddr, node_size: usize)
        requires
            self.inv(),
            self.in_locked_range(),
            self.va.reflect(self_va),
            node_size == page_size((self.guard_level + 1) as PagingLevel),
            self.locked_range().start <= va < self.locked_range().end,
        ensures
            nat_align_down(self_va as nat, node_size as nat) <= va as nat,
            (va as nat) - nat_align_down(self_va as nat, node_size as nat) < node_size as nat,
    {
        let gl = self.guard_level;
        let pg = page_size(gl as PagingLevel) as nat;
        let pg1 = node_size as nat;
        let ls = self.locked_range().start as nat;

        // Page-size positivity: `page_size(_) >= PAGE_SIZE > 0`.
        lemma_page_size_ge_page_size(gl as PagingLevel);
        lemma_page_size_ge_page_size((gl + 1) as PagingLevel);
        assert(pg > 0 && pg1 > 0);

        self.locked_range_span();
        crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_divides(
            gl as PagingLevel,
            (gl + 1) as PagingLevel,
        );
        self.va.reflect_prop(self_va);
        // `in_locked_range` + span: `ls <= self_va < ls + pg`, likewise `va`.
        // (`in_locked_range`: `locked_range.start <= self.va.to_vaddr() <
        // locked_range.end`; `reflect_prop`: `to_vaddr() == self_va`; span:
        // `end == start + pg`.) So the locked range is the `pg`-block at `ls`.
        assert(ls <= self_va < ls + pg);
        assert(ls <= va < ls + pg);

        vstd_extra::arithmetic::lemma_nat_align_down_sound(self_va as nat, pg);
        vstd_extra::arithmetic::lemma_nat_align_down_sound(self_va as nat, pg1);
        vstd_extra::arithmetic::lemma_nat_align_down_sound(va as nat, pg1);
        // `nat_align_down(self_va, pg) == ls`: `ls` is `pg`-aligned and the
        // unique `pg`-aligned value in `[ls, ls + pg)` (which holds self_va).
        assert(nat_align_down(self_va as nat, pg) == ls) by {
            vstd_extra::arithmetic::lemma_nat_align_down_sound(self_va as nat, pg);
            let nad = nat_align_down(self_va as nat, pg) as int;
            let lsi = ls as int;
            let pgi = pg as int;
            // `ls <= nad`: sound's `forall n <= self_va, n % pg == 0 ==> n <=
            // nad` instantiated at `n = ls` (`ls <= self_va`, `ls % pg == 0`).
            assert(lsi <= nad);
            // `nad <= self_va < ls + pg`  ⟹  `0 <= nad - ls < pg`.
            assert(0 <= nad - lsi && nad - lsi < pgi);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(nad, pgi);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(lsi, pgi);
            let kn = nad / pgi;
            let kl = lsi / pgi;
            assert(nad == pgi * kn);  // nad % pg == 0 (sound)
            assert(lsi == pgi * kl);  // ls  % pg == 0 (locked_range_span)
            assert(nad - lsi == pgi * (kn - kl)) by (nonlinear_arith)
                requires
                    nad == pgi * kn,
                    lsi == pgi * kl,
            ;
            assert(kn - kl == 0) by (nonlinear_arith)
                requires
                    0 <= pgi * (kn - kl) < pgi,
                    pgi > 0,
            ;
        };
        vstd_extra::arithmetic::lemma_nat_align_down_monotone(self_va as nat, pg, pg1);
        vstd_extra::arithmetic::lemma_nat_align_down_within_block(self_va as nat, pg, pg1);
        // node_start := nat_align_down(self_va, pg1).
        //   monotone:      node_start <= nat_align_down(self_va, pg) == ls
        //   within_block:  ls + pg == nat_align_down(self_va,pg) + pg
        //                            <= node_start + pg1
        // With `ls <= va < ls + pg`: node_start <= ls <= va, and
        // va < ls + pg <= node_start + pg1.
    }

    /// The node at `level+1` containing `va` fits within the locked range.
    #[verifier::rlimit(20000)]
    pub proof fn node_within_locked_range(self, level: PagingLevel)
        requires
            self.inv(),
            self.in_locked_range(),
            1 <= level < self.guard_level,
        ensures
            self.locked_range().start <= nat_align_down(
                self.va.to_vaddr() as nat,
                page_size((level + 1) as PagingLevel) as nat,
            ) as usize,
            nat_align_down(
                self.va.to_vaddr() as nat,
                page_size((level + 1) as PagingLevel) as nat,
            ) as usize + page_size((level + 1) as PagingLevel) <= self.locked_range().end,
    {
        let gl = self.guard_level;
        let ps_gl = page_size(gl as PagingLevel) as nat;
        let ps = page_size((level + 1) as PagingLevel) as nat;
        let pv = self.prefix.to_vaddr() as nat;
        let va = self.va.to_vaddr() as nat;

        lemma_page_size_ge_page_size(gl as PagingLevel);
        lemma_page_size_ge_page_size((level + 1) as PagingLevel);
        lemma_page_size_divides((level + 1) as PagingLevel, gl as PagingLevel);

        self.prefix.align_down_concrete(gl as int);
        self.prefix_aligned_to_guard_level();
        self.prefix_plus_ps_no_overflow();
        self.prefix.aligned_align_up_advances(gl as int);
        AbstractVaddr::from_vaddr_to_vaddr_roundtrip(nat_align_down(pv, ps_gl) as Vaddr);

        let start = nat_align_down(pv, ps_gl);
        // Locked range's end is `prefix + ps_gl` (aligned prefix, always-advance).
        let end = nat_align_down(pv, ps_gl) + ps_gl;

        lemma_nat_align_down_sound(pv, ps_gl);
        lemma_nat_align_down_sound(va, ps);
        let ad = nat_align_down(va, ps);

        // `start` and `end` are ps-aligned because ps | ps_gl.
        let q = (ps_gl / ps) as int;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ps_gl as int, ps as int);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(start as int, ps_gl as int);
        // New `end = nat_align_down(pv, ps_gl) + ps_gl` is ps_gl-aligned: both summands are.
        assert(end as int % ps_gl as int == 0) by {
            vstd::arithmetic::div_mod::lemma_add_mod_noop(start as int, ps_gl as int, ps_gl as int);
            vstd::arithmetic::div_mod::lemma_mod_self_0(ps_gl as int);
        };
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(end as int, ps_gl as int);
        let ks = start as int / ps_gl as int;
        let ke = end as int / ps_gl as int;
        vstd::arithmetic::mul::lemma_mul_is_associative(ps as int, q, ks);
        vstd::arithmetic::mul::lemma_mul_is_associative(ps as int, q, ke);
        vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(q * ks, 0int, ps as int);
        vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(q * ke, 0int, ps as int);
        vstd::arithmetic::div_mod::lemma_small_mod(0nat, ps);
        assert(start as int % ps as int == 0int);
        assert(end as int % ps as int == 0int);

        assert(ad >= start) by {
            vstd::arithmetic::div_mod::lemma_div_is_ordered(start as int, va as int, ps as int);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(start as int, ps as int);
            vstd::arithmetic::mul::lemma_mul_inequality(
                start as int / ps as int,
                va as int / ps as int,
                ps as int,
            );
        };

        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ad as int, ps as int);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(end as int, ps as int);
        vstd::arithmetic::div_mod::lemma_div_is_ordered(ad as int, end as int, ps as int);
        if ad as int / ps as int == end as int / ps as int {
            assert(false);
        }
        assert(ad as int / ps as int + 1 <= end as int / ps as int);
        let ad_q = ad as int / ps as int;
        let end_q = end as int / ps as int;
        let ps_i = ps as int;
        vstd_extra::arithmetic::lemma_nat_align_down_sound(va, ps);
        vstd_extra::arithmetic::lemma_nat_align_up_sound(pv, ps_gl);
        assert(ad as int % ps as int == 0);
        assert(end as int % ps as int == 0);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ad as int, ps as int);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(end as int, ps as int);
        // ad == ps * (ad / ps) + ad % ps (from fundamental_div_mod) with ad % ps == 0.
        assert(ad as int == (ps as int) * (ad as int / ps as int) + ad as int % ps as int);
        assert(end as int == (ps as int) * (end as int / ps as int) + end as int % ps as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(ps as int, ad as int / ps as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(ps as int, end as int / ps as int);
        assert(ad as int == ad_q * ps_i + (ad as int % ps as int));
        assert(ad as int % ps as int == 0);
        assert(ad as int == ad_q * ps_i);
        assert(end as int % ps as int == 0);
        assert(end as int == end_q * ps_i) by (nonlinear_arith)
            requires
                end as int == (ps as int) * (end as int / ps as int) + end as int % ps as int,
                end as int % ps as int == 0,
                end_q == end as int / ps as int,
                ps_i == ps as int,
        ;
        assert((ad_q + 1) * ps_i <= end_q * ps_i) by (nonlinear_arith)
            requires
                ad_q + 1 <= end_q,
                ps_i >= 0,
        ;
        assert((ad_q + 1) * ps_i == ad_q * ps_i + ps_i) by (nonlinear_arith);
    }

    /// The cursor's `prefix` is aligned to `page_size(self.guard_level)`, since the
    /// cursor invariant sets `prefix.offset == 0` and zeros all indices below
    /// `self.guard_level`.
    pub proof fn prefix_aligned_to_guard_level(self)
        requires
            self.inv(),
        ensures
            self.prefix.to_vaddr() as nat % page_size(self.guard_level as PagingLevel) as nat == 0,
    {
        let gl = self.guard_level;
        let ps = page_size(gl as PagingLevel) as nat;
        lemma_page_size_ge_page_size(gl as PagingLevel);

        // Show prefix.align_down(gl) == prefix structurally, since prefix is already
        // ps(gl)-aligned (offset == 0 and indices below gl are 0).
        self.prefix.align_down_shape(gl as int);
        self.prefix.align_down_leading_bits(gl as int);
        let aligned = self.prefix.align_down(gl as int);

        assert forall|i: int| 0 <= i < NR_LEVELS implies #[trigger] aligned.index[i]
            == self.prefix.index[i] by {
            assert(self.prefix.index.contains_key(i));
            assert(aligned.index.contains_key(i));
            if i < gl - 1 {
                assert(self.prefix.index[i] == 0);
            }
        };
        assert(aligned.index == self.prefix.index);
        assert(aligned == self.prefix);

        // Combine align_down_concrete + reflect_prop to get prefix.to_vaddr() == nat_align_down.
        self.prefix.align_down_concrete(gl as int);
        self.prefix.to_vaddr_bounded();
        vstd_extra::arithmetic::lemma_nat_align_down_sound(self.prefix.to_vaddr() as nat, ps);
        aligned.reflect_prop(nat_align_down(self.prefix.to_vaddr() as nat, ps) as Vaddr);
    }

    /// At `guard_level == NR_LEVELS`, the level-`(NR_LEVELS+1)` node
    /// (size `page_size(NR_LEVELS+1) == 2^48`, the whole positional
    /// space) covers the entire locked range: with `prefix.offset == 0`
    /// and every `prefix.index[i] == 0` (`i < guard_level == NR_LEVELS`),
    /// `prefix.to_vaddr() == leading_bits * 2^48`, and
    /// `locked_range == [lb*2^48, lb*2^48 + page_size(NR_LEVELS))`, which
    /// sits inside `[lb*2^48, (lb+1)*2^48)`. Since `self.va` shares
    /// `leading_bits` with `prefix` (`inv`), `nat_align_down(self.va,
    /// 2^48) == lb*2^48 == locked_range().start`. Hence `jump`'s in-node
    /// check provably succeeds at the top — *no `in_locked_range`
    /// needed*, so a drifted cursor never reaches `pop_level` at
    /// `level == NR_LEVELS`.
    pub proof fn in_node_holds_at_top(self, self_va: Vaddr, va: Vaddr, node_size: usize)
        requires
            self.inv(),
            self.va.reflect(self_va),
            self.guard_level == NR_LEVELS,
            node_size == page_size((NR_LEVELS + 1) as PagingLevel),
            self.locked_range().start <= va < self.locked_range().end,
        ensures
            nat_align_down(self_va as nat, node_size as nat) <= va as nat,
            (va as nat) - nat_align_down(self_va as nat, node_size as nat) < node_size as nat,
    {
        let gl = self.guard_level;
        let lb = self.prefix.leading_bits;
        let big = 0x1_0000_0000_0000int;  // 2^48 == page_size(NR_LEVELS+1)
        let ps_nr = page_size(NR_LEVELS as PagingLevel) as int;

        crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_spec_values();
        // node_size == page_size(5) == 2^48; page_size(NR_LEVELS) == 2^39 < 2^48.

        // ---- prefix.to_vaddr() == lb * 2^48 -------------------------------
        // offset == 0 and every positional index is 0 (i < gl == NR_LEVELS).
        assert forall|i: int| 0 <= i < NR_LEVELS implies self.prefix.index[i] == 0 by {
            assert(self.prefix.index.contains_key(i));
        };
        self.prefix.to_vaddr_indices_drop_zero_range(0, NR_LEVELS as int);
        assert(self.prefix.to_vaddr_indices(NR_LEVELS as int) == 0);
        assert(self.prefix.to_vaddr() as int == lb * big);

        // ---- locked_range().start == prefix.to_vaddr(); end == start + ps_nr
        self.prefix_aligned_to_guard_level();
        self.prefix_plus_ps_no_overflow();
        self.prefix.aligned_align_up_advances(gl as int);
        // align_down(gl) == prefix (already aligned: offset 0, indices 0).
        self.prefix.align_down_shape(gl as int);
        self.prefix.align_down_leading_bits(gl as int);
        let aligned = self.prefix.align_down(gl as int);
        assert forall|i: int| 0 <= i < NR_LEVELS implies #[trigger] aligned.index[i]
            == self.prefix.index[i] by {
            assert(self.prefix.index.contains_key(i));
            assert(aligned.index.contains_key(i));
        };
        assert(aligned.index == self.prefix.index);
        assert(aligned == self.prefix);
        assert(self.locked_range().start as int == lb * big);
        assert(self.locked_range().end as int == lb * big + ps_nr);

        // ---- nat_align_down(self_va, 2^48) == lb * 2^48 -------------------
        self.va.reflect_prop(self_va);  // self.va.to_vaddr() == self_va
        self.va.to_vaddr_bounded();  // 0 <= P_v < 2^48
        assert(self.va.leading_bits == lb);  // inv: va.lb == prefix.lb
        let pv = (self.va.offset + self.va.to_vaddr_indices(0)) as int;
        assert(0 <= pv < big);
        assert(self_va as int == pv + lb * big);
        vstd_extra::arithmetic::lemma_nat_align_down_sound(self_va as nat, big as nat);
        assert(0 <= lb < 0x1_0000int);
        assert(nat_align_down(self_va as nat, big as nat) == (lb * big) as nat) by (nonlinear_arith)
            requires
                self_va as nat == (pv + lb * big) as nat,
                0 <= pv < big,
                0 <= lb < 0x1_0000int,
                big == 0x1_0000_0000_0000int,
                nat_align_down(self_va as nat, big as nat) <= self_va as nat,
                nat_align_down(self_va as nat, big as nat) % (big as nat) == 0,
                (self_va as nat) - nat_align_down(self_va as nat, big as nat) < big as nat,
                forall|n: nat|
                    n <= self_va as nat && #[trigger] (n % (big as nat)) == 0 ==> n
                        <= nat_align_down(self_va as nat, big as nat),
        ;

        // ---- combine -----------------------------------------------------
        // node_start == lb*2^48 == locked_range().start <= va,
        // va < end == node_start + ps_nr <= node_start + 2^48 == node_start + node_size.
        assert(ps_nr < big);
    }

    /// `prefix.to_vaddr() + page_size(guard_level) <= usize::MAX`.
    ///
    /// Follows from the cursor invariant: prefix's lower indices and offset are zero,
    /// and the top-level index + leading_bits are bounded per config. For each
    /// guard_level case (1..NR_LEVELS), the sum stays within usize::MAX.
    pub proof fn prefix_plus_ps_no_overflow(self)
        requires
            self.inv(),
        ensures
            self.prefix.to_vaddr() + page_size(self.guard_level as PagingLevel) <= usize::MAX,
    {
        let gl = self.guard_level;
        lemma_page_size_ge_page_size(gl as PagingLevel);
        self.prefix.to_vaddr_bounded();
        self.prefix.to_vaddr_indices_gap_bound(0);
        vstd::arithmetic::power2::lemma2_to64();
        vstd::arithmetic::power2::lemma2_to64_rest();
        crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_spec_values();

        // prefix's lower indices are zero (i < gl), so
        // to_vaddr_indices(0) == to_vaddr_indices(gl).
        assert forall|i: int| 0 <= i < gl implies self.prefix.index[i] == 0 by {
            assert(self.prefix.index.contains_key(i));
        };
        self.prefix.to_vaddr_indices_drop_zero_range(0, gl as int);
        self.prefix.to_vaddr_indices_gap_bound(gl as int);

        // prefix.to_vaddr() == 0 + to_vaddr_indices(gl) + leading * 2^48
        //                   < pow2(12+9*NR_LEVELS) + 0xFFFF * 2^48 = 2^48 + 2^64 - 2^48 = 2^64.
        // Adding page_size(gl) — case analysis shows no overflow.
        let ps = page_size(gl as PagingLevel) as int;
        let pv = self.prefix.to_vaddr() as int;
        let lb = self.prefix.leading_bits;
        assert(pv == self.prefix.to_vaddr_indices(gl as int) + lb * 0x1_0000_0000_0000int);
        assert(self.prefix.to_vaddr_indices(gl as int) + pow2((12 + 9 * gl) as nat) as int <= pow2(
            (12 + 9 * NR_LEVELS) as nat,
        ) as int);
        assert(pow2((12 + 9 * NR_LEVELS) as nat) == 0x1_0000_0000_0000int) by (compute);
        assert(pow2((12 + 9 * gl) as nat) >= ps) by {
            // pow2(12+9*gl) == page_size(gl+1) >= page_size(gl) == ps.
            if gl == 1 {
                assert(ps == 0x1000);
            } else if gl == 2 {
                assert(ps == 0x20_0000);
            } else if gl == 3 {
                assert(ps == 0x4000_0000);
            } else {
                assert(ps == 0x80_0000_0000);
            }
        };
        // Key bound: tvi + page_size(gl+1) <= 2^48 from to_vaddr_indices_gap_bound(gl).
        // page_size(gl+1) == NR_ENTRIES * ps. So tvi <= 2^48 - NR_ENTRIES * ps.
        // Plus leading_bits <= 0xFFFF: lb * 2^48 <= (0x1_0000 - 1) * 2^48 = 2^64 - 2^48.
        // So pv <= 2^48 - NR_ENTRIES*ps + 2^64 - 2^48 = 2^64 - NR_ENTRIES*ps.
        // Adding ps: pv + ps <= 2^64 - (NR_ENTRIES - 1)*ps = 2^64 - 511*ps.
        // Since ps >= 4096 > 0, 511*ps > 0, so pv + ps < 2^64. Strict < usize::MAX works because
        // usize::MAX + 1 == 2^64.
        let tvi = self.prefix.to_vaddr_indices(gl as int) as int;
        assert(pow2((12 + 9 * gl) as nat) as int == NR_ENTRIES * ps) by {
            crate::arch::mm::lemma_nr_subpage_per_huge_eq_nr_entries();
            crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_nr_entries_times_sub_page_size(
            (gl + 1) as PagingLevel);
        };
        assert(tvi + NR_ENTRIES * ps <= 0x1_0000_0000_0000int);
        assert(ps >= 0x1000);

        assert(pv + ps <= usize::MAX as int) by (nonlinear_arith)
            requires
                pv == tvi + lb * 0x1_0000_0000_0000int,
                tvi + NR_ENTRIES * ps <= 0x1_0000_0000_0000int,
                0 <= lb < 0x1_0000int,
                ps >= 0x1000,
                NR_ENTRIES == 512,
                usize::MAX == 0xffff_ffff_ffff_ffffusize,
        ;
    }

    /// `self.va.to_vaddr() + page_size(level) <= usize::MAX` for any
    /// `level <= self.guard_level`, whenever the cursor is in the locked range.
    ///
    /// Derived from the cursor invariant: `in_locked_range` says
    /// `self.va < locked_range().end = prefix + page_size(guard_level)`
    /// (via `aligned_align_up_advances` applied to the aligned prefix), and
    /// `prefix_plus_ps_no_overflow` gives enough slack
    /// (`pv + page_size(gl) <= 2^64 - 511 * page_size(gl)`) to absorb another
    /// `page_size(level)` without wrapping, since `page_size(level) <= page_size(gl)`.
    pub proof fn va_plus_page_size_no_overflow(self, level: PagingLevel)
        requires
            self.inv(),
            self.in_locked_range(),
            1 <= level <= self.guard_level,
        ensures
            self.va.to_vaddr() + page_size(level) <= usize::MAX,
    {
        let gl = self.guard_level;
        lemma_page_size_ge_page_size(gl as PagingLevel);
        lemma_page_size_ge_page_size(level as PagingLevel);
        page_size_monotonic(level as PagingLevel, gl as PagingLevel);

        // Pin down locked_range().end == prefix.to_vaddr() + page_size(gl).
        self.prefix_aligned_to_guard_level();
        self.prefix_plus_ps_no_overflow();
        self.prefix.aligned_align_up_advances(gl as int);

        // Re-derive the structural bounds on prefix (as in prefix_plus_ps_no_overflow)
        // so nonlinear_arith has enough slack to discharge pv + ps + psl <= usize::MAX.
        self.prefix.to_vaddr_bounded();
        self.prefix.to_vaddr_indices_gap_bound(0);
        vstd::arithmetic::power2::lemma2_to64();
        vstd::arithmetic::power2::lemma2_to64_rest();
        crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_page_size_spec_values();

        assert forall|i: int| 0 <= i < gl implies self.prefix.index[i] == 0 by {
            assert(self.prefix.index.contains_key(i));
        };
        self.prefix.to_vaddr_indices_drop_zero_range(0, gl as int);
        self.prefix.to_vaddr_indices_gap_bound(gl as int);

        let ps = page_size(gl as PagingLevel) as int;
        let psl = page_size(level as PagingLevel) as int;
        let pv = self.prefix.to_vaddr() as int;
        let lb = self.prefix.leading_bits;
        let tvi = self.prefix.to_vaddr_indices(gl as int) as int;
        let va_val = self.va.to_vaddr() as int;
        assert(pv == tvi + lb * 0x1_0000_0000_0000int);
        assert(self.prefix.to_vaddr_indices(gl as int) + pow2((12 + 9 * gl) as nat) as int <= pow2(
            (12 + 9 * NR_LEVELS) as nat,
        ) as int);
        assert(pow2((12 + 9 * NR_LEVELS) as nat) == 0x1_0000_0000_0000int) by (compute);
        assert(pow2((12 + 9 * gl) as nat) >= ps) by {
            if gl == 1 {
                assert(ps == 0x1000);
            } else if gl == 2 {
                assert(ps == 0x20_0000);
            } else if gl == 3 {
                assert(ps == 0x4000_0000);
            } else {
                assert(ps == 0x80_0000_0000);
            }
        };
        assert(pow2((12 + 9 * gl) as nat) as int == NR_ENTRIES * ps) by {
            crate::arch::mm::lemma_nr_subpage_per_huge_eq_nr_entries();
            crate::specs::mm::page_table::cursor::page_size_lemmas::lemma_nr_entries_times_sub_page_size(
            (gl + 1) as PagingLevel);
        };
        assert(tvi + NR_ENTRIES * ps <= 0x1_0000_0000_0000int);
        assert(ps >= 0x1000);
        assert(psl >= 0x1000);
        assert(psl <= ps);
        assert(va_val < pv + ps);

        assert(va_val + psl <= usize::MAX as int) by (nonlinear_arith)
            requires
                va_val < pv + ps,
                pv == tvi + lb * 0x1_0000_0000_0000int,
                tvi + NR_ENTRIES * ps <= 0x1_0000_0000_0000int,
                0 <= lb < 0x1_0000int,
                ps >= 0x1000,
                psl >= 0x1000,
                psl <= ps,
                NR_ENTRIES == 512,
                usize::MAX == 0xffff_ffff_ffff_ffffusize,
        ;
    }

    pub proof fn locked_range_page_aligned(self)
        requires
            self.inv(),
        ensures
            self.locked_range().end % PAGE_SIZE == 0,
            self.locked_range().start % PAGE_SIZE == 0,
    {
        let gl = self.guard_level;
        let pv = self.prefix.to_vaddr() as nat;
        let ps = page_size(gl as PagingLevel) as nat;
        lemma_page_size_ge_page_size(gl as PagingLevel);
        lemma_page_size_divides(1u8, gl as PagingLevel);
        lemma_page_size_spec_level1();
        lemma_nat_align_down_sound(pv, ps);
        lemma_nat_align_up_sound(pv, ps);
        let start_va = nat_align_down(pv, ps);
        let end_va = nat_align_up(pv, ps);
        vstd::arithmetic::div_mod::lemma_mod_mod(
            start_va as int,
            PAGE_SIZE as int,
            ps as int / PAGE_SIZE as int,
        );
        vstd::arithmetic::div_mod::lemma_mod_mod(
            end_va as int,
            PAGE_SIZE as int,
            ps as int / PAGE_SIZE as int,
        );
        self.prefix.align_down_concrete(gl as int);
        self.prefix_aligned_to_guard_level();
        self.prefix_plus_ps_no_overflow();
        self.prefix.aligned_align_up_advances(gl as int);

        self.prefix.to_vaddr_bounded();
        self.prefix.to_vaddr_indices_gap_bound(0);
        vstd::arithmetic::power2::lemma2_to64();
        vstd::arithmetic::power2::lemma2_to64_rest();
        crate::arch::mm::lemma_nr_subpage_per_huge_eq_nr_entries();
        vstd_extra::external::ilog2::lemma_usize_ilog2_to32();
        page_size_monotonic(gl as PagingLevel, NR_LEVELS as PagingLevel);
        vstd::arithmetic::power2::lemma_pow2_adds(12nat, 27nat);
        assert(page_size(NR_LEVELS as PagingLevel) == pow2(39nat));
        vstd::arithmetic::power2::lemma_pow2_adds(1nat, 48nat);
        vstd_extra::external::ilog2::lemma_pow2_increases(49nat, 64nat);

        self.prefix.align_down_shape(gl as int);
        AbstractVaddr::from_vaddr_to_vaddr_roundtrip(start_va as Vaddr);
        AbstractVaddr::from_vaddr_to_vaddr_roundtrip(end_va as Vaddr);
    }

    pub proof fn cur_subtree_inv(self)
        requires
            self.inv(),
        ensures
            self.cur_subtree().inv(),
    {
        let cont = self.continuations[self.level - 1];
        cont.inv_children_unroll(cont.idx as int)
    }

    /// If the current entry is absent, `!self@.present()`.
    pub proof fn cur_entry_absent_not_present(self)
        requires
            self.inv(),
            self.in_locked_range(),
            self.cur_entry_owner().is_absent(),
        ensures
            !self@.present(),
    {
        self.cur_subtree_inv();
        let cur_va = self.cur_va();
        let cur_subtree = self.cur_subtree();
        let cur_path = cur_subtree.value.path;
        PageTableOwner(cur_subtree).view_rec_absent_empty(cur_path);

        assert forall|m: Mapping| self.view_mappings().contains(m) implies !(m.va_range.start
            <= cur_va < m.va_range.end) by {
            if m.va_range.start <= cur_va < m.va_range.end {
                self.mapping_covering_cur_va_from_cur_subtree(m);
            }
        };

        let filtered = self@.mappings.filter(
            |m: Mapping| m.va_range.start <= self@.cur_va < m.va_range.end,
        );
        assert(filtered == set![]) by {
            assert forall|m: Mapping| !filtered.contains(m) by {
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
            self.in_locked_range(),
            PageTableOwner(self.cur_subtree()).view_rec(self.cur_subtree().value.path) =~= set![],
        ensures
            !self@.present(),
    {
        let cur_va = self.cur_va();

        assert forall|m: Mapping| self.view_mappings().contains(m) implies !(m.va_range.start
            <= cur_va < m.va_range.end) by {
            if m.va_range.start <= cur_va < m.va_range.end {
                self.mapping_covering_cur_va_from_cur_subtree(m);
            }
        };

        let filtered = self@.mappings.filter(
            |m: Mapping| m.va_range.start <= self@.cur_va < m.va_range.end,
        );
        assert(filtered == set![]) by {
            assert forall|m: Mapping| !filtered.contains(m) by {
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
            self.in_locked_range(),
            self.cur_entry_owner().is_frame(),
        ensures
            self@.present(),
            self@.query(
                self.cur_entry_owner().frame().mapped_pa,
                self.cur_entry_owner().frame().size,
                self.cur_entry_owner().frame().prop,
            ),
    {
        self.cur_subtree_inv();
        self.cur_va_in_subtree_range();
        self.view_preserves_inv();
        let subtree = self.cur_subtree();
        let path = subtree.value.path;
        let frame = self.cur_entry_owner().frame();
        let pt_level = INC_LEVELS - path.len();
        let cont = self.continuations[self.level - 1];

        cont.path().push_tail_property_len(cont.idx as usize);

        let m = Mapping {
            va_range: Range {
                start: vaddr_of::<C>(path) as int,
                end: vaddr_of::<C>(path) as int + page_size(pt_level as PagingLevel) as int,
            },
            pa_range: Range {
                start: frame.mapped_pa,
                end: (frame.mapped_pa + page_size(pt_level as PagingLevel)) as Paddr,
            },
            page_size: page_size(pt_level as PagingLevel),
            property: frame.prop,
        };
        assert(PageTableOwner(subtree).view_rec(path) == set![m]);
        cont.lemma_view_mappings_intro(m, cont.idx as int);
        self.lemma_view_mappings_intro(m, (self.level - 1) as int);
        assert(m.va_range.start <= self@.cur_va < m.va_range.end) by {
            self.cur_va_in_subtree_range();
            crate::specs::mm::page_table::owners::lemma_vaddr_of_eq_int::<C>(path);
        };

        let filtered = self@.mappings.filter(
            |m2: Mapping| m2.va_range.start <= self@.cur_va < m2.va_range.end,
        );
        assert(filtered.contains(m));
        lemma_set_contains_len(filtered, m);
    }

    /// The entry_own at each continuation level satisfies `metaregion_sound`.
    pub open spec fn path_metaregion_sound(self, regions: MetaRegionOwners) -> bool {
        forall|i: int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS ==> self.continuations[i].entry_own.metaregion_sound(
                regions,
            )
    }

    pub open spec fn metaregion_sound(self, regions: MetaRegionOwners) -> bool {
        &&& self.map_full_tree(
            |entry_owner: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                entry_owner.metaregion_sound(regions),
        )
        &&& self.path_metaregion_sound(regions)
    }

    pub proof fn metaregion_preserved(
        self,
        other: Self,
        regions0: MetaRegionOwners,
        regions1: MetaRegionOwners,
    )
        requires
            self.inv(),
            self.metaregion_sound(regions0),
            self.level == other.level,
            self.continuations =~= other.continuations,
            OwnerSubtree::implies(
                PageTableOwner::<C>::metaregion_sound_pred(regions0),
                PageTableOwner::<C>::metaregion_sound_pred(regions1),
            ),
        ensures
            other.metaregion_sound(regions1),
    {
        let f = PageTableOwner::metaregion_sound_pred(regions0);
        let g = PageTableOwner::metaregion_sound_pred(regions1);

        assert forall|i: int| #![auto] self.level - 1 <= i < NR_LEVELS implies {
            other.continuations[i].map_children(g)
        } by {
            let cont = self.continuations[i];
            assert(cont.inv());
            assert(cont.map_children(f));
            reveal(CursorContinuation::inv_children);
            assert forall|j: int|
                0 <= j < NR_ENTRIES
                    && #[trigger] cont.children[j] is Some implies cont.children[j].unwrap().tree_predicate_map(
            cont.path().push_tail(j as usize), g) by {
                cont.inv_children_unroll(j);
                cont.children[j].unwrap().map_implies(cont.path().push_tail(j as usize), f, g);
            };
        };
        assert(other.path_metaregion_sound(regions1)) by {
            assert forall|i: int|
                #![trigger other.continuations[i]]
                self.level - 1 <= i
                    < NR_LEVELS implies other.continuations[i].entry_own.metaregion_sound(
                regions1,
            ) by {
                self.inv_continuation(i);
                let eo = self.continuations[i].entry_own;
                assert(eo.metaregion_sound(regions0));
                assert(g(eo, self.continuations[i].path()));
            };
        };
    }

    /// Transfers `metaregion_sound` when `slot_owners` is preserved.
    pub proof fn metaregion_slot_owners_preserved(
        self,
        regions0: MetaRegionOwners,
        regions1: MetaRegionOwners,
    )
        requires
            self.inv(),
            self.metaregion_sound(regions0),
            regions0.slot_owners =~= regions1.slot_owners,
            forall|k: usize|
                regions0.slots.contains_key(k) ==> #[trigger] regions1.slots.contains_key(k),
            forall|k: usize|
                regions0.slots.contains_key(k) ==> regions0.slots[k]
                    == #[trigger] regions1.slots[k],
        ensures
            self.metaregion_sound(regions1),
    {
        let f = PageTableOwner::<C>::metaregion_sound_pred(regions0);
        let g = PageTableOwner::<C>::metaregion_sound_pred(regions1);
        assert forall|entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
            entry.inv() && f(entry, path) implies #[trigger] g(entry, path) by {
            entry.metaregion_sound_slot_owners_only(regions0, regions1);
        };
        self.metaregion_preserved(self, regions0, regions1);
    }

    pub proof fn metaregion_slot_owners_rc_increment(
        self,
        regions0: MetaRegionOwners,
        regions1: MetaRegionOwners,
        idx: usize,
    )
        requires
            self.inv(),
            self.metaregion_sound(regions0),
            regions0.inv(),
            regions1.slots == regions0.slots,
            regions1.slot_owners.dom() == regions0.slot_owners.dom(),
            regions1.slot_owners[idx].inner_perms.ref_count.value()
                == regions0.slot_owners[idx].inner_perms.ref_count.value() + 1,
            regions1.slot_owners[idx].inner_perms.ref_count.id()
                == regions0.slot_owners[idx].inner_perms.ref_count.id(),
            regions1.slot_owners[idx].inner_perms.storage
                == regions0.slot_owners[idx].inner_perms.storage,
            regions1.slot_owners[idx].inner_perms.vtable_ptr
                == regions0.slot_owners[idx].inner_perms.vtable_ptr,
            regions1.slot_owners[idx].inner_perms.in_list
                == regions0.slot_owners[idx].inner_perms.in_list,
            regions1.slot_owners[idx].paths_in_pt == regions0.slot_owners[idx].paths_in_pt,
            regions1.slot_owners[idx].slot_vaddr == regions0.slot_owners[idx].slot_vaddr,
            regions1.slot_owners[idx].usage == regions0.slot_owners[idx].usage,
            regions1.slot_owners[idx].inner_perms.ref_count.value() != REF_COUNT_UNUSED,
            // Bumped rc stays in the SHARED range (needed for the node branch).
            regions1.slot_owners[idx].inner_perms.ref_count.value() <= REF_COUNT_MAX,
            forall|i: usize|
                #![trigger regions1.slot_owners[i]]
                i != idx && regions0.slot_owners.contains_key(i) ==> regions1.slot_owners[i]
                    == regions0.slot_owners[i],
        ensures
            self.metaregion_sound(regions1),
    {
        let f = PageTableOwner::<C>::metaregion_sound_pred(regions0);
        let g = PageTableOwner::<C>::metaregion_sound_pred(regions1);
        assert(OwnerSubtree::implies(f, g)) by {
            assert forall|entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                entry.inv() && f(entry, path) implies #[trigger] g(entry, path) by {
                if entry.meta_slot_paddr() is Some {
                    let eidx = frame_to_index(entry.meta_slot_paddr().unwrap());
                    if eidx != idx {
                    } else {
                        entry.metaregion_sound_rc_value_changed(regions0, regions1);
                    }
                }
            };
        };
        self.metaregion_preserved(self, regions0, regions1);
    }

    /// Transfers `metaregion_sound` when `raw_count` changed from 0 to 1 at one index.
    /// Uses `map_implies_and` with the trivial `not_in_scope_pred`.
    pub proof fn metaregion_borrow_slot(
        self,
        regions0: MetaRegionOwners,
        regions1: MetaRegionOwners,
        changed_idx: usize,
    )
        requires
            self.inv(),
            self.metaregion_sound(regions0),
            regions1.inv(),
            forall|k: usize|
                regions0.slots.contains_key(k) ==> #[trigger] regions1.slots.contains_key(k),
            // Borrow-protocol transition: `raw_count` is dormant, so the
            // borrow is net-zero on `regions` — the slot perm at
            // `changed_idx` is preserved too (the caller borrows it via
            // `Frame::borrow`, which leaves `slots` unchanged). With
            // `raw_count` no longer in `metaregion_sound`, full slot
            // preservation is what carries soundness across the borrow.
            forall|k: usize|
                regions0.slots.contains_key(k) ==> regions0.slots[k]
                    == #[trigger] regions1.slots[k],
            // All other fields at changed_idx preserved
            regions1.slot_owners[changed_idx].inner_perms
                == regions0.slot_owners[changed_idx].inner_perms,
            regions1.slot_owners[changed_idx].slot_vaddr
                == regions0.slot_owners[changed_idx].slot_vaddr,
            regions1.slot_owners[changed_idx].usage == regions0.slot_owners[changed_idx].usage,
            regions1.slot_owners[changed_idx].paths_in_pt
                == regions0.slot_owners[changed_idx].paths_in_pt,
            // All other slots unchanged
            forall|i: usize|
                #![trigger regions1.slot_owners[i]]
                i != changed_idx ==> regions0.slot_owners[i] == regions1.slot_owners[i],
            regions0.slot_owners.dom() =~= regions1.slot_owners.dom(),
        ensures
            self.metaregion_sound(regions1),
    {
        let f = PageTableOwner::<C>::metaregion_sound_pred(regions0);
        let g = PageTableOwner::<C>::metaregion_sound_pred(regions1);
        let nsp = PageTableOwner::<C>::not_in_scope_pred();

        assert(OwnerSubtree::implies(
            |v: EntryOwner<C>, p: TreePath<NR_ENTRIES>| f(v, p) && nsp(v, p),
            g,
        )) by {
            assert forall|entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                entry.inv() && f(entry, path) && nsp(entry, path) implies #[trigger] g(
                entry,
                path,
            ) by {
                if entry.meta_slot_paddr() is Some {
                    let eidx = frame_to_index(entry.meta_slot_paddr().unwrap());
                    if eidx != changed_idx {
                    } else if entry.is_frame() {
                        assert(regions1.slots.contains_key(eidx));
                    }
                }
            };
        };

        assert forall|i: int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i < NR_LEVELS implies { self.continuations[i].map_children(g) } by {
            let cont = self.continuations[i];
            reveal(CursorContinuation::inv_children);
            assert forall|j: int|
                0 <= j < NR_ENTRIES
                    && #[trigger] cont.children[j] is Some implies cont.children[j].unwrap().tree_predicate_map(
            cont.path().push_tail(j as usize), nsp) by {
                cont.inv_children_unroll(j);
                PageTableOwner::tree_not_in_scope(
                    cont.children[j].unwrap(),
                    cont.path().push_tail(j as usize),
                );
            };
            assert forall|j: int|
                0 <= j < NR_ENTRIES
                    && #[trigger] cont.children[j] is Some implies cont.children[j].unwrap().tree_predicate_map(
            cont.path().push_tail(j as usize), g) by {
                cont.inv_children_unroll(j);
                cont.children[j].unwrap().map_implies_and(
                    cont.path().push_tail(j as usize),
                    f,
                    nsp,
                    g,
                );
            };
        };

        assert(self.path_metaregion_sound(regions1)) by {
            assert forall|i: int|
                #![trigger self.continuations[i]]
                self.level - 1 <= i
                    < NR_LEVELS implies self.continuations[i].entry_own.metaregion_sound(
                regions1,
            ) by {
                self.inv_continuation(i);
                let eo = self.continuations[i].entry_own;
                if eo.meta_slot_paddr() is Some {
                    let eidx = frame_to_index(eo.meta_slot_paddr().unwrap());
                    if eidx != changed_idx {
                    }
                }
            };
        };
    }

    /// Continuation entry_owns satisfy `metaregion_sound`.
    ///
    /// ## Justification
    /// When the cursor descends into a subtree, each continuation's `entry_own`
    /// was previously checked by `tree_predicate_map` in the parent's child
    /// subtree.  After descent, `map_full_tree` only covers the siblings (the
    /// taken child is `None`), so the path entries' properties are no longer
    /// covered by `map_full_tree`.  However, `regions` is unchanged since
    /// descent, so the properties still hold.
    pub proof fn cont_entries_metaregion(self, regions: MetaRegionOwners)
        requires
            self.inv(),
            self.metaregion_sound(regions),
        ensures
            forall|i: int|
                #![trigger self.continuations[i]]
                self.level - 1 <= i < NR_LEVELS
                    ==> self.continuations[i].entry_own.metaregion_sound(regions),
    {
        // Follows directly from path_metaregion_sound,
        // which is part of metaregion_sound.
    }

    pub open spec fn new(
        owner_subtree: OwnerSubtree<C>,
        idx: usize,
        guard: PageTableGuard<'rcu, C>,
    ) -> Self {
        let va = AbstractVaddr {
            offset: 0,
            index: Map::new(Set::<int>::range(0, NR_LEVELS as int), |i: int| 0).insert(
                NR_LEVELS - 1,
                idx as int,
            ),
            // Canonical-high-half shift for this config. `UserPtConfig` has
            // `LEADING_BITS_spec() == 0`, making this identical to the old
            // hard-coded 0 and preserving all existing user-cursor proofs.
            // `KernelPtConfig` has `LEADING_BITS_spec() == 0xffff`, putting
            // kernel cursors in the canonical upper half from construction.
            leading_bits: C::LEADING_BITS_spec() as int,
        };
        Self {
            level: NR_LEVELS as PagingLevel,
            continuations: Map::empty().insert(
                NR_LEVELS - 1 as int,
                CursorContinuation::new(owner_subtree, idx, guard),
            ),
            va,
            guard_level: NR_LEVELS as PagingLevel,
            prefix: va,
            popped_too_high: false,
        }
    }

    pub axiom fn tracked_new(
        tracked owner_subtree: OwnerSubtree<C>,
        idx: usize,
        guard: PageTableGuard<'rcu, C>,
    ) -> (tracked res: Self)
        ensures
            res == Self::new(owner_subtree, idx, guard),
    ;

    pub broadcast group group_lemmas {
        CursorOwner::lemma_view_mappings_contains,
        CursorOwner::lemma_view_mappings_intro,
    }
}

pub ghost struct CursorView<C: PageTableConfig> {
    pub cur_va: Vaddr,
    pub mappings: Set<Mapping>,
    pub phantom: PhantomData<C>,
}

impl<'rcu, C: PageTableConfig> View for CursorOwner<'rcu, C> {
    type V = CursorView<C>;

    open spec fn view(&self) -> Self::V {
        CursorView { cur_va: self.cur_va(), mappings: self.view_mappings(), phantom: PhantomData }
    }
}

impl<C: PageTableConfig> Inv for CursorView<C> {
    open spec fn inv(self) -> bool {
        &&& forall|m: Mapping|
            #![auto]
            self.mappings.contains(m)
                ==> m.inv()
        // Config-aware VA range: user page tables live in `[0, 2^47)`,
        // kernel page tables in `[0xffff_8000_…, usize::MAX]`, etc.
        // `vaddr_range_bounds_spec<C>` gives inclusive `(start, end_inclusive)`
        // bounds derived from `LEADING_BITS_spec` + `TOP_LEVEL_INDEX_RANGE_spec`,
        // so `Mapping::inv` can stay config-agnostic.
        &&& forall|m: Mapping|
            #![auto]
            self.mappings.contains(m) ==> {
                &&& vaddr_range_bounds_spec::<C>().0 <= m.va_range.start
                &&& m.va_range.end <= vaddr_range_bounds_spec::<C>().1 + 1
            }
        &&& self.non_overlapping()
    }
}

impl<C: PageTableConfig> CursorView<C> {
    /// Mappings in the view are non-overlapping. This is a consequence of the
    /// page table tree structure: distinct paths map to disjoint VA ranges.
    pub open spec fn non_overlapping(self) -> bool {
        forall|m: Mapping, n: Mapping|
            #![auto]
            self.mappings.contains(m) ==> self.mappings.contains(n) ==> m != n ==> m.va_range.end
                <= n.va_range.start || n.va_range.end <= m.va_range.start
    }
}

/// Every mapping in a cursor's view has its VA range within the page
/// table's managed range.
pub proof fn lemma_view_in_vaddr_range<'rcu, C: PageTableConfig>(owner: &CursorOwner<'rcu, C>)
    requires
        owner.inv(),
    ensures
        forall|m: Mapping|
            #![auto]
            owner.view_mappings().contains(m) ==> {
                &&& vaddr_range_bounds_spec::<C>().0 <= m.va_range.start
                &&& m.va_range.end <= vaddr_range_bounds_spec::<C>().1 + 1
            },
{
    C::lemma_page_table_config_constant_requirements();
    crate::mm::page_table::lemma_pte_index_consts::<C>();
    lemma_vaddr_range_bounds_spec_unfold::<C>();
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma2_to64_rest();
    vstd::arithmetic::power2::lemma_pow2_adds(
        (C::ADDRESS_WIDTH() as int - pte_index_bit_offset_spec::<C>(C::NR_LEVELS())) as nat,
        pte_index_bit_offset_spec::<C>(C::NR_LEVELS()) as nat,
    );
    vstd::layout::unsigned_int_max_values();

    let idx = C::TOP_LEVEL_INDEX_RANGE_spec();
    let start = idx.start as int;
    let end = idx.end as int;
    let lb = C::LEADING_BITS_spec() as int;
    let base = lb * 0x1_0000_0000_0000int;
    let cell = 0x80_0000_0000int;
    let bounds = vaddr_range_bounds_spec::<C>();

    let aw = C::ADDRESS_WIDTH() as nat;
    let top_w = (C::ADDRESS_WIDTH() as int - pte_index_bit_offset_spec::<C>(C::NR_LEVELS())) as nat;
    let p_aw = pow2(aw) as int;
    let p_top = pow2(top_w) as int;
    assert(end * cell <= p_aw) by (nonlinear_arith)
        requires
            end <= p_top,
            cell > 0,
            p_aw == p_top * cell,
    ;
    let start_pre = base + start * cell;
    let end_exclusive = base + end * cell;
    let end_pre = end_exclusive - 1;
    if C::LEADING_BITS_spec() == 0usize {
        assert(0 <= start_pre < 0x1_0000_0000_0000_0000int) by (nonlinear_arith)
            requires
                start_pre == start * cell,
                start >= 0,
                start < end,
                cell > 0,
                end * cell <= usize::MAX as int,
                (usize::MAX as int) < 0x1_0000_0000_0000_0000int,
        ;
        assert(0 <= end_pre <= usize::MAX) by (nonlinear_arith)
            requires
                end_pre == end * cell - 1,
                end > 0,
                cell > 0,
                end * cell <= usize::MAX as int,
        ;
    } else {
        assert(base == 0x1_0000_0000_0000_0000int - p_aw);
        assert(0 <= start_pre < 0x1_0000_0000_0000_0000int) by (nonlinear_arith)
            requires
                start_pre == 0x1_0000_0000_0000_0000int - p_aw + start * cell,
                base == 0x1_0000_0000_0000_0000int - p_aw,
                p_aw <= 0x1_0000_0000_0000_0000int,
                start >= 0,
                start < end,
                cell > 0,
                end * cell <= p_aw,
        ;
        assert(0 <= end_pre <= usize::MAX as int) by (nonlinear_arith)
            requires
                end_pre == 0x1_0000_0000_0000_0000int - p_aw + end * cell - 1,
                base == 0x1_0000_0000_0000_0000int - p_aw,
                end > 0,
                cell > 0,
                end * cell <= p_aw,
                p_aw <= 0x1_0000_0000_0000_0000int,
                usize::MAX == 0x1_0000_0000_0000_0000int - 1,
        ;
    }
    assert(bounds.0 as int == base + start * cell);
    assert(bounds.1 as int == base + end * cell - 1);

    assert forall|m: Mapping| #[trigger] owner.view_mappings().contains(m) implies {
        &&& vaddr_range_bounds_spec::<C>().0 <= m.va_range.start
        &&& m.va_range.end <= vaddr_range_bounds_spec::<C>().1 + 1
    } by {
        owner.lemma_view_mappings_contains();
        let i = choose|i: int|
            owner.level - 1 <= i < NR_LEVELS && (
            #[trigger] owner.continuations[i]).view_mappings().contains(m);
        owner.inv_continuation(i);
        let cont = owner.continuations[i];
        cont.lemma_view_mappings_contains();
        let j = choose|j: int|
            0 <= j < cont.children.len() && #[trigger] cont.children[j] is Some && PageTableOwner(
                cont.children[j].unwrap(),
            ).view_rec(cont.path().push_tail(j as usize)).contains(m);
        cont.pt_inv_children_unroll(j);
        cont.inv_children_rel_unroll(j);
        let child = PageTableOwner(cont.children[j].unwrap());
        let p = cont.path().push_tail(j as usize);
        cont.path().push_tail_property_len(j as usize);
        cont.path().push_tail_property_index(j as usize);
        let pidx = p.index(0) as int;
        assert(start <= pidx < end) by {
            if i != NR_LEVELS - 1 {
                assert(cont.path().index(0) == owner.continuations[NR_LEVELS - 1].idx) by {
                    owner.inv_continuation(NR_LEVELS - 1);
                    owner.continuations[NR_LEVELS - 1].path().push_tail_property_index(
                        owner.continuations[NR_LEVELS - 1].idx,
                    );
                    if i == 2 {
                    } else if i == 1 {
                        owner.continuations[2].path().push_tail_property_index(
                            owner.continuations[2].idx,
                        );
                    } else {
                        owner.continuations[2].path().push_tail_property_index(
                            owner.continuations[2].idx,
                        );
                        owner.continuations[1].path().push_tail_property_index(
                            owner.continuations[1].idx,
                        );
                    }
                }
            }
        }
        child.view_rec_top_index_va_bound(p, m, end);
    }
}

/// USER isolation theorem (proven, per-config): every mapping a `UserPtConfig`
/// cursor exposes lives strictly in the user low half `[0, 2^47)`. Discharges
/// the generic `axiom_view_in_vaddr_range` bound for `UserPtConfig`. The nested
/// `view_mappings → continuations → view_rec` decomposition
/// is exposed via `lemma_view_mappings_contains` (cursor + continuation forms)
/// before each `choose`; a contributing (frame/node) root child is neither
/// borrowed nor absent, so the cursor-inv top-level clause forces it in-range,
/// and `view_rec_top_index_va_bound` gives the per-mapping VA bound.
pub proof fn lemma_view_in_vaddr_range_user<'rcu>(
    owner: &CursorOwner<'rcu, crate::mm::vm_space::UserPtConfig>,
)
    requires
        owner.inv(),
    ensures
        forall|m: Mapping|
            #![auto]
            owner.view_mappings().contains(m) ==> {
                &&& 0 <= m.va_range.start
                &&& m.va_range.end <= 0x8000_0000_0000int
            },
{
    let end = crate::mm::vm_space::UserPtConfig::TOP_LEVEL_INDEX_RANGE_spec().end as int;
    assert(end == 256);
    assert(end * 0x80_0000_0000int == 0x8000_0000_0000int) by (nonlinear_arith)
        requires
            end == 256,
    ;
    assert forall|m: Mapping| #[trigger] owner.view_mappings().contains(m) implies {
        &&& 0 <= m.va_range.start
        &&& m.va_range.end <= 0x8000_0000_0000int
    } by {
        owner.lemma_view_mappings_contains();
        let i = choose|i: int|
            owner.level - 1 <= i < NR_LEVELS && (
            #[trigger] owner.continuations[i]).view_mappings().contains(m);
        owner.inv_continuation(i);
        let cont = owner.continuations[i];
        cont.lemma_view_mappings_contains();
        let j = choose|j: int|
            0 <= j < cont.children.len() && #[trigger] cont.children[j] is Some && PageTableOwner(
                cont.children[j].unwrap(),
            ).view_rec(cont.path().push_tail(j as usize)).contains(m);
        cont.pt_inv_children_unroll(j);
        cont.inv_children_rel_unroll(j);
        let child = PageTableOwner(cont.children[j].unwrap());
        let p = cont.path().push_tail(j as usize);
        cont.path().push_tail_property_index(j as usize);
        assert(0 <= (p.index(0) as int) < end) by {
            if i == NR_LEVELS - 1 {
                // Root continuation: `p == [j]`. A contributing child is a
                // frame/node (borrowed/absent give an empty `view_rec`), hence
                // neither borrowed nor absent; the cursor-inv top-level clause
                // then forces `j ∈ [0, 256)`.
                assert(cont.path().len() == 0);
                assert(p.index(0) == j);
                assert(child.0.value.is_frame() || child.0.value.is_node());
                assert(!child.0.value.is_borrowed());
                assert(!child.0.value.is_absent());
                assert(0 <= j < end);
            } else {
                // Non-root continuation: `p.index(0) == cont.path().index(0)`,
                // which (via the inv path chain) equals the root continuation's
                // descended index, in `[0, 256)` by the cursor-inv idx clause.
                assert(cont.path().len() > 0);
                assert(p.index(0) == cont.path().index(0));
                assert(cont.path().index(0) == owner.continuations[NR_LEVELS - 1].idx) by {
                    owner.inv_continuation(NR_LEVELS - 1);
                    owner.continuations[NR_LEVELS - 1].path().push_tail_property_index(
                        owner.continuations[NR_LEVELS - 1].idx,
                    );
                    if i == 2 {
                    } else if i == 1 {
                        owner.continuations[2].path().push_tail_property_index(
                            owner.continuations[2].idx,
                        );
                    } else {
                        owner.continuations[2].path().push_tail_property_index(
                            owner.continuations[2].idx,
                        );
                        owner.continuations[1].path().push_tail_property_index(
                            owner.continuations[1].idx,
                        );
                    }
                }
                assert(0 <= owner.continuations[NR_LEVELS - 1].idx < end);
            }
        }
        child.view_rec_top_index_va_bound(p, m, end);
    }
}

/// KERNEL isolation theorem (proven, per-config): every mapping a
/// `KernelPtConfig` cursor exposes lives in the kernel high half. Mirror of
/// `lemma_view_in_vaddr_range_user` with `TOP_LEVEL_INDEX_RANGE == 256..512` and
/// `LEADING_BITS == 0xffff` (canonical high-half base).
pub proof fn lemma_view_in_vaddr_range_kernel<'rcu>(
    owner: &CursorOwner<'rcu, crate::mm::kspace::KernelPtConfig>,
)
    requires
        owner.inv(),
    ensures
        forall|m: Mapping|
            #![auto]
            owner.view_mappings().contains(m) ==> {
                &&& vaddr_range_bounds_spec::<crate::mm::kspace::KernelPtConfig>().0
                    <= m.va_range.start
                &&& m.va_range.end <= vaddr_range_bounds_spec::<
                    crate::mm::kspace::KernelPtConfig,
                >().1 + 1
            },
{
    crate::mm::page_table::lemma_vaddr_range_bounds_spec_kernel();
    let start = crate::mm::kspace::KernelPtConfig::TOP_LEVEL_INDEX_RANGE_spec().start as int;
    let end = crate::mm::kspace::KernelPtConfig::TOP_LEVEL_INDEX_RANGE_spec().end as int;
    let lb = crate::mm::kspace::KernelPtConfig::LEADING_BITS_spec() as int;
    assert(start == 256);
    assert(end == 512);
    assert(lb == 0xffff);
    // bound == (256·2^39 + 0xffff·2^48, 512·2^39 + 0xffff·2^48 - 1)
    //       == (0xFFFF_8000_0000_0000, 0xFFFF_FFFF_FFFF_FFFF).
    assert(start * 0x80_0000_0000int + lb * 0x1_0000_0000_0000int == 0xFFFF_8000_0000_0000int)
        by (nonlinear_arith)
        requires
            start == 256,
            lb == 0xffff,
    ;
    assert(end * 0x80_0000_0000int + lb * 0x1_0000_0000_0000int == 0x1_0000_0000_0000_0000int)
        by (nonlinear_arith)
        requires
            end == 512,
            lb == 0xffff,
    ;
    assert forall|m: Mapping| #[trigger] owner.view_mappings().contains(m) implies {
        &&& vaddr_range_bounds_spec::<crate::mm::kspace::KernelPtConfig>().0 <= m.va_range.start
        &&& m.va_range.end <= vaddr_range_bounds_spec::<crate::mm::kspace::KernelPtConfig>().1 + 1
    } by {
        owner.lemma_view_mappings_contains();
        let i = choose|i: int|
            owner.level - 1 <= i < NR_LEVELS && (
            #[trigger] owner.continuations[i]).view_mappings().contains(m);
        owner.inv_continuation(i);
        let cont = owner.continuations[i];
        cont.lemma_view_mappings_contains();
        let j = choose|j: int|
            0 <= j < cont.children.len() && #[trigger] cont.children[j] is Some && PageTableOwner(
                cont.children[j].unwrap(),
            ).view_rec(cont.path().push_tail(j as usize)).contains(m);
        cont.pt_inv_children_unroll(j);
        cont.inv_children_rel_unroll(j);
        let child = PageTableOwner(cont.children[j].unwrap());
        let p = cont.path().push_tail(j as usize);
        cont.path().push_tail_property_index(j as usize);
        assert(start <= (p.index(0) as int) < end) by {
            if i == NR_LEVELS - 1 {
                // Root: `p == [j]`. A contributing child is a frame/node (not
                // borrowed/absent, else empty `view_rec`); the cursor-inv
                // top-level clause then forces `j ∈ [256, 512)`.
                assert(cont.path().len() == 0);
                assert(p.index(0) == j);
                assert(child.0.value.is_frame() || child.0.value.is_node());
                assert(!child.0.value.is_borrowed());
                assert(!child.0.value.is_absent());
                assert(start <= j < end);
            } else {
                // Non-root: `p.index(0) == cont.path().index(0) == root.idx ∈
                // [256, 512)` (path chain + cursor-inv idx clause).
                assert(cont.path().len() > 0);
                assert(p.index(0) == cont.path().index(0));
                assert(cont.path().index(0) == owner.continuations[NR_LEVELS - 1].idx) by {
                    owner.inv_continuation(NR_LEVELS - 1);
                    owner.continuations[NR_LEVELS - 1].path().push_tail_property_index(
                        owner.continuations[NR_LEVELS - 1].idx,
                    );
                    if i == 2 {
                    } else if i == 1 {
                        owner.continuations[2].path().push_tail_property_index(
                            owner.continuations[2].idx,
                        );
                    } else {
                        owner.continuations[2].path().push_tail_property_index(
                            owner.continuations[2].idx,
                        );
                        owner.continuations[1].path().push_tail_property_index(
                            owner.continuations[1].idx,
                        );
                    }
                }
                assert(start <= owner.continuations[NR_LEVELS - 1].idx < end);
            }
        }
        child.view_rec_top_index_va_bound(p, m, end);
        // m.start ≥ index(0)·2^39 + lb·2^48 ≥ start·2^39 + lb·2^48 = bound.0.
        assert((p.index(0) as int) * 0x80_0000_0000int + lb * 0x1_0000_0000_0000int >= start
            * 0x80_0000_0000int + lb * 0x1_0000_0000_0000int) by (nonlinear_arith)
            requires
                start <= p.index(0) as int,
        ;
    }
}

impl<'rcu, C: PageTableConfig> InvView for CursorOwner<'rcu, C> {
    proof fn view_preserves_inv(self) {
        // (1) Non-overlapping: tree collapse + view_rec_disjoint_vaddrs.
        self.view_non_overlapping();
        // (2) Per-mapping `Mapping::inv()`: page_size ∈ {4K,2M,1G}, PA/VA
        //     alignment, PA/VA size equal page_size, and PA bound.
        self.view_mapping_inv();
        // (4) Config-aware VA bound: every mapping's VA range is contained
        //     in `vaddr_range_bounds_spec::<C>()`.
        lemma_view_in_vaddr_range::<C>(&self);
    }
}

impl<'rcu, C: PageTableConfig> CursorOwner<'rcu, C> {
    /// The cursor's view has non-overlapping mappings. This follows from the
    /// tree structure alone: `as_page_table_owner_preserves_view_mappings`
    /// collapses the union-over-continuations view into a single root-rooted
    /// `view_rec`, after which `view_rec_disjoint_vaddrs` gives pairwise
    /// disjointness directly.
    pub proof fn view_non_overlapping(self)
        requires
            self.inv(),
        ensures
            self@.non_overlapping(),
    {
        self.as_page_table_owner_view_non_overlapping();
    }
}

impl<'rcu, C: PageTableConfig, A: InAtomicMode> Inv for Cursor<'rcu, C, A> {
    open spec fn inv(self) -> bool {
        // `level <= NR_LEVELS + 1` (not `<= NR_LEVELS`), mirroring the
        // `guard_level + 1` slack below: it admits the transient "popped
        // past the root" state without constraining anything (the
        // weakening is zero-blast-radius). A drifted lock-from-root
        // cursor that ascends past the root would, on the next
        // `pop_level`, read `self.path[NR_LEVELS]` — out of bounds, a
        // real Rust panic — which `jump` models as a sound divergence.
        &&& 1 <= self.level <= NR_LEVELS
            + 1
        // `level <= guard_level + 1` (not `<= guard_level`) admits the
        // transient "popped one above the guard" state: `pop_level` at
        // `level == guard_level` legitimately yields `level == guard_level
        // + 1` (real Rust does not panic there — the guard-node lock slot
        // is still `Some`). The next `pop_level` on such a cursor reads a
        // `None` path slot (`level > guard_level`, by `wf`) and diverges,
        // so the state never propagates further.
        &&& self.level <= self.guard_level + 1
        &&& self.guard_level
            <= NR_LEVELS
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
        &&& owner.guard_level
            == self.guard_level
        //        &&& owner.index() == self.va % page_size(self.level)
        // `path` holds lock guards only for levels in `[self.level,
        // self.guard_level]` (see the `Cursor.path` doc comment and
        // `locking.rs`: `lock_range` only locks the subtree rooted at
        // `guard_level`). The ghost `continuations` chain still extends above
        // `guard_level` up to the root, but those ancestor nodes are NOT
        // locked, so their `path` slots are `None` and are not tied to a
        // continuation guard.
        &&& self.level <= 4 ==> {
            &&& 4 <= self.guard_level ==> {
                &&& self.path[3] is Some
                &&& owner.continuations.contains_key(3)
                &&& owner.continuations[3].guard == self.path[3]->0
            }
            &&& 4 > self.guard_level ==> self.path[3] is None
        }
        &&& self.level <= 3 ==> {
            &&& 3 <= self.guard_level ==> {
                &&& self.path[2] is Some
                &&& owner.continuations.contains_key(2)
                &&& owner.continuations[2].guard == self.path[2]->0
            }
            &&& 3 > self.guard_level ==> self.path[2] is None
        }
        &&& self.level <= 2 ==> {
            &&& 2 <= self.guard_level ==> {
                &&& self.path[1] is Some
                &&& owner.continuations.contains_key(1)
                &&& owner.continuations[1].guard == self.path[1]->0
            }
            &&& 2 > self.guard_level ==> self.path[1] is None
        }
        &&& self.level == 1 ==> {
            // `1 <= self.guard_level` always holds (`inv` gives
            // `guard_level >= 1`), so this clause is equivalent to the
            // original level-1 case; the `None` branch is vacuous.
            &&& 1 <= self.guard_level ==> {
                &&& self.path[0] is Some
                &&& owner.continuations.contains_key(0)
                &&& owner.continuations[0].guard == self.path[0]->0
            }
            &&& 1 > self.guard_level ==> self.path[0] is None
        }
        &&& self.barrier_va.start == owner.locked_range().start
        &&& self.barrier_va.end == owner.locked_range().end
    }
}

} // verus!
