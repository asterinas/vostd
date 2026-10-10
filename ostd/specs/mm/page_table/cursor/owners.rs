use vstd::{
    arithmetic::{
        div_mod::{lemma_div_non_zero, lemma_fundamental_div_mod},
        mul::lemma_mul_is_commutative,
        power2::pow2,
    },
    bits::lemma_usize_shr_is_div,
    prelude::*,
    seq_lib::*,
    set::lemma_set_contains_len,
};
use vstd_extra::{
    drop_tracking::*,
    ghost_tree::*,
    ownership::*,
    panic::may_panic,
    prelude::*,
    seq_extra::{forall_seq, lemma_forall_seq_index},
};

use crate::specs::{
    arch::*,
    mm::{
        frame::{
            mapping::{frame_to_index, index_to_meta},
            meta_owners::MetaSlotStorage,
            meta_region_owners::MetaRegionOwners,
        },
        page_table::{
            Guards, Mapping, lemma_aligned_vaddr_slack, lemma_inc_slot_indices,
            lemma_lower_indices_aligned, lemma_page_size_base, lemma_page_size_divides,
            lemma_page_size_ge_base, lemma_page_size_is_pow2_pte_index_bit_offset,
            lemma_page_size_next, lemma_pte_index_bound, lemma_vaddr_range_spec_kernel,
            lemma_vaddr_range_spec_user, lemma_vaddr_upper_part_is_align_down, owners::*,
            page_table_vaddr_bits_spec, pte_index_bit_offset_spec, pte_index_spec,
            vaddr_range_spec, vaddr_replace_pte_index_spec, vaddr_upper_bits_spec,
            vaddr_upper_part_spec,
        },
    },
    task::InAtomicMode,
};

use crate::arch::mm::PagingConsts;
use crate::mm::{
    MAX_USERSPACE_VADDR, Paddr, PagingConstsTrait, PagingLevel, Vaddr,
    frame::{
        Frame,
        meta::{REF_COUNT_MAX, REF_COUNT_UNIQUE, REF_COUNT_UNUSED},
    },
    kspace::KernelPtConfig,
    nr_subpage_per_huge,
    page_prop::PageProperty,
    page_size,
    page_table::*,
};
use core::{marker::PhantomData, ops::Range};

verus! {

broadcast use group_ghost_tree_lemmas;

pub tracked struct CursorContinuation<'rcu, C: PageTableConfig> {
    pub entry_own: EntryOwner<C>,
    pub ghost idx: usize,
    pub ghost tree_level: nat,
    pub children: Seq<Option<OwnerSubtree<C>>>,
    pub ghost path: TreePath<NR_ENTRIES>,
    pub ghost guard: PageTableGuard<'rcu, C>,
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

    /// Taking a child preserves the continuation invariant.
    pub proof fn take_child_preserves_inv(self)
        requires
            self.inv(),
            self.idx < self.children.len(),
            self.children[self.idx as int] is Some,
        ensures
            self.take_child().1.inv(),
    {
    }

    pub open spec fn make_cont(self, idx: usize, guard: PageTableGuard<'rcu, C>) -> (Self, Self) {
        let child = Self {
            entry_own: self.children[self.idx as int]->0.value(),
            tree_level: (self.tree_level + 1) as nat,
            idx: idx,
            children: self.children[self.idx as int]->0.children(),
            path: self.path.push_tail(self.idx as int),
            guard: guard,
        };
        let cont = Self { children: self.children.update(self.idx as int, None), ..self };
        (child, cont)
    }

    pub proof fn tracked_make_cont(
        tracked &mut self,
        idx: usize,
        guard: PageTableGuard<'rcu, C>,
    ) -> (tracked res: Self)
        requires
            old(self).all_some(),
            old(self).children.len() == NR_ENTRIES,
            old(self).idx < NR_ENTRIES,
            idx < NR_ENTRIES,
        ensures
            res == old(self).make_cont(idx, guard).0,
            *final(self) == old(self).make_cont(idx, guard).1,
    {
        lemma_update_is_remove_insert(self.children, old(self).idx as int, None);
        let tracked child = self.children.tracked_remove(old(self).idx as int).tracked_unwrap();
        self.children.tracked_insert(old(self).idx as int, None);
        let tracked (entry_own, children) = child.tracked_into_parts();
        Self {
            entry_own,
            tree_level: (old(self).tree_level + 1) as nat,
            idx,
            children,
            path: old(self).path.push_tail(old(self).idx as int),
            guard,
        }
    }

    pub open spec fn restore(self, child: Self) -> (Self, PageTableGuard<'rcu, C>) {
        let child_node = OwnerSubtree::new(child.entry_own, child.tree_level, child.children);
        (
            Self { children: self.children.update(self.idx as int, Some(child_node)), ..self },
            child.guard,
        )
    }

    pub proof fn tracked_restore(tracked &mut self, tracked child: Self) -> (guard: PageTableGuard<
        'rcu,
        C,
    >)
        requires
            old(self).idx < old(self).children.len(),
        ensures
            *final(self) == old(self).restore(child).0,
            guard == old(self).restore(child).1,
    {
        let tracked child_node = OwnerSubtree::tracked_new(
            child.entry_own,
            child.tree_level,
            child.children,
        );
        lemma_update_is_remove_insert(self.children, self.idx as int, Some(child_node));
        let _ = self.children.tracked_remove(self.idx as int);
        self.children.tracked_insert(self.idx as int, Some(child_node));
        child.guard
    }

    pub open spec fn new(
        owner_subtree: OwnerSubtree<C>,
        idx: usize,
        guard: PageTableGuard<'rcu, C>,
    ) -> Self {
        Self {
            entry_own: owner_subtree.value(),
            idx: idx,
            tree_level: owner_subtree.level(),
            children: owner_subtree.children(),
            path: TreePath::new(Seq::empty()),
            guard: guard,
        }
    }

    pub proof fn tracked_new(
        tracked owner_subtree: OwnerSubtree<C>,
        idx: usize,
        guard: PageTableGuard<'rcu, C>,
    ) -> tracked Self
        returns
            Self::new(owner_subtree, idx, guard),
    {
        let ghost tree_level = owner_subtree.level();
        let tracked (entry_own, children) = owner_subtree.tracked_into_parts();
        Self { entry_own, idx, tree_level, children, path: TreePath::new(Seq::empty()), guard }
    }

    /// Every present child subtree satisfies `f` at its corresponding tree path.
    #[verifier::opaque]
    pub open spec fn map_children(
        self,
        f: spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool,
    ) -> bool {
        forall|i: int|
            #![trigger(self.children[i])]
            0 <= i < self.children.len() ==> self.children[i] is Some
                ==> self.children[i]->0.subtree_satisfies(self.path().push_tail(i), f)
    }

    /// Extracts one child's property without exposing the sibling quantifier.
    pub proof fn lemma_map_children_unroll(
        self,
        f: spec_fn(EntryOwner<C>, TreePath<NR_ENTRIES>) -> bool,
        i: int,
    )
        requires
            self.map_children(f),
            0 <= i < self.children.len(),
            self.children[i] is Some,
        ensures
            self.children[i]->0.subtree_satisfies(self.path().push_tail(i), f),
    {
        reveal(CursorContinuation::map_children);
    }

    // map_children_lift, map_children_lift_skip_idx, as_subtree_restore
    // have been moved to tree_lemmas.rs.
    pub open spec fn level(self) -> PagingLevel {
        self.entry_own.node().level()
    }

    pub open spec fn inv_children(self) -> bool {
        self.children.all(|child: Option<OwnerSubtree<C>>| child is Some ==> child->0.inv())
    }

    pub proof fn lemma_inv_children_unroll(self, i: int)
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

    pub proof fn lemma_inv_children_unroll_all(self)
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
            self.lemma_inv_children_unroll(i)
        }
    }

    pub open spec fn inv_children_rel_pred(self) -> spec_fn(int, Option<OwnerSubtree<C>>) -> bool {
        |i: int, child: Option<OwnerSubtree<C>>|
            {
                child is Some ==> {
                    &&& child->0.value().parent_level == self.level()
                    &&& child->0.level() == self.tree_level + 1
                    &&& child->0.value().path.len() == self.entry_own.node().tree_level + 1
                    &&& child->0.value().match_pte(
                        self.entry_own.node().children_perm.value()[i],
                        self.entry_own.node().level(),
                    )
                    &&& child->0.value().path == self.path().push_tail(i)
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

    pub proof fn lemma_pt_inv_children_unroll(self, i: int)
        requires
            self.pt_inv_children(),
            0 <= i < self.children.len(),
            self.children[i] is Some,
        ensures
            PageTableOwner(self.children[i]->0).pt_inv(),
    {
    }

    pub proof fn lemma_inv_children_rel_unroll(self, i: int)
        requires
            self.inv_children_rel(),
            0 <= i < self.children.len(),
            self.children[i] is Some,
        ensures
            self.children[i]->0.value().parent_level == self.level(),
            self.children[i]->0.level() == self.tree_level + 1,
            self.children[i]->0.value().path.len() == self.entry_own.node().tree_level + 1,
            self.children[i]->0.value().match_pte(
                self.entry_own.node().children_perm.value()[i],
                self.entry_own.node().level(),
            ),
            self.children[i]->0.value().path == self.path().push_tail(i),
    {
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

    pub open spec fn node_locked(self, guards: Guards) -> bool {
        guards.lock_held(self.guard.inner.inner@.ptr.addr())
    }

    pub open spec fn view_mappings(self) -> Set<Mapping> {
        self.children.map(
            |i, child: Option<OwnerSubtree<C>>|
                if child is Some {
                    PageTableOwner(child->0).view_rec(self.path().push_tail(i))
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
                    ).view_rec(self.path().push_tail(i)).contains(m),
    {
        broadcast use vstd::seq_lib::group_seq_properties;

    }

    pub broadcast proof fn lemma_view_mappings_intro(self, m: Mapping, i: int)
        requires
            0 <= i < self.children.len(),
            self.children[i] is Some,
            #[trigger] PageTableOwner(self.children[i]->0).view_rec(
                self.path().push_tail(i),
            ).contains(m),
        ensures
            self.view_mappings().contains(m),
    {
        broadcast use vstd::seq_lib::group_seq_properties;

        let mapped = self.children.map(
            |i, child: Option<OwnerSubtree<C>>|
                if child is Some {
                    PageTableOwner(child->0).view_rec(self.path().push_tail(i))
                } else {
                    Set::empty()
                },
        );
        assert(mapped.to_set().contains(mapped[i]));
    }

    pub open spec fn as_subtree(self) -> OwnerSubtree<C> {
        OwnerSubtree::new(self.entry_own, self.tree_level, self.children)
    }

    pub open spec fn as_page_table_owner(self) -> PageTableOwner<C> {
        PageTableOwner(self.as_subtree())
    }

    pub open spec fn view_mappings_take_child_spec(self) -> Set<Mapping> {
        PageTableOwner(self.children[self.idx as int]->0).view_rec(
            self.path().push_tail(self.idx as int),
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
    pub proof fn lemma_rel_children_from_node_matching(
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
            child_value.path == entry_own.path.push_tail(idx as int),
            child_value.path.len() == parent_owner.tree_level + 1,
        ensures
            child_value.path.len() == parent_owner.tree_level + 1,
            child_value.match_pte(
                parent_owner.children_perm.value()[idx as int],
                parent_owner.level(),
            ),
            child_value.path == entry_own.path.push_tail(idx as int),
            child_value.parent_level == parent_owner.level(),
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
    pub proof fn lemma_continuation_inv_holds_after_child_restore(
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
            self.entry_own.node().level() == parent_old.level(),
            self.entry_own.node().tree_level == parent_old.tree_level,
            // Other PTEs preserved (operation only touched the entry at idx)
            forall|j: int|
                0 <= j < NR_ENTRIES && j != self.idx
                    ==> #[trigger] self.entry_own.node().children_perm.value()[j]
                    == parent_old.children_perm.value()[j],
            // Children at j != idx untouched
            forall|j: int|
                0 <= j < NR_ENTRIES && j != self.idx ==> #[trigger] self.children[j]
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
            self.children[self.idx as int]->0.value().parent_level == self.level(),
            self.children[self.idx as int]->0.value().path == self.path().push_tail(
                self.idx as int,
            ),
            self.children[self.idx as int]->0.level() == self.tree_level + 1,
            self.children[self.idx as int]->0.value().path.len() == self.entry_own.node().tree_level
                + 1,
            self.children[self.idx as int]->0.value().match_pte(
                self.entry_own.node().children_perm.value()[self.idx as int],
                self.entry_own.node().level(),
            ),
            // The new child satisfies the PT-specific tree invariant. This is
            // operation-specific (alloc_if_none/protect/split_if_mapped_huge/
            // replace each establish it differently) so it's lifted to a
            // precondition rather than discharged here.
            PageTableOwner(self.children[self.idx as int]->0).pt_inv(),
        ensures
            self.inv(),
    {
    }

    pub proof fn tracked_new_child(
        tracked &self,
        paddr: Paddr,
        prop: PageProperty,
        tracked permission: Option<C::Perm>,
        tracked regions: &mut MetaRegionOwners,
    ) -> (tracked res: OwnerSubtree<C>)
        requires
            self.inv(),
            self.level() < NR_LEVELS,
            old(regions).slots.contains_key(frame_to_index(paddr)),
            valid_frame_paddr(paddr),
            paddr % page_size::<PagingConsts>(self.level()) == 0,
            paddr + page_size::<PagingConsts>(self.level()) <= MAX_PADDR,
            C::raw_item_well_formed((paddr, self.level(), prop, Tracked(permission))),
            C::E::new_page_req(paddr, self.level(), prop),
            self.path().push_tail(self.idx as int).inv(),
        ensures
            final(regions).slot_owners == old(regions).slot_owners,
            final(regions).slots == old(regions).slots,
            // Allocating a child doesn't touch the segment obligation ledger.
            res.value() == EntryOwner::<C>::new_frame(
                paddr,
                self.path().push_tail(self.idx as int),
                self.level(),
                prop,
                permission,
            ),
            res.inv(),
            res.level() == self.tree_level + 1,
            res == OwnerSubtree::new_val(res.value(), res.level() as nat),
    {
        let tracked mut owner = EntryOwner::<C>::tracked_new_frame(
            paddr,
            self.path().push_tail(self.idx as int),
            self.level(),
            prop,
            permission,
        );
        OwnerSubtree::tracked_new_val(owner, self.tree_level + 1)
    }

    pub broadcast group group_lemmas {
        CursorContinuation::lemma_view_mappings_contains,
        CursorContinuation::lemma_view_mappings_intro,
    }
}

pub tracked struct CursorOwner<'rcu, C: PageTableConfig> {
    pub ghost level: PagingLevel,
    pub continuations: Map<int, CursorContinuation<'rcu, C>>,
    pub ghost va: Vaddr,
    pub ghost guard_level: PagingLevel,
    pub ghost prefix: Vaddr,
    pub ghost popped_too_high: bool,
}

impl<'rcu, C: PageTableConfig> Inv for CursorOwner<'rcu, C> {
    open spec fn inv(self) -> bool {
        &&& self.va % C::BASE_PAGE_SIZE() == 0
        &&& 1 <= self.level <= NR_LEVELS
        &&& 1 <= self.guard_level
            <= NR_LEVELS
        // The top-level index of the cursor's VA must be within the page table config's
        // managed range. This ensures cursors for UserPtConfig and KernelPtConfig operate
        // on disjoint portions of the virtual address space.
        &&& C::TOP_LEVEL_INDEX_RANGE().start <= pte_index_spec::<C>(
            self.va,
            (NR_LEVELS - 1 + 1) as PagingLevel,
        )
        // The top index may equal TOP_LEVEL_INDEX_RANGE.end as a "one-past-end"
        // sentinel meaning the cursor has been advanced past the very last in-range
        // top-level slot. In this state the cursor is `above_locked_range`.
        &&& pte_index_spec::<C>(self.va, (NR_LEVELS - 1 + 1) as PagingLevel)
            <= C::TOP_LEVEL_INDEX_RANGE().end
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
            &&& C::TOP_LEVEL_INDEX_RANGE().start <= self.continuations[NR_LEVELS - 1].idx
            &&& self.continuations[NR_LEVELS - 1].idx < C::TOP_LEVEL_INDEX_RANGE().end
        }
        &&& forall|j: int|
            #![trigger self.continuations[NR_LEVELS - 1].children[j]]
            0 <= j < NR_ENTRIES && !(C::TOP_LEVEL_INDEX_RANGE().start <= j
                < C::TOP_LEVEL_INDEX_RANGE().end) ==> self.continuations[NR_LEVELS
                - 1].children[j] is Some ==> (self.continuations[NR_LEVELS
                - 1].children[j].unwrap().value().is_borrowed() || self.continuations[NR_LEVELS
                - 1].children[j].unwrap().value().is_absent())
        &&& self.prefix % C::BASE_PAGE_SIZE() == 0
        &&& forall|i: int|
            1 <= i <= self.guard_level ==> #[trigger] pte_index_spec::<C>(
                self.prefix,
                i as PagingLevel,
            )
                == 0
            // The prefix's top-level index is within the configured page-table range.
            // This is established at construction (when prefix == va, which itself starts
            // strictly in-range) and preserved by all cursor operations (none touch prefix).
        &&& pte_index_spec::<C>(self.prefix, (NR_LEVELS - 1 + 1) as PagingLevel)
            >= C::TOP_LEVEL_INDEX_RANGE().start
        &&& pte_index_spec::<C>(self.prefix, (NR_LEVELS - 1 + 1) as PagingLevel)
            < C::TOP_LEVEL_INDEX_RANGE().end
        // Top-of-address-space sentinel reservation: none of our `PtConfig`s actually use
        // the very last index. The first half of the address space
        &&& pte_index_spec::<C>(self.prefix, (NR_LEVELS - 1 + 1) as PagingLevel) + 1
            < NR_ENTRIES
        // Locked range stays within the config's managed VA space. Established at
        // cursor construction (barrier_va == *va with is_valid_range_spec(va)) and
        // preserved by all cursor operations since they don't modify prefix/guard_level.
        &&& self.locked_range().end <= vaddr_range_spec::<C>().end
            + 1
        // Per-config tightening: e.g. `KernelPtConfig` overrides this to
        // `FRAME_METADATA_BASE_VADDR`, which the kvirt allocator enforces and
        // is what `move_forward` uses to prove `prefix.idx[NR_LEVELS-1] + 1
        // < NR_ENTRIES` at the wrap-pop boundary. Default is trivial.
        &&& self.locked_range().end
            <= C::LOCKED_END_BOUND_spec()
        // The cursor stays within the same canonical half of the address
        // space as its prefix — so `leading_bits` agrees throughout traversal.
        &&& vaddr_upper_bits_spec::<C>(self.va) == vaddr_upper_bits_spec::<C>(
            self.prefix,
        )
        // Established at construction (new initializes both va and
        // prefix with LEADING_BITS_spec()) and preserved by cursor ops.
        &&& vaddr_upper_bits_spec::<C>(self.prefix) == C::LEADING_BITS_spec()
        &&& self.level <= self.guard_level ==> forall|i: int|
            #![trigger self.continuations[i].idx]
            self.guard_level <= i < NR_LEVELS ==> self.continuations[i].idx == pte_index_spec::<C>(
                self.prefix,
                (i + 1) as PagingLevel,
            )
        // The cursor's VA shares upper indices with the prefix when the
        // cursor hasn't popped above guard_level AND is either in_locked_range
        // OR strictly below guard_level. The wrap branch of
        // `move_forward_owner_spec` (level == guard_level && idx+1 ==
        // NR_ENTRIES) advances `va` past the prefix's chunk; that state has
        // `level == guard_level` and `above_locked_range`, and is excluded
        // from this clause.
        &&& !self.popped_too_high && (self.in_locked_range() || self.level < self.guard_level)
            ==> forall|i: int|
            self.guard_level <= i < NR_LEVELS ==> #[trigger] pte_index_spec::<C>(
                self.va,
                (i + 1) as PagingLevel,
            ) == pte_index_spec::<C>(self.prefix, (i + 1) as PagingLevel)
        &&& !self.popped_too_high && self.guard_level >= 1 && self.level < self.guard_level
            ==> pte_index_spec::<C>(self.va, (self.guard_level - 1 + 1) as PagingLevel)
            == pte_index_spec::<C>(self.prefix, (self.guard_level - 1 + 1) as PagingLevel)
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
            &&& self.in_locked_range() ==> pte_index_spec::<C>(self.va, (3 + 1) as PagingLevel)
                == self.continuations[3].idx
        }
        &&& self.level <= 3 ==> {
            &&& self.continuations.contains_key(2)
            &&& self.continuations[2].inv()
            &&& self.continuations[2].level() == 3
            &&& self.continuations[2].entry_own.parent_level == 4
            &&& self.in_locked_range() ==> pte_index_spec::<C>(self.va, (2 + 1) as PagingLevel)
                == self.continuations[2].idx
            &&& self.continuations[2].guard.inner.inner@.ptr.addr()
                != self.continuations[3].guard.inner.inner@.ptr.addr()
            // Path consistency: child path = parent path pushed with parent's index
            &&& self.continuations[2].path() == self.continuations[3].path().push_tail(
                self.continuations[3].idx as int,
            )
            // PTE consistency
            &&& self.continuations[2].entry_own.path.len()
                == self.continuations[3].entry_own.node().tree_level + 1
            &&& self.continuations[2].entry_own.match_pte(
                self.continuations[3].entry_own.node().children_perm.value()[self.continuations[3].idx as int],
                self.continuations[3].entry_own.node().level(),
            )
            &&& self.continuations[2].entry_own.parent_level
                == self.continuations[3].entry_own.node().level()
        }
        &&& self.level <= 2 ==> {
            &&& self.continuations.contains_key(1)
            &&& self.continuations[1].inv()
            &&& self.continuations[1].level() == 2
            &&& self.continuations[1].entry_own.parent_level == 3
            &&& self.in_locked_range() ==> pte_index_spec::<C>(self.va, (1 + 1) as PagingLevel)
                == self.continuations[1].idx
            &&& self.continuations[1].guard.inner.inner@.ptr.addr()
                != self.continuations[2].guard.inner.inner@.ptr.addr()
            &&& self.continuations[1].guard.inner.inner@.ptr.addr()
                != self.continuations[3].guard.inner.inner@.ptr.addr()
            // Path consistency: child path = parent path pushed with parent's index
            &&& self.continuations[1].path() == self.continuations[2].path().push_tail(
                self.continuations[2].idx as int,
            )
            // PTE consistency
            &&& self.continuations[1].entry_own.path.len()
                == self.continuations[2].entry_own.node().tree_level + 1
            &&& self.continuations[1].entry_own.match_pte(
                self.continuations[2].entry_own.node().children_perm.value()[self.continuations[2].idx as int],
                self.continuations[2].entry_own.node().level(),
            )
            &&& self.continuations[1].entry_own.parent_level
                == self.continuations[2].entry_own.node().level()
        }
        &&& self.level == 1 ==> {
            &&& self.continuations.contains_key(0)
            &&& self.continuations[0].inv()
            &&& self.continuations[0].level() == 1
            &&& self.continuations[0].entry_own.parent_level == 2
            &&& self.in_locked_range() ==> pte_index_spec::<C>(self.va, (0 + 1) as PagingLevel)
                == self.continuations[0].idx
            &&& self.continuations[0].guard.inner.inner@.ptr.addr()
                != self.continuations[1].guard.inner.inner@.ptr.addr()
            &&& self.continuations[0].guard.inner.inner@.ptr.addr()
                != self.continuations[2].guard.inner.inner@.ptr.addr()
            &&& self.continuations[0].guard.inner.inner@.ptr.addr()
                != self.continuations[3].guard.inner.inner@.ptr.addr()
            // Path consistency: child path = parent path pushed with parent's index
            &&& self.continuations[0].path() == self.continuations[1].path().push_tail(
                self.continuations[1].idx as int,
            )
            // PTE consistency
            &&& self.continuations[0].entry_own.path.len()
                == self.continuations[1].entry_own.node().tree_level + 1
            &&& self.continuations[0].entry_own.match_pte(
                self.continuations[1].entry_own.node().children_perm.value()[self.continuations[1].idx as int],
                self.continuations[1].entry_own.node().level(),
            )
            &&& self.continuations[0].entry_own.parent_level
                == self.continuations[1].entry_own.node().level()
        }
    }
}

impl<'rcu, C: PageTableConfig> CursorOwner<'rcu, C> {
    pub open spec fn node_unlocked(guards: Guards) -> (spec_fn(
        EntryOwner<C>,
        TreePath<NR_ENTRIES>,
    ) -> bool) {
        |owner: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
            owner.is_node() ==> guards.unlocked(owner.node().slot_vaddr())
    }

    pub open spec fn node_unlocked_except(guards: Guards, addr: usize) -> (spec_fn(
        EntryOwner<C>,
        TreePath<NR_ENTRIES>,
    ) -> bool) {
        |owner: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
            owner.is_node() ==> owner.node().slot_vaddr() != addr ==> guards.unlocked(
                owner.node().slot_vaddr(),
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

    pub open spec fn children_not_locked(self, guards: Guards) -> bool {
        self.map_only_children(Self::node_unlocked(guards))
    }

    pub proof fn lemma_children_not_locked_unroll(self, guards: Guards)
        requires
            self.children_not_locked(guards),
        ensures
            forall|i: int|
                #![trigger self.continuations[i]]
                self.level - 1 <= i < NR_LEVELS ==> self.continuations[i].map_children(
                    Self::node_unlocked(guards),
                ),
    {
    }

    pub open spec fn only_current_locked(self, guards: Guards) -> bool {
        self.map_only_children(
            Self::node_unlocked_except(guards, self.cur_entry_owner().node().slot_vaddr()),
        )
    }

    pub proof fn lemma_never_drop_restores_children_not_locked(
        self,
        guard: PageTableGuard<'rcu, C>,
        guards0: Guards,
        guards1: Guards,
    )
        requires
            self.inv(),
            self.only_current_locked(guards0),
            guards0.lock_held(guard.inner.inner@.ptr.addr()),
            guards1.guards == guards0.guards.remove(guard.inner.inner@.ptr.addr()),
            // The dropped guard is for the current entry's node (from pop_level).
            self.cur_entry_owner().is_node(),
            guard.inner.inner@.ptr.addr() == self.cur_entry_owner().node().slot_vaddr(),
        ensures
            self.children_not_locked(guards1),
    {
        let current_addr = self.cur_entry_owner().node().slot_vaddr();
        let f = Self::node_unlocked_except(guards0, current_addr);
        let g = Self::node_unlocked(guards1);

        self.map_children_implies(f, g);
    }

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
    pub open spec fn nodes_locked(self, guards: Guards) -> bool {
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
            va: vaddr_replace_pte_index_spec::<C>(
                self.va,
                self.level,
                self.continuations[self.level - 1].inc_index().idx as int,
            ),
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
                <= C::TOP_LEVEL_INDEX_RANGE().end,
        ensures
            final(self).inv(),
            *final(self) == old(self).inc_index(),
    {
        C::lemma_paging_consts_properties();
        lemma_inc_slot_indices::<C>(old(self).va, old(self).level);
        old(self).lemma_inc_index_va();
        self.popped_too_high = false;
        let tracked mut cont = self.continuations.tracked_remove(self.level - 1);
        cont.do_inc_index();
        self.va = old(self).inc_index().va;
        self.continuations.tracked_insert(self.level - 1, cont);
        assert(self.continuations == old(self).continuations.insert(self.level - 1, cont));

    }

    pub proof fn lemma_inv_continuation(self, i: int)
        requires
            self.inv(),
            self.level - 1 <= i <= NR_LEVELS - 1,
        ensures
            self.continuations.contains_key(i),
            self.continuations[i].inv(),
            self.continuations[i].children.len() == NR_ENTRIES,
    {
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
        assert(values.contains(mapped[i]));
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
        self.cur_subtree().value()
    }

    pub open spec fn cur_subtree(self) -> OwnerSubtree<C> {
        self.continuations[self.level - 1].children[self.index() as int]->0
    }

    /// Axiom: the item reconstructed from the current frame's physical address satisfies
    /// `clone_requires`.
    ///
    /// Safety: When `metaregion_sound` holds for a frame entry, the item reconstructed via
    /// `item_from_raw(pa, ...)` is the original frame item.  The frame's slot permission
    /// (owned by the cursor) has the correct address, is initialised, and its ref count is in the
    /// valid clonable range (> 0, < REF_COUNT_MAX), so `clone_requires` is satisfied.
    ///
    /// This is a *trait-level* axiom: `C::Item::clone_requires` is fully generic in the
    /// `PageTableConfig` trait, so the postcondition cannot be discharged without knowing
    /// the concrete item type.  It holds for every `PageTableConfig` used in `ostd` because
    /// `item_from_raw` always returns a freshly-constructed `Frame<M>` handle whose
    /// `Frame::<M>::clone_requires` unfolds to slot-address equality, initialisation, and a
    /// bounded ref-count — all delivered by `metaregion_sound` for frame entries.
    pub proof fn lemma_cur_frame_clone_requires(
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
            C::item_from_raw(pa, level, prop, C::item_into_raw(item).3) == item,
            C::item_into_raw(item).3@ == self.cur_entry_owner().frame_permission(),
            valid_frame_paddr(pa),
            C::raw_item_well_formed((pa, level, prop, C::item_into_raw(item).3)),
            // The recorded entry trackedness matches the item being cloned.
            (C::item_into_raw(item).3@ is Some) == self.cur_entry_owner().frame_is_tracked(),
            // Saturation aborts (Arc-style) via `inc_ref_count`'s diverging panic.
            C::item_into_raw(item).3@ is Some ==> (regions.slot_owner(pa).ref_count()
                < REF_COUNT_MAX || may_panic()),
        ensures
            item.clone_requires(regions),
    {
        broadcast use crate::specs::mm::frame::meta_owners::axiom_mmio_usage_iff_mmio_paddr;

        let entry = self.cur_entry_owner();
        let idx = frame_to_index(pa);
        EntryOwner::<C>::axiom_frame_is_tracked_iff_not_mmio(entry);
        let cont = self.continuations[self.level - 1];
        cont.lemma_map_children_unroll(
            PageTableOwner::<C>::metaregion_sound_pred(regions),
            cont.idx as int,
        );
        C::lemma_clone_requires_concrete(item, pa, level, prop, regions);
    }

    /// Incrementing the ref count of the current frame preserves `regions.inv()` and
    /// `self.metaregion_sound(new_regions)`.
    pub proof fn lemma_clone_item_preserves_invariants(
        self,
        old_regions: MetaRegionOwners,
        new_regions: MetaRegionOwners,
        idx: int,
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
            new_regions.ref_count(idx) == old_regions.ref_count(idx) + 1,
            // All other inner_perms fields at idx are identical (same tracked object)
            new_regions.slot_owners[idx].ref_count_perm.id()
                == old_regions.slot_owners[idx].ref_count_perm.id(),
            new_regions.slot_owners[idx].metadata_perm.id()
                == old_regions.slot_owners[idx].metadata_perm.id(),
            new_regions.slot_owners[idx].metadata_perm.frac() + 1
                == old_regions.slot_owners[idx].metadata_perm.frac(),
            new_regions.slot_owners[idx].in_list_perm == old_regions.slot_owners[idx].in_list_perm,
            // Other MetaSlotOwner fields at idx unchanged
            new_regions.slot_owners[idx].paths_in_pt == old_regions.slot_owners[idx].paths_in_pt,
            new_regions.slot_owners[idx].slot_vaddr == old_regions.slot_owners[idx].slot_vaddr,
            new_regions.slot_owners[idx].usage == old_regions.slot_owners[idx].usage,
            // All other slot_owners unchanged
            new_regions.slot_owners.dom() == old_regions.slot_owners.dom(),
            forall|i: int|
                #![trigger new_regions.slot_owners[i]]
                i != idx && old_regions.slot_owners.contains_key(i) ==> new_regions.slot_owners[i]
                    == old_regions.slot_owners[i],
            // slots map unchanged
            new_regions.slots == old_regions.slots,
            new_regions.inv(),
            // obligation ledger unchanged (clone bumps a ref count only)
            // rc overflow guard: old rc is a normal shared count; the bumped rc fits
            // in the valid `[1, REF_COUNT_MAX]` range. The `<=` form (vs strict `<`)
            // matches what callers actually have: post-`clone_item`, the new rc is
            // bounded by the slot's `inv()` (which permits `rc == REF_COUNT_MAX`).
            0 < old_regions.ref_count(idx),
            old_regions.ref_count(idx) + 1 <= REF_COUNT_MAX,
        ensures
            new_regions.inv(),
            self.metaregion_sound(new_regions),
    {
        self.lemma_metaregion_slot_owners_rc_increment(old_regions, new_regions, idx);
    }

    /// A new frame subtree at the current position has mappings equal to the singleton
    /// mapping covering the current slot range.
    pub proof fn lemma_new_child_mappings_eq_target(
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
            new_subtree.value().is_frame(),
            new_subtree.value().path == self.continuations[self.level - 1].path().push_tail(
                self.continuations[self.level - 1].idx as int,
            ),
            new_subtree.value().frame().mapped_pa == pa,
            new_subtree.value().frame().prop == prop,
        ensures
            PageTableOwner(new_subtree)@.mappings
                == set![Mapping {
                va_range: self@.cur_slot_range(page_size::<PagingConsts>(level)),
                pa_range: pa..(pa + page_size::<PagingConsts>(level)) as usize,
                page_size: page_size::<PagingConsts>(level),
                property: prop,
            }],
    {
        self.cur_va_in_subtree_range();
    }

    /// The guard-level slot containing the numeric prefix, with its end excluded.
    pub open spec fn locked_range(self) -> Range<Vaddr> {
        let size = page_size::<C>(self.guard_level) as nat;
        let start = nat_align_down(self.prefix as nat, size);
        Range { start: start as Vaddr, end: (start + size) as Vaddr }
    }

    pub open spec fn in_locked_range(self) -> bool {
        self.locked_range().start <= self.va < self.locked_range().end
    }

    pub open spec fn above_locked_range(self) -> bool {
        self.va >= self.locked_range().end
    }

    pub proof fn lemma_prefix_in_locked_range(self)
        requires
            self.inv(),
            !self.popped_too_high,
            self.level < self.guard_level,
        ensures
            self.in_locked_range(),
    {
        C::lemma_paging_consts_properties();
        self.lemma_locked_range_span();
        let gl = self.guard_level;
        let path = TreePath::new(
            Seq::new(
                (C::NR_LEVELS() - gl + 1) as nat,
                |k: int|
                    pte_index_spec::<C>(self.prefix, (C::NR_LEVELS() - k) as PagingLevel) as int,
            ),
        );
        assert forall|k: int| 0 <= k < path.len() implies {
            &&& TreePath::<NR_ENTRIES>::elem_inv(#[trigger] path[k])
            &&& path[k] == pte_index_spec::<C>(self.va, (C::NR_LEVELS() - k) as PagingLevel)
        } by {
            let level = (C::NR_LEVELS() - k) as PagingLevel;
            lemma_pte_index_bound::<C>(self.prefix, level);
            lemma_pte_index_bound::<C>(self.va, level);
        };
        lemma_vaddr_path_aligned::<C>(path, self.prefix);
        lemma_vaddr_path_aligned::<C>(path, self.va);
        lemma_page_size_ge_base::<PagingConsts>(gl);
        lemma_nat_align_down_sound(self.va as nat, page_size::<PagingConsts>(gl) as nat);
    }

    /// The cursor and prefix select the same guard-level entry within the locked range.
    #[verifier::rlimit(200)]
    pub proof fn lemma_in_locked_range_guard_index_eq_prefix(self)
        requires
            self.inv(),
            1 <= self.guard_level <= NR_LEVELS,
            self.in_locked_range(),
        ensures
            pte_index_spec::<C>(self.va, (self.guard_level - 1 + 1) as PagingLevel)
                == pte_index_spec::<C>(self.prefix, (self.guard_level - 1 + 1) as PagingLevel),
    {
        C::lemma_paging_consts_properties();
        self.lemma_locked_range_vaddr_prefix_match(self.va);
        assert(pte_index_spec::<C>(self.va, self.guard_level) == pte_index_spec::<C>(
            self.prefix,
            self.guard_level,
        ));
        lemma_pte_index_bound::<C>(self.va, self.guard_level);
        lemma_pte_index_bound::<C>(self.prefix, self.guard_level);
    }

    pub proof fn lemma_in_locked_range_level_le_nr_levels(self)
        requires
            self.inv(),
            self.in_locked_range(),
            !self.popped_too_high,
        ensures
            self.level <= NR_LEVELS,
    {
    }

    /// When the cursor is in the locked range and not popped, its top-level
    /// index is strictly less than `TOP_LEVEL_INDEX_RANGE.end` (the relaxed inv
    /// only allows `<=`, but the operational state is strict).
    pub proof fn lemma_in_locked_range_top_index_lt_top_end(self)
        requires
            self.inv(),
            self.in_locked_range(),
            !self.popped_too_high,
        ensures
            pte_index_spec::<C>(self.va, (NR_LEVELS - 1 + 1) as PagingLevel)
                < C::TOP_LEVEL_INDEX_RANGE().end,
    {
        if self.guard_level == NR_LEVELS {
            // level < guard_level: va.index[guard_level-1] == prefix.index[guard_level-1]
            // < TOP_LEVEL_INDEX_RANGE.end, straight from the cursor invariant.
            if self.level >= self.guard_level {
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
                self.lemma_in_locked_range_guard_index_eq_prefix();
            }
        }
    }

    pub proof fn lemma_in_locked_range_level_le_guard_level(self)
        requires
            self.inv(),
            self.in_locked_range(),
            !self.popped_too_high,
        ensures
            self.level <= self.guard_level,
    {
    }

    /// The locked range spans exactly one guard-level node:
    /// `end - start == page_size(guard_level)`.
    pub proof fn lemma_locked_range_span(self)
        requires
            self.inv(),
        ensures
            self.locked_range().start as nat == nat_align_down(
                self.prefix as nat,
                page_size::<PagingConsts>(self.guard_level as PagingLevel) as nat,
            ),
            self.locked_range().start == self.prefix,
            self.locked_range().end == self.prefix + page_size::<PagingConsts>(self.guard_level),
            self.locked_range().start as nat % page_size::<PagingConsts>(
                self.guard_level as PagingLevel,
            ) as nat == 0,
            self.locked_range().end - self.locked_range().start == page_size::<PagingConsts>(
                self.guard_level as PagingLevel,
            ),
    {
        C::lemma_paging_consts_properties();
        self.lemma_prefix_aligned_to_guard_level();
        self.lemma_prefix_plus_ps_no_overflow();
        lemma_page_size_ge_base::<PagingConsts>(self.guard_level);
        lemma_nat_align_down_sound(
            self.prefix as nat,
            page_size::<PagingConsts>(self.guard_level) as nat,
        );
    }

    /// The cursor's `prefix` is aligned to `page_size(self.guard_level)`, since the
    /// cursor invariant makes the prefix base-page-aligned and zeros all indices below
    /// `self.guard_level`.
    pub proof fn lemma_prefix_aligned_to_guard_level(self)
        requires
            self.inv(),
        ensures
            self.prefix as nat % page_size::<PagingConsts>(self.guard_level) as nat == 0,
    {
        C::lemma_paging_consts_properties();
        lemma_lower_indices_aligned::<C>(self.prefix, self.guard_level);
    }

    /// At the top guard level, the node determined by the cursor's upper address bits
    /// contains the entire locked range, even after the cursor leaves that range.
    pub proof fn lemma_in_node_holds_at_top(self, self_va: Vaddr, va: Vaddr, node_size: usize)
        requires
            self.inv(),
            self_va == self.va,
            self.guard_level == NR_LEVELS,
            node_size == page_size::<PagingConsts>((NR_LEVELS + 1) as PagingLevel),
            self.locked_range().start <= va < self.locked_range().end,
        ensures
            nat_align_down(self_va as nat, node_size as nat) <= va as nat,
            (va as nat) - nat_align_down(self_va as nat, node_size as nat) < node_size as nat,
    {
        C::lemma_paging_consts_properties();
        self.lemma_locked_range_span();
        let body_level = (C::NR_LEVELS() + 1) as PagingLevel;
        lemma_page_size_is_pow2_pte_index_bit_offset::<C>(body_level);
        lemma_page_size_next::<C>(self.guard_level);
        lemma_usize_shr_is_div(self_va, page_table_vaddr_bits_spec::<C>());
        lemma_fundamental_div_mod(self_va as int, node_size as int);
        lemma_mul_is_commutative(self_va as int / node_size as int, node_size as int);
        lemma_nat_align_down_sound(self_va as nat, node_size as nat);
        assert(nat_align_down(self_va as nat, node_size as nat) == vaddr_upper_part_spec::<C>(
            self_va,
        ));

        lemma_vaddr_upper_part_is_align_down::<C>(self_va);
        lemma_lower_indices_aligned::<C>(self.prefix, body_level);
        lemma_usize_shr_is_div(self.prefix, page_table_vaddr_bits_spec::<C>());
        lemma_fundamental_div_mod(self.prefix as int, node_size as int);
        assert(nat_align_down(self_va as nat, node_size as nat) == self.prefix);
    }

    /// `prefix + page_size(guard_level) <= usize::MAX`.
    ///
    /// The prefix is aligned to a parent slot, leaving a complete fanout of slots
    /// before machine-word wrap.
    pub proof fn lemma_prefix_plus_ps_no_overflow(self)
        requires
            self.inv(),
        ensures
            self.prefix + page_size::<PagingConsts>(self.guard_level) <= usize::MAX,
    {
        C::lemma_paging_consts_properties();
        let gl = self.guard_level;
        lemma_lower_indices_aligned::<C>(self.prefix, (gl + 1) as PagingLevel);
        lemma_aligned_vaddr_slack::<C>(self.prefix, (gl + 1) as PagingLevel);
        lemma_page_size_next::<C>(gl);
        vstd::arithmetic::mul::lemma_mul_left_inequality(
            page_size::<C>(gl) as int,
            2,
            crate::mm::nr_subpage_per_huge::<C>() as int,
        );
    }

    /// `self.va + page_size(level) <= usize::MAX` for any
    /// `level <= self.guard_level`, whenever the cursor is in the locked range.
    ///
    /// Derived from the cursor invariant: `in_locked_range` says
    /// `self.va < locked_range().end = prefix + page_size(guard_level)`
    /// and parent-slot alignment leaves enough slack for one more configured slot,
    /// since `page_size(level) <= page_size(gl)`.
    pub proof fn lemma_va_plus_page_size_no_overflow(self, level: PagingLevel)
        requires
            self.inv(),
            self.in_locked_range(),
            1 <= level <= self.guard_level,
        ensures
            self.va + page_size::<PagingConsts>(level) <= usize::MAX,
    {
        C::lemma_paging_consts_properties();
        self.lemma_locked_range_span();
        let gl = self.guard_level;
        lemma_lower_indices_aligned::<C>(self.prefix, (gl + 1) as PagingLevel);
        lemma_aligned_vaddr_slack::<C>(self.prefix, (gl + 1) as PagingLevel);
        lemma_page_size_next::<C>(gl);
        lemma_page_size_divides::<C>(level, gl);
        vstd::arithmetic::mul::lemma_mul_left_inequality(
            page_size::<C>(gl) as int,
            2,
            crate::mm::nr_subpage_per_huge::<C>() as int,
        );
    }

    pub proof fn lemma_locked_range_page_aligned(self)
        requires
            self.inv(),
        ensures
            self.locked_range().end % PAGE_SIZE == 0,
            self.locked_range().start % PAGE_SIZE == 0,
    {
        self.lemma_locked_range_span();
        let gl = self.guard_level;
        lemma_page_size_base::<PagingConsts>();
        lemma_page_size_ge_base::<PagingConsts>(gl);
        lemma_page_size_divides::<PagingConsts>(1u8, gl);
        lemma_div_non_zero(page_size::<PagingConsts>(gl) as int, PAGE_SIZE as int);
        lemma_fundamental_div_mod(page_size::<PagingConsts>(gl) as int, PAGE_SIZE as int);
        vstd::arithmetic::div_mod::lemma_mod_mod(
            self.prefix as int,
            PAGE_SIZE as int,
            page_size::<PagingConsts>(gl) as int / PAGE_SIZE as int,
        );
        vstd::arithmetic::div_mod::lemma_add_mod_noop(
            self.prefix as int,
            page_size::<PagingConsts>(gl) as int,
            PAGE_SIZE as int,
        );
    }

    pub proof fn lemma_cur_subtree_inv(self)
        requires
            self.inv(),
        ensures
            self.cur_subtree().inv(),
    {
        let cont = self.continuations[self.level - 1];
        cont.lemma_inv_children_unroll(cont.idx as int)
    }

    /// If the current entry is absent, `!self@.present()`.
    pub proof fn lemma_cur_entry_absent_not_present(self)
        requires
            self.inv(),
            self.in_locked_range(),
            self.cur_entry_owner().is_absent(),
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
        assert(filtered == set![]) by {};
    }

    /// Generalises `lemma_cur_entry_absent_not_present` to any empty subtree.
    pub proof fn lemma_cur_subtree_empty_not_present(self)
        requires
            self.inv(),
            self.in_locked_range(),
            PageTableOwner(self.cur_subtree()).view_rec(self.cur_subtree().value().path) =~= set![],
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
        assert(filtered == set![]) by {};
    }

    pub proof fn lemma_cur_entry_frame_present(self)
        requires
            self.inv(),
            self.in_locked_range(),
            self.cur_entry_owner().is_frame(),
        ensures
            self@.present(),
            self@.query(
                self.cur_entry_owner().frame().mapped_pa,
                page_size::<PagingConsts>(self.cur_entry_owner().parent_level),
                self.cur_entry_owner().frame().prop,
            ),
    {
        self.view_preserves_inv();
        let subtree = self.cur_subtree();
        let path = subtree.value().path;
        let frame = self.cur_entry_owner().frame();
        let pt_level = INC_LEVELS - path.len();
        let cont = self.continuations[self.level - 1];

        let m = Mapping {
            va_range: Range {
                start: vaddr_of::<C>(path) as int,
                end: vaddr_of::<C>(path) + page_size::<PagingConsts>(pt_level as PagingLevel),
            },
            pa_range: Range {
                start: frame.mapped_pa,
                end: (frame.mapped_pa + page_size::<PagingConsts>(
                    pt_level as PagingLevel,
                )) as Paddr,
            },
            page_size: page_size::<PagingConsts>(pt_level as PagingLevel),
            property: frame.prop,
        };
        cont.lemma_view_mappings_intro(m, cont.idx as int);
        self.lemma_view_mappings_intro(m, self.level - 1);
        assert(m.va_range.start <= self@.cur_va < m.va_range.end) by {
            self.cur_va_in_subtree_range();
        };

        let filtered = self@.mappings.filter(
            |m2: Mapping| m2.va_range.start <= self@.cur_va < m2.va_range.end,
        );
        lemma_set_contains_len(filtered, m);
        // Non-overlap makes the covering mapping unique, so `choose` returns this frame.
        let queried = self@.query_mapping();
        assert(filtered.contains(queried));
        assert(queried == m);
    }

    /// The entry_own at each continuation level satisfies `metaregion_sound`.
    #[verifier::opaque]
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

    pub proof fn lemma_metaregion_preserved(
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
            reveal(CursorContinuation::map_children);
            let cont = self.continuations[i];
            assert forall|j: int|
                0 <= j < NR_ENTRIES
                    && #[trigger] cont.children[j] is Some implies cont.children[j].unwrap().subtree_satisfies(
            cont.path().push_tail(j), g) by {
                cont.children[j].unwrap().lemma_subtree_satisfies_implies(
                    cont.path().push_tail(j),
                    f,
                    g,
                );
            };
        };
        assert(other.path_metaregion_sound(regions1)) by {
            reveal(CursorOwner::path_metaregion_sound);
            assert forall|i: int|
                #![trigger other.continuations[i]]
                self.level - 1 <= i
                    < NR_LEVELS implies other.continuations[i].entry_own.metaregion_sound(
                regions1,
            ) by {
                let eo = self.continuations[i].entry_own;
                assert(g(eo, self.continuations[i].path()));
            };
        };
    }

    /// Transfers `metaregion_sound` when `slot_owners` is preserved.
    pub proof fn lemma_metaregion_slot_owners_preserved(
        self,
        regions0: MetaRegionOwners,
        regions1: MetaRegionOwners,
    )
        requires
            self.inv(),
            self.metaregion_sound(regions0),
            regions0.slot_owners =~= regions1.slot_owners,
            forall|k: int|
                regions0.slots.contains_key(k) ==> #[trigger] regions1.slots.contains_key(k),
            forall|k: int|
                regions0.slots.contains_key(k) ==> regions0.slots[k]
                    == #[trigger] regions1.slots[k],
        ensures
            self.metaregion_sound(regions1),
    {
        let f = PageTableOwner::<C>::metaregion_sound_pred(regions0);
        let g = PageTableOwner::<C>::metaregion_sound_pred(regions1);
        assert(OwnerSubtree::implies(f, g)) by {
            assert forall|entry: EntryOwner<C>, path: TreePath<NR_ENTRIES>|
                entry.inv() && f(entry, path) implies #[trigger] g(entry, path) by {
                entry.metaregion_sound_slot_owners_only(regions0, regions1);
            };
        };
        self.lemma_metaregion_preserved(self, regions0, regions1);
    }

    pub proof fn lemma_metaregion_slot_owners_rc_increment(
        self,
        regions0: MetaRegionOwners,
        regions1: MetaRegionOwners,
        idx: int,
    )
        requires
            self.inv(),
            self.metaregion_sound(regions0),
            regions0.inv(),
            regions1.slots == regions0.slots,
            regions1.slot_owners.dom() == regions0.slot_owners.dom(),
            regions1.ref_count(idx) == regions0.ref_count(idx) + 1,
            regions1.slot_owners[idx].ref_count_perm.id()
                == regions0.slot_owners[idx].ref_count_perm.id(),
            regions1.slot_owners[idx].metadata_perm.id()
                == regions0.slot_owners[idx].metadata_perm.id(),
            regions1.slot_owners[idx].metadata_perm.frac() + 1
                == regions0.slot_owners[idx].metadata_perm.frac(),
            regions1.slot_owners[idx].in_list_perm == regions0.slot_owners[idx].in_list_perm,
            regions1.slot_owners[idx].paths_in_pt == regions0.slot_owners[idx].paths_in_pt,
            regions1.slot_owners[idx].slot_vaddr == regions0.slot_owners[idx].slot_vaddr,
            regions1.slot_owners[idx].usage == regions0.slot_owners[idx].usage,
            regions1.ref_count(idx) != REF_COUNT_UNUSED,
            // Bumped rc stays in the SHARED range (needed for the node branch).
            regions1.ref_count(idx) <= REF_COUNT_MAX,
            regions1.inv(),
            forall|i: int|
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
                if entry.is_frame() {
                    let pa = entry.frame().mapped_pa;
                    C::lemma_perm_well_formed_with_region_preserved(
                        pa,
                        Tracked(entry.frame_permission()),
                        regions0,
                        regions1,
                    );
                }
            };
        };
        self.lemma_metaregion_preserved(self, regions0, regions1);
    }

    /// The continuation entry at `i` satisfies `metaregion_sound`.
    pub proof fn lemma_cont_entry_metaregion_at(self, regions: MetaRegionOwners, i: int)
        requires
            self.inv(),
            self.metaregion_sound(regions),
            self.level - 1 <= i < NR_LEVELS,
        ensures
            self.continuations[i].entry_own.metaregion_sound(regions),
    {
        reveal(CursorOwner::path_metaregion_sound);
    }

    pub open spec fn new(
        owner_subtree: OwnerSubtree<C>,
        idx: usize,
        guard: PageTableGuard<'rcu, C>,
    ) -> Self {
        let va = (C::LEADING_BITS_spec() as int * pow2(page_table_vaddr_bits_spec::<C>() as nat)
            + idx * pow2(pte_index_bit_offset_spec::<C>(C::NR_LEVELS()) as nat)) as Vaddr;
        Self {
            level: C::NR_LEVELS(),
            continuations: Map::empty().insert(
                C::NR_LEVELS() - 1,
                CursorContinuation::new(owner_subtree, idx, guard),
            ),
            va,
            guard_level: C::NR_LEVELS(),
            prefix: va,
            popped_too_high: false,
        }
    }

    pub proof fn tracked_new(
        tracked owner_subtree: OwnerSubtree<C>,
        idx: usize,
        guard: PageTableGuard<'rcu, C>,
    ) -> tracked Self
        returns
            Self::new(owner_subtree, idx, guard),
    {
        let ghost va = (C::LEADING_BITS_spec() as int * pow2(
            page_table_vaddr_bits_spec::<C>() as nat,
        ) + idx * pow2(pte_index_bit_offset_spec::<C>(C::NR_LEVELS()) as nat)) as Vaddr;
        let tracked continuation = CursorContinuation::tracked_new(owner_subtree, idx, guard);
        let tracked mut continuations = Map::tracked_empty();
        continuations.tracked_insert(C::NR_LEVELS() - 1, continuation);
        Self {
            level: C::NR_LEVELS(),
            continuations,
            va,
            guard_level: C::NR_LEVELS(),
            prefix: va,
            popped_too_high: false,
        }
    }

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
        // `vaddr_range_spec<C>` gives inclusive `(start, end_inclusive)`
        // bounds derived from `LEADING_BITS_spec` + `TOP_LEVEL_INDEX_RANGE`,
        // so `Mapping::inv` can stay config-agnostic.
        &&& forall|m: Mapping|
            #![auto]
            self.mappings.contains(m) ==> {
                &&& vaddr_range_spec::<C>().start <= m.va_range.start
                &&& m.va_range.end <= vaddr_range_spec::<C>().end + 1
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
                &&& vaddr_range_spec::<C>().start <= m.va_range.start
                &&& m.va_range.end <= vaddr_range_spec::<C>().end + 1
            },
{
    C::lemma_paging_consts_properties();
    C::lemma_page_table_config_constant_properties();
    lemma_arch_specific_consts_properties::<C>();

    let idx = C::TOP_LEVEL_INDEX_RANGE();
    let start = idx.start as int;
    let end = idx.end as int;
    let lb = C::LEADING_BITS_spec() as int;
    let base = lb * 0x1_0000_0000_0000int;
    let cell = 0x80_0000_0000int;
    let bounds = vaddr_range_spec::<C>();

    let end_exclusive = base + end * cell;
    let end_pre = end_exclusive - 1;

    assert forall|m: Mapping| #[trigger] owner.view_mappings().contains(m) implies {
        &&& vaddr_range_spec::<C>().start <= m.va_range.start
        &&& m.va_range.end <= vaddr_range_spec::<C>().end + 1
    } by {
        let i = choose|i: int|
            owner.level - 1 <= i < NR_LEVELS && (
            #[trigger] owner.continuations[i]).view_mappings().contains(m);
        let cont = owner.continuations[i];
        let j = choose|j: int|
            0 <= j < cont.children.len() && #[trigger] cont.children[j] is Some && PageTableOwner(
                cont.children[j].unwrap(),
            ).view_rec(cont.path().push_tail(j)).contains(m);
        let child = PageTableOwner(cont.children[j].unwrap());
        let p = cont.path().push_tail(j);
        let pidx = p[0] as int;
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
    let end = crate::mm::vm_space::UserPtConfig::TOP_LEVEL_INDEX_RANGE().end as int;
    assert forall|m: Mapping| #[trigger] owner.view_mappings().contains(m) implies {
        &&& 0 <= m.va_range.start
        &&& m.va_range.end <= 0x8000_0000_0000int
    } by {
        let i = choose|i: int|
            owner.level - 1 <= i < NR_LEVELS && (
            #[trigger] owner.continuations[i]).view_mappings().contains(m);
        let cont = owner.continuations[i];
        let j = choose|j: int|
            0 <= j < cont.children.len() && #[trigger] cont.children[j] is Some && PageTableOwner(
                cont.children[j].unwrap(),
            ).view_rec(cont.path().push_tail(j)).contains(m);
        let child = PageTableOwner(cont.children[j].unwrap());
        let p = cont.path().push_tail(j);
        child.view_rec_top_index_va_bound(p, m, end);
    }
}

/// KERNEL isolation theorem (proven, per-config): every mapping a
/// `KernelPtConfig` cursor exposes lives in the kernel high half. Mirror of
/// `lemma_view_in_vaddr_range_user` with `TOP_LEVEL_INDEX_RANGE == 256..512` and
/// `LEADING_BITS == 0xffff` (canonical high-half base).
pub proof fn lemma_view_in_vaddr_range_kernel<'rcu>(owner: CursorOwner<'rcu, KernelPtConfig>)
    requires
        owner.inv(),
    ensures
        forall|m: Mapping|
            #![auto]
            owner.view_mappings().contains(m) ==> {
                &&& vaddr_range_spec::<KernelPtConfig>().start <= m.va_range.start
                &&& m.va_range.end <= vaddr_range_spec::<KernelPtConfig>().end + 1
            },
{
    lemma_vaddr_range_spec_kernel();
    let end = KernelPtConfig::TOP_LEVEL_INDEX_RANGE().end as int;
    assert forall|m: Mapping| #[trigger] owner.view_mappings().contains(m) implies {
        &&& vaddr_range_spec::<KernelPtConfig>().start <= m.va_range.start
        &&& m.va_range.end <= vaddr_range_spec::<KernelPtConfig>().end + 1
    } by {
        let i = choose|i: int|
            owner.level - 1 <= i < NR_LEVELS && (
            #[trigger] owner.continuations[i]).view_mappings().contains(m);
        let cont = owner.continuations[i];
        let j = choose|j: int|
            0 <= j < cont.children.len() && #[trigger] cont.children[j] is Some && PageTableOwner(
                cont.children[j].unwrap(),
            ).view_rec(cont.path().push_tail(j)).contains(m);
        let child = PageTableOwner(cont.children[j].unwrap());
        let p = cont.path().push_tail(j);
        child.view_rec_top_index_va_bound(p, m, end);
        // m.start ≥ index(0)·2^39 + lb·2^48 ≥ start·2^39 + lb·2^48 = bound.0.
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
        //     in `vaddr_range_spec::<C>()`.
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
        &&& owner.va == self.va
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
