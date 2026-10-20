use vstd::{arithmetic::div_mod::lemma_mod_add_multiples_vanish, prelude::*};
use vstd_extra::{
    arithmetic::{lemma_nat_align_down_sound, lemma_nat_align_down_within_block, nat_align_down},
    ghost_tree::*,
    ownership::*,
};

use crate::specs::{
    arch::{NR_ENTRIES, NR_LEVELS},
    mm::{
        frame::mapping::meta_to_index,
        page_table::{
            cursor::{
                owners::*,
                page_size_lemmas::{lemma_page_size_ge_base, lemma_page_size_monotone},
            },
            node::EntryOwner,
            owners::*,
            vaddr_range_proofs::lemma_page_table_managed_index_bounds,
            *,
        },
        *,
    },
};

use crate::arch::mm::PagingConsts;
use crate::mm::{Paddr, PagingConstsTrait, PagingLevel, Vaddr, page_size, page_table::*};
use core::ops::Range;

verus! {

broadcast use group_ghost_tree_lemmas;

/// Upgrade `node_unlocked_except` to `node_unlocked` on a subtree where the excepted
/// entry cannot appear. The precondition `path == subtree.value.path` ties structural
/// positions to entry paths. `excepted_path` must differ from all descendant paths,
/// which is guaranteed when `excepted_path != path` and `excepted_path` is not an
/// extension of `path` (all descendants have paths extending `path`).
pub proof fn subtree_unlock_upgrade<'rcu, C: PageTableConfig>(
    subtree: OwnerSubtree<C>,
    path: TreePath<NR_ENTRIES>,
    guards: Guards,
    regions: MetaRegionOwners,
    excepted_addr: usize,
    excepted_path: TreePath<NR_ENTRIES>,
)
    requires
        subtree.inv(),
        PageTableOwner::<C>(subtree).pt_inv(),
        subtree.subtree_satisfies(path, PageTableOwner::<C>::metaregion_sound_pred(regions)),
        subtree.subtree_satisfies(
            path,
            CursorOwner::<'rcu, C>::node_unlocked_except(guards, excepted_addr),
        ),
        regions.slot_owners[meta_to_index(excepted_addr)].paths_in_pt == set![excepted_path],
        // Structural path == value path
        path == subtree.value().path,
        path.inv(),
        // excepted_path does not match this subtree root
        path != excepted_path,
        // excepted_path is not a descendant (all descendants extend path, so if
        // excepted_path.len() <= path.len() it can't be a descendant; otherwise
        // it must diverge at some index below path.len())
        excepted_path.len() <= path.len() || (exists|k: int|
            0 <= k < path.len() && #[trigger] excepted_path[k] != path[k]),
    ensures
        subtree.subtree_satisfies(path, CursorOwner::<'rcu, C>::node_unlocked(guards)),
    decreases INC_LEVELS - subtree.level(),
{
    reveal(PageTableOwner::pt_inv_at_depth);
    let f = PageTableOwner::<C>::metaregion_sound_pred(regions);
    let g = CursorOwner::<'rcu, C>::node_unlocked_except(guards, excepted_addr);
    let h = CursorOwner::<'rcu, C>::node_unlocked(guards);

    if subtree.value().is_node() {
        if subtree.value().node().slot_vaddr() == excepted_addr {
            // addr == excepted_addr contradicts path != excepted_path
            // via metaregion_sound's singleton paths_in_pt.
            let idx = meta_to_index(excepted_addr);

            assert(set![subtree.value().path].contains(excepted_path));
            assert(false);
        }
    }
    if subtree.level() < INC_LEVELS - 1 && subtree.value().is_node() {
        assert forall|i: int|
            #![trigger subtree.children()[i]]
            0 <= i < subtree.children().len() && subtree.has_child(i) implies subtree.child(
            i,
        ).subtree_satisfies(path.push_tail(i), h) by {
            let child = subtree.child(i);

            let child_path = path.push_tail(i);

            subtree_unlock_upgrade(
                child,
                child_path,
                guards,
                regions,
                excepted_addr,
                excepted_path,
            );
        };
    } else if subtree.level() < INC_LEVELS - 1 && !subtree.value().is_node() {
        // Non-node: pt_inv gives children[i] is None, so subtree_satisfies
        // has no children to recurse into.
    }
}

impl<'rcu, C: PageTableConfig> CursorOwner<'rcu, C> {
    /// The number of steps it will take to walk through every node of a full
    /// page table at level `level`
    pub open spec fn max_steps_subtree(level: usize) -> nat
        decreases level,
    {
        if level <= 1 {
            NR_ENTRIES as nat
        } else {
            (NR_ENTRIES as nat) * (Self::max_steps_subtree((level - 1) as usize) + 1)
        }
    }

    /// Per-level "above-current" contribution: count `NR_ENTRIES - cont.idx - 1`
    /// at every level (the entry at `cont.idx` is being descended into; its
    /// work is captured at lower levels in the recursion). `max_steps()`
    /// adds back one `subtree(self.level)` to count the current level's
    /// in-progress entry.
    ///
    /// The base case is `level > NR_LEVELS` (not `== NR_LEVELS`) so that
    /// `level == NR_LEVELS` itself contributes a non-zero term. This avoids
    /// degenerate behavior at the root: without it, `max_steps` collapses
    /// to 0 at the root and `push_level` from the root cannot decrease
    /// (and the popped_too_high `q` at NR_LEVELS would dominate `self`).
    pub open spec fn max_steps_partial(self, level: usize) -> nat
        decreases NR_LEVELS + 1 - level,
        when level <= NR_LEVELS + 1
    {
        if level > NR_LEVELS {
            0
        } else {
            let cont = self.continuations[level - 1];
            let count: nat = (NR_ENTRIES - cont.idx - 1) as nat;
            let steps = Self::max_steps_subtree(level) * count;
            let remaining_steps = self.max_steps_partial((level + 1) as usize);
            steps + remaining_steps
        }
    }

    pub open spec fn max_steps(self) -> nat {
        if self.at_or_past_barrier_end() {
            0
        } else {
            (self.max_steps_partial(self.level as usize) + Self::max_steps_subtree(
                self.level as usize,
            )) as nat
        }
    }

    /// Two owners with the same idx values from `start` upward have the same max_steps_partial.
    pub proof fn lemma_max_steps_partial_eq(self, other: Self, start: usize)
        requires
            1 <= start <= NR_LEVELS + 1,
            forall|k: int|
                start - 1 <= k < NR_LEVELS ==> #[trigger] self.continuations[k].idx
                    == other.continuations[k].idx,
        ensures
            self.max_steps_partial(start) == other.max_steps_partial(start),
        decreases NR_LEVELS + 1 - start,
    {
        if start <= NR_LEVELS {
            self.lemma_max_steps_partial_eq(other, (start + 1) as usize);
        }
    }

    pub open spec fn push_level_owner(self, guard: PageTableGuard<'rcu, C>) -> Self {
        let cont = self.continuations[self.level - 1];
        let (child, cont) = cont.make_cont(
            pte_index_spec::<C>(self.cur_va(), (self.level - 1) as PagingLevel),
            guard,
        );
        let new_continuations = self.continuations.insert(self.level - 1, cont).insert(
            self.level - 2,
            child,
        );

        let new_level = (self.level - 1) as u8;
        Self { continuations: new_continuations, level: new_level, popped_too_high: false, ..self }
    }

    pub proof fn push_level_owner_decreases_steps(self, guard: PageTableGuard<'rcu, C>)
        requires
            self.inv(),
            self.in_barrier_va(),
            self.level > 1,
        ensures
            self.push_level_owner(guard).max_steps() < self.max_steps(),
    {
        C::axiom_current_paging_consts_hardcoded();
        lemma_pte_index_bound::<C>(self.cur_va(), (self.level - 1) as PagingLevel);
        let new_self = self.push_level_owner(guard);
        let l = self.level as usize;
        let lm1 = (self.level - 1) as usize;
        // Continuations agree at indices [l-1, NR_LEVELS): only [l-2] changed.
        new_self.lemma_max_steps_partial_eq(self, l);
        let new_child = new_self.continuations[lm1 - 1];

        // subtree(l) == NR * (subtree(lm1) + 1) (from def of max_steps_subtree, l > 1).
        // subtree(lm1) * (NR - new_child.idx) <= subtree(lm1) * NR < subtree(l).
        vstd::arithmetic::mul::lemma_mul_inequality(
            (NR_ENTRIES - new_child.idx) as int,
            NR_ENTRIES as int,
            Self::max_steps_subtree(lm1) as int,
        );
        vstd::arithmetic::mul::lemma_mul_is_distributive_add(
            Self::max_steps_subtree(lm1) as int,
            NR_ENTRIES - new_child.idx - 1,
            1,
        );
        vstd::arithmetic::mul::lemma_mul_is_commutative(
            (NR_ENTRIES - new_child.idx) as int,
            Self::max_steps_subtree(lm1) as int,
        );

    }

    pub proof fn push_level_owner_preserves_mappings(self, guard: PageTableGuard<'rcu, C>)
        requires
            self.inv(),
            self.level > 1,
            self.cur_entry_owner().is_node(),
        ensures
            self.push_level_owner(guard)@.mappings == self@.mappings,
    {
        C::axiom_current_paging_consts_hardcoded();
        broadcast use {
            CursorContinuation::group_lemmas,
            CursorOwner::group_lemmas,
            PageTableOwner::group_lemmas,
        };

        let new_owner = self.push_level_owner(guard);
        let old_cont = self.continuations[self.level - 1];
        let (_, modified_cont) = old_cont.make_cont(
            pte_index_spec::<C>(self.cur_va(), (self.level - 1) as PagingLevel),
            guard,
        );

        old_cont.view_mappings_take_child();

        let taken = old_cont.take_child().1;

        assert(modified_cont.children == taken.children) by {};

        assert forall|m: Mapping|
            self.view_mappings().contains(m) implies new_owner.view_mappings().contains(m) by {
            let i = choose|i: int|
                self.level - 1 <= i < NR_LEVELS && (
                #[trigger] self.continuations[i]).view_mappings().contains(m);
            if i == self.level - 1 {
                if old_cont.view_mappings_take_child_spec().contains(m) {
                    assert(new_owner.continuations[self.level - 2].view_mappings().contains(m));
                } else {
                    assert(new_owner.continuations[self.level - 1].view_mappings().contains(m));
                }
            } else {
                assert(new_owner.continuations[i] == self.continuations[i]);
            }
        };

    }

    pub proof fn push_level_owner_preserves_inv(self, guard: PageTableGuard<'rcu, C>)
        requires
            self.inv(),
            self.level > 1,
            !self.popped_too_high,
            self.level <= self.guard_level,
            self.in_barrier_va(),
            // The current entry is a node (we're descending into it)
            self.cur_entry_owner().is_node(),
            // The child node's guard relates to the new guard
            self.cur_entry_owner().node().relate_guard(guard),
            // Guard distinctness: the new guard points to a different node than all existing continuations
            forall|i: int|
                #![trigger self.continuations[i]]
                self.level - 1 <= i < NR_LEVELS
                    ==> self.continuations[i].guard.inner.inner@.ptr.addr()
                    != guard.inner.inner@.ptr.addr(),
        ensures
            self.push_level_owner(guard).inv(),
    {
        C::axiom_current_paging_consts_hardcoded();
        lemma_pte_index_bound::<C>(self.cur_va(), (self.level - 1) as PagingLevel);
        let new_owner = self.push_level_owner(guard);

        let old_cont = self.continuations[self.level - 1];

        let child_node = old_cont.children[old_cont.idx as int].unwrap();
        let (child, _) = old_cont.make_cont(
            pte_index_spec::<C>(self.cur_va(), (self.level - 1) as PagingLevel),
            guard,
        );

        assert(child.inv_children_rel()) by {
            assert forall|j: int|
                0 <= j < NR_ENTRIES && #[trigger] child.children[j] is Some implies {
                &&& child.children[j].unwrap().value().parent_level == child.level()
                &&& child.children[j].unwrap().level() == child.tree_level + 1
                &&& child.children[j].unwrap().value().path.len()
                    == child.entry_own.node().tree_level + 1
                &&& child.children[j].unwrap().value().match_pte(
                    child.entry_own.node().children_perm.value()[j],
                    child.entry_own.node().level(),
                )
                &&& <EntryOwner<C> as TreeNodeValue<NR_LEVELS>>::rel_children(
                    child.entry_own,
                    j,
                    Some(child.children[j].unwrap().value()),
                )
                &&& child.children[j].unwrap().value().path == child.path().push_tail(j)
            } by {
                let gc = child.children[j].unwrap();
                PageTableOwner(child_node).pt_inv_unroll(j);

            };
        };
        assert(child.pt_inv_children()) by {
            assert forall|j: int|
                0 <= j < child.children.len()
                    && #[trigger] child.children[j] is Some implies PageTableOwner(
                child.children[j].unwrap(),
            ).pt_inv() by {
                PageTableOwner(child_node).pt_inv_unroll(j);

            };
        };

        assert(new_owner.continuations[new_owner.level - 1].all_some()) by {
            assert forall|j: int| 0 <= j < NR_ENTRIES implies child.children[j] is Some by {
                PageTableOwner(child_node).pt_inv_unroll(j);

            };
        };

    }

    #[verifier::spinoff_prover]
    #[verifier::rlimit(20)]
    pub proof fn push_level_owner_preserves_invs(
        self,
        guard: PageTableGuard<'rcu, C>,
        regions: MetaRegionOwners,
        guards: Guards,
    )
        requires
            self.inv(),
            self.level > 1,
            !self.popped_too_high,
            self.level <= self.guard_level,
            self.in_barrier_va(),
            self.only_current_locked(guards),
            self.nodes_locked(guards),
            self.metaregion_sound(regions),
            // The current entry is a node (we're descending into it)
            self.cur_entry_owner().is_node(),
            // The child node's guard relates to the new guard
            self.cur_entry_owner().node().relate_guard(guard),
            // The new guard must be locked in guards
            guards.lock_held(guard.inner.inner@.ptr.addr()),
        ensures
            self.push_level_owner(guard).inv(),
            self.push_level_owner(guard).children_not_locked(guards),
            self.push_level_owner(guard).nodes_locked(guards),
            self.push_level_owner(guard).metaregion_sound(regions),
    {
        C::axiom_current_paging_consts_hardcoded();
        reveal(CursorContinuation::map_children);
        let new_owner = self.push_level_owner(guard);
        let old_cont = self.continuations[self.level - 1];

        let (child_cont, modified_cont) = old_cont.make_cont(
            pte_index_spec::<C>(self.cur_va(), (self.level - 1) as PagingLevel),
            guard,
        );

        let cur_entry = self.cur_entry_owner();
        let cur_entry_addr = cur_entry.node().slot_vaddr();
        let cur_entry_path = old_cont.path().push_tail(old_cont.idx as int);

        assert forall|i: int|
            #![trigger self.continuations[i]]
            self.level - 1 <= i
                < NR_LEVELS implies self.continuations[i].guard.inner.inner@.ptr.addr()
            != guard.inner.inner@.ptr.addr() by {
            reveal(CursorOwner::path_metaregion_sound);
            let cont_i = self.continuations[i];

            if cont_i.guard.inner.inner@.ptr.addr() == guard.inner.inner@.ptr.addr() {
                assert(set![cont_i.path()].contains(cur_entry_path));

                assert(false);
            }
        };

        self.push_level_owner_preserves_inv(guard);

        let f = PageTableOwner::<C>::metaregion_sound_pred(regions);
        let g_except = CursorOwner::<'rcu, C>::node_unlocked_except(guards, cur_entry_addr);
        let h = CursorOwner::<'rcu, C>::node_unlocked(guards);

        assert forall|i: int|
            #![trigger new_owner.continuations[i]]
            new_owner.level - 1 <= i < NR_LEVELS implies new_owner.continuations[i].map_children(
            h,
        ) by {
            if i == self.level - 2 {
                assert forall|j: int|
                    #![trigger child_cont.children[j]]
                    0 <= j < child_cont.children.len()
                        && child_cont.children[j] is Some implies child_cont.children[j].unwrap().subtree_satisfies(
                child_cont.path().push_tail(j), h) by {
                    let gc = child_cont.children[j].unwrap();
                    let gc_path = child_cont.path().push_tail(j);

                    let child_subtree = old_cont.children[old_cont.idx as int].unwrap();
                    child_subtree.lemma_subtree_satisfies_unroll_once(cur_entry_path, f, j);
                    child_subtree.lemma_subtree_satisfies_unroll_once(cur_entry_path, g_except, j);

                    subtree_unlock_upgrade(
                        gc,
                        gc_path,
                        guards,
                        regions,
                        cur_entry_addr,
                        cur_entry_path,
                    );
                };
            } else if i == self.level - 1 {
                assert forall|j: int|
                    #![trigger modified_cont.children[j]]
                    0 <= j < modified_cont.children.len()
                        && modified_cont.children[j] is Some implies modified_cont.children[j].unwrap().subtree_satisfies(
                modified_cont.path().push_tail(j), h) by {
                    let sibling = old_cont.children[j].unwrap();
                    let sibling_path = old_cont.path().push_tail(j);

                    subtree_unlock_upgrade(
                        sibling,
                        sibling_path,
                        guards,
                        regions,
                        cur_entry_addr,
                        cur_entry_path,
                    );
                };
            } else {
                let cont_i = self.continuations[i];

                assert(cur_entry_path[cont_i.tree_level as int] == cont_i.idx);

                assert forall|j: int|
                    #![trigger cont_i.children[j]]
                    0 <= j < cont_i.children.len()
                        && cont_i.children[j] is Some implies cont_i.children[j].unwrap().subtree_satisfies(
                cont_i.path().push_tail(j), h) by {
                    let child_sub = cont_i.children[j].unwrap();
                    let child_path = cont_i.path().push_tail(j);

                    subtree_unlock_upgrade(
                        child_sub,
                        child_path,
                        guards,
                        regions,
                        cur_entry_addr,
                        cur_entry_path,
                    );
                };
            }
        };

        let f = PageTableOwner::<C>::metaregion_sound_pred(regions);
        let child_subtree = child_cont.as_subtree();

        assert(child_cont.map_children(f)) by {
            assert forall|j: int|
                0 <= j < child_cont.children.len()
                    && #[trigger] child_cont.children[j] is Some implies child_cont.children[j].unwrap().subtree_satisfies(
            child_cont.path().push_tail(j), f) by {
                child_subtree.lemma_subtree_satisfies_unroll_once(child_cont.path(), f, j);

            };
        };
        reveal(CursorOwner::path_metaregion_sound);
    }

    pub proof fn tracked_push_level_owner(tracked &mut self, guard: PageTableGuard<'rcu, C>)
        requires
            old(self).inv(),
            old(self).level > 1,
        ensures
            *final(self) == old(self).push_level_owner(guard),
    {
        C::axiom_current_paging_consts_hardcoded();
        lemma_pte_index_bound::<C>(self.cur_va(), (self.level - 1) as PagingLevel);

        let ghost self0 = *self;
        let tracked mut cont = self.continuations.tracked_remove(self.level - 1);
        let tracked child = cont.tracked_make_cont(
            pte_index_spec::<C>(self.cur_va(), (self.level - 1) as PagingLevel),
            guard,
        );

        self.continuations.tracked_insert(self.level - 1, cont);
        self.continuations.tracked_insert(self.level - 2, child);

        assert(self.continuations == self0.continuations.insert(self.level - 1, cont).insert(
            self.level - 2,
            child,
        ));

        self.popped_too_high = false;

        self.level = (self.level - 1) as u8;
    }

    pub open spec fn pop_level_owner(self) -> (Self, PageTableGuard<'rcu, C>) {
        let child = self.continuations[self.level - 1];
        let cont = self.continuations[self.level as int];
        let (new_cont, guard) = cont.restore(child);
        let new_continuations = self.continuations.insert(self.level as int, new_cont).remove(
            self.level - 1,
        );
        let new_level = (self.level + 1) as u8;
        let popped_too_high = if new_level > self.guard_level {
            true
        } else {
            false
        };
        (
            Self {
                continuations: new_continuations,
                level: new_level,
                popped_too_high: popped_too_high,
                ..self
            },
            guard,
        )
    }

    #[verifier::rlimit(200)]
    pub proof fn pop_level_owner_preserves_invs(self, guards: Guards, regions: MetaRegionOwners)
        requires
            self.inv(),
            self.level < NR_LEVELS,
            self.children_not_locked(guards),
            self.nodes_locked(guards),
            self.metaregion_sound(regions),
        ensures
            self.pop_level_owner().0.inv(),
            self.pop_level_owner().0.only_current_locked(guards),
            self.pop_level_owner().0.nodes_locked(guards),
            self.pop_level_owner().0.metaregion_sound(regions),
    {
        reveal(PageTableOwner::pt_inv_at_depth);
        let child = self.continuations[self.level - 1];
        let child_addr = child.entry_own.node().slot_vaddr();

        self.lemma_map_children_implies(
            CursorOwner::<'rcu, C>::node_unlocked(guards),
            CursorOwner::<'rcu, C>::node_unlocked_except(guards, child_addr),
        );
        reveal(CursorContinuation::map_children);
        reveal(CursorOwner::path_metaregion_sound);
    }

    pub open spec fn move_forward_owner_spec(self) -> Self
        decreases NR_LEVELS - self.level,
        when self.level <= NR_LEVELS
    {
        if self.index() + 1 == NR_ENTRIES && self.level == self.guard_level {
            Self {
                va: (nat_align_down(self.va as nat, page_size::<C>(self.level) as nat)
                    + page_size::<C>(self.level)) as Vaddr,
                popped_too_high: false,
                ..self
            }
        } else if self.index() + 1 < NR_ENTRIES {
            // Advance to the next aligned slot boundary. At the end of the managed
            // range, the resulting VA is exactly the exclusive end sentinel.
            self.inc_index().zero_below_level()
        } else if self.level < NR_LEVELS {
            self.pop_level_owner().0.move_forward_owner_spec()
        } else {
            // self.level == NR_LEVELS && self.index() + 1 == NR_ENTRIES.
            // Preserve lower address bits and the former address-word wrapping semantics.
            Self {
                va: (self.va + page_size::<C>(C::NR_LEVELS())) as Vaddr,
                popped_too_high: false,
                ..self
            }
        }
    }

    pub proof fn lemma_move_forward_increases_va(self)
        requires
            self.inv(),
            self.level <= NR_LEVELS,
            self.in_barrier_va(),
            !self.popped_too_high,
        ensures
            self.move_forward_owner_spec().va > self.va,
    {
        self.lemma_move_forward_va_is_align_up();
        self.lemma_va_plus_page_size_no_overflow(self.level);
        lemma_page_size_ge_base::<PagingConsts>(self.level);
        lemma_nat_align_down_sound(self.va as nat, page_size::<PagingConsts>(self.level) as nat);
    }

    pub proof fn lemma_move_forward_not_popped_too_high(self)
        requires
            self.inv(),
            self.level <= NR_LEVELS,
            self.in_barrier_va(),
        ensures
            !self.move_forward_owner_spec().popped_too_high,
        decreases NR_LEVELS - self.level,
    {
        reveal(PageTableOwner::pt_inv_at_depth);
        if self.level == self.guard_level && self.index() + 1 == NR_ENTRIES {
            return;
        }
        if self.index() + 1 >= NR_ENTRIES && self.level < NR_LEVELS {
            self.pop_level_owner().0.lemma_move_forward_not_popped_too_high();
        }
    }

    proof fn lemma_move_forward_owner_popped_too_high_decreases(self)
        requires
            self.inv(),
            self.level <= NR_LEVELS,
            self.in_barrier_va(),
            self.popped_too_high,
            self.continuations[NR_LEVELS - 1].idx + 1 < NR_ENTRIES,
        ensures
            self.move_forward_owner_spec().max_steps() + Self::max_steps_subtree(
                self.level as usize,
            ) <= self.max_steps(),
        decreases NR_LEVELS - self.level,
    {
        reveal(PageTableOwner::pt_inv_at_depth);
        let l = self.level as usize;
        let st_l = Self::max_steps_subtree(l) as int;

        if self.level == self.guard_level && self.index() + 1 == NR_ENTRIES {
            self.lemma_move_forward_guard_end();
            return;
        }
        if self.index() + 1 < NR_ENTRIES {
            // Case A: advance via inc_index().zero_below_level().
            // (Mirror of subcase A in the main lemma's case 2b.)
            let inc = self.inc_index();

            let new_state = inc.zero_below_level();

            new_state.lemma_max_steps_partial_eq(self, (self.level + 1) as usize);
            let self_idx = self.continuations[self.level - 1].idx as int;
            vstd::arithmetic::mul::lemma_mul_is_distributive_add(
                st_l,
                NR_ENTRIES - self_idx - 2,
                1,
            );

        } else if self.level < NR_LEVELS {
            let popped2 = self.pop_level_owner().0;
            let lp1 = (self.level + 1) as usize;
            popped2.lemma_max_steps_partial_eq(self, lp1);

            assert(Self::max_steps_subtree(l) * 0nat == 0) by (nonlinear_arith);
            popped2.lemma_move_forward_owner_popped_too_high_decreases();

        } else {
            assert(false);
        }
    }

    pub proof fn lemma_move_forward_owner_decreases_steps(self)
        requires
            self.inv(),
            self.level <= NR_LEVELS,
            self.in_barrier_va(),
            !self.popped_too_high,
        ensures
            self.move_forward_owner_spec().max_steps() + Self::max_steps_subtree(
                self.level as usize,
            ) <= self.max_steps(),
            self.move_forward_owner_spec().max_steps() < self.max_steps(),
        decreases NR_LEVELS - self.level,
    {
        reveal(PageTableOwner::pt_inv_at_depth);
        self.lemma_in_barrier_va_level_le_guard_level();
        let l = self.level as usize;
        let st_l = Self::max_steps_subtree(l) as int;

        if self.level == self.guard_level && self.index() + 1 == NR_ENTRIES {
            self.lemma_move_forward_guard_end();
            return;
        }
        if self.index() + 1 < NR_ENTRIES {
            let inc = self.inc_index();

            let new_state = inc.zero_below_level();

            new_state.lemma_max_steps_partial_eq(self, (self.level + 1) as usize);
            let self_idx = self.continuations[self.level - 1].idx as int;
            let tail = self.max_steps_partial((self.level + 1) as usize) as int;
            vstd::arithmetic::mul::lemma_mul_is_distributive_add(
                st_l,
                NR_ENTRIES - self_idx - 2,
                1,
            );

        } else if self.level < NR_LEVELS {
            let popped = self.pop_level_owner().0;
            let lp1 = (self.level + 1) as usize;
            popped.lemma_max_steps_partial_eq(self, lp1);

            assert(Self::max_steps_subtree(l) * 0nat == 0) by (nonlinear_arith);

            if !popped.popped_too_high {
                popped.lemma_move_forward_owner_decreases_steps();

            } else {
                popped.lemma_move_forward_owner_popped_too_high_decreases();
            }
        } else {
            assert(false);
        }
    }

    /// Advancing the cursor reaches the next slot boundary, including carries to a parent.
    #[verifier::spinoff_prover]
    pub proof fn lemma_move_forward_va_is_align_up(self)
        requires
            self.inv(),
            self.level <= NR_LEVELS,
            self.in_barrier_va(),
            !self.popped_too_high,
        ensures
            self.move_forward_owner_spec().va == self@.align_up_spec(
                page_size::<PagingConsts>(self.level),
            ),
        decreases NR_LEVELS - self.level,
    {
        C::lemma_paging_consts_properties();
        C::axiom_current_paging_consts_hardcoded();
        reveal(PageTableOwner::pt_inv_at_depth);
        if self.level == self.guard_level && self.index() + 1 == NR_ENTRIES {
            self.lemma_move_forward_guard_end();
            return;
        }
        if self.index() + 1 < NR_ENTRIES {
            self.inc_and_zero_increases_va();
            return;
        }
        assert(self.level < NR_LEVELS);
        let popped = self.pop_level_owner().0;
        assert(self.move_forward_owner_spec().va == popped.move_forward_owner_spec().va);
        if !popped.popped_too_high {
            popped.lemma_move_forward_va_is_align_up();
            popped.lemma_va_plus_page_size_no_overflow(popped.level);
        } else {
            popped.inc_and_zero_increases_va();
            popped.lemma_inc_index_va();
        }

        self.lemma_va_plus_page_size_no_overflow(self.level);
        lemma_page_size_next::<C>(self.level);
        lemma_page_size_ge_base::<PagingConsts>(self.level);
        lemma_nat_align_down_sound(self.va as nat, page_size::<PagingConsts>(self.level) as nat);
        let next = self@.align_up_spec(page_size::<PagingConsts>(self.level));
        lemma_mod_add_multiples_vanish(
            nat_align_down(self.va as nat, page_size::<PagingConsts>(self.level) as nat) as int,
            page_size::<PagingConsts>(self.level) as int,
        );
        lemma_next_slot_pte_index::<C>(self.va, next, self.level);
        assert(pte_index_spec::<C>(next, self.level) == 0);
        lemma_next_slot_pte_index::<C>(popped.va, next, popped.level);
        assert(self@.align_up_spec(page_size::<PagingConsts>(self.level)) == popped@.align_up_spec(
            page_size::<PagingConsts>(popped.level),
        ));
    }

    /// After popping a level, the total view_mappings is preserved.
    /// The restored parent at index self.level absorbs the child's mappings,
    /// and both are within the view_mappings range [self.level, NR_LEVELS).
    pub proof fn lemma_pop_level_owner_preserves_mappings(self)
        requires
            self.inv(),
            self.level < NR_LEVELS,
            self.in_barrier_va(),
        ensures
            self.pop_level_owner().0@.mappings == self@.mappings,
    {
        broadcast use {CursorContinuation::group_lemmas, CursorOwner::group_lemmas};

        let child = self.continuations[self.level - 1];
        let parent = self.continuations[self.level as int];
        let (restored_parent, _) = parent.restore(child);
        let popped = self.pop_level_owner().0;
        let child_subtree = child.as_subtree();

        let r = restored_parent;
        let p = parent.put_child(child_subtree);
        assert forall|j: int| 0 <= j < r.children.len() implies r.children[j]
            == p.children[j] by {};

        assert(restored_parent.view_mappings() == parent.put_child(child_subtree).view_mappings())
            by {};

        parent.view_mappings_put_child(child_subtree);
        child.as_page_table_owner_preserves_view_mappings();

        assert(popped.view_mappings() == self.view_mappings()) by {
            assert forall|m: Mapping|
                self.view_mappings().contains(m) implies popped.view_mappings().contains(m) by {
                let i = choose|i: int|
                    self.level - 1 <= i < NR_LEVELS && (
                    #[trigger] self.continuations[i]).view_mappings().contains(m);
                if i == self.level - 1 {
                    assert(popped.continuations[self.level as int].view_mappings().contains(m));
                } else if i == self.level {
                    assert(popped.continuations[self.level as int].view_mappings().contains(m));
                } else {
                    assert(popped.continuations[i] == self.continuations[i]);
                }
            };

        };
    }

    pub proof fn lemma_move_forward_owner_preserves_mappings(self)
        requires
            self.inv(),
            self.in_barrier_va(),
        ensures
            self.move_forward_owner_spec()@.mappings == self@.mappings,
        decreases NR_LEVELS - self.level,
    {
        reveal(PageTableOwner::pt_inv_at_depth);
        broadcast use {CursorContinuation::group_lemmas, CursorOwner::group_lemmas};

        if self.level == self.guard_level && self.index() + 1 == NR_ENTRIES {
            return;
        }
        if self.index() + 1 < NR_ENTRIES {
            let inc = self.inc_index();
            let result = inc.zero_below_level();

            let old_cont = self.continuations[self.level - 1];
            let new_cont = old_cont.inc_index();

            assert(result.view_mappings() == self.view_mappings()) by {
                assert forall|m: Mapping|
                    self.view_mappings().contains(m) implies result.view_mappings().contains(m) by {
                    let i = choose|i: int|
                        self.level - 1 <= i < NR_LEVELS && (
                        #[trigger] self.continuations[i]).view_mappings().contains(m);
                    if i == self.level - 1 {
                        assert(result.continuations[i].view_mappings().contains(m));
                    } else {
                        assert(result.continuations[i] == self.continuations[i]);
                    }
                };

            };

        } else if self.level < NR_LEVELS {
            let popped = self.pop_level_owner().0;

            self.lemma_pop_level_owner_preserves_mappings();
            popped.lemma_move_forward_owner_preserves_mappings();
        }
    }

    /// Advancing the guard's final entry retains its continuation at the node-end sentinel.
    pub proof fn lemma_move_forward_guard_end(self)
        requires
            self.inv(),
            self.in_barrier_va(),
            self.level == self.guard_level,
            self.index() + 1 == NR_ENTRIES,
        ensures
            self.move_forward_owner_spec().va == self.locked_range().end,
            self.move_forward_owner_spec().at_or_past_barrier_end(),
            self.move_forward_owner_spec().inv(),
            self.move_forward_owner_spec().max_steps() == 0,
            self.move_forward_owner_spec().va == self@.align_up_spec(
                page_size::<PagingConsts>(self.level),
            ),
    {
        use vstd::arithmetic::div_mod::*;
        C::lemma_paging_consts_properties();
        C::axiom_current_paging_consts_hardcoded();
        self.lemma_cur_pte_index();
        self.lemma_locked_range_span();
        self.lemma_va_plus_page_size_no_overflow(self.level);
        lemma_page_size_next::<C>(self.level);
        lemma_pte_index_spec_is_div_mod::<C>(self.va, self.level);
        let ps = page_size::<C>(self.level) as int;
        let node_ps = page_size::<C>((self.level + 1) as PagingLevel) as int;
        lemma_fundamental_div_mod(self.prefix as int, node_ps);
        lemma_fundamental_div_mod_converse(
            self.va as int,
            node_ps,
            self.prefix as int / node_ps,
            self.va - self.prefix,
        );
        lemma_mod_breakdown(self.va as int, ps, NR_ENTRIES as int);
        lemma_nat_align_down_sound(self.va as nat, ps as nat);
        assert(nat_align_down(self.va as nat, ps as nat) + ps == self.prefix + node_ps)
            by (nonlinear_arith)
            requires
                self.va as int % node_ps == self.va - self.prefix,
                self.va as int % node_ps == ps * (self.va as int / ps % NR_ENTRIES as int)
                    + self.va as int % ps,
                self.va as int / ps % NR_ENTRIES as int == NR_ENTRIES - 1,
                node_ps == ps * NR_ENTRIES,
                nat_align_down(self.va as nat, ps as nat) == self.va - self.va as int % ps,
        ;
        let next = self.move_forward_owner_spec().va;
        self.lemma_locked_range_page_aligned();
        lemma_page_table_managed_index_bounds::<C>(self.va);
        lemma_page_size_divides::<C>(self.level, C::NR_LEVELS());
        lemma_nat_align_down_within_block(
            self.va as nat,
            page_size::<C>(self.level) as nat,
            page_size::<C>(C::NR_LEVELS()) as nat,
        );
        lemma_page_size_next::<C>(C::NR_LEVELS());
        lemma_vaddr_leading_part_is_align_down::<C>(self.va);
        let root_base = vaddr_leading_part_spec::<C>(self.va);
        let root_size = page_size::<C>((C::NR_LEVELS() + 1) as PagingLevel);
        lemma_nat_align_down_sound(self.va as nat, root_size as nat);
        lemma_same_node_vaddr_leading_part_match::<C>(next, self.va, root_base, C::NR_LEVELS());
        assert(self.move_forward_owner_spec().inv()) by {
            reveal(<CursorOwner as Inv>::inv);
        };
    }
}

} // verus!
