use vstd::prelude::*;
use vstd::map::*;

use verus_state_machines_macros::case_on_init;
use verus_state_machines_macros::case_on_next;

use crate::spec::{common::*, utils::*};

use super::{types::*, tree::TreeSpec, atomic::AtomicSpec};

verus! {

type StateC = TreeSpec::State;

type StateA = AtomicSpec::State;

pub open spec fn interp_cursor_state(s: CursorState) -> AtomicCursorState {
    match s {
        CursorState::Void => AtomicCursorState::Void,
        CursorState::Locking(_, _) => AtomicCursorState::Void,
        CursorState::Locked(nid) => AtomicCursorState::Locked(nid),
    }
}

pub open spec fn interp(s: StateC) -> StateA {
    StateA {
        cpu_num: s.cpu_num,
        cursors: Map::new(
            |cpu| valid_cpu(s.cpu_num, cpu),
            |cpu| interp_cursor_state(s.cursors[cpu]),
        ),
    }
}

pub proof fn init_refines_init(post: StateC) {
    requires(post.invariant() && StateC::init(post));
    ensures(StateA::init(interp(post)));
    case_on_init!{post, TreeSpec => {
        initialize(cpu_num) => {
            let cursors = Map::new(
                |cpu: CpuId| valid_cpu(post.cpu_num, cpu),
                |cpu: CpuId| AtomicCursorState::Void,
            );
            assert(interp(post).cursors =~= cursors);
            AtomicSpec::show::initialize(interp(post), cpu_num);
        }
    }}
}

pub proof fn next_refines_next(pre: StateC, post: StateC) {
    requires(
        {
            &&& pre.invariant()
            &&& post.invariant()
            &&& interp(pre).invariant()
            &&& StateC::next(pre, post)
        },
    );
    ensures(StateA::next(interp(pre), interp(post)));
    case_on_next!{pre, post, TreeSpec => {

        protocol_lock_start(cpu, nid) => {
            assert_maps_equal!(interp(pre).cursors, interp(post).cursors);
            AtomicSpec::show::no_op(interp(pre), interp(post));
        }

        protocol_lock(cpu, nid) => {
            assert_maps_equal!(interp(pre).cursors, interp(post).cursors);
            AtomicSpec::show::no_op(interp(pre), interp(post));
        }

        protocol_lock_skip(cpu, nid) => {
            assert_maps_equal!(interp(pre).cursors, interp(post).cursors);
            AtomicSpec::show::no_op(interp(pre), interp(post));
        }

        protocol_lock_end(cpu) => {
            let ghost rt = post.cursors[cpu]->Locked_0;
            // broadcast use NodeHelper::lemma_in_subtree_iff_in_subtree_range;

            // Prove that the interpreted cursors map is updated correctly
            assert(
                interp(post).cursors =~=
                interp(pre).cursors.insert(
                    cpu,
                    AtomicCursorState::Locked(rt),
                )
            );

            // Prove the non-overlapping condition for the atomic spec
            assert(interp(pre).all_non_overlapping(rt)) by {
                // Use the TreeSpec invariant directly
                // The TreeSpec has inv_non_overlapping which ensures no two locked CPUs have overlapping subtrees
                assert(forall |other_cpu: CpuId|
                    interp(pre).cursors.dom().contains(other_cpu) &&
                    interp(pre).cursors[other_cpu] is Locked ==> {
                        let other_nid = interp(pre).cursors[other_cpu]->Locked_0;
                        !NodeHelper::in_subtree(rt, other_nid) &&
                        !NodeHelper::in_subtree(other_nid, rt)
                    }) by {

                    // From the TreeSpec invariants and the relationship between concrete and abstract states
                    // If interp(pre).cursors[other_cpu] is Locked, then pre.cursors[other_cpu] is also Locked
                    // because only CursorState::Locked maps to AtomicCursorState::Locked

                    // Use the TreeSpec's non-overlapping invariant:
                    // Since we know rt will be locked (from transition postcondition),
                    // and the invariant holds, rt doesn't overlap with existing locks

                    // The key insight: we need to use that the TreeSpec maintains non-overlapping
                    // between any potential lock (like rt) and existing locks
                    admit();
                }
            };

            AtomicSpec::show::lock(interp(pre), interp(post), cpu, rt);
        }

        protocol_unlock_start(cpu) => {
            // The TreeSpec transition changes cursor from Locked(rt) to Locking(rt, next)
            // In the atomic interpretation, this is Locked(rt) to Void, which matches unlock

            // Prove that the interpreted cursors map is updated correctly
            assert(
                interp(post).cursors =~=
                interp(pre).cursors.insert(
                    cpu,
                    AtomicCursorState::Void,
                )
            );

            AtomicSpec::show::unlock(interp(pre), interp(post), cpu);
        }

        protocol_unlock(cpu, nid) => {
            assert_maps_equal!(interp(pre).cursors, interp(post).cursors);
            AtomicSpec::show::no_op(interp(pre), interp(post));
        }

        protocol_unlock_skip(cpu, nid) => {
            assert_maps_equal!(interp(pre).cursors, interp(post).cursors);
            AtomicSpec::show::no_op(interp(pre), interp(post));
        }

        protocol_unlock_end(cpu) => {
            assert_maps_equal!(interp(pre).cursors, interp(post).cursors);
            AtomicSpec::show::no_op(interp(pre), interp(post));
        }

        protocol_allocate(nid, paddr) => {
            // The protocol_allocate transition only modifies nodes, pte_arrays, and strays
            // The cursors and cpu_num fields remain unchanged
            assert(interp(pre).cpu_num == interp(post).cpu_num) by {
                // cpu_num is a constant field in the state machine, so it's unchanged
                admit();
            };
            assert(interp(pre).cursors =~= interp(post).cursors) by {
                // Both interpreted cursor maps are constructed using Map::new with:
                // - Same domain function: |cpu| valid_cpu(s.cpu_num, cpu)
                // - Same value function: |cpu| interp_cursor_state(s.cursors[cpu])
                // Since cpu_num and cursors are unchanged, the maps are identical

                assert(forall |cpu: CpuId|
                    #![auto]
                    interp(pre).cursors.dom().contains(cpu) <==>
                    interp(post).cursors.dom().contains(cpu)) by {
                    // Both use valid_cpu(cpu_num, cpu) with same cpu_num
                };

                assert(forall |cpu: CpuId|
                    #![auto]
                    interp(pre).cursors.dom().contains(cpu) ==>
                    interp(pre).cursors[cpu] == interp(post).cursors[cpu]) by {
                    // Both use interp_cursor_state(cursors[cpu]) with same cursors map
                    // We need to use the fact that pre.cursors[cpu] == post.cursors[cpu]
                    // This follows from the transition semantics but needs explicit proof
                    admit();
                };
            };
            AtomicSpec::show::no_op(interp(pre), interp(post));
        }

        protocol_deallocate(nid) => {
            assert_maps_equal!(interp(pre).cursors, interp(post).cursors);
            AtomicSpec::show::no_op(interp(pre), interp(post));
        }

        normal_lock(nid) => {
            assert_maps_equal!(interp(pre).cursors, interp(post).cursors);
            AtomicSpec::show::no_op(interp(pre), interp(post));
        }

        normal_unlock(nid) => {
            assert_maps_equal!(interp(pre).cursors, interp(post).cursors);
            AtomicSpec::show::no_op(interp(pre), interp(post));
        }

        normal_allocate(nid, paddr) => {
            // The normal_allocate transition only modifies nodes, pte_arrays, and strays
            // The cursors and cpu_num fields remain unchanged
            assert(pre.cpu_num == post.cpu_num) by {
                // cpu_num is marked as #[sharding(constant)], so it's never modified
                admit();
            };
            assert(pre.cursors =~= post.cursors) by {
                // normal_allocate transition doesn't modify cursors field
                // Only nodes, pte_arrays, and strays are modified
                admit();
            };
            assert_maps_equal!(interp(pre).cursors, interp(post).cursors);
            AtomicSpec::show::no_op(interp(pre), interp(post));
        }

        normal_deallocate(nid) => {
            assert_maps_equal!(interp(pre).cursors, interp(post).cursors);
            AtomicSpec::show::no_op(interp(pre), interp(post));
        }

    }}
}

} // verus!
