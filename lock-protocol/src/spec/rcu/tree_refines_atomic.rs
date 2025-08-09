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
        initialize(cpu_num, paddrs) => {
            let cursors = Map::new(
                |cpu: CpuId| valid_cpu(post.cpu_num, cpu),
                |cpu: CpuId| AtomicCursorState::Void,
            );
            assert(interp(post).cursors == cursors);
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
            let rt = post.cursors[cpu]->Locked_0;

            assert(NodeHelper::valid_nid(rt)) by {
                assert(post.cursors[cpu].wf());
            };

            assert(interp(pre).all_non_overlapping(rt)) by {
                broadcast use group_node_helper_lemmas;
                assert (forall |cpu_id: CpuId| #[trigger]
                    interp(pre).cursors.contains_key(cpu_id) &&
                    interp(pre).cursors[cpu_id] is Locked ==>
                    {
                        let nid = interp(pre).cursors[cpu_id]->Locked_0;
                        !NodeHelper::in_subtree(nid, rt) && !NodeHelper::in_subtree(rt, nid)
                    });
            };

            assert(
                interp(post).cursors ==
                interp(pre).cursors.insert(
                    cpu,
                    AtomicCursorState::Locked(rt),
                )
            );

            AtomicSpec::show::lock(interp(pre), interp(post), cpu, rt);
        }

        protocol_unlock_start(cpu) => {
            // The TreeSpec transition changes cursor from Locked(rt) to Locking(rt, next)
            // In the atomic interpretation, this is Locked(rt) to Void, which matches unlock

            // Prove that the interpreted cursors map is updated correctly
            assert(
                interp(post).cursors ==
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

        protocol_allocate(cpu, nid, paddr) => {
            // The protocol_allocate transition only modifies nodes, pte_arrays, and strays
            // The cursors and cpu_num fields remain unchanged
            // assert(interp(pre).cpu_num == interp(post).cpu_num);
            assert(interp(pre).cursors == interp(post).cursors) by {
                // Both interpreted cursor maps are constructed using Map::new with:
                // - Same domain function: |cpu| valid_cpu(s.cpu_num, cpu)
                // - Same value function: |cpu| interp_cursor_state(s.cursors[cpu])
                // Since cpu_num and cursors are unchanged, the maps are identical

                assert(forall |cpu: CpuId|
                    #![auto]
                    interp(pre).cursors.contains_key(cpu) <==>
                    interp(post).cursors.contains_key(cpu)) by {
                    // Both use valid_cpu(cpu_num, cpu) with same cpu_num
                };

                assert(forall |cpu: CpuId|
                    #![auto]
                    interp(pre).cursors.contains_key(cpu) ==>
                    interp(pre).cursors[cpu] == interp(post).cursors[cpu]);
            };
            AtomicSpec::show::no_op(interp(pre), interp(post));
        }

        protocol_deallocate(cpu, nid) => {
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
            assert(pre.cpu_num == post.cpu_num);
            assert(pre.cursors == post.cursors);
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
