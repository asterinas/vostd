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
        CursorState::ReadLocking(_) => AtomicCursorState::Void,
        CursorState::WriteLocked(path) => AtomicCursorState::Locked(path.last()),
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

        locking_start(cpu) => {
            assert_maps_equal!(interp(pre).cursors, interp(post).cursors);
            AtomicSpec::show::no_op(interp(pre), interp(post));
        }

        unlocking_end(cpu) => {
            assert_maps_equal!(interp(pre).cursors, interp(post).cursors);
            AtomicSpec::show::no_op(interp(pre), interp(post));
        }

        read_lock(cpu, nid) => {
            assert_maps_equal!(interp(pre).cursors, interp(post).cursors);
            AtomicSpec::show::no_op(interp(pre), interp(post));
        }

        read_unlock(cpu, nid) => {
            assert_maps_equal!(interp(pre).cursors, interp(post).cursors);
            AtomicSpec::show::no_op(interp(pre), interp(post));
        }

        write_lock(cpu, nid) => {
            broadcast use NodeHelper::lemma_in_subtree_iff_in_subtree_range;
            assert(
                interp(post).cursors =~=
                interp(pre).cursors.insert(
                    cpu,
                    AtomicCursorState::Locked(nid),
                )
            );
            assert forall |_cpu|
                #[trigger] interp(pre).cursors.contains_key(_cpu) &&
                interp(pre).cursors[_cpu] is Locked
            implies {
                let _nid = interp(pre).cursors[_cpu]->Locked_0;
                !NodeHelper::in_subtree(nid, _nid) &&
                !NodeHelper::in_subtree(_nid, nid)
            } by {
                let _nid = interp(pre).cursors[_cpu]->Locked_0;
                assert(pre.cursors.contains_key(_cpu));
                assert(pre.cursors[_cpu] is WriteLocked);
                assert(pre.cursors[_cpu].get_write_lock_node() == _nid);
                if _cpu != cpu {
                    assert(post.cursors[_cpu] =~= pre.cursors[_cpu]);
                    assert(post.inv_non_overlapping()) by {
                        post.lemma_inv_implies_inv_non_overlapping();
                    };
                }
            };
            AtomicSpec::show::lock(interp(pre), interp(post), cpu, nid);
        }

        write_unlock(cpu, nid) => {
            assert(
                interp(post).cursors =~=
                interp(pre).cursors.insert(
                    cpu,
                    AtomicCursorState::Void,
                )
            );
            AtomicSpec::show::unlock(interp(pre), interp(post), cpu);
        }

        in_protocol_write_lock(cpu, nid) => {
            assert_maps_equal!(interp(pre).cursors, interp(post).cursors);
            AtomicSpec::show::no_op(interp(pre), interp(post));
        }

        in_protocol_write_unlock(cpu, nid) => {
            assert_maps_equal!(interp(pre).cursors, interp(post).cursors);
            AtomicSpec::show::no_op(interp(pre), interp(post));
        }

        allocate(cpu, nid) => {
            assert_maps_equal!(interp(pre).cursors, interp(post).cursors);
            AtomicSpec::show::no_op(interp(pre), interp(post));
        }

        deallocate(cpu, nid) => {
            assert_maps_equal!(interp(pre).cursors, interp(post).cursors);
            AtomicSpec::show::no_op(interp(pre), interp(post));
        }

    }}
}

} // verus!
