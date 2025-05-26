use builtin::*;
use builtin_macros::*;
use vstd::*;
use vstd::map::*;

use state_machines_macros::case_on_init;
use state_machines_macros::case_on_next;
// use state_machines_macros::case_on_next_strong;

use super::common::*;
use super::utils::*;

use super::{concrete_tree_spec::ConcreteSpec, range_spec::RangeSpec};

verus! {

type StateC = ConcreteSpec::State;

type StateA = RangeSpec::State;

pub open spec fn node_to_slot(s: NodeState) -> SlotState {
    match s {
        NodeState::Empty => SlotState::Empty,
        NodeState::EmptyLocked => SlotState::EmptyLocked,
        NodeState::Free => SlotState::Free,
        NodeState::Locked => SlotState::Locked,
        NodeState::LockedOutside => SlotState::LockedOutside,
    }
}

pub open spec fn cursor_to_range(s: CursorState) -> RangeState {
    match s {
        CursorState::Empty => RangeState::Empty,
        CursorState::Creating(l, r, cur_p) => RangeState::Creating(l, r, cur_p),
        CursorState::Hold(l, r) => RangeState::Hold(l, r),
        CursorState::Destroying(l, r, cur_p) => RangeState::Destroying(l, r, cur_p),
    }
}

pub open spec fn interp(s: StateC) -> StateA {
    StateA {
        cpu_num: s.cpu_num,
        size: NodeHelper::total_size(),
        slots: Map::new(|nid: NodeId| NodeHelper::valid_nid(nid), |nid| node_to_slot(s.nodes[nid])),
        ranges: Map::new(
            |cpu: CpuId| valid_cpu(s.cpu_num, cpu),
            |cpu| cursor_to_range(s.cursors[cpu]),
        ),
    }
}

pub proof fn init_refines_init(post: StateC) {
    requires(post.invariant() && StateC::init(post));
    ensures(StateA::init(interp(post)));
    case_on_init!{post, ConcreteSpec => {
        initialize(cpu_num) => {
            assert(NodeHelper::total_size() > 0) by {
                NodeHelper::lemma_tree_size_spec_table();
            };
            let slots = Map::new(
                |i| valid_pos(NodeHelper::total_size(), i),
                |i| if i == 0 { SlotState::Free } else { SlotState::Empty },
            );
            assert(interp(post).slots =~= slots);
            let ranges = Map::new(
                |cpu: CpuId| valid_cpu(post.cpu_num, cpu),
                |cpu: CpuId| RangeState::Empty,
            );
            assert(interp(post).ranges =~= ranges);

            RangeSpec::show::initialize(interp(post), cpu_num, NodeHelper::total_size());
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
    case_on_next!{pre, post, ConcreteSpec => {

        node_acquire_outside_cursor(nid) => {
            assert(interp(post).slots =~= interp(pre).slots.insert(nid, SlotState::LockedOutside));
            RangeSpec::show::slot_acquire_outside_range(interp(pre), interp(post), nid);
        }

        node_release_outside_cursor(nid) => {
            assert(interp(post).slots =~= interp(pre).slots.insert(nid, SlotState::Free));
            RangeSpec::show::slot_release_outside_range(interp(pre), interp(post), nid);
        }

        node_create_in_cursor(cpu, nid) => {
            assert(interp(post).slots =~= interp(pre).slots.insert(nid, SlotState::Locked));
            RangeSpec::show::slot_create_in_range(interp(pre), interp(post), cpu, nid);
        }

        node_create_outside_cursor(nid) => {
            assert(interp(post).slots =~= interp(pre).slots.insert(nid, SlotState::LockedOutside));
            RangeSpec::show::slot_create_outside_range(interp(pre), interp(post), nid);
        }

        cursor_create_start(cpu, nid) => {
            let new_range = RangeState::Creating(nid, NodeHelper::next_outside_subtree(nid), nid);
            assert(interp(post).ranges =~= interp(pre).ranges.insert(cpu, new_range));
            RangeSpec::show::range_acquire_start(interp(pre), interp(post),
                cpu, nid, NodeHelper::next_outside_subtree(nid)
            );
        }

        node_acquire(cpu, nid) => {
            assert(interp(post).slots =~= interp(pre).slots.insert(nid, SlotState::Locked));
            let l = interp(pre).ranges[cpu]->Creating_0;
            let r = interp(pre).ranges[cpu]->Creating_1;
            let cur_p = interp(pre).ranges[cpu]->Creating_2;
            let new_range = RangeState::Creating(l, r, cur_p + 1);
            assert(interp(post).ranges =~= interp(pre).ranges.insert(cpu, new_range));
            RangeSpec::show::pos_acquire(interp(pre), interp(post), cpu, nid);
        }

        node_acquire_skip(cpu, nid) => {
            assert(NodeHelper::sub_tree_size(nid) > 0) by {
                NodeHelper::lemma_sub_tree_size_lowerbound(nid);
            };
            let _nodes = Map::new(
                |_nid: NodeId| NodeHelper::in_subtree_range(nid, _nid),
                |_nid| NodeState::Empty,
            );
            assert(_nodes.submap_of(pre.nodes));
            assert forall |_nid| #[trigger] NodeHelper::in_subtree_range(nid, _nid) implies {
                pre.nodes[_nid] is Empty
            } by {
                assert(_nodes.dom().contains(_nid));
                assert(pre.nodes.dom().contains(_nid));
            };
            assert(forall |_nid| NodeHelper::in_subtree_range(nid, _nid) <==>
                nid <= _nid < NodeHelper::next_outside_subtree(nid)
            );
            assert forall |i| nid <= i < NodeHelper::next_outside_subtree(nid) implies {
                interp(pre).slots[i] is Empty
            } by {
                assert(pre.nodes[i] is Empty) by {
                    assert(NodeHelper::in_subtree_range(nid, i));
                };
            };
            assert(forall |_nid| #[trigger] NodeHelper::in_subtree_range(nid, _nid) ==>
                post.nodes[_nid] is EmptyLocked
            );
            let _slots = Map::new(
                |i| nid <= i < NodeHelper::next_outside_subtree(nid),
                |i| SlotState::EmptyLocked,
            );
            assert(interp(post).slots =~= interp(pre).slots.union_prefer_right(_slots));

            let l = interp(pre).ranges[cpu]->Creating_0;
            let r = interp(pre).ranges[cpu]->Creating_1;
            let cur_p = interp(pre).ranges[cpu]->Creating_2;
            let new_range = RangeState::Creating(l, r, NodeHelper::next_outside_subtree(nid));
            assert(interp(post).ranges =~= interp(pre).ranges.insert(cpu, new_range));

            RangeSpec::show::pos_acquire_skip(interp(pre), interp(post),
                cpu, nid, NodeHelper::sub_tree_size(nid)
            );
        }

        cursor_create_end(cpu) => {
            let l = interp(pre).ranges[cpu]->Creating_0;
            let r = interp(pre).ranges[cpu]->Creating_1;
            let cur_p = interp(pre).ranges[cpu]->Creating_2;
            let new_range = RangeState::Hold(l, r);
            assert(interp(post).ranges =~= interp(pre).ranges.insert(cpu, new_range));
            RangeSpec::show::range_acquire_end(interp(pre), interp(post), cpu);
        }

        cursor_destroy_start(cpu) => {
            let l = interp(pre).ranges[cpu]->Hold_0;
            let r = interp(pre).ranges[cpu]->Hold_1;
            let new_range = RangeState::Destroying(l, r, r);
            assert(interp(post).ranges =~= interp(pre).ranges.insert(cpu, new_range));
            RangeSpec::show::range_release_start(interp(pre), interp(post), cpu);
        }

        node_release(cpu, nid) => {
            assert(interp(post).slots =~= interp(pre).slots.insert(nid, SlotState::Free));
            let l = interp(pre).ranges[cpu]->Destroying_0;
            let r = interp(pre).ranges[cpu]->Destroying_1;
            let cur_p = interp(pre).ranges[cpu]->Destroying_2;
            let new_range = RangeState::Destroying(l, r, nid);
            assert(interp(post).ranges =~= interp(pre).ranges.insert(cpu, new_range));
            RangeSpec::show::pos_release(interp(pre), interp(post), cpu, nid);
        }

        node_release_skip(cpu, nid) => {
            assert(NodeHelper::sub_tree_size(nid) > 0) by {
                NodeHelper::lemma_sub_tree_size_lowerbound(nid);
            };
            let _nodes = Map::new(
                |_nid: NodeId| NodeHelper::in_subtree_range(nid, _nid),
                |_nid| NodeState::EmptyLocked,
            );
            assert(_nodes.submap_of(pre.nodes));
            assert forall |_nid| #[trigger] NodeHelper::in_subtree_range(nid, _nid) implies {
                pre.nodes[_nid] is EmptyLocked
            } by {
                assert(_nodes.dom().contains(_nid));
                assert(pre.nodes.dom().contains(_nid));
            };
            assert(forall |_nid| NodeHelper::in_subtree_range(nid, _nid) <==>
                nid <= _nid < NodeHelper::next_outside_subtree(nid)
            );
            assert forall |i| nid <= i < NodeHelper::next_outside_subtree(nid) implies {
                interp(pre).slots[i] is EmptyLocked
            } by {
                assert(pre.nodes[i] is EmptyLocked) by {
                    assert(NodeHelper::in_subtree_range(nid, i));
                };
            };
            assert(forall |_nid| #[trigger] NodeHelper::in_subtree_range(nid, _nid) ==>
                post.nodes[_nid] is Empty
            );
            let _slots = Map::new(
                |i| nid <= i < NodeHelper::next_outside_subtree(nid),
                |i| SlotState::Empty,
            );
            assert(interp(post).slots =~= interp(pre).slots.union_prefer_right(_slots));

            let l = interp(pre).ranges[cpu]->Destroying_0;
            let r = interp(pre).ranges[cpu]->Destroying_1;
            let cur_p = interp(pre).ranges[cpu]->Destroying_2;
            let new_range = RangeState::Destroying(l, r, nid);
            assert(interp(post).ranges =~= interp(pre).ranges.insert(cpu, new_range));

            RangeSpec::show::pos_release_skip(interp(pre), interp(post),
                cpu, nid, NodeHelper::sub_tree_size(nid),
            );
        }

        cursor_destroy_end(cpu) => {
            let new_range = RangeState::Empty;
            assert(interp(post).ranges =~= interp(pre).ranges.insert(cpu, new_range));
            RangeSpec::show::range_release_end(interp(pre), interp(post), cpu);
        }

    }}
}

} // verus!
