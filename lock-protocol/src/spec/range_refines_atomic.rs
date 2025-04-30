use builtin::*;
use builtin_macros::*;
use vstd::*;
use vstd::map::*;

use state_machines_macros::case_on_init;
use state_machines_macros::case_on_next;
// use state_machines_macros::case_on_next_strong;

use super::common::*;

use super::{range_spec::RangeSpec, atomic_spec::AtomicSpec};

verus! {

type StateC = RangeSpec::State;

type StateA = AtomicSpec::State;

pub open spec fn state_trans(s: RangeState) -> RangeState {
    match s {
        RangeState::Empty => RangeState::Empty,
        RangeState::Creating(_, _, _) => RangeState::Empty,
        RangeState::Hold(l, r) => RangeState::Hold(l, r),
        RangeState::Destroying(_, _, _) => RangeState::Empty,
    }
}

pub open spec fn interp(s: StateC) -> StateA {
    StateA {
        cpu_num: s.cpu_num,
        size: s.size,
        ranges: Map::new(
            |cpu: CpuId| valid_cpu(s.cpu_num, cpu),
            |cpu: CpuId| state_trans(s.ranges[cpu]),
        ),
    }
}

pub proof fn init_refines_init(post: StateC) {
    requires(post.invariant() && StateC::init(post));
    ensures(StateA::init(interp(post)));
    case_on_init!{post, RangeSpec => {
        initialize(cpu_num, size) => {
            let new_map = Map::new(
                |cpu: CpuId| valid_cpu(post.cpu_num, cpu),
                |cpu: CpuId| RangeState::Empty,
            );
            assert(interp(post).ranges =~= new_map);

            AtomicSpec::show::initialize(interp(post), cpu_num, size);
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
    case_on_next!{pre, post, RangeSpec => {

        slot_acquire_outside_range(p) => {
            assert_maps_equal!(interp(pre).ranges, interp(post).ranges);
            AtomicSpec::show::no_op(interp(pre), interp(post));
        }

        slot_release_outside_range(p) => {
            assert_maps_equal!(interp(pre).ranges, interp(post).ranges);
            AtomicSpec::show::no_op(interp(pre), interp(post));
        }

        slot_create_in_range(cpu, p) => {
            assert_maps_equal!(interp(pre).ranges, interp(post).ranges);
            AtomicSpec::show::no_op(interp(pre), interp(post));
        }

        slot_create_outside_range(p) => {
            assert_maps_equal!(interp(pre).ranges, interp(post).ranges);
            AtomicSpec::show::no_op(interp(pre), interp(post));
        }

        range_acquire_start(cpu, l, r) => {
            assert_maps_equal!(interp(pre).ranges, interp(post).ranges);
            AtomicSpec::show::no_op(interp(pre), interp(post));
        }

        pos_acquire(cpu, p) => {
            assert_maps_equal!(interp(pre).ranges, interp(post).ranges);
            AtomicSpec::show::no_op(interp(pre), interp(post));
        }

        pos_acquire_skip(cpu, p, skip_len) => {
            assert_maps_equal!(interp(pre).ranges, interp(post).ranges);
            AtomicSpec::show::no_op(interp(pre), interp(post));
        }

        range_acquire_end(cpu) => {
            let l = post.ranges[cpu].get_Hold_0();
            let r = post.ranges[cpu].get_Hold_1();
            let new_range = RangeState::Hold(l, r);
            assert(interp(pre).ranges.insert(cpu, new_range) =~= interp(post).ranges);

            assert(forall |_cpu| #![auto] _cpu != cpu && post.ranges.contains_key(_cpu) ==>
                post.ranges[cpu].no_overlap(&post.ranges[_cpu])
            );
            assert forall |_cpu| _cpu != cpu && #[trigger] interp(post).ranges.contains_key(_cpu) implies {
                new_range.no_overlap(&interp(post).ranges[_cpu])
            } by {
                assert(state_trans(post.ranges[cpu]) =~= new_range);
                assert(state_trans(post.ranges[_cpu]) =~= interp(post).ranges[_cpu]);
                assert(post.ranges[cpu].no_overlap(&post.ranges[_cpu]));
            };
            assert(interp(pre).all_no_overlap(&new_range));

            AtomicSpec::show::acquire(interp(pre), interp(post), cpu, l, r);
        }

        range_release_start(cpu) => {
            let new_range = RangeState::Empty;
            assert(interp(pre).ranges.insert(cpu, new_range) =~= interp(post).ranges);
            AtomicSpec::show::release(interp(pre), interp(post), cpu);
        }

        pos_release(cpu, p) => {
            assert_maps_equal!(interp(pre).ranges, interp(post).ranges);
            AtomicSpec::show::no_op(interp(pre), interp(post));
        }

        pos_release_skip(cpu, p, skip_len) => {
            assert_maps_equal!(interp(pre).ranges, interp(post).ranges);
            AtomicSpec::show::no_op(interp(pre), interp(post));
        }

        range_release_end(cpu) => {
            assert_maps_equal!(interp(pre).ranges, interp(post).ranges);
            AtomicSpec::show::no_op(interp(pre), interp(post));
        }

        no_op() => {
            AtomicSpec::show::no_op(interp(pre), interp(post));
        }

    }}
}

} // verus!
