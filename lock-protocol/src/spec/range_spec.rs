use builtin::*;
use builtin_macros::*;
use state_machines_macros::state_machine;
use vstd::prelude::*;

use super::common::*;

verus! {

state_machine!{

RangeSpec {

fields {
    pub cpu_num: nat,
    pub size: nat,
    pub slots: Map<nat, SlotState>,
    pub ranges: Map<CpuId, RangeState>,
}

#[invariant]
pub fn inv_slots(&self) -> bool {
    forall |i| #![auto] self.slots.contains_key(i) <==> valid_pos(self.size, i)
}

#[invariant]
pub fn inv_ranges(&self) -> bool {
    &&& forall |cpu: CpuId| #![auto]
        valid_cpu(self.cpu_num, cpu) <==> self.ranges.contains_key(cpu)

    &&& forall |cpu: CpuId| #![auto] self.ranges.contains_key(cpu) ==> {
        &&& self.ranges[cpu].inv()
        &&& match self.ranges[cpu] {
            RangeState::Empty => true,
            RangeState::Creating(l, r, _) | RangeState::Hold(l, r) | RangeState::Destroying(l, r, _) => {
                valid_range(self.size, l, r)
            },
        }
    }

    &&& forall |cpu1: CpuId, cpu2: CpuId|
        cpu1 != cpu2 && self.ranges.contains_key(cpu1) && self.ranges.contains_key(cpu2) ==>
            self.ranges[cpu1].no_overlap(&self.ranges[cpu2])
}

pub open spec fn is_locked(&self, l: nat, r: nat) -> bool {
    forall |i| l <= i < r ==> (self.slots[i].is_EmptyLocked() || self.slots[i].is_Locked())
}

#[invariant]
pub fn inv_ranges_slots_relation(&self) -> bool {
    forall |cpu| self.ranges.contains_key(cpu) ==> match self.ranges[cpu] {
        RangeState::Empty => true,
        RangeState::Creating(l, _, r) | RangeState::Hold(l, r) | RangeState::Destroying(l, _, r) => {
            self.is_locked(l, r)
        },
    }
}

init!{
    initialize(cpu_num: nat, size: nat) {
        require(cpu_num > 0);
        require(size > 0);

        init cpu_num = cpu_num;
        init size = size;
        init slots = Map::new(
            |i| valid_pos(size, i),
            |i| if i == 0 { SlotState::Free } else { SlotState::Empty },
        );
        init ranges = Map::new(
            |cpu| valid_cpu(cpu_num, cpu),
            |cpu| RangeState::Empty,
        );
    }
}

transition!{
    slot_acquire_outside_range(p: nat) {
        require(valid_pos(pre.size, p));

        require(pre.slots[p].is_Free());
        update slots = pre.slots.insert(p, SlotState::LockedOutside);
    }
}

transition!{
    slot_release_outside_range(p: nat) {
        require(valid_pos(pre.size, p));

        require(pre.slots[p].is_LockedOutside());
        update slots = pre.slots.insert(p, SlotState::Free);
    }
}

transition!{
    slot_create_in_range(cpu: CpuId, p: nat) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(valid_pos(pre.size, p));

        require(pre.slots[p].is_EmptyLocked());
        update slots = pre.slots.insert(p, SlotState::Locked);

        require(pre.ranges[cpu].is_Hold());
        let l = pre.ranges[cpu].get_Hold_0();
        let r = pre.ranges[cpu].get_Hold_1();
        require(l <= p < r);
    }
}

transition!{
    slot_create_outside_range(p: nat) {
        require(valid_pos(pre.size, p));

        require(pre.slots[p].is_Empty());
        update slots = pre.slots.insert(p, SlotState::LockedOutside);
    }
}

transition!{
    range_acquire_start(cpu: CpuId, l: nat, r: nat) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(valid_range(pre.size, l, r));

        require(pre.ranges[cpu].is_Empty());
        update ranges = pre.ranges.insert(cpu, RangeState::Creating(l, r, l));
    }
}

transition!{
    pos_acquire(cpu: CpuId, p: nat) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(valid_pos(pre.size, p));

        require(pre.slots[p].is_Free());
        update slots = pre.slots.insert(p, SlotState::Locked);

        require(pre.ranges[cpu].is_Creating());
        let l = pre.ranges[cpu].get_Creating_0();
        let r = pre.ranges[cpu].get_Creating_1();
        let cur_p = pre.ranges[cpu].get_Creating_2();
        require(p == cur_p && p < r);
        update ranges = pre.ranges.insert(cpu, RangeState::Creating(l, r, p + 1));
    }
}

transition!{
    pos_acquire_skip(cpu: CpuId, p: nat, skip_len: nat) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(valid_pos(pre.size, p));
        require(skip_len > 0);
        require(p + skip_len <= pre.size);

        let old_slots = Map::new(
            |i: nat| p <= i < p + skip_len,
            |i| SlotState::Empty,
        );
        let new_slots = Map::new(
            |i: nat| p <= i < p + skip_len,
            |i| SlotState::EmptyLocked,
        );
        require(old_slots.submap_of(pre.slots));
        update slots = pre.slots.union_prefer_right(new_slots);

        require(pre.ranges[cpu].is_Creating());
        let l = pre.ranges[cpu].get_Creating_0();
        let r = pre.ranges[cpu].get_Creating_1();
        let cur_p = pre.ranges[cpu].get_Creating_2();
        require(p == cur_p && p + skip_len <= r);
        update ranges = pre.ranges.insert(cpu, RangeState::Creating(l, r, p + skip_len));
    }
}

transition!{
    range_acquire_end(cpu: CpuId) {
        require(valid_cpu(pre.cpu_num, cpu));

        require(pre.ranges[cpu].is_Creating());
        let l = pre.ranges[cpu].get_Creating_0();
        let r = pre.ranges[cpu].get_Creating_1();
        let cur_p = pre.ranges[cpu].get_Creating_2();
        require(cur_p == r);
        update ranges = pre.ranges.insert(cpu, RangeState::Hold(l, r));
    }
}

transition!{
    range_release_start(cpu: CpuId) {
        require(valid_cpu(pre.cpu_num, cpu));

        require(pre.ranges[cpu].is_Hold());
        let l = pre.ranges[cpu].get_Hold_0();
        let r = pre.ranges[cpu].get_Hold_1();
        update ranges = pre.ranges.insert(cpu, RangeState::Destroying(l, r, r));
    }
}

transition!{
    pos_release(cpu: CpuId, p: nat) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(valid_pos(pre.size, p));

        require(pre.slots[p].is_Locked());
        update slots = pre.slots.insert(p, SlotState::Free);

        require(pre.ranges[cpu].is_Destroying());
        let l = pre.ranges[cpu].get_Destroying_0();
        let r = pre.ranges[cpu].get_Destroying_1();
        let cur_p = pre.ranges[cpu].get_Destroying_2();
        require(cur_p == p + 1 && p >= l);
        update ranges = pre.ranges.insert(cpu, RangeState::Destroying(l, r, p));
    }
}

transition!{
    pos_release_skip(cpu: CpuId, p: nat, skip_len: nat) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(valid_pos(pre.size, p));
        require(skip_len > 0);
        require(p + skip_len <= pre.size);

        let old_slots = Map::new(
            |i: nat| p <= i < p + skip_len,
            |i| SlotState::EmptyLocked,
        );
        let new_slots = Map::new(
            |i: nat| p <= i < p + skip_len,
            |i| SlotState::Empty,
        );
        require(old_slots.submap_of(pre.slots));
        update slots = pre.slots.union_prefer_right(new_slots);

        require(pre.ranges[cpu].is_Destroying());
        let l = pre.ranges[cpu].get_Destroying_0();
        let r = pre.ranges[cpu].get_Destroying_1();
        let cur_p = pre.ranges[cpu].get_Destroying_2();
        require(cur_p == p + skip_len && p >= l);
        update ranges = pre.ranges.insert(cpu, RangeState::Destroying(l, r, p));
    }
}

transition!{
    range_release_end(cpu: CpuId) {
        require(valid_cpu(pre.cpu_num, cpu));

        require(pre.ranges[cpu].is_Destroying());
        let l = pre.ranges[cpu].get_Destroying_0();
        let r = pre.ranges[cpu].get_Destroying_1();
        let cur_p = pre.ranges[cpu].get_Destroying_2();
        require(cur_p == l);
        update ranges = pre.ranges.insert(cpu, RangeState::Empty);
    }
}

transition!{
    no_op() {}
}

#[inductive(initialize)]
fn initialize_inductive(post: Self, cpu_num: nat, size: nat) {}

#[inductive(slot_acquire_outside_range)]
fn slot_acquire_outside_range_inductive(pre: Self, post: Self, p: nat) {
    assert forall |cpu| post.ranges.contains_key(cpu) implies {
        match post.ranges[cpu] {
            RangeState::Empty => true,
            RangeState::Creating(l, _, r) | RangeState::Hold(l, r) | RangeState::Destroying(l, _, r) => {
                post.is_locked(l, r)
            },
        }
    } by {
        assert(pre.ranges[cpu] =~= post.ranges[cpu]);
        if !pre.ranges[cpu].is_Empty() {
            let (l, r) = pre.ranges[cpu].get_locked_range();
            assert forall |i| l <= i < r implies {
                post.slots[i].is_EmptyLocked() || post.slots[i].is_Locked()
            } by {
                assert(valid_pos(pre.size, i));
                if i != p {
                    assert(post.slots[i] =~= pre.slots[i]);
                } else {
                    assert(post.slots[p].is_LockedOutside());
                }
            };
        }
    };
}

#[inductive(slot_release_outside_range)]
fn slot_release_outside_range_inductive(pre: Self, post: Self, p: nat) {
    assert forall |cpu| post.ranges.contains_key(cpu) implies {
        match post.ranges[cpu] {
            RangeState::Empty => true,
            RangeState::Creating(l, _, r) | RangeState::Hold(l, r) | RangeState::Destroying(l, _, r) => {
                post.is_locked(l, r)
            },
        }
    } by {
        assert(pre.ranges[cpu] =~= post.ranges[cpu]);
        if !pre.ranges[cpu].is_Empty() {
            let (l, r) = pre.ranges[cpu].get_locked_range();
            assert forall |i| l <= i < r implies {
                post.slots[i].is_EmptyLocked() || post.slots[i].is_Locked()
            } by {
                assert(valid_pos(pre.size, i));
                if i != p {
                    assert(post.slots[i] =~= pre.slots[i]);
                } else {
                    assert(post.slots[p].is_Free());
                }
            };
        }
    };
}

#[inductive(slot_create_in_range)]
fn slot_create_in_range_inductive(pre: Self, post: Self, cpu: CpuId, p: nat) {
    assert forall |_cpu| _cpu != cpu && post.ranges.contains_key(_cpu) implies {
        match post.ranges[_cpu] {
            RangeState::Empty => true,
            RangeState::Creating(l, _, r) | RangeState::Hold(l, r) | RangeState::Destroying(l, _, r) => {
                post.is_locked(l, r)
            },
        }
    } by {
        assert(pre.ranges[_cpu] =~= post.ranges[_cpu]);
        assert(pre.ranges[cpu].no_overlap(&pre.ranges[_cpu]));
        if !pre.ranges[_cpu].is_Empty() {
            let (l, r) = pre.ranges[_cpu].get_locked_range();
            assert forall |i| l <= i < r implies {
                post.slots[i].is_EmptyLocked() || post.slots[i].is_Locked()
            } by {
                assert(valid_pos(pre.size, i));
                assert(post.slots[i] =~= pre.slots[i]);
            };
        }
    };

    assert(post.ranges[cpu].is_Hold());
    let l = post.ranges[cpu].get_Hold_0();
    let r = post.ranges[cpu].get_Hold_1();
    assert forall |i| l <= i < r implies {
        post.slots[i].is_EmptyLocked() || post.slots[i].is_Locked()
    } by {
        if i == p { assert(post.slots[p].is_Locked()); }
        else {
            assert(valid_pos(pre.size, i));
            assert(post.slots[i] =~= pre.slots[i]);
        }
    };
}

#[inductive(slot_create_outside_range)]
fn slot_create_outside_range_inductive(pre: Self, post: Self, p: nat) {
    assert forall |cpu| post.ranges.contains_key(cpu) implies {
        match post.ranges[cpu] {
            RangeState::Empty => true,
            RangeState::Creating(l, _, r) | RangeState::Hold(l, r) | RangeState::Destroying(l, _, r) => {
                post.is_locked(l, r)
            },
        }
    } by {
        assert(pre.ranges[cpu] =~= post.ranges[cpu]);
        if !pre.ranges[cpu].is_Empty() {
            let (l, r) = pre.ranges[cpu].get_locked_range();
            assert forall |i| l <= i < r implies {
                post.slots[i].is_EmptyLocked() || post.slots[i].is_Locked()
            } by {
                assert(valid_pos(pre.size, i));
                if i != p {
                    assert(post.slots[i] =~= pre.slots[i]);
                } else {
                    assert(post.slots[p].is_LockedOutside());
                }
            };
        }
    };
}

#[inductive(range_acquire_start)]
fn range_acquire_start_inductive(pre: Self, post: Self, cpu: CpuId, l: nat, r: nat) {
    assert(pre.slots =~= post.slots);
    assert(pre.ranges.contains_key(cpu) && pre.ranges[cpu] =~= RangeState::Empty);
    assert(pre.ranges.insert(cpu, RangeState::Creating(l, r, l)) =~= post.ranges);
}

#[inductive(pos_acquire)]
fn pos_acquire_inductive(pre: Self, post: Self, cpu: CpuId, p: nat) {
    assert(pre.slots[p].is_Free());
    assert(pre.slots.insert(p, SlotState::Locked) =~= post.slots);

    let l = pre.ranges[cpu].get_Creating_0();
    let r = pre.ranges[cpu].get_Creating_1();
    let cur_p = pre.ranges[cpu].get_Creating_2();
    assert(cur_p == p && cur_p < r);
    assert(pre.ranges.insert(cpu, RangeState::Creating(l, r, cur_p + 1)) =~= post.ranges);

    assert(forall |cpu: CpuId| pre.ranges.contains_key(cpu) ==>
        #[trigger] pre.ranges[cpu].pos_is_not_held(p)
    );
    assert(!post.ranges[cpu].pos_is_not_held(p));
    assert(!(forall |cpu: CpuId| post.ranges.contains_key(cpu) ==>
        #[trigger] post.ranges[cpu].pos_is_not_held(p)
    ));

    assert forall |_cpu: CpuId| _cpu != cpu && #[trigger] post.ranges.contains_key(_cpu) implies {
        post.ranges[cpu].no_overlap(&post.ranges[_cpu])
    } by {
        assert(pre.ranges[cpu].no_overlap(&pre.ranges[_cpu]));
        assert(post.ranges[_cpu].pos_is_not_held(p));
        match post.ranges[_cpu] {
            RangeState::Empty => (),
            RangeState::Creating(l2, _, r2) | RangeState::Hold(l2, r2) | RangeState::Destroying(l2, _, r2) => {
                assert(p < l2 || p >= r2);
            },
        }
    };

    assert forall |_cpu| _cpu != cpu && post.ranges.contains_key(_cpu) implies {
        match post.ranges[_cpu] {
            RangeState::Empty => true,
            RangeState::Creating(l, _, r) | RangeState::Hold(l, r) | RangeState::Destroying(l, _, r) => {
                post.is_locked(l, r)
            },
        }
    } by {
        assert(pre.ranges[_cpu] =~= post.ranges[_cpu]);
        assert(pre.ranges[cpu].no_overlap(&pre.ranges[_cpu]));
        if !pre.ranges[_cpu].is_Empty() {
            let (l, r) = pre.ranges[_cpu].get_locked_range();
            assert forall |_i| l <= _i < r implies {
                post.slots[_i].is_EmptyLocked() || post.slots[_i].is_Locked()
            } by {
                assert(valid_pos(pre.size, _i));
                assert(post.slots[_i] =~= pre.slots[_i]);
            };
        }
    };
    assert forall |i| l <= i < cur_p implies {
        post.slots[i].is_EmptyLocked() || post.slots[i].is_Locked()
    } by {
        if i == p { assert(post.slots[p].is_Locked()); }
        else {
            assert(valid_pos(pre.size, i));
        }
    }
}

#[inductive(pos_acquire_skip)]
fn pos_acquire_skip_inductive(pre: Self, post: Self, cpu: CpuId, p: nat, skip_len: nat) {
    let _slots = Map::new(
        |i: nat| p <= i < p + skip_len,
        |i| SlotState::Empty,
    );
    assert(_slots.submap_of(pre.slots));
    assert forall |i| p <= i < p + skip_len implies {
        pre.slots[i].is_Empty()
    } by {
        assert(_slots.dom().contains(i));
        assert(pre.slots.dom().contains(i));
    }
    assert(forall |i| p <= i < p + skip_len ==>
        post.slots[i].is_EmptyLocked()
    );

    assert forall |_cpu| _cpu != cpu && #[trigger] post.ranges.contains_key(_cpu) implies {
        post.ranges[cpu].no_overlap(&post.ranges[_cpu])
    } by {
        assert(pre.ranges[cpu].no_overlap(&pre.ranges[_cpu]));
        assert forall |i: nat| #[trigger] pos_in_range(p, p + skip_len, i) implies {
            match post.ranges[_cpu] {
                RangeState::Empty => true,
                RangeState::Creating(l, _, r) | RangeState::Hold(l, r) | RangeState::Destroying(l, _, r) => {
                    i < l || i >= r
                },
            }
        } by {
            assert(pre.slots[i].is_Empty());
            assert(pre.ranges[_cpu].pos_is_not_held(i));
        };
        match post.ranges[_cpu] {
            RangeState::Empty => (),
            RangeState::Creating(l, _, r) | RangeState::Hold(l, r) | RangeState::Destroying(l, _, r) => {
                let tail = (p + skip_len - 1) as nat;
                assert(tail < l || p >= r || l == r) by {
                    assert(p < l || p >= r) by {
                        assert(pos_in_range(p, p + skip_len, p));
                    };
                    assert(tail < l || tail >= r) by {
                        assert(pos_in_range(p, p + skip_len, tail));
                    };
                    if p < l && tail >= r && l != r {
                        assert(pos_in_range(p, p + skip_len, l));
                    }
                };
            },
        };
    };

    assert(post.ranges[cpu].is_Creating());
    let l = post.ranges[cpu].get_Creating_0();
    let r = post.ranges[cpu].get_Creating_1();
    let cur_p = post.ranges[cpu].get_Creating_2();
    assert forall |_cpu| _cpu != cpu && post.ranges.contains_key(_cpu) implies {
        match post.ranges[_cpu] {
            RangeState::Empty => true,
            RangeState::Creating(l, _, r) | RangeState::Hold(l, r) | RangeState::Destroying(l, _, r) => {
                post.is_locked(l, r)
            },
        }
    } by {
        assert(pre.ranges[_cpu] =~= post.ranges[_cpu]);
        assert(pre.ranges[cpu].no_overlap(&pre.ranges[_cpu]));
        if !pre.ranges[_cpu].is_Empty() {
            let (l, r) = pre.ranges[_cpu].get_locked_range();
            assert forall |_i| l <= _i < r implies {
                post.slots[_i].is_EmptyLocked() || post.slots[_i].is_Locked()
            } by {
                assert(valid_pos(pre.size, _i));
                assert(post.slots[_i] =~= pre.slots[_i]);
            };
        }
    };
    assert forall |i| l <= i < cur_p implies {
        post.slots[i].is_EmptyLocked() || post.slots[i].is_Locked()
    } by {
        if i >= p { assert(post.slots[i].is_EmptyLocked()); }
        else {
            assert(valid_pos(pre.size, i));
        }
    }
}

#[inductive(range_acquire_end)]
fn range_acquire_end_inductive(pre: Self, post: Self, cpu: CpuId) {
    assert(pre.slots =~= post.slots);

    let l = pre.ranges[cpu].get_Creating_0();
    let r = pre.ranges[cpu].get_Creating_1();
    assert(pre.ranges[cpu] =~= RangeState::Creating(l, r, r));
    assert(pre.ranges.insert(cpu, RangeState::Hold(l, r)) =~= post.ranges);
    assert(forall |i: nat| #![auto]
        pre.ranges[cpu].pos_is_not_held(i) <==>
        post.ranges[cpu].pos_is_not_held(i)
    );

    assert forall |_cpu: CpuId| _cpu != cpu && #[trigger] post.ranges.contains_key(_cpu) implies {
        post.ranges[cpu].no_overlap(&post.ranges[_cpu])
    } by {
        assert(pre.ranges[cpu].no_overlap(&pre.ranges[_cpu]));
    };
}

#[inductive(range_release_start)]
fn range_release_start_inductive(pre: Self, post: Self, cpu: CpuId) {
    assert forall |_cpu| _cpu != cpu && #[trigger] post.ranges.contains_key(_cpu) implies {
        post.ranges[cpu].no_overlap(&post.ranges[_cpu])
    } by {
        assert(pre.ranges[cpu].no_overlap(&pre.ranges[_cpu]));
    };

    assert(forall |i| #![auto]
        pre.ranges[cpu].pos_is_not_held(i) <==>
        post.ranges[cpu].pos_is_not_held(i)
    );
}

#[inductive(pos_release)]
fn pos_release_inductive(pre: Self, post: Self, cpu: CpuId, p: nat) {
    assert forall |_cpu| _cpu != cpu && #[trigger] post.ranges.contains_key(_cpu) implies {
        post.ranges[cpu].no_overlap(&post.ranges[_cpu])
    } by {
        assert(pre.ranges[cpu].no_overlap(&pre.ranges[_cpu]));
    };
    assert(forall |i| i != p ==> {
        pre.ranges[cpu].pos_is_not_held(i) <==>
        post.ranges[cpu].pos_is_not_held(i)
    });
    assert forall |_cpu| _cpu != cpu && #[trigger] pre.ranges.contains_key(_cpu) implies {
        pre.ranges[_cpu].pos_is_not_held(p)
    } by {
        assert(pre.ranges[cpu].pos_is_held(p));
        assert(pre.ranges[cpu].no_overlap(&pre.ranges[_cpu]));
    };

    assert forall |_cpu| _cpu != cpu && post.ranges.contains_key(_cpu) implies {
        match post.ranges[_cpu] {
            RangeState::Empty => true,
            RangeState::Creating(l, _, r) | RangeState::Hold(l, r) | RangeState::Destroying(l, _, r) => {
                post.is_locked(l, r)
            },
        }
    } by {
        assert(pre.ranges[_cpu] =~= post.ranges[_cpu]);
        assert(pre.ranges[cpu].no_overlap(&pre.ranges[_cpu]));
        if !pre.ranges[_cpu].is_Empty() {
            let (l, r) = pre.ranges[_cpu].get_locked_range();
            assert forall |_i| l <= _i < r implies {
                post.slots[_i].is_EmptyLocked() || post.slots[_i].is_Locked()
            } by {
                assert(valid_pos(pre.size, _i));
                assert(post.slots[_i] =~= pre.slots[_i]);
            };
        }
    };
    assert(post.ranges[cpu].is_Destroying());
    let l = post.ranges[cpu].get_Destroying_0();
    let r = post.ranges[cpu].get_Destroying_1();
    let cur_p = post.ranges[cpu].get_Destroying_2();
    assert forall |i| l <= i < cur_p implies {
        post.slots[i].is_EmptyLocked() || post.slots[i].is_Locked()
    } by {
        assert(valid_pos(pre.size, i));
    }
}

#[inductive(pos_release_skip)]
fn pos_release_skip_inductive(pre: Self, post: Self, cpu: CpuId, p: nat, skip_len: nat) {
    let _slots = Map::new(
        |i: nat| p <= i < p + skip_len,
        |i| SlotState::EmptyLocked,
    );
    assert(_slots.submap_of(pre.slots));
    assert forall |i| p <= i < p + skip_len implies {
        pre.slots[i].is_EmptyLocked()
    } by {
        assert(_slots.dom().contains(i));
        assert(pre.slots.dom().contains(i));
    }
    assert(forall |i| p <= i < p + skip_len ==>
        post.slots[i].is_Empty()
    );

    assert forall |_cpu| _cpu != cpu && #[trigger] post.ranges.contains_key(_cpu) implies {
        post.ranges[cpu].no_overlap(&post.ranges[_cpu])
    } by {
        assert(pre.ranges[cpu].no_overlap(&pre.ranges[_cpu]));
        assert forall |i: nat| #[trigger] pos_in_range(p, p + skip_len, i) implies {
            match post.ranges[_cpu] {
                RangeState::Empty => true,
                RangeState::Creating(l, _, r) | RangeState::Hold(l, r) | RangeState::Destroying(l, _, r) => {
                    i < l || i >= r
                },
            }
        } by {
            assert(pre.slots[i].is_EmptyLocked());
            assert(pre.ranges[_cpu].pos_is_not_held(i));
        };
        match post.ranges[_cpu] {
            RangeState::Empty => (),
            RangeState::Creating(l, _, r) | RangeState::Hold(l, r) | RangeState::Destroying(l, _, r) => {
                let tail = (p + skip_len - 1) as nat;
                assert(tail < l || p >= r || l == r) by {
                    assert(p < l || p >= r) by {
                        assert(pos_in_range(p, p + skip_len, p));
                    };
                    assert(tail < l || tail >= r) by {
                        assert(pos_in_range(p, p + skip_len, tail));
                    };
                    if p < l && tail >= r && l != r {
                        assert(pos_in_range(p, p + skip_len, l));
                    }
                };
            },
        };
    };

    assert(post.ranges[cpu].is_Destroying());
    let l = post.ranges[cpu].get_Destroying_0();
    let r = post.ranges[cpu].get_Destroying_1();
    let cur_p = post.ranges[cpu].get_Destroying_2();
    assert forall |_cpu| _cpu != cpu && post.ranges.contains_key(_cpu) implies {
        match post.ranges[_cpu] {
            RangeState::Empty => true,
            RangeState::Creating(l, _, r) | RangeState::Hold(l, r) | RangeState::Destroying(l, _, r) => {
                post.is_locked(l, r)
            },
        }
    } by {
        assert(pre.ranges[_cpu] =~= post.ranges[_cpu]);
        assert(pre.ranges[cpu].no_overlap(&pre.ranges[_cpu]));
        if !pre.ranges[_cpu].is_Empty() {
            let (l, r) = pre.ranges[_cpu].get_locked_range();
            assert forall |_i| l <= _i < r implies {
                post.slots[_i].is_EmptyLocked() || post.slots[_i].is_Locked()
            } by {
                assert(valid_pos(pre.size, _i));
                assert(post.slots[_i] =~= pre.slots[_i]);
            };
        }
    };
    assert forall |i| l <= i < cur_p implies {
        post.slots[i].is_EmptyLocked() || post.slots[i].is_Locked()
    } by {
        assert(valid_pos(pre.size, i));
    }
}

#[inductive(range_release_end)]
fn range_release_end_inductive(pre: Self, post: Self, cpu: CpuId) {}

#[inductive(no_op)]
fn no_op_inductive(pre: Self, post: Self) {}

}

}

} // verus!
