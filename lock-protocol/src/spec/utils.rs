use std::intrinsics::offset;
use std::intrinsics::ptr_offset_from;

use vstd::bytes;
use vstd::prelude::*;
use vstd::arithmetic::power::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::set::*;
use vstd_extra::prelude::*;

use crate::mm::child;

use super::common::*;
use super::rcu::tree;

verus! {

broadcast use vstd_extra::seq_extra::group_forall_seq_lemmas;

pub struct NodeHelper;

pub broadcast group group_node_helper_lemmas {
    NodeHelper::lemma_in_subtree_iff_in_subtree_range,
}

impl NodeHelper {
    /// depth starts from 0(root) to 3 (leaf),
    /// level starts from 4(root) to 1 (leaf).
    #[verifier::inline]
    pub open spec fn level_to_dep(level: nat) -> nat
        recommends
            1 <= level <= 4,
    {
        (4 - level) as nat
    }

    #[verifier::inline]
    pub open spec fn dep_to_level(dep: nat) -> nat
        recommends
            0 <= dep < 4,
    {
        (4 - dep) as nat
    }

    pub proof fn lemma_level_to_dep_bijective(level: nat)
        requires
            1 <= level <= 4,
        ensures
            Self::dep_to_level(Self::level_to_dep(level)) == level,
    {
    }

    pub proof fn lemma_dep_to_level_bijective(dep: nat)
        requires
            0 <= dep < 4,
        ensures
            Self::level_to_dep(Self::dep_to_level(dep)) == dep,
    {
    }

    /// The number of nodes at a given level.
    pub closed spec fn size_at_dep(dep: nat) -> nat
        recommends
            0 <= dep < 4,
    {
        pow(512, dep) as nat
    }

    pub proof fn lemma_size_at_dep_table()
        ensures
            Self::size_at_dep(0) == 1,
            Self::size_at_dep(1) == 512,
            Self::size_at_dep(2) == 262144,
            Self::size_at_dep(3) == 134217728,
    {
        reveal(pow);
        assert(Self::size_at_dep(0) == 1) by (compute_only);
        assert(Self::size_at_dep(1) == 512) by (compute_only);
        assert(Self::size_at_dep(2) == 262144) by (compute_only);
        assert(Self::size_at_dep(3) == 134217728) by (compute_only);
    }

    /// Returns the size of the tree with nodes at most `max_dep` depth.
    #[verifier::memoize]
    pub closed spec fn tree_size_spec(max_dep: int) -> nat
        recommends
            0 <= max_dep < 4,
        decreases max_dep,
        when max_dep >= 0
    {
        let cur_dep = max_dep as nat;
        if max_dep == 0 {
            1
        } else {
            512 * Self::tree_size_spec(max_dep - 1) + 1
        }
    }

    pub proof fn lemma_tree_size_spec_table()
        ensures
            Self::tree_size_spec(0) == 1,
            Self::tree_size_spec(1) == 513,
            Self::tree_size_spec(2) == 262657,
            Self::tree_size_spec(3) == 134480385,
    {
        assert(Self::tree_size_spec(0) == 1) by (compute_only);
        assert(Self::tree_size_spec(1) == 513) by (compute_only);
        assert(Self::tree_size_spec(2) == 262657) by (compute_only);
        assert(Self::tree_size_spec(3) == 134480385) by (compute_only);
    }

    pub open spec fn tree_size_weighted_spec(k: int) -> nat
        recommends
            1 <= k < 4,
    {
        511 * Self::tree_size_spec(k) + 1
    }

    pub open spec fn tree_size_weighted_sum_spec(k: int) -> nat
        recommends
            0 <= k < 4,
        decreases k,
    {
        if k <= 0 {
            0
        } else {
            Self::tree_size_weighted_spec(k - 1) + Self::tree_size_weighted_sum_spec(k - 1)
        }
    }

    pub open spec fn tree_size_relation_spec(k: int) -> bool {
        Self::tree_size_weighted_sum_spec(k) + 1 == Self::tree_size_spec(k)
    }

    pub proof fn lemma_tree_size_relation()
        ensures
            Self::tree_size_relation_spec(0),
            Self::tree_size_relation_spec(1),
            Self::tree_size_relation_spec(2),
            Self::tree_size_relation_spec(3),
    {
        assert(Self::tree_size_relation_spec(0)) by (compute_only);
        assert(Self::tree_size_relation_spec(1)) by (compute_only);
        assert(Self::tree_size_relation_spec(2)) by (compute_only);
        assert(Self::tree_size_relation_spec(3)) by (compute_only);
    }

    /// The total size of the tree with 4 levels.
    pub open spec fn total_size() -> nat {
        Self::tree_size_spec(3)
    }

    // Do not inline this function, it serves as a trigger.
    pub open spec fn valid_nid(nid: NodeId) -> bool {
        0 <= nid < Self::total_size()
    }

    #[verifier::inline]
    pub open spec fn root_id() -> NodeId {
        0
    }

    pub proof fn lemma_root_id()
        ensures
            Self::valid_nid(Self::root_id()),
    {
    }

    // Lemmas about trace.
    // A trace is a sequence of offsets from the root to a node.
    // The length of the trace is at most 3.
    pub open spec fn valid_trace(trace: Seq<nat>) -> bool {
        &&& 0 <= trace.len() < 4
        &&& trace.all(|offset: nat| 0 <= offset < 512)
    }

    /// The set of all valid node ids.
    pub open spec fn valid_nid_set() -> Set<NodeId> {
        Set::new(|nid: NodeId| Self::valid_nid(nid))
    }

    /// The set of all valid traces.
    pub open spec fn valid_trace_set() -> Set<Seq<nat>> {
        Set::new(|trace: Seq<nat>| Self::valid_trace(trace))
    }

    pub open spec fn trace_lt(t1: Seq<nat>, t2: Seq<nat>) -> bool
        decreases t1.len(),
    {
        if t2.len() == 0 {
            false
        } else if t1.len() == 0 {
            true
        } else {
            if t1[0] < t2[0] {
                true
            } else if t1[0] > t2[0] {
                false
            } else {
                Self::trace_lt(t1.drop_first(), t2.drop_first())
            }
        }
    }

    /// Returns the trace from cur_rt to the node with id `nid`.
    pub closed spec fn nid_to_trace_rec(nid: NodeId, cur_level: nat, cur_rt: NodeId) -> Seq<nat>
        decreases cur_level,
    {
        if cur_level == 0 {
            seq![]
        } else {
            let child_size = Self::tree_size_spec(cur_level - 1);
            let offset = ((nid - cur_rt - 1) / child_size as int) as nat;
            let child_root = cur_rt + offset * child_size + 1;
            if child_root == nid {
                seq![offset]
            } else {
                seq![offset].add(Self::nid_to_trace_rec(nid, (cur_level - 1) as nat, child_root))
            }
        }
    }

    /// Returns the trace from root to the node with id `nid`.
    pub open spec fn nid_to_trace(nid: NodeId) -> Seq<nat>
        recommends
            Self::valid_nid(nid),
    {
        if nid == Self::root_id() {
            Seq::empty()
        } else {
            Self::nid_to_trace_rec(nid, 3, Self::root_id())
        }
    }

    /// Returns the node id from the trace.
    #[verifier::opaque]
    pub open spec fn trace_to_nid_rec(trace: Seq<nat>, cur_rt: NodeId, cur_level: int) -> NodeId
        recommends
            Self::valid_trace(trace),
            Self::valid_nid(cur_rt),
            trace.len() <= cur_level <= 3,
    {
        trace.fold_left_alt(
            (cur_rt, cur_level as int),
            |param: (NodeId, int), offset: nat|
                {
                    let nid = param.0;
                    let cur_level = param.1;
                    let sz = Self::tree_size_spec(cur_level - 1);
                    (nid + offset * sz + 1, cur_level - 1)
                },
        ).0
    }

    /// Returns the node id from the trace starting from root.
    pub open spec fn trace_to_nid(trace: Seq<nat>) -> NodeId
        recommends
            Self::valid_trace(trace),
    {
        Self::trace_to_nid_rec(trace, 0, 3)
    }

    /// Returns the child node id from the trace and offset.
    pub open spec fn child_nid_from_trace_offset(trace: Seq<nat>, offset: nat) -> NodeId
        recommends
            Self::valid_trace(trace),
            0 <= offset < 512,
            trace.len() < 3,
    {
        let nid1 = Self::trace_to_nid(trace);
        let level = 3 - trace.len();
        let sz = Self::tree_size_spec(level - 1);
        nid1 + offset * sz + 1
    }

    /// Returns true is the node is not a leaf
    pub open spec fn is_not_leaf(nid: NodeId) -> bool
        recommends
            Self::valid_nid(nid),
    {
        Self::nid_to_dep(nid) < 3
    }

    /// Returns the child node id from the node id and offset.
    pub open spec fn get_child(nid: NodeId, offset: nat) -> NodeId
        recommends
            Self::valid_nid(nid),
            Self::nid_to_dep(nid) < 3,
            0 <= offset < 512,
    {
        Self::trace_to_nid(Self::nid_to_trace(nid).push(offset))
    }

    /// Returns the parent node id from the node id.
    /// If the node id is root, the result is arbitrary.
    pub open spec fn get_parent(nid: NodeId) -> NodeId
        recommends
            Self::valid_nid(nid),
            nid != Self::root_id(),
    {
        Self::trace_to_nid(Self::nid_to_trace(nid).drop_last())
    }

    /// Returns true if `ch` is a child of `pa (the trace of 'pa' is equal to the drooping last element trace of 'ch').
    pub open spec fn is_child(pa: NodeId, ch: NodeId) -> bool
        recommends
            Self::valid_nid(pa),
            Self::valid_nid(ch),
    {
        &&& Self::nid_to_trace(pa) == Self::nid_to_trace(ch).drop_last()
        &&& ch != Self::root_id()
    }

    /// Returns the offset of the node id from its parent.
    pub open spec fn get_offset(nid: NodeId) -> nat
        recommends
            Self::valid_nid(nid),
            nid != Self::root_id(),
    {
        let trace = Self::nid_to_trace(nid);
        trace.last()
    }

    pub open spec fn nid_to_dep(nid: NodeId) -> nat
        recommends
            Self::valid_nid(nid),
    {
        Self::nid_to_trace(nid).len()
    }

    pub open spec fn nid_to_level(nid: NodeId) -> nat
        recommends
            Self::valid_nid(nid),
    {
        Self::dep_to_level(Self::nid_to_dep(nid))
    }

    /// Returns the size of the subtree rooted at `nid`.
    pub open spec fn sub_tree_size(nid: NodeId) -> nat
        recommends
            Self::valid_nid(nid),
    {
        let level = Self::nid_to_level(nid);
        Self::tree_size_spec(level - 1)
    }

    /// The next node id outside the subtree rooted at `nid`.
    pub open spec fn next_outside_subtree(nid: NodeId) -> NodeId
        recommends
            Self::valid_nid(nid),
    {
        nid + Self::sub_tree_size(nid)
    }

    /// Returns 'true' if 'nd' is in the subtree of 'rt' (the trace of 'rt' is a prefix of the trace of 'nd' and 'nd' is valid).
    pub open spec fn in_subtree(rt: NodeId, nd: NodeId) -> bool
        recommends
            Self::valid_nid(rt),
            Self::valid_nid(nd),
    {
        &&& Self::nid_to_trace(rt).is_prefix_of(Self::nid_to_trace(nd))
        &&& Self::valid_nid(nd)
    }

    pub open spec fn in_subtree_range(rt: NodeId, nd: NodeId) -> bool
        recommends
            Self::valid_nid(rt),
    {
        rt <= nd < Self::next_outside_subtree(rt)
    }

    /// Returns the NodeIds in the path from the trace.
    pub open spec fn trace_to_tree_path(trace: Seq<nat>) -> Seq<NodeId>
        recommends
            Self::valid_trace(trace),
        decreases trace.len(),
    {
        let ids = trace.map(|i: int, offset: nat| Self::trace_to_nid(trace.subrange(0, i + 1)));
        seq![Self::root_id()] + ids
    }

    /// Returns the traces in the subtree of the given trace.
    pub open spec fn get_subtree_traces(trace: Seq<nat>) -> Set<Seq<nat>>
        recommends
            Self::valid_trace(trace),
    {
        Self::valid_trace_set().filter(|subtree_trace| trace.is_prefix_of(subtree_trace))
    }

    proof fn lemma_trace_to_nid_rec_inductive(trace: Seq<nat>, cur_rt: NodeId, cur_level: int)
        ensures
            trace.len() > 0 ==> Self::trace_to_nid_rec(trace, cur_rt, cur_level)
                == Self::trace_to_nid_rec(
                trace.drop_first(),
                cur_rt + trace[0] * Self::tree_size_spec(cur_level - 1) + 1,
                cur_level - 1,
            ),
    {
        reveal(NodeHelper::trace_to_nid_rec);
    }

    pub open spec fn trace_to_nid_upperbound_spec(max_dep: nat) -> nat
        decreases max_dep,
    {
        let cur_dep = max_dep;
        let level = Self::dep_to_level(max_dep);
        if cur_dep == 0 {
            0
        } else {
            Self::tree_size_weighted_spec(level - 1) + Self::trace_to_nid_upperbound_spec(
                (max_dep - 1) as nat,
            )
        }
    }

    pub proof fn lemma_trace_to_nid_upperbound_spec(max_dep: nat)
        requires
            0 <= max_dep < 4,
        ensures
            Self::trace_to_nid_upperbound_spec(max_dep) == Self::tree_size_spec(3)
                - Self::tree_size_spec(3 - max_dep),
        decreases max_dep,
    {
        Self::lemma_tree_size_relation();
        if max_dep > 0 {
            Self::lemma_trace_to_nid_upperbound_spec((max_dep - 1) as nat);
        }
    }

    proof fn lemma_trace_to_nid_inner(trace: Seq<nat>)
        requires
            Self::valid_trace(trace),
        ensures
            trace.fold_left_alt(
                (0, 3),
                |param: (NodeId, int), offset: nat|
                    {
                        let nid = param.0;
                        let cur_level = param.1;
                        let sz = Self::tree_size_spec(cur_level - 1);
                        (nid + offset * sz + 1, cur_level - 1)
                    },
            ).0 <= Self::trace_to_nid_upperbound_spec(trace.len()),
            trace.fold_left_alt(
                (0, 3),
                |param: (NodeId, int), offset: nat|
                    {
                        let nid = param.0;
                        let cur_level = param.1;
                        let sz = Self::tree_size_spec(cur_level - 1);
                        (nid + offset * sz + 1, cur_level - 1)
                    },
            ).1 == 3 - trace.len(),
        decreases trace.len(),
    {
        let func = |param: (NodeId, int), offset: nat|
            {
                let nid = param.0;
                let cur_level = param.1;
                let sz = Self::tree_size_spec(cur_level - 1);
                (nid + offset * sz + 1, cur_level - 1)
            };

        if trace.len() != 0 {
            let new_trace = trace.drop_last();
            Self::lemma_trace_to_nid_inner(new_trace);
            lemma_mul_inequality(
                trace.last() as int,
                511,
                Self::tree_size_spec(3 - trace.len()) as int,
            );
            trace.lemma_fold_left_alt((0, 3), func);
            new_trace.lemma_fold_left_alt((0, 3), func);
        }
    }

    proof fn lemma_trace_to_nid_rec_lower_bound(trace: Seq<nat>, root: NodeId, level: int)
        ensures
            trace.len() > 0 ==> Self::trace_to_nid_rec(trace, root, level) > root,
            trace.len() == 0 ==> Self::trace_to_nid_rec(trace, root, level) == root,
        decreases trace.len(),
    {
        reveal(NodeHelper::trace_to_nid_rec);
        if trace.len() != 0 {
            let new_trace = trace.subrange(1, trace.len() as int);
            let new_rt = root + trace[0] * Self::tree_size_spec(level - 1) + 1;
            if new_trace.len() > 0 {
                Self::lemma_trace_to_nid_rec_lower_bound(new_trace, new_rt, level - 1);
            }
        }
    }

    proof fn lemma_trace_to_nid_rec_upper_bound(trace: Seq<nat>, root: NodeId, level: int)
        requires
            Self::valid_trace(trace),
            trace.len() <= level,
        ensures
            Self::trace_to_nid_rec(trace, root, level) < root + Self::tree_size_spec(level),
        decreases trace.len(),
    {
        reveal(NodeHelper::trace_to_nid_rec);
        Self::lemma_tree_size_spec_table();
        if trace.len() != 0 {
            let new_trace = trace.subrange(1, trace.len() as int);
            let new_rt = root + trace[0] * Self::tree_size_spec(level - 1) + 1;
            assert(new_rt + Self::tree_size_spec(level - 1) <= root + Self::tree_size_spec(level))
                by {
                lemma_mul_is_distributive_add_other_way(
                    Self::tree_size_spec(level - 1) as int,
                    trace[0] as int,
                    1,
                );
                lemma_mul_inequality(
                    (trace[0] + 1) as int,
                    512,
                    Self::tree_size_spec(level - 1) as int,
                );
            };
            Self::lemma_trace_to_nid_rec_upper_bound(new_trace, new_rt, level - 1);
        }
    }

    pub proof fn lemma_trace_to_nid_increasing(trace1: Seq<nat>, trace2: Seq<nat>)
        requires
            Self::trace_lt(trace1, trace2),
            Self::valid_trace(trace1),
            Self::valid_trace(trace2),
        ensures
            Self::trace_to_nid(trace1) < Self::trace_to_nid(trace2),
    {
        Self::lemma_trace_to_nid_rec_increasing(trace1, trace2, 0, 3);
    }

    proof fn lemma_trace_to_nid_rec_increasing(
        trace1: Seq<nat>,
        trace2: Seq<nat>,
        root: NodeId,
        level: int,
    )
        requires
            Self::trace_lt(trace1, trace2),
            Self::valid_trace(trace1),
            Self::valid_trace(trace2),
            trace2.len() <= level,
            trace1.len() <= level,
        ensures
            Self::trace_to_nid_rec(trace1, root, level) < Self::trace_to_nid_rec(
                trace2,
                root,
                level,
            ),
        decreases trace1.len(),
    {
        reveal(NodeHelper::trace_to_nid_rec);
        if trace1.len() == 0 {
            if trace2.len() != 0 {
                Self::lemma_trace_to_nid_rec_lower_bound(trace2, root, level);
            }
        } else {
            if trace2.len() != 0 {
                let new_trace1 = trace1.subrange(1, trace1.len() as int);
                let new_trace2 = trace2.subrange(1, trace2.len() as int);
                if trace1[0] == trace2[0] {
                    let new_rt = root + trace1[0] * Self::tree_size_spec(level - 1) + 1;
                    Self::lemma_trace_to_nid_rec_increasing(
                        new_trace1,
                        new_trace2,
                        new_rt,
                        level - 1,
                    );
                } else if trace1[0] < trace2[0] {
                    let new_rt1 = root + trace1[0] * Self::tree_size_spec(level - 1) + 1;
                    let new_rt2 = root + trace2[0] * Self::tree_size_spec(level - 1) + 1;
                    assert(Self::trace_to_nid_rec(trace1, root, level) < new_rt1
                        + Self::tree_size_spec(level - 1)) by {
                        Self::lemma_trace_to_nid_rec_upper_bound(new_trace1, new_rt1, level - 1);
                    }
                    assert(Self::trace_to_nid_rec(trace2, root, level) >= new_rt2) by {
                        Self::lemma_trace_to_nid_rec_lower_bound(new_trace2, new_rt2, level - 1);
                    }
                    assert(trace1[0] * Self::tree_size_spec(level - 1) + Self::tree_size_spec(
                        level - 1,
                    ) <= trace2[0] * Self::tree_size_spec(level - 1)) by (nonlinear_arith)
                        requires
                            0 <= trace1[0] < trace2[0],
                    ;
                }
            }
        }
    }

    /// `child_nid_from_trace_offset` correctly returns the child node id from the trace and offset,
    /// i.e. `child_nid_from_trace_offset(trace, offset) == trace_to_nid(trace.push(offset))`.
    pub proof fn lemma_child_nid_from_trace_offset_sound(trace: Seq<nat>, offset: nat)
        requires
            0 <= offset < 512,
            Self::valid_trace(trace),
        ensures
            Self::child_nid_from_trace_offset(trace, offset) == Self::trace_to_nid(
                trace.push(offset),
            ),
    {
        reveal(NodeHelper::trace_to_nid_rec);
        let func = |param: (NodeId, int), offset: nat|
            {
                let nid = param.0;
                let cur_level = param.1;
                let sz = Self::tree_size_spec(cur_level - 1);
                (nid + offset * sz + 1, cur_level - 1)
            };

        assert(trace.push(offset).drop_last() =~= trace);
        assert(func(trace.fold_left_alt((0, 3), func), offset) == trace.push(offset).fold_left_alt(
            (0, 3),
            func,
        )) by {
            trace.lemma_fold_left_alt((0, 3), func);
            trace.push(offset).lemma_fold_left_alt((0, 3), func);
        };
        assert(trace.fold_left_alt((0, 3), func).1 == 3 - trace.len()) by {
            Self::lemma_trace_to_nid_inner(trace);
        };
    }

    /// The result of `trace_to_nid` is the same as splitting the trace into two parts
    /// and calling `trace_to_nid_rec` on the second part.
    pub proof fn lemma_trace_to_nid_split(
        trace1: Seq<nat>,
        trace2: Seq<nat>,
        cur_rt: NodeId,
        cur_level: int,
    )
        requires
            Self::valid_trace(trace1.add(trace2)),
            cur_rt == Self::trace_to_nid(trace1),
            cur_level == Self::level_to_dep(trace1.len()) - 1,
        ensures
            Self::trace_to_nid(trace1.add(trace2)) == Self::trace_to_nid_rec(
                trace2,
                cur_rt,
                cur_level,
            ),
        decreases trace2.len(),
    {
        reveal(NodeHelper::trace_to_nid_rec);
        if trace2.len() == 0 {
            assert(trace1.add(trace2) =~= trace1);
        } else {
            // Induction step: use `lemma_child_nid_from_trace_offset_sound` to move the first element
            // of `trace2` to the end of `trace1` and then use the inductive hypothesis on the rest of `trace2`.
            let new_trace1 = trace1.push(trace2[0]);
            let new_trace2 = trace2.subrange(1, trace2.len() as int);
            assert(new_trace1.add(new_trace2) =~= trace1.add(trace2));
            let new_rt = cur_rt + trace2[0] * Self::tree_size_spec(cur_level - 1) + 1;
            assert(new_rt == Self::trace_to_nid(new_trace1)) by {
                Self::lemma_child_nid_from_trace_offset_sound(trace1, trace2[0]);
            };
            Self::lemma_trace_to_nid_split(new_trace1, new_trace2, new_rt, cur_level - 1)
        }
    }

    /// `nid_to_trace_rec` correcly returns a trace from `cur_rt` to the node id `nid`.
    /// By applying `trace_to_nid_rec' to the trace produced by `nid_to_trace_rec`, we can
    /// reconstruct the original node id.
    pub proof fn lemma_nid_to_trace_rec_sound(nid: NodeId, cur_level: nat, cur_rt: NodeId)
        requires
            Self::valid_nid(nid),
            cur_level <= 3,
            cur_rt < nid < cur_rt + Self::tree_size_spec(cur_level as int),
        ensures
            Self::nid_to_trace_rec(nid, cur_level, cur_rt).len() <= cur_level,
            Self::valid_trace(Self::nid_to_trace_rec(nid, cur_level, cur_rt)),
            nid == Self::trace_to_nid_rec(
                Self::nid_to_trace_rec(nid, cur_level, cur_rt),
                cur_rt,
                cur_level as int,
            ),
        decreases cur_level,
    {
        if cur_level == 0 {
        } else {
            let sz = Self::tree_size_spec(cur_level - 1);
            let offset = ((nid - cur_rt - 1) / sz as int) as nat;
            assert(offset < 512) by {
                lemma_multiply_divide_lt(nid - cur_rt - 1, sz as int, 512);
            };

            let new_rt = cur_rt + offset * sz + 1;
            assert(new_rt <= nid) by {
                lemma_remainder_lower(nid - cur_rt - 1, sz as int);
            };
            assert(nid < new_rt + sz) by {
                lemma_remainder(nid - cur_rt - 1, sz as int);
            };

            if new_rt == nid {
                let trace = seq![offset];
                reveal(NodeHelper::trace_to_nid_rec);
                assert(Self::trace_to_nid_rec(trace, cur_rt, cur_level as int) == nid) by {
                    Self::lemma_trace_to_nid_rec_inductive(trace, cur_rt, cur_level as int);
                };
            } else {
                Self::lemma_nid_to_trace_rec_sound(nid, (cur_level - 1) as nat, new_rt);
                let _trace = Self::nid_to_trace_rec(nid, (cur_level - 1) as nat, new_rt);
                let trace = seq![offset].add(_trace);
                assert(Self::trace_to_nid_rec(trace, cur_rt, cur_level as int) == nid) by {
                    Self::lemma_trace_to_nid_rec_inductive(trace, cur_rt, cur_level as int);
                    assert(_trace =~= trace.subrange(1, trace.len() as int));
                };
            }
        }
    }

    /// `nid_to_trace` correctly returns a trace of the node id `nid` starting from the root.
    /// By applying `nid_to_trace` to the trace produced by `nid_to_trace`, we can
    /// reconstruct the original node id.
    pub proof fn lemma_nid_to_trace_sound(nid: NodeId)
        requires
            Self::valid_nid(nid),
        ensures
            Self::valid_trace(Self::nid_to_trace(nid)),
            Self::trace_to_nid(Self::nid_to_trace(nid)) == nid,
    {
        reveal(NodeHelper::trace_to_nid_rec);
        if nid != Self::root_id() {
            Self::lemma_nid_to_trace_rec_sound(nid, 3, 0)
        }
    }

    /// 'trace_to_nid` is the left inverse of `nid_to_trace` between the valid node id set and the valid trace set.
    pub proof fn lemma_nid_to_trace_left_inverse()
        ensures
            left_inverse_on(
                |nid| Self::nid_to_trace(nid),
                |trace| Self::trace_to_nid(trace),
                Self::valid_nid_set(),
                Self::valid_trace_set(),
            ),
    {
        assert forall|nid| #[trigger]
            Self::valid_nid_set().contains(nid) implies Self::valid_trace_set().contains(
            Self::nid_to_trace(nid),
        ) && Self::trace_to_nid(Self::nid_to_trace(nid)) == nid by {
            Self::lemma_nid_to_trace_sound(nid);
        };
    }

    /// `trace_to_nid_rec` correctly returns a node id from the trace starting from `cur_rt`.
    /// We can reconstruct the trace using `nid_to_trace_rec` with the trace given by `trace_to_nid_rec`.
    #[verifier::spinoff_prover]
    pub proof fn lemma_trace_to_nid_rec_sound(trace: Seq<nat>, cur_rt: NodeId, cur_level: int)
        requires
            Self::valid_trace(trace),
            cur_rt + Self::tree_size_spec(cur_level) <= Self::total_size(),
            trace.len() <= cur_level,
        ensures
            cur_rt <= Self::trace_to_nid_rec(trace, cur_rt, cur_level) < cur_rt
                + Self::tree_size_spec(cur_level),
            Self::trace_to_nid_rec(trace, cur_rt, cur_level) == cur_rt <==> trace.len() == 0,
            trace.len() != 0 ==> trace =~= Self::nid_to_trace_rec(
                Self::trace_to_nid_rec(trace, cur_rt, cur_level),
                cur_level as nat,
                cur_rt,
            ),
        decreases trace.len(),
    {
        reveal(NodeHelper::trace_to_nid_rec);
        if trace.len() == 0 {
        } else {
            let new_trace = trace.subrange(1, trace.len() as int);

            let new_rt = cur_rt + trace[0] * Self::tree_size_spec(cur_level - 1) + 1;
            assert({
                &&& Self::valid_nid(new_rt)
                &&& new_rt + Self::tree_size_spec(cur_level - 1) <= Self::total_size()
            }) by {
                lemma_mul_is_distributive_sub_other_way(
                    Self::tree_size_spec(cur_level - 1) as int,
                    512,
                    trace[0] as int,
                );
                lemma_mul_inequality(1, 512 - trace[0], Self::tree_size_spec(cur_level - 1) as int);
            };

            let new_level = cur_level - 1;

            Self::lemma_trace_to_nid_rec_sound(new_trace, new_rt, new_level);
            let nid = Self::trace_to_nid_rec(trace, cur_rt, cur_level);

            let sz = Self::tree_size_spec(cur_level - 1);
            reveal(NodeHelper::trace_to_nid_rec);
            assert(new_rt + sz <= cur_rt + Self::tree_size_spec(cur_level)) by {
                lemma_mul_is_distributive_add_other_way(sz as int, trace[0] as int, 1);
                lemma_mul_inequality((trace[0] + 1) as int, 512, sz as int);
            };

            let offset = ((nid - cur_rt - 1) / sz as int) as nat;
            assert(trace[0] == offset) by {
                lemma_mul_is_distributive_add_other_way(sz as int, trace[0] as int, 1);
                lemma_div_is_ordered((trace[0] * sz) as int, (nid - cur_rt - 1) as int, sz as int);
                lemma_div_by_multiple_is_strongly_ordered(
                    (nid - cur_rt - 1) as int,
                    ((trace[0] + 1) * sz) as int,
                    (trace[0] + 1) as int,
                    sz as int,
                );
                lemma_div_by_multiple(trace[0] as int, sz as int);
                lemma_div_by_multiple((trace[0] + 1) as int, sz as int);
            }
        }
    }

    /// `trace_to_nid` correctly returns a node id from the trace starting from the root.
    /// We can reconstruct the node id using `trace_to_nid` with the trace given by `nid_to_trace`.
    pub proof fn lemma_trace_to_nid_sound(trace: Seq<nat>)
        requires
            Self::valid_trace(trace),
        ensures
            Self::valid_nid(Self::trace_to_nid(trace)),
            trace =~= Self::nid_to_trace(Self::trace_to_nid(trace)),
    {
        Self::lemma_trace_to_nid_rec_sound(trace, 0, 3)
    }

    /// `nid_to_trace` is the right inverse of `trace_to_nid` between the valid node id set and the valid trace set.
    pub proof fn lemma_nid_to_trace_right_inverse()
        ensures
            right_inverse_on(
                |trace| Self::nid_to_trace(trace),
                |nid| Self::trace_to_nid(nid),
                Self::valid_nid_set(),
                Self::valid_trace_set(),
            ),
    {
        assert forall|trace| #[trigger]
            Self::valid_trace_set().contains(trace) implies Self::valid_nid_set().contains(
            Self::trace_to_nid(trace),
        ) && Self::nid_to_trace(Self::trace_to_nid(trace)) == trace by {
            Self::lemma_trace_to_nid_sound(trace);
        };
    }

    /// The function `nid_to_trace` is bijective between the valid node id set and the valid trace set.
    pub proof fn lemma_nid_to_trace_bijective()
        ensures
            bijective_on(
                |nid| Self::nid_to_trace(nid),
                Self::valid_nid_set(),
                Self::valid_trace_set(),
            ),
    {
        Self::lemma_nid_to_trace_left_inverse();
        Self::lemma_nid_to_trace_right_inverse();
    }

    /// The function `trace_to_nid` is bijective between the valid trace set and the valid node id set.
    pub proof fn lemma_trace_to_nid_bijective()
        ensures
            bijective_on(
                |trace| Self::trace_to_nid(trace),
                Self::valid_trace_set(),
                Self::valid_nid_set(),
            ),
    {
        Self::lemma_nid_to_trace_bijective();
        Self::lemma_nid_to_trace_left_inverse();
        lemma_inverse_of_bijection_is_bijective(
            |nid| Self::nid_to_trace(nid),
            |trace| Self::trace_to_nid(trace),
            Self::valid_nid_set(),
            Self::valid_trace_set(),
        );
    }

    // Helper lemma: prove that the result length of nid_to_trace_rec does not exceed cur_level
    proof fn lemma_trace_rec_len_le_level(nid: NodeId, cur_level: nat, cur_rt: NodeId)
        ensures
            Self::nid_to_trace_rec(nid, cur_level, cur_rt).len() <= cur_level,
        decreases cur_level,
    // Induction proof on cur_level

    {
        if cur_level == 0 {
            assert(Self::nid_to_trace_rec(nid, 0, cur_rt).len() == 0);
        } else {
            let sz = Self::tree_size_spec(cur_level - 1);
            let offset = ((nid - cur_rt - 1) / sz as int) as nat;
            let new_rt = cur_rt + offset * sz + 1;

            if new_rt == nid {
            } else {
                Self::lemma_trace_rec_len_le_level(nid, (cur_level - 1) as nat, new_rt);
            }
        }
    }

    /// `nid_to_depth` correctly returns a depth of 3 or less.
    pub proof fn lemma_nid_to_dep_le_3(nid: NodeId)
        ensures
            Self::nid_to_dep(nid) <= 3,
    {
        if nid != Self::root_id() {
            Self::lemma_trace_rec_len_le_level(nid, 3, Self::root_id());
        }
    }

    /// The relation between nid_to_level and nid_to_dep.
    pub proof fn lemma_level_dep_relation(nid: NodeId)
        ensures
            Self::nid_to_level(nid) == 4 - Self::nid_to_dep(nid),
    {
        Self::lemma_nid_to_dep_le_3(nid);
    }

    /// A valid node's descendant's id is less than or equal to the total size.
    pub proof fn lemma_valid_level_to_node(nid: NodeId)
        requires
            Self::valid_nid(nid),
        ensures
            nid + Self::tree_size_spec(Self::nid_to_level(nid) - 1) <= Self::total_size(),
    {
        let trace = Self::nid_to_trace(nid);
        Self::lemma_nid_to_trace_sound(nid);
        reveal(NodeHelper::trace_to_nid_rec);
        Self::lemma_trace_to_nid_inner(trace);
        Self::lemma_trace_to_nid_upperbound_spec(trace.len());
    }

    /// A valid node's subtree size is at least 1.
    pub proof fn lemma_sub_tree_size_lowerbound(nid: NodeId)
        requires
            Self::valid_nid(nid),
        ensures
            Self::sub_tree_size(nid) >= 1,
    {
        Self::lemma_nid_to_trace_sound(nid);
    }

    /// A valid node plus its subtree size is less than or equal to the total size.
    pub proof fn lemma_next_outside_subtree_bounded(nid: NodeId)
        requires
            Self::valid_nid(nid),
        ensures
            Self::next_outside_subtree(nid) <= Self::total_size(),
    {
        Self::lemma_valid_level_to_node(nid);
    }

    /// A node is in its own subtree.
    pub proof fn lemma_in_subtree_self(nid: NodeId)
        requires
            Self::valid_nid(nid),
        ensures
            Self::in_subtree(nid, nid),
    {
    }

    /// A child is in the subtree of its parent.
    pub proof fn lemma_is_child_implies_in_subtree(pa: NodeId, ch: NodeId)
        requires
            Self::is_child(pa, ch),
            Self::valid_nid(ch),
        ensures
            Self::in_subtree(pa, ch),
            Self::nid_to_dep(pa) + 1 == Self::nid_to_dep(ch),
    {
    }

    pub proof fn lemma_is_child_bound(pa: NodeId, ch: NodeId)
        requires
            Self::valid_nid(pa),
            Self::valid_nid(ch),
            Self::is_child(pa, ch),
        ensures
            Self::next_outside_subtree(ch) <= Self::next_outside_subtree(pa),
    {
        let dep_pa = Self::nid_to_dep(pa);
        let dep_ch = Self::nid_to_dep(ch);
        let sz_pa = Self::sub_tree_size(pa);
        let sz_ch = Self::sub_tree_size(ch);
        let trace_pa = Self::nid_to_trace(pa);
        let trace_ch = Self::nid_to_trace(ch);
        Self::lemma_nid_to_trace_sound(pa);
        Self::lemma_nid_to_trace_sound(ch);
        Self::lemma_is_child_implies_in_subtree(pa, ch);

        // Verify subtree containment.
        assert((ch as int) + (sz_ch as int) <= (pa as int) + (sz_pa as int)) by {
            // Break down into two cases:
            // 1. If ch == pa, then ch + sz_ch == pa + sz_ch < pa + sz_pa, because sz_ch < sz_pa
            // 2. If ch > pa, we need more detailed analysis
            if ch == pa {
            } else {
                let offset = trace_ch.last();
                let pa_level = Self::dep_to_level(dep_pa);
                let sz = Self::tree_size_spec(pa_level - 2);
                Self::lemma_child_nid_from_trace_offset_sound(trace_pa, offset);
                assert(ch == pa + offset * sz + 1) by {
                    assert(trace_ch.drop_last() =~= trace_pa) by {
                        Self::lemma_trace_to_nid_sound(trace_ch.drop_last());
                    }

                    assert(trace_ch.last() == offset) by {
                        assert(trace_ch =~= trace_pa.push(offset));
                        assert(Self::trace_to_nid(trace_ch) == Self::trace_to_nid(
                            trace_pa.push(offset),
                        ));
                    }
                    assert(ch == pa + offset * sz + 1);
                };

                assert(ch + sz_ch <= pa + sz_pa) by {
                    lemma_mul_inequality(offset as int + 1, 512, sz as int);
                    lemma_mul_is_distributive_add_other_way(sz as int, offset as int, 1);
                };
            }
        };
    }

    // If 'nd' is in the subtree of 'rt', then `next_outside_subtree(nd)` (the next node id outside the subtree of 'nd') is less than or equal to
    // `next_outside_subtree(rt)`.
    pub proof fn lemma_in_subtree_bounded(rt: NodeId, nd: NodeId)
        requires
            Self::valid_nid(rt),
            Self::in_subtree(rt, nd),
        ensures
            Self::next_outside_subtree(nd) <= Self::next_outside_subtree(rt),
        decreases Self::nid_to_trace(nd).len() - Self::nid_to_trace(rt).len(),
    {
        if rt == nd {
        } else {
            // Induction step: use `lemma_is_child_bound` to prove the relationship between `nd` and its parent,
            // and then use the induction hypothesis between `rt` and `nd`'s parent.
            let parent = Self::get_parent(nd);
            assert(Self::nid_to_trace(rt).len() < Self::nid_to_trace(nd).len()) by {
                if Self::nid_to_trace(rt).len() == Self::nid_to_trace(nd).len() {
                    assert(Self::nid_to_trace(rt) == Self::nid_to_trace(nd));
                    Self::lemma_nid_to_trace_sound(rt);
                    Self::lemma_nid_to_trace_sound(nd);
                    assert(rt == nd);
                }
            }
            Self::lemma_get_parent_sound(nd);
            assert(Self::nid_to_trace(rt).is_prefix_of(Self::nid_to_trace(parent)));
            Self::lemma_in_subtree_bounded(rt, parent);
            Self::lemma_is_child_bound(parent, nd);
        }
    }

    /// `get_parent` correctly returns the parent of a node.
    /// The result indeed satisfies `is_child(get_parent(nid), nid)`.
    pub proof fn lemma_get_parent_sound(nid: NodeId)
        requires
            Self::valid_nid(nid),
            nid != Self::root_id(),
        ensures
            Self::valid_nid(Self::get_parent(nid)),
            Self::is_child(Self::get_parent(nid), nid),
    {
        Self::lemma_nid_to_trace_sound(nid);
        Self::lemma_trace_to_nid_sound(Self::nid_to_trace(nid).drop_last());
    }

    /// `get_offset` returns the offset in a correct range.
    pub proof fn lemma_get_offset_sound(nid: NodeId)
        requires
            Self::valid_nid(nid),
            nid != Self::root_id(),
        ensures
            0 <= Self::get_offset(nid) < 512,
    {
        Self::lemma_nid_to_trace_sound(nid);
    }

    pub proof fn lemma_parent_offset_uniqueness(nid1: NodeId, nid2: NodeId)
        requires
            Self::valid_nid(nid1),
            Self::valid_nid(nid2),
            nid1 != Self::root_id(),
            nid2 != Self::root_id(),
            nid1 != nid2,
        ensures
            !(Self::get_parent(nid1) == Self::get_parent(nid2) && Self::get_offset(nid1)
                == Self::get_offset(nid2)),
    {
        if Self::get_parent(nid1) == Self::get_parent(nid2) && Self::get_offset(nid1)
            == Self::get_offset(nid2) {
            let trace1 = Self::nid_to_trace(nid1);
            let trace2 = Self::nid_to_trace(nid2);

            Self::lemma_nid_to_trace_sound(nid1);
            Self::lemma_nid_to_trace_sound(nid2);

            Self::lemma_nid_to_trace_left_inverse();
            Self::lemma_trace_to_nid_sound(trace1.drop_last());
            Self::lemma_trace_to_nid_sound(trace2.drop_last());
            assert(Self::trace_to_nid(trace1.drop_last()) == Self::trace_to_nid(
                trace2.drop_last(),
            ));

            assert(trace1 =~= trace2) by {
                let common_prefix = trace1.drop_last();
                let common_last = trace1.last();
                assert(trace1 =~= common_prefix.push(common_last));
                assert(trace2 =~= common_prefix.push(common_last));
            };

            // But since nid_to_trace is bijective (left inverse to trace_to_nid)
            // and trace1 == trace2, we must have nid1 == nid2
            Self::lemma_nid_to_trace_right_inverse();
            assert(nid1 == nid2);  // contradiction with nid1 != nid2
        }
    }

    /// `get_child` correctly returns the child of a node.
    /// The result indeed satisfies `is_child(nid, get_child(nid, offset))`.
    pub proof fn lemma_get_child_sound(nid: NodeId, offset: nat)
        requires
            Self::valid_nid(nid),
            Self::nid_to_dep(nid) < 3,
            0 <= offset < 512,
        ensures
            Self::valid_nid(Self::get_child(nid, offset)),
            nid == Self::get_parent(Self::get_child(nid, offset)),
            offset == Self::get_offset(Self::get_child(nid, offset)),
            Self::is_child(nid, Self::get_child(nid, offset)),
    {
        Self::lemma_nid_to_trace_sound(nid);
        Self::lemma_trace_to_nid_sound(Self::nid_to_trace(nid).push(offset));
        assert(Self::nid_to_trace(nid).push(offset).drop_last() =~= Self::nid_to_trace(nid));
    }

    /// The valid nid set's cardinality is `total_size`.
    pub proof fn lemma_valid_nid_set_cardinality()
        ensures
            Self::valid_nid_set().finite(),
            Self::valid_nid_set().len() == Self::total_size(),
    {
        assert(Self::valid_nid_set() =~= Set::new(|nid| 0 <= nid < Self::total_size()));
        lemma_nat_range_finite(0, Self::total_size());
    }

    /// The valid trace set's cardinality is `total_size`.
    pub proof fn lemma_valid_trace_set_cardinality()
        ensures
            Self::valid_trace_set().finite(),
            Self::valid_trace_set().len() == Self::total_size(),
    {
        Self::lemma_valid_nid_set_cardinality();
        Self::lemma_nid_to_trace_bijective();
        lemma_bijective_cardinality(
            |nid| Self::nid_to_trace(nid),
            Self::valid_nid_set(),
            Self::valid_trace_set(),
        );
    }

    /// `get_subtree_traces` returns a finite set of traces.
    pub proof fn lemma_get_subtree_traces_finite(trace: Seq<nat>)
        ensures
            Self::get_subtree_traces(trace).finite(),
    {
        Self::lemma_valid_trace_set_cardinality();
    }

    /// `get_subtree_traces` contains the input trace.
    pub proof fn lemma_get_subtree_traces_contains_self(trace: Seq<nat>)
        requires
            Self::valid_trace(trace),
        ensures
            Self::get_subtree_traces(trace).contains(trace),
            Self::get_subtree_traces(trace).len() > 0,
    {
        Self::lemma_get_subtree_traces_finite(trace);
        axiom_set_contains_len(Self::get_subtree_traces(trace), trace);
    }

    /// `get_subtree_traces` is injective
    pub proof fn lemma_get_subtree_traces_injective()
        ensures
            injective_on(|trace| Self::get_subtree_traces(trace), Self::valid_trace_set()),
    {
        assert forall|x, y|
            #![trigger Self::get_subtree_traces(x), Self::get_subtree_traces(y)]
            Self::valid_trace_set().contains(x) && Self::valid_trace_set().contains(y)
                && Self::get_subtree_traces(x) == Self::get_subtree_traces(y) implies x == y by {
            Self::lemma_get_subtree_traces_contains_self(x);
            Self::lemma_get_subtree_traces_contains_self(y);
            let z = choose|z| Self::get_subtree_traces(x).contains(z);
            lemma_prefix_of_common_sequence(x, y, z);
        }

    }

    /// The cardinality of the subtree traces is equal to the tree size specification.
    pub proof fn lemma_get_subtree_traces_cardinality(trace: Seq<nat>)
        requires
            Self::valid_trace(trace),
        ensures
            Self::get_subtree_traces(trace).len() == Self::tree_size_spec(3 - trace.len()),
        decreases 3 - trace.len(),
    {
        let subtree_trace_set = Self::get_subtree_traces(trace);
        assert(subtree_trace_set.contains(trace));
        Self::lemma_valid_trace_set_cardinality();
        if trace.len() == 3 {
            assert(forall|subtree_trace| #[trigger]
                subtree_trace_set.contains(subtree_trace) ==> subtree_trace =~= trace);
            assert(subtree_trace_set.is_singleton()) by {
                assert(forall|x, y|
                    #![trigger subtree_trace_set.contains(x),subtree_trace_set.contains(y)]
                    subtree_trace_set.contains(x) && subtree_trace_set.contains(y) ==> x == y);
            }
            subtree_trace_set.lemma_singleton_size();
        } else {
            // Split the set between the singleton `trace` and `child_trace_set`.
            let f = |child_trace: Seq<nat>| child_trace.len() > trace.len();
            let child_trace_set = subtree_trace_set.filter(f);
            let trace_singleton_set = subtree_trace_set.filter(
                |child_trace: Seq<nat>| !f(child_trace),
            );
            assert(trace_singleton_set.is_singleton()) by {
                assert(trace_singleton_set.contains(trace));
                assert forall|x, y|
                    #![trigger trace_singleton_set.contains(x), trace_singleton_set.contains(y)]
                    trace_singleton_set.contains(x) && trace_singleton_set.contains(y) implies x
                    == y by {
                    assert(x =~= trace);
                    assert(y =~= trace);
                }
            }
            assert(subtree_trace_set.len() == child_trace_set.len() + 1) by {
                lemma_set_separation(subtree_trace_set, f);
                trace_singleton_set.lemma_singleton_size();
                trace_singleton_set.lemma_singleton_size();
            }

            // Split `child_trace_set` into sets of traces with different offsets.
            let offset_set = Set::new(|i: nat| 0 <= i < 512);
            assert(offset_set.len() == 512 && offset_set.finite()) by {
                lemma_nat_range_finite(0, 512);
            }
            // The set of all child traces
            let child_traces = offset_set.map(|offset| trace.push(offset));
            assert(child_traces.len() == 512 && child_traces.finite()) by {
                // Prove that push is injective
                assert forall|t1: nat, t2: nat|
                    #![trigger trace.push(t1), trace.push(t2)]
                    trace.push(t1) == trace.push(t2) implies t1 == t2 by {
                    assert(trace.push(t1).last() == trace.push(t2).last());
                }
                lemma_injective_implies_injective_on(|offset| trace.push(offset), offset_set);
                lemma_injective_map_cardinality(
                    |offset| trace.push(offset),
                    offset_set,
                    offset_set,
                );
            }
            assert(child_traces <= Self::valid_trace_set());
            // The set of each child trace's subtree traces set
            let child_subtree_trace_set = child_traces.map(
                |child_trace| Self::get_subtree_traces(child_trace),
            );
            // Use induction hypothesis here, prove that each child trace's subtree traces set has the size of tree with a
            // height of 2 - trace.len()
            assert forall|child_trace| #[trigger]
                child_traces.contains(child_trace) implies Self::get_subtree_traces(
                child_trace,
            ).len() == Self::tree_size_spec(2 - trace.len()) by {
                Self::lemma_get_subtree_traces_cardinality(child_trace);
            };
            assert(child_subtree_trace_set.len() == 512 && child_subtree_trace_set.finite()) by {
                Self::lemma_get_subtree_traces_injective();
                lemma_injective_map_cardinality(
                    |child_trace| Self::get_subtree_traces(child_trace),
                    Self::valid_trace_set(),
                    child_traces,
                );
            }

            // Show that the child traces are disjoint
            assert(pairwise_disjoint(child_subtree_trace_set));
            // Show that the flatten of the child_subtree_trace_set is equal to the child_trace_set
            assert(child_trace_set =~= child_subtree_trace_set.flatten()) by {
                assert forall|child_trace: Seq<nat>| #[trigger]
                    child_trace_set.contains(child_trace)
                        == child_subtree_trace_set.flatten().contains(child_trace) by {
                    if child_trace_set.contains(child_trace) {
                        assert(trace.is_prefix_of(child_trace));
                        let trace_child = child_trace.subrange(0, (trace.len() + 1) as int);
                        let offset = child_trace[trace.len() as int];
                        assert(trace_child =~= trace.push(offset));
                        assert(offset_set.contains(offset));
                        // Definition of flatten
                        assert(child_traces.contains(trace_child));
                        assert(child_subtree_trace_set.contains(
                            Self::get_subtree_traces(trace_child),
                        ));
                    }
                    if child_subtree_trace_set.flatten().contains(child_trace) {
                        let child_subtree_trace = choose|t: Set<Seq<nat>>|
                            child_subtree_trace_set.contains(t) && t.contains(child_trace);
                        let trace_child = choose|t: Seq<nat>| #[trigger]
                            child_traces.contains(t) && Self::get_subtree_traces(t)
                                == child_subtree_trace;
                        assert(trace.is_prefix_of(trace_child));
                        assert(trace_child.is_prefix_of(child_trace));
                        assert(trace.is_prefix_of(child_trace));
                    }
                }
            }

            assert(child_trace_set.len() == 512 * Self::tree_size_spec(2 - trace.len())) by {
                lemma_flatten_cardinality_under_disjointness_same_length(
                    child_subtree_trace_set,
                    Self::tree_size_spec(2 - trace.len()),
                );
            }
        }
    }

    /// The cardinality of nodes in subtree is `sub_tree_size`
    pub proof fn lemma_in_subtree_cardinality(nid: NodeId)
        requires
            Self::valid_nid(nid),
        ensures
            Self::valid_nid_set().filter(|id| Self::in_subtree(nid, id)).len()
                == Self::sub_tree_size(nid),
    {
        let nid_trace = Self::nid_to_trace(nid);
        let subtree_traces = Self::get_subtree_traces(nid_trace);
        let subtree_ids = Self::valid_nid_set().filter(|id| Self::in_subtree(nid, id));
        Self::lemma_nid_to_trace_sound(nid);
        Self::lemma_valid_nid_set_cardinality();
        assert(subtree_traces.len() == Self::sub_tree_size(nid) && subtree_traces.finite()) by {
            Self::lemma_get_subtree_traces_cardinality(nid_trace);
            Self::lemma_get_subtree_traces_finite(nid_trace);
        }
        assert(bijective_on(|id| Self::nid_to_trace(id), subtree_ids, subtree_traces)) by {
            Self::lemma_nid_to_trace_bijective();
            // Prove subtree_traces =~= subtree_ids.map(nid_to_trace)
            assert forall|trace| #[trigger]
                subtree_traces.contains(trace) == subtree_ids.map(
                    |id| Self::nid_to_trace(id),
                ).contains(trace) by {
                if subtree_traces.contains(trace) {
                    let trace_id = Self::trace_to_nid(trace);
                    assert(subtree_ids.contains(trace_id) && Self::nid_to_trace(trace_id) == trace)
                        by {
                        Self::lemma_trace_to_nid_sound(trace);
                    }
                }
            }
            assert(subtree_traces =~= subtree_ids.map(|id| Self::nid_to_trace(id)));

        }
        lemma_bijective_cardinality(|id| Self::nid_to_trace(id), subtree_ids, subtree_traces);
    }

    /// If a node id is in the subtree, than it falls in the range of [rt, next_outside_subtree(rt)).
    proof fn lemma_in_subtree_implies_in_subtree_range(rt: NodeId, nd: NodeId)
        requires
            Self::valid_nid(rt),
            Self::in_subtree(rt, nd),
        ensures
            Self::in_subtree_range(rt, nd),
    {
        assert(rt <= nd < Self::next_outside_subtree(rt)) by {
            assert(Self::next_outside_subtree(nd) <= Self::next_outside_subtree(rt)) by {
                Self::lemma_in_subtree_bounded(rt, nd);
            };
            assert(nd < Self::next_outside_subtree(nd)) by {
                Self::lemma_sub_tree_size_lowerbound(nd);
            };
            assert(rt <= nd) by {
                let rt_trace = Self::nid_to_trace(rt);
                let nd_trace = Self::nid_to_trace(nd);

                // First prove that both are valid traces
                assert(Self::valid_trace(rt_trace)) by {
                    Self::lemma_nid_to_trace_sound(rt);
                }
                assert(Self::valid_trace(nd_trace)) by {
                    Self::lemma_nid_to_trace_sound(nd);
                }

                if rt_trace.len() == 0 {
                } else {
                    if rt == nd {
                    } else {
                        let suffix = nd_trace.subrange(
                            rt_trace.len() as int,
                            nd_trace.len() as int,
                        );

                        let cur_level = 3 - rt_trace.len();
                        assert(Self::valid_trace(suffix)) by {
                            assert(forall|i: int|
                                #![trigger suffix[i]]
                                0 <= i < suffix.len() ==> 0 <= suffix[i] < 512) by {
                                assert(forall|i: int|
                                    #![trigger nd_trace[i + rt_trace.len()]]
                                    0 <= i < suffix.len() ==> 0 <= nd_trace[i + rt_trace.len()]
                                        < 512);
                            }
                        }

                        // Apply trace_to_nid_rec_sound directly using our key insights:
                        // 1. rt = trace_to_nid(rt_trace)
                        // 2. nd = trace_to_nid(rt_trace.add(suffix))
                        // 3. Using lemma_trace_to_nid_rec_sound, we know:
                        //    cur_rt <= trace_to_nid_rec(trace, cur_rt, level)

                        assert(rt + Self::tree_size_spec(cur_level) <= Self::total_size()) by {
                            Self::lemma_next_outside_subtree_bounded(rt);
                        }

                        assert(nd == Self::trace_to_nid_rec(suffix, rt, cur_level)) by {
                            assert(rt_trace.add(suffix) =~= nd_trace) by {
                                assert(rt_trace.is_prefix_of(nd_trace));
                                assert(rt_trace =~= nd_trace.subrange(0, rt_trace.len() as int));
                            }

                            assert(rt == Self::trace_to_nid(rt_trace)) by {
                                Self::lemma_nid_to_trace_sound(rt);
                            }

                            assert(Self::nid_to_trace(nd) =~= rt_trace.add(suffix)) by {
                                assert(Self::nid_to_trace(nd) =~= nd_trace);
                                assert(nd_trace =~= rt_trace.add(suffix));
                            }
                            Self::lemma_nid_to_trace_bijective();

                            assert(Self::trace_to_nid(Self::nid_to_trace(nd)) == nd) by {
                                Self::lemma_nid_to_trace_sound(nd);
                            }

                            assert(Self::trace_to_nid(Self::nid_to_trace(nd)) == Self::trace_to_nid(
                                rt_trace.add(suffix),
                            )) by {
                                let t1 = Self::nid_to_trace(nd);
                                let t2 = rt_trace.add(suffix);

                                Self::lemma_trace_to_nid_sound(t1);
                                Self::lemma_trace_to_nid_sound(t2);
                                assert(t1 =~= t2);
                                assert(t1 =~= Self::nid_to_trace(Self::trace_to_nid(t1)));
                                assert(t2 =~= Self::nid_to_trace(Self::trace_to_nid(t2)));
                                Self::lemma_nid_to_trace_right_inverse();
                            }
                            assert(nd == Self::trace_to_nid(rt_trace.add(suffix)));

                            Self::lemma_trace_to_nid_split(rt_trace, suffix, rt, cur_level);

                            // By the ensures clause of lemma_trace_to_nid_split, we have:
                            // trace_to_nid(rt_trace.add(suffix)) == trace_to_nid_rec(suffix, rt, cur_level)
                            // Therefore, nd == trace_to_nid_rec(suffix, rt, cur_level)
                        }
                        assert(rt <= Self::trace_to_nid_rec(suffix, rt, cur_level)) by {
                            Self::lemma_trace_to_nid_rec_sound(suffix, rt, cur_level);
                        }
                    }
                }
            };
        };
    }

    /// If a node id is in the range [rt, next_outside_subtree(rt)), then it is in the subtree (given by trace prefix).
    /// We prove this by showing that we can find exactly `sub_tree_size(rt)` node ids in the range
    /// `rt <= nd < next_outside_subtree(rt)` that is in the subtree, so every node id in the range
    /// is in the subtree.
    pub proof fn lemma_in_subtree_range_implies_in_subtree(rt: NodeId, nd: NodeId)
        requires
            Self::valid_nid(rt),
            rt <= nd < Self::next_outside_subtree(rt),
        ensures
            Self::in_subtree(rt, nd),
    {
        // Showing every node id in the range is valid and the range is `Self::sub_tree_size(rt)`
        let nid_set = Set::new(|nid: nat| rt <= nid < Self::next_outside_subtree(rt));
        assert(nid_set.len() == Self::sub_tree_size(rt) && nid_set.finite()) by {
            lemma_nat_range_finite(rt, Self::next_outside_subtree(rt));
        }
        assert(nid_set =~= nid_set.filter(|id| Self::valid_nid(id))) by {
            assert forall|id| #[trigger] nid_set.contains(id) implies Self::valid_nid(id) by {
                Self::lemma_next_outside_subtree_bounded(rt);
            }
        }
        assert(nid_set =~= Self::valid_nid_set().filter(
            |id| rt <= id < Self::next_outside_subtree(rt),
        ));

        // Shhowing there are exactly `sub_tree_size(rt)` node ids that are in the subtree
        let child_set = Self::valid_nid_set().filter(|id| Self::in_subtree(rt, id));
        assert(child_set.len() == Self::sub_tree_size(rt)) by {
            Self::lemma_in_subtree_cardinality(rt);
        };
        // Every node id in the subtree falls in the range
        assert(child_set =~= child_set.filter(|id| rt <= id < Self::next_outside_subtree(rt))) by {
            assert forall|id| #[trigger] child_set.contains(id) implies rt <= id
                < Self::next_outside_subtree(rt) by {
                Self::lemma_in_subtree_implies_in_subtree_range(rt, id);
            }
        }
        // So we can find exactly `sub_tree_size(rt)` node ids in the range that are in the subtree
        assert(child_set =~= nid_set.filter(|id| Self::in_subtree(rt, id)));
        assert(nid_set.len() == nid_set.filter(|id| Self::in_subtree(rt, id)).len());
        // Therefore, every node id in the range is in the subtree
        assert(nid_set == nid_set.filter(|id| Self::in_subtree(rt, id))) by {
            lemma_filter_len_unchanged_implies_equal(nid_set, |id| Self::in_subtree(rt, id));
        }
        assert(nid_set.contains(nd));
    }

    /// 'in_subtree' is equivalent to 'in_subtree_range' (nd in [rt, next_outside_subtree(rt)))
    pub broadcast proof fn lemma_in_subtree_iff_in_subtree_range(rt: NodeId, nd: NodeId)
        requires
            Self::valid_nid(rt),
        ensures
            #![trigger Self::in_subtree(rt, nd)]
            #![trigger Self::in_subtree_range(rt, nd)]
            Self::in_subtree(rt, nd) <==> Self::in_subtree_range(rt, nd),
    {
        if Self::in_subtree(rt, nd) {
            Self::lemma_in_subtree_implies_in_subtree_range(rt, nd);
        }
        if rt <= nd < Self::next_outside_subtree(rt) {
            Self::lemma_next_outside_subtree_bounded(rt);
            Self::lemma_in_subtree_range_implies_in_subtree(rt, nd);
        }
    }

    /// If `ch` is a child of `pa`, `ch` is in the subtree of `rt`, and `rt` is not equal to `ch`,
    /// then `pa` is in the subtree of `rt`.
    pub proof fn lemma_child_in_subtree_implies_in_subtree(rt: NodeId, pa: NodeId, ch: NodeId)
        requires
            Self::valid_nid(rt),
            Self::valid_nid(pa),
            Self::in_subtree(rt, ch),
            Self::is_child(pa, ch),
            rt != ch,
        ensures
            Self::in_subtree(rt, pa),
    {
        if (Self::nid_to_trace(ch).len() == Self::nid_to_trace(rt).len()) {
            assert(Self::nid_to_trace(ch) =~= Self::nid_to_trace(rt));
            Self::lemma_nid_to_trace_sound(ch);
            Self::lemma_nid_to_trace_sound(rt);
            assert(ch == rt);
        }
    }

    /// The `in_subtree_range` version of `lemma_child_in_subtree_implies_in_subtree`.
    pub proof fn lemma_child_in_subtree_range_implies_in_subtree_range(
        rt: NodeId,
        pa: NodeId,
        ch: NodeId,
    )
        requires
            Self::valid_nid(rt),
            Self::valid_nid(pa),
            Self::in_subtree_range(rt, ch),
            Self::is_child(pa, ch),
            rt != ch,
        ensures
            Self::in_subtree_range(rt, pa),
    {
        Self::lemma_in_subtree_iff_in_subtree_range(rt, ch);
        Self::lemma_in_subtree_iff_in_subtree_range(rt, pa);
        Self::lemma_child_in_subtree_implies_in_subtree(rt, pa, ch);
    }

    /// If `pa` is not in the subtree of `rt`, `ch` is a child of `pa`, and `rt` is not equal to `ch`,
    /// then `ch` is not in the subtree of `rt`.
    pub proof fn lemma_not_in_subtree_range_implies_child_not_in_subtree_range(
        rt: NodeId,
        pa: NodeId,
        ch: NodeId,
    )
        requires
            Self::valid_nid(rt),
            Self::valid_nid(pa),
            Self::is_child(pa, ch),
            rt != ch,
            !Self::in_subtree_range(rt, pa),
        ensures
            !Self::in_subtree_range(rt, ch),
    {
        if Self::in_subtree_range(rt, ch) {
            Self::lemma_next_outside_subtree_bounded(rt);
            Self::lemma_child_in_subtree_range_implies_in_subtree_range(rt, pa, ch);
        }
    }

    /// If `pa` is in the subtree of `rt`, `ch` is a child of `pa`, then `ch` is in the subtree of `rt`.
    pub proof fn lemma_in_subtree_is_child_in_subtree(rt: NodeId, nd: NodeId, ch: NodeId)
        requires
            Self::in_subtree(rt, nd),
            Self::valid_nid(ch),
            Self::is_child(nd, ch),
        ensures
            Self::in_subtree(rt, ch),
    {
    }

    /// If `pa` is the parent of `ch`, then `pa` is less than `ch`.
    pub proof fn lemma_is_child_nid_increasing(pa: NodeId, ch: NodeId)
        requires
            Self::valid_nid(pa),
            Self::valid_nid(ch),
            Self::is_child(pa, ch),
        ensures
            pa < ch,
    {
        Self::lemma_is_child_implies_in_subtree(pa, ch);
        Self::lemma_in_subtree_iff_in_subtree_range(pa, ch);
    }

    pub proof fn lemma_brother_nid_increasing(pa: NodeId, offset1: nat, offset2: nat)
        requires
            Self::valid_nid(pa),
            Self::is_not_leaf(pa),
            0 <= offset1 < offset2 < 512,
        ensures
            Self::get_child(pa, offset1) < Self::get_child(pa, offset2),
    {
        Self::lemma_parent_child_algebraic_relation(pa, offset1);
        Self::lemma_parent_child_algebraic_relation(pa, offset2);
        let tree_size = Self::tree_size_spec(Self::nid_to_level(pa) - 2);
        assert(offset1 * tree_size < offset2 * tree_size) by (nonlinear_arith)
            requires
                0 <= offset1 < offset2,
                tree_size > 0,
        ;
    }

    pub proof fn lemma_is_child_level_relation(pa: NodeId, ch: NodeId)
        requires
            Self::valid_nid(pa),
            Self::valid_nid(ch),
            Self::is_child(pa, ch),
        ensures
            Self::nid_to_level(pa) == Self::nid_to_level(ch) + 1,
    {
        Self::lemma_is_child_implies_in_subtree(pa, ch);
        Self::lemma_level_dep_relation(pa);
        Self::lemma_level_dep_relation(ch);
    }

    proof fn lemma_trace_to_nid_rec_push(trace: Seq<nat>, offset: nat, rt: NodeId, level: int)
        requires
            Self::valid_trace(trace),
            trace.len() < level,
        ensures
            Self::trace_to_nid_rec(trace.push(offset), rt, level) == Self::trace_to_nid_rec(
                trace,
                rt,
                level,
            ) + offset * Self::tree_size_spec(level - trace.len() - 1) + 1,
        decreases trace.len(),
    {
        reveal(NodeHelper::trace_to_nid_rec);
        let pushed_trace = trace.push(offset);
        Self::lemma_trace_to_nid_rec_inductive(pushed_trace, rt, level);
        if trace.len() == 0 {
            assert(pushed_trace.drop_first() == Seq::<nat>::empty());
        } else {
            let new_rt = rt + trace[0] * Self::tree_size_spec(level - 1) + 1;
            Self::lemma_trace_to_nid_rec_push(trace.drop_first(), offset, new_rt, level - 1);
            assert(pushed_trace.drop_first() == trace.drop_first().push(offset));
        }
    }

    pub proof fn lemma_trace_to_nid_push(trace: Seq<nat>, offset: nat)
        requires
            Self::valid_trace(trace),
            trace.len() < 3,
        ensures
            Self::trace_to_nid(trace.push(offset)) == Self::trace_to_nid(trace) + offset
                * Self::tree_size_spec(3 - trace.len() - 1) + 1,
    {
        Self::lemma_trace_to_nid_rec_push(trace, offset, 0, 3);
    }

    pub proof fn lemma_parent_child_algebraic_relation(nid: NodeId, offset: nat)
        requires
            Self::valid_nid(nid),
            Self::is_not_leaf(nid),
            0 <= offset < 512,
        ensures
            Self::get_child(nid, offset) == nid + offset * Self::tree_size_spec(
                Self::nid_to_level(nid) - 2,
            ) + 1,
    {
        Self::lemma_nid_to_trace_sound(nid);
        Self::lemma_trace_to_nid_push(Self::nid_to_trace(nid), offset);
    }

    pub proof fn lemma_brother_algebraic_relation(nid: NodeId, offset: nat)
        requires
            Self::valid_nid(nid),
            Self::is_not_leaf(nid),
            0 <= offset < 511,
        ensures
            Self::next_outside_subtree(NodeHelper::get_child(nid, offset)) == NodeHelper::get_child(
                nid,
                offset + 1,
            ),
    {
        Self::lemma_parent_child_algebraic_relation(nid, offset);
        Self::lemma_parent_child_algebraic_relation(nid, offset + 1);
        Self::lemma_get_child_sound(nid, offset);
        Self::lemma_get_child_sound(nid, offset + 1);
        let tree_size = Self::tree_size_spec(Self::nid_to_level(nid) - 2);
        assert(offset * tree_size + tree_size == (offset + 1) * tree_size) by (nonlinear_arith);
    }

    pub proof fn lemma_last_child_next_outside_subtree(nid: NodeId)
        requires
            Self::valid_nid(nid),
            Self::is_not_leaf(nid),
        ensures
            Self::next_outside_subtree(Self::get_child(nid, 511)) == Self::next_outside_subtree(
                nid,
            ),
    {
        Self::lemma_parent_child_algebraic_relation(nid, 511);
        Self::lemma_get_child_sound(nid, 511);
    }

    pub proof fn lemma_brothers_have_different_offset(nid1: NodeId, nid2: NodeId)
        requires
            Self::valid_nid(nid1),
            nid1 != Self::root_id(),
            Self::valid_nid(nid2),
            nid2 != Self::root_id(),
            Self::get_parent(nid1) == Self::get_parent(nid2),
        ensures
            Self::get_offset(nid1) != Self::get_offset(nid2),
    {
        admit();
    }
}

} // verus!
