use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::arithmetic::power::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;

use super::common::*;

verus! {

pub struct NodeHelper;

impl NodeHelper {
    pub open spec fn level_to_dep(level: nat) -> nat
        recommends
            1 <= level <= 4,
    {
        (4 - level) as nat
    }

    pub open spec fn dep_to_level(dep: nat) -> nat
        recommends
            0 <= dep < 4,
    {
        (4 - dep) as nat
    }

    pub proof fn lemma_level_to_dep(level: nat)
        requires
            1 <= level <= 4,
        ensures
            Self::dep_to_level(Self::level_to_dep(level)) == level,
    {
    }

    pub proof fn lemma_dep_to_level(dep: nat)
        requires
            0 <= dep < 4,
        ensures
            Self::level_to_dep(Self::dep_to_level(dep)) == dep,
    {
    }

    pub open spec fn size_at_dep(dep: nat) -> nat
        recommends
            0 <= dep < 4,
    {
        pow(512, dep) as nat
    }

    pub proof fn lemma_size_at_dep()
        ensures
            Self::size_at_dep(0) == 1,
            Self::size_at_dep(1) == 512,
            Self::size_at_dep(2) == 262144,
            Self::size_at_dep(3) == 134217728,
    {
    }

    pub open spec fn tree_size_spec(max_dep: int) -> nat
        recommends
            0 <= max_dep < 4,
        decreases max_dep,
    {
        let cur_dep = max_dep as nat;
        if max_dep == 0 {
            Self::size_at_dep(cur_dep)
        } else if max_dep > 0 {
            Self::size_at_dep(cur_dep) + Self::tree_size_spec(max_dep - 1)
        } else {
            arbitrary()
        }
    }

    pub proof fn lemma_tree_size_spec()
        ensures
            Self::tree_size_spec(0) == 1,
            Self::tree_size_spec(1) == 513,
            Self::tree_size_spec(2) == 262657,
            Self::tree_size_spec(3) == 134480385,
    {
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
        Self::lemma_tree_size_spec();
    }

    pub open spec fn total_size() -> nat {
        Self::tree_size_spec(3)
    }

    pub open spec fn valid_nid(nid: NodeId) -> bool {
        0 <= nid < Self::total_size()
    }

    pub open spec fn root_id() -> NodeId {
        0
    }

    pub proof fn lemma_root_id()
        ensures
            Self::valid_nid(Self::root_id()),
    {
        Self::lemma_tree_size_spec();
    }

    pub open spec fn nid_to_trace_rec(nid: NodeId, cur_level: nat, cur_rt: NodeId) -> Seq<nat>
        decreases cur_level,
    {
        if cur_level == 0 {
            Seq::empty()
        } else {
            let sz = Self::tree_size_spec(cur_level - 1);
            let offset = ((nid - cur_rt - 1) / sz as int) as nat;
            let new_rt = cur_rt + offset * sz + 1;
            if new_rt == nid {
                seq![offset]
            } else {
                seq![offset].add(Self::nid_to_trace_rec(nid, (cur_level - 1) as nat, new_rt))
            }
        }
    }

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

    pub open spec fn valid_trace(trace: Seq<nat>) -> bool {
        &&& 0 <= trace.len() < 4
        &&& forall|i| #![trigger trace[i]] 0 <= i < trace.len() ==> 0 <= trace[i] < 512
    }

    pub open spec fn trace_to_nid(trace: Seq<nat>, cur_rt: NodeId, cur_level: int) -> NodeId
        recommends
            Self::valid_trace(trace),
            Self::valid_nid(cur_rt),
            0 <= cur_level <= 3,
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

    pub proof fn lemma_trace_to_nid_inductive(trace: Seq<nat>, cur_rt: NodeId, cur_level: int)
        requires
            Self::valid_trace(trace),
            Self::valid_nid(cur_rt),
            0 <= cur_level <= 3,
        ensures
            if trace.len() > 0 {
                Self::trace_to_nid(trace, cur_rt, cur_level) == Self::trace_to_nid(
                    trace.subrange(1, trace.len() as int),
                    cur_rt + trace[0] * Self::tree_size_spec(cur_level - 1) + 1,
                    cur_level - 1,
                )
            } else {
                true
            },
    {
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
            assert(Self::trace_to_nid_upperbound_spec(max_dep)
                == Self::trace_to_nid_upperbound_spec((max_dep - 1) as nat)
                + Self::tree_size_weighted_spec(3 - max_dep));
        }
    }

    pub proof fn lemma_trace_to_nid_inner(trace: Seq<nat>)
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
            assert(new_trace.len() + 1 == trace.len());
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

    pub open spec fn trace_to_nid_increment_spec(trace: Seq<nat>, offset: nat) -> bool {
        let nid1 = Self::trace_to_nid_from_root(trace);
        let nid2 = Self::trace_to_nid_from_root(trace.push(offset));
        let level = 3 - trace.len();
        let sz = Self::tree_size_spec(level - 1);
        nid2 == nid1 + offset * sz + 1
    }

    pub proof fn lemma_trace_to_nid_increment(trace: Seq<nat>, offset: nat)
        requires
            0 <= offset < 512,
            Self::valid_trace(trace.push(offset)),
        ensures
            Self::trace_to_nid_increment_spec(trace, offset),
    {
        assert(Self::valid_trace(trace)) by {
            assert(trace.is_prefix_of(trace.push(offset)));
        };

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

    pub proof fn lemma_trace_to_nid_split(
        trace1: Seq<nat>,
        trace2: Seq<nat>,
        cur_rt: NodeId,
        cur_level: int,
    ) -> (nid: NodeId)
        requires
            Self::valid_trace(trace1.add(trace2)),
            cur_rt == Self::trace_to_nid_from_root(trace1),
            cur_level == Self::level_to_dep(trace1.len()) - 1,
        ensures
            nid == Self::trace_to_nid(trace2, cur_rt, cur_level),
            nid == Self::trace_to_nid_from_root(trace1.add(trace2)),
        decreases trace2.len(),
    {
        if trace2.len() == 0 {
            assert(trace1.add(trace2) =~= trace1);

            cur_rt
        } else {
            let new_trace1 = trace1.push(trace2[0]);
            let new_trace2 = trace2.subrange(1, trace2.len() as int);
            assert(new_trace1.add(new_trace2) =~= trace1.add(trace2));
            let new_rt = cur_rt + trace2[0] * Self::tree_size_spec(cur_level - 1) + 1;
            assert(new_rt == Self::trace_to_nid_from_root(new_trace1)) by {
                assert(trace1.is_prefix_of(trace1.add(trace2)));
                assert(trace2.is_suffix_of(trace1.add(trace2)));
                Self::lemma_trace_to_nid_increment(trace1, trace2[0]);
            };
            Self::lemma_trace_to_nid_split(new_trace1, new_trace2, new_rt, cur_level - 1)
        }
    }

    pub open spec fn trace_to_nid_from_root(trace: Seq<nat>) -> NodeId
        recommends
            Self::valid_trace(trace),
    {
        Self::trace_to_nid(trace, 0, 3)
    }

    pub proof fn lemma_nid_to_trace_rec(nid: NodeId, cur_level: nat, cur_rt: NodeId) -> (trace: Seq<
        nat,
    >)
        requires
            Self::valid_nid(nid),
            Self::valid_nid(cur_rt),
            0 <= cur_level <= 3,
            cur_rt < nid < cur_rt + Self::tree_size_spec(cur_level as int),
        ensures
            trace =~= Self::nid_to_trace_rec(nid, cur_level, cur_rt),
            trace.len() <= cur_level,
            Self::valid_trace(trace),
            nid == Self::trace_to_nid(trace, cur_rt, cur_level as int),
        decreases cur_level,
    {
        if cur_level == 0 {
            Seq::empty()
        } else {
            assert(1 <= cur_level <= 3);
            assert(Self::tree_size_spec(cur_level - 1) * 512 + 1 == Self::tree_size_spec(
                cur_level as int,
            )) by { Self::lemma_tree_size_spec() };

            let sz = Self::tree_size_spec(cur_level - 1);
            let offset = ((nid - cur_rt - 1) / sz as int) as nat;
            assert(0 <= offset < 512) by {
                assert(cur_rt < nid < cur_rt + Self::tree_size_spec(cur_level as int));
                assert(0 <= nid - cur_rt - 1 < Self::tree_size_spec(cur_level as int) - 1);
                assert(nid - cur_rt - 1 < sz * 512);
                assert(offset * sz <= nid - cur_rt - 1) by {
                    lemma_fundamental_div_mod(nid - cur_rt - 1, sz as int);
                };
                assert(offset < 512) by {
                    lemma_div_by_multiple_is_strongly_ordered(
                        offset * sz as int,
                        512 * sz as int,
                        512,
                        sz as int,
                    );
                    lemma_div_multiples_vanish(offset as int, sz as int);
                    lemma_div_multiples_vanish(512, sz as int);
                };
            };

            let new_rt = cur_rt + offset * sz + 1;
            assert(new_rt <= nid) by {
                assert(offset * sz <= nid - cur_rt - 1) by {
                    lemma_remainder_lower(nid - cur_rt - 1, sz as int);
                };
            };
            assert(nid < new_rt + sz) by {
                assert(nid - cur_rt - 1 < offset * sz + sz) by {
                    lemma_remainder(nid - cur_rt - 1, sz as int);
                };
            };

            if new_rt == nid {
                let trace = seq![offset];
                assert(Self::trace_to_nid(trace, cur_rt, cur_level as int) == nid) by {
                    Self::lemma_trace_to_nid_inductive(trace, cur_rt, cur_level as int);
                };
                trace
            } else {
                let _trace = Self::lemma_nid_to_trace_rec(nid, (cur_level - 1) as nat, new_rt);
                let trace = seq![offset].add(_trace);
                assert(Self::trace_to_nid(_trace, new_rt, cur_level - 1) == nid);
                assert(new_rt == cur_rt + offset * sz + 1);
                assert(Self::trace_to_nid(trace, cur_rt, cur_level as int) == nid) by {
                    Self::lemma_trace_to_nid_inductive(trace, cur_rt, cur_level as int);
                    assert(_trace =~= trace.subrange(1, trace.len() as int));
                };
                trace
            }
        }
    }

    pub proof fn lemma_nid_to_trace(nid: NodeId) -> (trace: Seq<nat>)
        requires
            Self::valid_nid(nid),
        ensures
            trace =~= Self::nid_to_trace(nid),
            Self::valid_trace(trace),
            Self::trace_to_nid_from_root(trace) == nid,
    {
        if nid != Self::root_id() {
            Self::lemma_nid_to_trace_rec(nid, 3, 0)
        } else {
            Seq::empty()
        }
    }

    #[verifier::spinoff_prover]
    pub proof fn lemma_trace_to_nid_rec(trace: Seq<nat>, cur_rt: NodeId, cur_level: int) -> (nid:
        NodeId)
        requires
            Self::valid_trace(trace),
            Self::valid_nid(cur_rt),
            cur_rt + Self::tree_size_spec(cur_level) <= Self::total_size(),
            0 <= cur_level <= 3,
            trace.len() <= cur_level,
        ensures
            nid == Self::trace_to_nid(trace, cur_rt, cur_level),
            cur_rt <= nid < cur_rt + Self::tree_size_spec(cur_level),
            nid == cur_rt <==> trace.len() == 0,
            trace.len() != 0 ==> trace =~= Self::nid_to_trace_rec(nid, cur_level as nat, cur_rt),
        decreases trace.len(),
    {
        if trace.len() == 0 {
            assert(Self::tree_size_spec(cur_level) > 0) by { Self::lemma_tree_size_spec() };

            cur_rt
        } else {
            let new_trace = trace.subrange(1, trace.len() as int);
            assert(new_trace.len() == trace.len() - 1);

            let new_rt = cur_rt + trace[0] * Self::tree_size_spec(cur_level - 1) + 1;
            assert({
                &&& Self::valid_nid(new_rt)
                &&& new_rt + Self::tree_size_spec(cur_level - 1) <= Self::total_size()
            }) by {
                assert(Self::tree_size_spec(cur_level - 1) * 512 + 1 == Self::tree_size_spec(
                    cur_level,
                )) by { Self::lemma_tree_size_spec() };
                assert(Self::tree_size_spec(cur_level) - 1 - trace[0] * Self::tree_size_spec(
                    cur_level - 1,
                ) == (512 - trace[0]) * Self::tree_size_spec(cur_level - 1)) by {
                    lemma_mul_is_distributive_sub_other_way(
                        Self::tree_size_spec(cur_level - 1) as int,
                        512,
                        trace[0] as int,
                    );
                };
                assert(512 - trace[0] >= 1);
                assert(new_rt + (512 - trace[0]) * Self::tree_size_spec(cur_level - 1)
                    <= Self::total_size());
                assert(Self::tree_size_spec(cur_level - 1) <= (512 - trace[0])
                    * Self::tree_size_spec(cur_level - 1)) by {
                    lemma_mul_inequality(
                        1,
                        512 - trace[0],
                        Self::tree_size_spec(cur_level - 1) as int,
                    )
                };
                assert(Self::tree_size_spec(cur_level - 1) > 0) by { Self::lemma_tree_size_spec() };
            };

            let new_level = cur_level - 1;

            let nid = Self::lemma_trace_to_nid_rec(new_trace, new_rt, new_level);
            assert(nid == Self::trace_to_nid(trace, cur_rt, cur_level));

            let sz = Self::tree_size_spec(cur_level - 1);
            assert(new_rt <= nid < new_rt + sz);
            assert(cur_rt + trace[0] * sz + 1 <= nid < cur_rt + trace[0] * sz + sz + 1);
            assert(cur_rt <= nid);
            // first, we still know from earlier that nid < new_rt + sz
            assert(nid < new_rt + sz);
            // then prove that new_rt + sz <= cur_rt + tree_size_spec(cur_level)
            assert(new_rt + sz <= cur_rt + Self::tree_size_spec(cur_level)) by {
                // tree_size_spec(cur_level) = 512*sz + 1
                assert(Self::tree_size_spec(cur_level) == Self::tree_size_spec(cur_level - 1) * 512
                    + 1) by { Self::lemma_tree_size_spec() };

                // need: trace[0]*sz + sz <= 512*sz
                assert(trace[0] < 512);
                assert(trace[0] * sz + sz <= 512 * sz) by {
                    lemma_mul_is_distributive_add_other_way(sz as int, trace[0] as int, 1);
                    lemma_mul_inequality((trace[0] + 1) as int, 512, sz as int);
                };
            };

            // now re‑combine for the final bound
            assert(nid < cur_rt + Self::tree_size_spec(cur_level));

            let offset = ((nid - cur_rt - 1) / sz as int) as nat;
            assert(trace[0] == offset) by {
                assert(trace[0] * sz <= (nid - cur_rt - 1) < (trace[0] + 1) * sz) by {
                    lemma_mul_is_distributive_add_other_way(sz as int, trace[0] as int, 1);
                };
                assert(trace[0] <= offset < trace[0] + 1) by {
                    lemma_div_is_ordered(
                        (trace[0] * sz) as int,
                        (nid - cur_rt - 1) as int,
                        sz as int,
                    );
                    lemma_div_by_multiple_is_strongly_ordered(
                        (nid - cur_rt - 1) as int,
                        ((trace[0] + 1) * sz) as int,
                        (trace[0] + 1) as int,
                        sz as int,
                    );
                    lemma_div_by_multiple(trace[0] as int, sz as int);
                    lemma_div_by_multiple((trace[0] + 1) as int, sz as int);
                };
            }
            assert(trace =~= seq![offset].add(new_trace));

            let _trace = Self::nid_to_trace_rec(nid, cur_level as nat, cur_rt);
            assert(_trace =~= seq![offset].add(new_trace));

            nid
        }
    }

    pub proof fn lemma_trace_to_nid_from_root(trace: Seq<nat>) -> (nid: NodeId)
        requires
            Self::valid_trace(trace),
        ensures
            nid == Self::trace_to_nid_from_root(trace),
            Self::valid_nid(nid),
            trace =~= Self::nid_to_trace(nid),
    {
        Self::lemma_tree_size_spec();
        Self::lemma_trace_to_nid_rec(trace, 0, 3)
    }

    pub open spec fn nid_to_dep(nid: NodeId) -> nat
        recommends
            Self::valid_nid(nid),
    {
        Self::nid_to_trace(nid).len()
    }

    pub proof fn lemma_valid_level_to_node(nid: NodeId, level: nat)
        requires
            Self::valid_nid(nid),
            level == Self::dep_to_level(Self::nid_to_dep(nid)),
        ensures
            nid + Self::tree_size_spec(level - 1) <= Self::total_size(),
    {
        let trace = Self::lemma_nid_to_trace(nid);
        assert(nid == Self::trace_to_nid_from_root(trace)) by {
            Self::lemma_nid_to_trace(nid);
        };
        assert(nid <= Self::trace_to_nid_upperbound_spec(trace.len())) by {
            Self::lemma_trace_to_nid_inner(trace);
        };
        assert(Self::trace_to_nid_upperbound_spec(trace.len()) == Self::tree_size_spec(3)
            - Self::tree_size_spec(3 - trace.len())) by {
            Self::lemma_trace_to_nid_upperbound_spec(trace.len())
        };
    }

    pub open spec fn sub_tree_size(nid: NodeId) -> nat
        recommends
            Self::valid_nid(nid),
    {
        let dep = Self::nid_to_dep(nid);
        let level = Self::dep_to_level(dep);
        Self::tree_size_spec(level - 1)
    }

    pub proof fn lemma_sub_tree_size_lowerbound(nid: NodeId)
        requires
            Self::valid_nid(nid),
        ensures
            Self::sub_tree_size(nid) >= 1,
    {
        Self::lemma_tree_size_spec();
        Self::lemma_nid_to_trace(nid);
    }

    pub proof fn lemma_sub_tree_size_bounded(nid: NodeId)
        requires
            Self::valid_nid(nid),
        ensures
            nid + Self::sub_tree_size(nid) <= Self::total_size(),
    {
        let level = Self::dep_to_level(Self::nid_to_dep(nid));
        Self::lemma_valid_level_to_node(nid, level);
    }

    pub open spec fn next_outside_subtree(nid: NodeId) -> NodeId
        recommends
            Self::valid_nid(nid),
    {
        nid + Self::sub_tree_size(nid)
    }

    pub proof fn lemma_next_outside_subtree_bounded(nid: NodeId) -> (nxt: NodeId)
        requires
            Self::valid_nid(nid),
        ensures
            nxt == Self::next_outside_subtree(nid),
            nxt <= Self::total_size(),
    {
        Self::lemma_sub_tree_size_bounded(nid);
        nid + Self::sub_tree_size(nid)
    }

    pub open spec fn in_subtree(rt: NodeId, nd: NodeId) -> bool
        recommends
            Self::valid_nid(rt),
            Self::valid_nid(nd),
    {
        let sz = Self::sub_tree_size(rt);
        rt <= nd < rt + sz
    }

    pub proof fn lemma_in_subtree_0(nid: NodeId)
        requires
            Self::valid_nid(nid),
        ensures
            Self::in_subtree(nid, nid),
    {
        Self::lemma_sub_tree_size_lowerbound(nid);
    }

    pub proof fn lemma_in_subtree(rt: NodeId, nd: NodeId)
        requires
            Self::valid_nid(rt),
            Self::valid_nid(nd),
            Self::in_subtree(rt, nd),
        ensures
            rt <= nd < Self::next_outside_subtree(rt),
    {
    }

    pub proof fn lemma_in_subtree_bounded_is_child(pa: NodeId, ch: NodeId)
        requires
            Self::valid_nid(pa),
            Self::valid_nid(ch),
            Self::is_child(pa, ch),
        ensures
            Self::next_outside_subtree(ch) <= Self::next_outside_subtree(pa),
    {
        admit()
    }

    pub proof fn lemma_in_subtree_bounded(rt: NodeId, nd: NodeId)
        requires
            Self::valid_nid(rt),
            Self::valid_nid(nd),
            Self::in_subtree(rt, nd),
        ensures
            Self::next_outside_subtree(nd) <= Self::next_outside_subtree(rt),
        decreases Self::nid_to_dep(nd) - Self::nid_to_dep(rt),
    {
        // if rt != nd {
        //     let pa = Self::get_parent(nd);
        //     assert(Self::nid_to_dep(pa) + 1 == Self::nid_to_dep(nd));
        //     Self::lemma_in_subtree_bounded(rt, pa);
        //     Self::lemma_in_subtree_bounded_is_child(pa, nd);
        // }
        admit();
    }

    pub open spec fn is_child(pa: NodeId, ch: NodeId) -> bool
        recommends
            Self::valid_nid(pa),
            Self::valid_nid(ch),
    {
        &&& Self::in_subtree(pa, ch)
        &&& Self::nid_to_dep(pa) + 1 == Self::nid_to_dep(ch)
    }

    pub open spec fn get_parent(nid: NodeId) -> NodeId
        recommends
            Self::valid_nid(nid),
            nid != Self::root_id(),
    {
        if nid == Self::root_id() {
            arbitrary()
        } else {
            let trace = Self::nid_to_trace(nid);
            Self::trace_to_nid_from_root(trace.drop_last())
        }
    }

    pub proof fn lemma_parent_child(nid: NodeId)
        requires
            Self::valid_nid(nid),
            nid != Self::root_id(),
        ensures
            Self::is_child(Self::get_parent(nid), nid),
    {
        let trace = Self::nid_to_trace(nid);
        assert(Self::valid_trace(trace)) by {
            Self::lemma_nid_to_trace(nid);
        };
        let pa = Self::get_parent(nid);
        assert(pa == Self::trace_to_nid_from_root(trace.drop_last()));
        let pa_trace = Self::nid_to_trace(pa);
        assert(pa_trace =~= trace.drop_last()) by {
            Self::lemma_trace_to_nid_from_root(trace.drop_last());
        };
        assert(pa_trace.len() + 1 == trace.len());
        assert(Self::nid_to_dep(pa) + 1 == Self::nid_to_dep(nid));

        let pa_level = Self::dep_to_level(pa_trace.len());
        let _nid = Self::lemma_trace_to_nid_split(pa_trace, seq![trace.last()], pa, pa_level - 1);
        assert(_nid == nid) by {
            assert(pa_trace.add(seq![trace.last()]) =~= trace);
            assert(_nid == Self::trace_to_nid_from_root(trace));
            Self::lemma_nid_to_trace(nid);
        };
        assert(Self::valid_nid(pa)) by {
            Self::lemma_trace_to_nid_from_root(trace.drop_last());
        };
        assert(pa + Self::tree_size_spec(pa_level - 1) <= Self::total_size()) by {
            Self::lemma_valid_level_to_node(pa, pa_level)
        };
        Self::lemma_trace_to_nid_rec(seq![trace.last()], pa, pa_level - 1);
    }

    pub open spec fn get_offset(nid: NodeId) -> nat
        recommends
            Self::valid_nid(nid),
            nid != Self::root_id(),
    {
        if nid == Self::root_id() {
            arbitrary()
        } else {
            let trace = Self::nid_to_trace(nid);
            trace.last()
        }
    }

    pub proof fn lemma_get_offset(nid: NodeId) -> (offset: nat)
        requires
            Self::valid_nid(nid),
            nid != Self::root_id(),
        ensures
            offset == Self::get_offset(nid),
            valid_pte_offset(offset),
    {
        let trace = Self::lemma_nid_to_trace(nid);
        trace.last()
    }

    pub open spec fn get_child(nid: NodeId, offset: nat) -> NodeId
        recommends
            Self::valid_nid(nid),
            Self::nid_to_dep(nid) < 3,
            valid_pte_offset(offset),
    {
        let level = Self::dep_to_level(Self::nid_to_dep(nid));
        let sz = Self::tree_size_spec(level - 2);
        nid + offset * sz + 1
    }

    pub proof fn lemma_get_child(nid: NodeId, offset: nat)
        requires
            Self::valid_nid(nid),
            Self::nid_to_dep(nid) < 3,
            valid_pte_offset(offset),
        ensures
            Self::valid_nid(Self::get_child(nid, offset)),
            nid == Self::get_parent(Self::get_child(nid, offset)),
            offset == Self::get_offset(Self::get_child(nid, offset)),
    {
        admit();
    }

    pub open spec fn is_not_leaf(nid: NodeId) -> bool
        recommends
            Self::valid_nid(nid),
    {
        Self::nid_to_dep(nid) < 3
    }
}

} // verus!
