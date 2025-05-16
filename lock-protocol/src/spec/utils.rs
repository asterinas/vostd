use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::arithmetic::power::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd_extra::prelude::*;

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
            assert(Self::tree_size_spec(cur_level - 1) * 512 + 1 == Self::tree_size_spec(
                cur_level as int,
            )) by { Self::lemma_tree_size_spec() };

            let sz = Self::tree_size_spec(cur_level - 1);
            // Prove offset < 512
            let offset = ((nid - cur_rt - 1) / sz as int) as nat;
            // now offset < 512 follows
            assert(offset < 512) by {
                // offset*sz <= nid - cur_rt - 1 < sz*512
                assert(nid - cur_rt - 1 < sz * 512);
                // Now use the actual quotient form:
                lemma_multiply_divide_lt(nid - cur_rt - 1, sz as int, 512);
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
        let dep_pa = Self::nid_to_dep(pa);
        let dep_ch = Self::nid_to_dep(ch);
        assert(dep_ch == dep_pa + 1);  // from is_child

        let sz_pa = Self::sub_tree_size(pa);
        let sz_ch = Self::sub_tree_size(ch);
        Self::lemma_tree_size_spec();  // Assuming it works for both pa and ch

        let level_pa = 4 - dep_pa;
        let level_ch = 4 - dep_ch;

        assert(level_ch == level_pa - 1);

        // Verify tree size assumptions and properties
        let tr_ch = Self::lemma_nid_to_trace(ch);
        assert(tr_ch =~= Self::nid_to_trace(ch));  // from lemma
        assert(Self::valid_trace(tr_ch));  // from lemma
        assert(tr_ch.len() <= 3);  // by valid_trace(trace)
        assert(dep_ch == tr_ch.len());  // from nid_to_dep
        assert(dep_ch < 4);  // to satisfy dep_to_level
        assert(dep_pa + 1 == dep_ch);  // from is_child
        assert(dep_pa <= 2);  // dep_ch < 4 ⇒ dep_pa ≤ 2

        // Bound for tree size based on level
        assert(1 <= level_ch <= 3);
        assert(2 <= level_pa <= 4);

        assert(sz_ch < sz_pa) by {
            let size_pa = Self::tree_size_spec(level_pa - 1);
            let size_ch = Self::tree_size_spec(level_ch - 1);

            // Simplify case splitting on level_ch-1 ∈ {0,1,2}
            // Now case‐split on level_ch-1 ∈ {0,1,2}
            if level_ch - 1 == 0 {
                // size_ch == 1, size_pa ≥ 513
                assert(size_ch == 1);
                assert(size_pa >= 513);
                assert(1 < 513);
            } else if level_ch - 1 == 1 {
                // size_ch == 513, size_pa ≥ 262_657
                assert(size_ch == 513) by {
                    Self::lemma_tree_size_spec();
                }
                assert(size_pa >= 262_657) by {
                    Self::lemma_tree_size_spec();
                }
                assert(513 < 262_657);
            } else {
                // level_ch - 1 == 2
                // size_ch == 262_657, size_pa ≥ 134_480_385
                assert(size_ch == 262_657) by {
                    Self::lemma_tree_size_spec();
                }
                assert(size_pa >= 134_480_385) by {
                    Self::lemma_tree_size_spec();
                }
                assert(262_657 < 134_480_385);
            }
        };

        // Bound the positions of pa and ch in the tree
        assert(pa <= ch);  // because is_child ⇒ in_subtree ⇒ ch ∈ [pa, pa + sz_pa)
        assert(ch < pa + sz_pa);

        // Verify ch fits within the subtree of pa
        assert((ch as int) + (sz_ch as int) <= (pa as int) + (sz_pa as int)) by {
            // Since is_child(pa, ch) implies in_subtree(pa, ch)
            // we know that ch >= pa and ch < pa + sz_pa
            // We have already proved that sz_ch < sz_pa
            assert(sz_ch < sz_pa);

            // Break down into two cases:
            // 1. If ch == pa, then ch + sz_ch == pa + sz_ch < pa + sz_pa, because sz_ch < sz_pa
            // 2. If ch > pa, we need more detailed analysis
            if ch == pa {
                assert(ch + sz_ch == pa + sz_ch);
                assert(pa + sz_ch < pa + sz_pa);
                // By transitivity, ch + sz_ch < pa + sz_pa
                assert(ch + sz_ch < pa + sz_pa);
            } else {
                // If ch > pa, we can calculate the exact value of ch
                // According to the definition of is_child, ch must be a direct child node of pa
                // From the structure of ch we can calculate: ch = pa + offset * sz_ch + 1, where offset < 512
                // From tr_ch and is_child we know that the depth of ch is the depth of pa plus 1
                assert(dep_ch == dep_pa + 1);

                // Get the offset of ch relative to pa
                let trace_pa = Self::lemma_nid_to_trace(pa);
                let trace_ch = Self::lemma_nid_to_trace(ch);

                // Assert that trace_ch is trace_pa plus one element
                assert(trace_ch.len() == trace_pa.len() + 1) by {
                    assert(dep_ch == trace_ch.len());
                    assert(dep_pa == trace_pa.len());
                    assert(dep_ch == dep_pa + 1);
                };

                // We can use lemma_trace_to_nid_increment to prove the relationship
                // but first we need to prove the related path relationship
                assert(Self::valid_trace(trace_pa));
                let offset = trace_ch.last();  // The offset is the last element of ch's path

                // ch_level - 1 == pa_level - 2
                let ch_sz_level = level_ch - 1;
                let pa_sz_level = level_pa - 1;
                assert(ch_sz_level == pa_sz_level - 1);

                // According to the definition of tree_size_spec, sz_ch is much smaller than sz_pa
                // Even adding the difference between ch and pa, the sum is still less than pa + sz_pa

                // In the maximum case, ch = pa + offset * sz + 1, where offset < 512
                // And sz_pa = sz_(level-1) >> sz_(level-2) * 512
                // So ch + sz_ch < pa + sz_pa always holds

                // Prove using the specific hierarchical structure of the tree:
                assert(level_ch == level_pa - 1);

                // Calculate the offset based on the properties of nid_to_trace
                let pa_level = Self::dep_to_level(dep_pa);

                // Ensure pa_level - 2 satisfies the constraints of tree_size_spec (0 <= max_dep < 4)
                assert(0 <= pa_level - 2 && pa_level - 2 < 4) by {
                    // From pa_dep <= 2, we get pa_level = 4 - pa_dep >= 2
                    // Therefore pa_level - 2 >= 0
                    assert(2 <= pa_level && pa_level <= 4);
                };

                let sz = Self::tree_size_spec(pa_level - 2);

                // Prove the position of ch using lemma_trace_to_nid_increment
                assert(Self::valid_trace(trace_pa.push(offset))) by {
                    // trace_pa is valid, and adding an offset less than 512 keeps it valid
                    assert(Self::valid_trace(trace_pa));
                    assert(offset < 512);
                };

                // Use trace_to_nid_increment_spec to prove how ch is calculated
                assert(Self::trace_to_nid_increment_spec(trace_pa, offset)) by {
                    Self::lemma_trace_to_nid_increment(trace_pa, offset);
                };

                // Directly prove the positional relationship of ch
                // First, by definition, is_child means ch is a child node of pa
                // According to the design of NodeHelper, a child node has the form pa + offset * tree_size_spec(level - 2) + 1

                // Get the corresponding size
                let trace_pa_len = trace_pa.len();
                let pa_dep_level = 3 - trace_pa_len;  // level used in trace_to_nid
                let child_sz_level = pa_dep_level - 1;  // size level used by child nodes

                // Ensure the level is within valid range
                assert(0 <= child_sz_level && child_sz_level < 3) by {
                    assert(trace_pa_len <= 2);  // From dep_pa <= 2 and trace_pa_len == dep_pa
                    assert(pa_dep_level >= 1);
                    assert(child_sz_level >= 0);
                };

                // Get the subtree size
                let sz_child_calc = Self::tree_size_spec(child_sz_level);

                // Verify the calculation method of ch according to trace definition
                // Based on the guarantee of lemma_trace_to_nid_increment
                assert(Self::trace_to_nid_from_root(trace_pa.push(offset))
                    == Self::trace_to_nid_from_root(trace_pa) + offset * sz_child_calc + 1);

                // Use the result of trace_to_nid_increment directly to prove the relationship
                // First verify that we can apply this lemma
                assert(Self::valid_trace(trace_pa));
                assert(offset < 512);
                assert(Self::valid_trace(trace_pa.push(offset))) by {
                    assert(trace_pa.is_prefix_of(trace_pa.push(offset)));
                    assert(offset < 512);
                };

                // Apply trace_to_nid_increment
                Self::lemma_trace_to_nid_increment(trace_pa, offset);

                // trace_to_nid_increment_spec gives us:
                let nid_pa = Self::trace_to_nid_from_root(trace_pa);
                let nid_ch_expected = Self::trace_to_nid_from_root(trace_pa.push(offset));
                let trace_level = 3 - trace_pa.len();
                let sz_trace = Self::tree_size_spec(trace_level - 1);

                // Ensure trace_level is consistent with our calculation
                assert(trace_level == pa_dep_level) by {
                    assert(trace_pa.len() == dep_pa);
                    assert(trace_level == 3 - dep_pa);
                    assert(pa_dep_level == 3 - trace_pa_len);
                    assert(trace_pa_len == dep_pa);
                };

                // Ensure sz_trace is consistent with our calculation
                assert(sz_trace == sz_child_calc) by {
                    assert(trace_level - 1 == pa_dep_level - 1);
                    assert(pa_dep_level - 1 == child_sz_level);
                };

                // According to lemma_trace_to_nid_increment and trace relationships, we have:
                assert(nid_ch_expected == nid_pa + offset * sz_trace + 1);

                // Now prove that ch and pa equal nid_ch_expected and nid_pa respectively
                assert(pa == nid_pa) by {
                    // Guaranteed by lemma_nid_to_trace
                    Self::lemma_nid_to_trace(pa);
                };

                // The trace of ch is determined by its parent node's trace plus an offset
                assert(Self::valid_nid(ch));
                assert(Self::valid_nid(pa));
                assert(ch != Self::root_id()) by {
                    // A child node cannot be the root node, because it has depth > 0
                    assert(dep_ch > 0);
                    assert(Self::root_id() == 0);
                    assert(ch > 0);
                };
                // We know ch and pa are both valid node IDs
                assert(Self::valid_nid(ch));
                assert(Self::valid_nid(pa));

                // From trace_ch.last() we can get the offset from pa to ch
                assert(trace_ch.len() == trace_pa.len() + 1);

                // Now derive the calculation formula of ch directly from first principles
                // We start from the definition of trace_to_nid_from_root

                // First, we know the relationship between trace_ch and trace_pa
                // trace_ch = trace_pa.push(offset)

                // Then, we know that ch and pa equal respectively
                // ch = trace_to_nid_from_root(trace_ch)
                // pa = trace_to_nid_from_root(trace_pa)

                // Combining these two points, we can use the trace_to_nid_increment lemma
                // It tells us: for any trace and offset,
                // trace_to_nid_from_root(trace.push(offset)) = trace_to_nid_from_root(trace) + offset * tree_size_spec(level - 1) + 1
                // where level = 3 - trace.len()

                // For our example, trace = trace_pa, so
                // ch = pa + offset * tree_size_spec((3 - trace_pa.len()) - 1) + 1

                // We already know that pa_level = 4 - dep_pa, and trace_pa.len() = dep_pa
                // So 3 - trace_pa.len() = 3 - dep_pa = 4 - dep_pa - 1 = pa_level - 1

                // Therefore ch = pa + offset * tree_size_spec(pa_level - 2) + 1

                // Finally, we get ch = pa + offset * sz + 1, where sz = tree_size_spec(pa_level - 2)
                assert(ch == pa + offset * sz + 1) by {
                    // Use the trace_to_nid_increment lemma
                    Self::lemma_trace_to_nid_increment(trace_pa, offset);

                    // Extract the variables needed for calculation
                    let trace_level = 3 - trace_pa.len();
                    let sz_from_trace = Self::tree_size_spec(trace_level - 1);

                    // Prove the equivalence of variables
                    assert(trace_pa.len() == dep_pa);
                    assert(trace_level == 3 - dep_pa);
                    assert(pa_level == 4 - dep_pa);
                    assert(trace_level == pa_level - 1);
                    assert(pa_level - 2 == trace_level - 1);
                    assert(sz == sz_from_trace);

                    // According to the definition of trace_to_nid_increment_spec
                    let nid1 = Self::trace_to_nid_from_root(trace_pa);
                    let nid2 = Self::trace_to_nid_from_root(trace_pa.push(offset));

                    // Prove that pa == nid1 and ch == nid2
                    assert(pa == Self::trace_to_nid_from_root(trace_pa)) by {
                        Self::lemma_trace_to_nid_from_root(trace_pa);
                    };

                    let trace_pa_push_offset = trace_pa.push(offset);
                    // Instead of directly asserting the complex sequence equality,
                    // we'll prove it step by step using intermediate relations and lemmas

                    // First, verify pa is the parent of ch by definition of is_child
                    assert(Self::is_child(pa, ch));

                    // This means the parent is derivable via trace operations
                    assert(pa == Self::get_parent(ch)) by {
                        // is_child implies parent-child relationship
                        Self::is_child(pa, ch);
                        // FIXME: need to prove this without admit
                        admit();
                    }

                    // By definition, get_parent uses trace.drop_last()
                    assert(Self::get_parent(ch) == Self::trace_to_nid_from_root(
                        Self::nid_to_trace(ch).drop_last(),
                    ));

                    // We can show that trace_ch is exactly ch's trace
                    assert(trace_ch =~= Self::nid_to_trace(ch)) by {
                        // This comes from our prior lemma_nid_to_trace call
                        Self::lemma_nid_to_trace(ch);
                    }

                    // We know the depths have to be related for parent-child
                    assert(dep_ch == trace_ch.len());
                    assert(dep_pa == trace_pa.len());
                    assert(dep_ch == dep_pa + 1);

                    // From nid_to_dep we know the trace length is exactly the depth
                    assert(Self::nid_to_dep(ch) == dep_ch);
                    assert(Self::nid_to_dep(pa) == dep_pa);

                    // Direct proof that trace_ch's prefix must be trace_pa
                    assert(trace_ch.drop_last() =~= trace_pa) by {
                        // From the parent relationship
                        assert(pa == Self::trace_to_nid_from_root(trace_ch.drop_last()));

                        // Unique trace representation means these traces are equal
                        assert(trace_pa =~= Self::nid_to_trace(pa));
                        assert(Self::trace_to_nid_from_root(trace_pa) == pa);
                        assert(Self::trace_to_nid_from_root(trace_ch.drop_last()) == pa);

                        // Using uniqueness of trace to nid mapping
                        Self::lemma_trace_to_nid_from_root(trace_ch.drop_last());
                    }

                    // Now we prove that the last element of trace_ch is offset
                    assert(trace_ch.last() == offset) by {
                        // Using the parent-child relation and nid calculation
                        assert(ch == Self::trace_to_nid_from_root(trace_ch));
                        assert(pa == Self::trace_to_nid_from_root(trace_pa));

                        // The trace_to_nid_increment lemma tells us exactly how ch relates to pa
                        Self::lemma_trace_to_nid_increment(trace_pa, offset);

                        // Apply the increment specification to connect the relationship
                        assert(Self::trace_to_nid_increment_spec(trace_pa, offset)) by {
                            Self::lemma_trace_to_nid_increment(trace_pa, offset);
                        };

                        // Using the spec, we know the exact relationship:
                        let level = 3 - trace_pa.len();
                        let sz_incr = Self::tree_size_spec(level - 1);

                        // Extract the direct relationship from the spec
                        assert(Self::trace_to_nid_from_root(trace_pa.push(offset))
                            == Self::trace_to_nid_from_root(trace_pa) + offset * sz_incr + 1);

                        // And we already proved pa is the result of trace_pa
                        assert(pa == Self::trace_to_nid_from_root(trace_pa));

                        // Now we can derive the relationship between ch and trace_ch
                        assert(trace_ch =~= trace_pa.push(offset)) by {
                            // Proven earlier: trace_ch.drop_last() =~= trace_pa
                            assert(trace_ch.drop_last() =~= trace_pa);
                            assert(trace_ch.last() == offset);
                            assert(trace_pa.push(offset).drop_last() =~= trace_pa);
                            assert(trace_pa.push(offset).last() == offset);
                        };

                        // Since trace_ch =~= trace_pa.push(offset), we know
                        assert(Self::trace_to_nid_from_root(trace_ch)
                            == Self::trace_to_nid_from_root(trace_pa.push(offset)));

                        // From lemma_nid_to_trace for ch, we know
                        assert(ch == Self::trace_to_nid_from_root(trace_ch));

                        // By transitivity, we can connect all pieces
                        assert(ch == Self::trace_to_nid_from_root(trace_pa.push(offset)));
                        assert(ch == Self::trace_to_nid_from_root(trace_pa) + offset * sz_incr + 1);

                        // And since pa = trace_to_nid_from_root(trace_pa)
                        assert(ch == pa + offset * sz_incr + 1);

                        // Now we can assert the relationship with sz (will prove sz_incr == sz next)
                        assert(sz_incr == sz) by {
                            // Both calculate the tree size at the same level
                            // Define level relationships explicitly
                            assert(level == 3 - trace_pa.len());
                            assert(trace_pa.len() == dep_pa);

                            // Calculate level and sz_incr level
                            assert(level == 3 - dep_pa);
                            let sz_incr_level = level - 1;
                            assert(sz_incr_level == 3 - dep_pa - 1);
                            assert(sz_incr_level == 2 - dep_pa);

                            // Define pa_level relationships
                            assert(pa_level == 4 - dep_pa);
                            let sz_level = pa_level - 2;
                            assert(sz_level == 4 - dep_pa - 2);
                            assert(sz_level == 2 - dep_pa);

                            // Therefore they calculate size at the same level
                            assert(sz_incr_level == sz_level);

                            // And by the definition of tree_size_spec, equal levels produce equal results
                            assert(sz_incr == Self::tree_size_spec(sz_incr_level));
                            assert(sz == Self::tree_size_spec(sz_level));
                        };

                        // Finally, we can assert what we want
                        assert(ch == pa + offset * sz + 1);

                        // Show that sz_incr is the same as sz
                        assert(sz_incr == sz) by {
                            // Both calculate the tree size at the same level
                            assert(level - 1 == pa_level - 2) by {
                                assert(level == 3 - trace_pa.len());
                                assert(trace_pa.len() == dep_pa);
                                assert(pa_level == 4 - dep_pa);
                                assert(level == 3 - dep_pa);
                                assert(pa_level == 4 - dep_pa);
                                assert(level == pa_level - 1);
                                assert(level - 1 == pa_level - 2);
                            };
                        };

                        // Now establish the equality through transitive relations
                        assert(Self::trace_to_nid_from_root(trace_pa.push(offset)) == pa + offset
                            * sz + 1);
                        assert(Self::trace_to_nid_from_root(trace_pa.push(offset)) == ch);

                        // Therefore the offset must be the last element of trace_ch
                        // because it's the only way to satisfy the increment relation
                    }

                    // With these two facts, we can construct the full proof:
                    // 1. trace_ch.drop_last() =~= trace_pa
                    // 2. trace_ch.last() == offset
                    // Therefore: trace_ch =~= trace_pa.push(offset)

                    // Also ensure we have the right length
                    assert(trace_ch.len() == trace_pa.len() + 1);

                    // Final step using sequence properties
                    assert(trace_ch =~= trace_pa_push_offset) by {
                        // If two sequences have the same length, same initial elements,
                        // and same last element, they must be equivalent
                        assert(trace_pa_push_offset.len() == trace_pa.len() + 1);
                        assert(trace_pa_push_offset.drop_last() =~= trace_pa);
                        assert(trace_pa_push_offset.last() == offset);
                    }
                    assert(ch == Self::trace_to_nid_from_root(trace_ch)) by {
                        Self::lemma_trace_to_nid_from_root(trace_ch);
                    };

                    // Apply trace_to_nid_increment_spec
                    assert(Self::trace_to_nid_increment_spec(trace_pa, offset)) by {
                        Self::lemma_trace_to_nid_increment(trace_pa, offset);
                    };

                    // Draw conclusions
                    assert(nid2 == nid1 + offset * sz_from_trace + 1);
                    assert(ch == pa + offset * sz + 1);
                };

                // Equivalence proof completed
                assert(ch == pa + offset * sz + 1) by {
                    assert(sz == sz_child_calc);
                };

                // Now prove the relationship between ch and pa
                assert(ch == Self::trace_to_nid_from_root(trace_ch)) by {
                    // Guaranteed by lemma_nid_to_trace
                    Self::lemma_nid_to_trace(ch);
                };

                assert(pa == Self::trace_to_nid_from_root(trace_pa)) by {
                    // Guaranteed by lemma_nid_to_trace
                    Self::lemma_nid_to_trace(pa);
                };

                // Directly verify that ch == pa + offset * sz + 1
                assert(ch == pa + offset * sz + 1) by {
                    // Combining the assertions above
                    assert(sz_child_calc == sz) by {
                        // Both are calculated based on the same level
                        assert(pa_level - 2 == child_sz_level) by {
                            assert(pa_level == 4 - dep_pa);
                            assert(pa_dep_level == 3 - trace_pa_len);
                            assert(trace_pa_len == dep_pa);
                            assert(pa_level - 1 == pa_dep_level);
                        };
                    };
                };

                // We have proven that ch == pa + offset * sz + 1
                // Also, we have proven that sz_ch < sz_pa
                // So ch + sz_ch <= pa + offset * sz + 1 + sz_ch

                // In the maximum case, offset is close to 512, and sz_pa is at least 512 * sz_ch + 1
                // So ch + sz_ch < pa + sz_pa always holds

                // sz_ch <= sz, because sz is the subtree size of the child node
                assert(sz_ch <= sz) by {
                    // sz_ch is the subtree size of the child node, while sz is the tree size used to calculate child nodes
                    assert(sz_ch == Self::tree_size_spec(level_ch - 1));
                    assert(sz == Self::tree_size_spec(pa_level - 2));
                    assert(level_ch - 1 == pa_level - 2);
                };

                // Finally prove that ch + sz_ch <= pa + sz_pa
                assert(ch + sz_ch <= pa + sz_pa) by {
                    assert(ch == pa + offset * sz + 1);
                    assert(ch + sz_ch == pa + offset * sz + 1 + sz_ch);
                    assert(sz_ch <= sz);
                    // In the maximum case: offset=511, then we have:
                    // ch + sz_ch = pa + 511*sz + 1 + sz_ch <= pa + 511*sz + 1 + sz
                    //            = pa + 512*sz + 1 <= pa + sz_pa
                };

                // And sz_pa = Self::tree_size_spec(pa_level - 1)
                // According to the relationship of tree_size_spec:
                // tree_size_spec(level-1) = size_at_dep(level-1) + tree_size_spec(level-2)
                // = 512^(level-1) + tree_size_spec(level-2)
                // >= 512 * tree_size_spec(level-2)

                // So sz_pa >> 512 * sz, and ch + sz_ch <= pa + offset * sz + 1 + sz_ch
                // Since sz_ch <= sz, we always have ch + sz_ch < pa + sz_pa

                // Finally apply transitivity
                assert(ch + sz_ch <= pa + sz_pa);
            }
        };

        // Explicitly assert the postcondition to ensure verification succeeds
        assert(Self::next_outside_subtree(ch) <= Self::next_outside_subtree(pa)) by {
            assert(Self::next_outside_subtree(ch) == ch + sz_ch);
            assert(Self::next_outside_subtree(pa) == pa + sz_pa);
        };
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
        // ==== 0. Prep the dep/level/size and discharge all `recommends` ====
        let dep = Self::nid_to_dep(nid);
        assert(0 <= dep && dep < 4) by {
            // from nid_to_dep(nid) < 3
        };
        let level = Self::dep_to_level(dep);
        assert(1 <= level && level <= 4) by {
            // lemma_dep_to_level: level = 4 - dep, and 0 ≤ dep < 4
            Self::lemma_dep_to_level(dep);
        };
        let sz_dep = (level as int) - 2;
        assert(0 <= sz_dep && sz_dep < 4) by {
            // level ∈ {2,3,4} ⇒ level–2 ∈ {0,1,2} ⊂ [0,4)
        };
        let sz: nat = Self::tree_size_spec(sz_dep);

        // ==== 1. Show the child is within [0, total_size()) ====

        let child = Self::get_child(nid, offset);
        // From lemma_valid_level_to_node(nid, level):
        Self::lemma_valid_level_to_node(nid, level);
        //   ⇒ nid + tree_size_spec(level-1) ≤ total_size
        // We need:
        //   nid + offset*sz + 1 ≤ nid + tree_size_spec(level-1)
        //
        // First:  offset*sz + 1 ≤ (offset+1)*sz
        assert(sz >= 1) by {
            Self::lemma_tree_size_spec();
        };
        assert(offset * (sz as int) + 1 <= (offset + 1) * (sz as int)) by {
            assert(((offset as int) + 1) * (sz as int) == (offset as int) * (sz as int) + (
            sz as int)) by {
                lemma_mul_is_distributive_add(sz as int, offset as int, 1);
            };
            assert(offset * sz + 1 <= offset * sz + sz);
        };
        // Next: (offset+1)*sz ≤ 512*sz
        assert((offset + 1) * (sz as int) <= 512 * (sz as int)) by {
            lemma_mul_inequality(offset as int + 1, 512, sz as int);
        };
        // Finally:     512*sz < tree_size_spec(level-1)
        assert(512 * (sz as int) < (Self::tree_size_spec((level as int) - 1) as int)) by {
            // tree_size_spec(level) = 512 * tree_size_spec(level-1) + 1
            Self::lemma_tree_size_spec();
        };
        // Chain them
        assert(nid + offset * (sz as int) + 1 <= nid + Self::tree_size_spec((level as int) - 1))
            by {}
        assert(nid + offset * (sz as int) + 1 < Self::total_size()) by {}

        // ==== 2. Show `child` agrees with `trace_to_nid_from_root(trace.push(offset))` ====

        // Extract the root‐based trace for `nid`
        let trace = Self::lemma_nid_to_trace(nid);
        // By lemma_trace_to_nid_increment:
        Self::lemma_trace_to_nid_increment(trace, offset);
        assert(Self::trace_to_nid_from_root(trace.push(offset)) == child) by {}

        // ==== 3. Round‐trip through get_parent and get_offset ====

        // get_parent(child) unfolds to trace_to_nid_from_root((trace.push(offset)).drop_last())
        assert(child != Self::root_id()) by {
            // child ≥ nid+1 > 0
        };
        assert(Self::valid_nid(child));
        assert((trace.push(offset)).drop_last() =~= trace) by {}
        assert(Self::valid_trace((trace.push(offset)).drop_last()));
        assert(Self::valid_trace(trace));
        assert(Self::nid_to_trace(child) == trace.push(offset)) by {
            Self::lemma_trace_to_nid_from_root(trace.push(offset));
        };
        assert(Self::get_parent(child) == Self::trace_to_nid_from_root(trace));
        // But trace_to_nid_from_root(trace) = nid
        Self::lemma_trace_to_nid_from_root(trace);
        assert(Self::get_parent(child) == nid) by {}

        // Finally, get_offset(child) = trace.last() = offset
        assert(Self::get_offset(child) == offset);
    }

    pub open spec fn is_not_leaf(nid: NodeId) -> bool
        recommends
            Self::valid_nid(nid),
    {
        Self::nid_to_dep(nid) < 3
    }

    pub proof fn lemma_valid_nid_set_finite(nid: NodeId)
        ensures
            Set::new(|nid| Self::valid_nid(nid)).finite(),
            Set::new(|nid| Self::valid_nid(nid)).len() == Self::total_size(),
    {
        assert(Set::new(|nid| Self::valid_nid(nid)) =~= Set::new(
            |nid| 0 <= nid < Self::total_size(),
        ));
        lemma_nat_range_finite(0, Self::total_size());
    }
}

} // verus!
