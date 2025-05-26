use vstd::prelude::*;

verus! {

pub open spec fn valid_nid(nid: nat) -> bool {
    0 <= nid < tree_size_spec(3)
}

/// Returns the size of the tree with nodes at most `max_dep` depth.
pub open spec fn tree_size_spec(max_dep: int) -> nat
    recommends
        0 <= max_dep < 4,
    decreases max_dep,
    when max_dep >= 0
{
    let cur_dep = max_dep as nat;
    if max_dep == 0 {
        1
    } else {
        512 * tree_size_spec(max_dep - 1) + 1
    }
}

/// Returns the trace from cur_rt to the node with id `nid`.
pub open spec fn nid_to_trace_rec(nid: nat, cur_level: nat, cur_rt: nat) -> Seq<nat>
    decreases cur_level,
{
    if cur_level == 0 {
        seq![]
    } else {
        let child_size = tree_size_spec(cur_level - 1);
        let offset = ((nid - cur_rt - 1) / child_size as int) as nat;
        let child_root = cur_rt + offset * child_size + 1;
        if child_root == nid {
            seq![offset]
        } else {
            seq![offset].add(nid_to_trace_rec(nid, (cur_level - 1) as nat, child_root))
        }
    }
}

/// Returns the trace from root to the node with id `nid`.
pub open spec fn nid_to_trace(nid: nat) -> Seq<nat>
    recommends
        valid_nid(nid),
{
    if nid == 0 {
        Seq::empty()
    } else {
        nid_to_trace_rec(nid, 3, 0)
    }
}

pub uninterp spec fn trace_to_nid_rec(trace: Seq<nat>, cur_rt: nat, dep_level: nat) -> nat;

pub uninterp spec fn trace_to_nid(trace: Seq<nat>) -> nat;

pub axiom fn axiom_nid_to_trace_sound(nid:nat)
    requires
        valid_nid(nid),
    ensures
        trace_to_nid(nid_to_trace(nid)) == nid,
;

pub proof fn lemma_test(rt: nat, nd: nat)
    requires
        valid_nid(rt),
        valid_nid(nd),
        nid_to_trace(rt).is_prefix_of(nid_to_trace(nd)),
    ensures
        rt <= nd,
{
    let rt_trace = nid_to_trace(rt);
    let nd_trace = nid_to_trace(nd);
    axiom_nid_to_trace_sound(rt);
    axiom_nid_to_trace_sound(nd);
    if rt_trace.len() == 0 {} else
    {
        if rt == nd {} else
        {
            let trace_diff = nd_trace.len() - rt_trace.len();
            if trace_diff == 0 {
                assert(rt_trace =~= nd_trace);
                assert(rt==nd);
            } else
            {
                let suffix = nd_trace.subrange(
                    rt_trace.len() as int,
                    nd_trace.len() as int,
                );
                let dep_level = 3- rt_trace.len();
                assert(rt+ tree_size_spec(dep_level) <= tree_size_spec(3)) by {admit();};
                assert(trace_to_nid(rt_trace.add(suffix)) == trace_to_nid_rec(suffix,rt,dep_level as nat)) by {admit();};
                assert(rt<= trace_to_nid_rec(suffix,rt,dep_level as nat)) by {admit();};
            }
        }
    }
    }

} // verus!
