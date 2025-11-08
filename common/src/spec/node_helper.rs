use std::intrinsics::offset;
use std::intrinsics::ptr_offset_from;

use vstd::bytes;
use vstd::prelude::*;
use vstd::arithmetic::power::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::set::*;
use vstd_extra::prelude::*;

use crate::mm::nr_subpage_per_huge;
use crate::spec::common::NodeId;

use crate::mm::page_table::{PageTableConfig, PagingConstsTrait};

verus! {

broadcast use vstd_extra::seq_extra::group_forall_seq_lemmas;

pub broadcast group group_node_helper_lemmas {
    lemma_in_subtree_iff_in_subtree_range,
    lemma_trace_to_nid_sound,
    lemma_nid_to_trace_sound,
    lemma_get_parent_sound,
    lemma_get_offset_sound,
    lemma_get_child_sound,
    lemma_next_outside_subtree_bounded,
}

/// If C::NR_LEVELS_SPEC() is 4,
/// depth starts from 0(root) to 3 (leaf),
/// level starts from 4(root) to 1 (leaf).
#[verifier::inline]
pub open spec fn level_to_dep<C: PageTableConfig>(level: nat) -> nat
    recommends
        1 <= level <= C::NR_LEVELS_SPEC(),
{
    (C::NR_LEVELS_SPEC() - level) as nat
}

#[verifier::inline]
pub open spec fn dep_to_level<C: PageTableConfig>(dep: nat) -> nat
    recommends
        0 <= dep < C::NR_LEVELS_SPEC(),
{
    (C::NR_LEVELS_SPEC() - dep) as nat
}

pub proof fn lemma_level_to_dep_bijective<C: PageTableConfig>(level: nat)
    requires
        1 <= level <= C::NR_LEVELS_SPEC(),
    ensures
        dep_to_level::<C>(level_to_dep::<C>(level)) == level,
{
}

pub proof fn lemma_dep_to_level_bijective<C: PageTableConfig>(dep: nat)
    requires
        0 <= dep < C::NR_LEVELS_SPEC(),
    ensures
        level_to_dep::<C>(dep_to_level::<C>(dep)) == dep,
{
}

/// The number of nodes at a given level.
pub closed spec fn size_at_dep<C: PageTableConfig>(dep: nat) -> nat
    recommends
        0 <= dep < C::NR_LEVELS_SPEC(),
{
    pow(512, dep) as nat
}

pub proof fn lemma_size_at_dep_table<C: PageTableConfig>()
    ensures
        size_at_dep::<C>(0) == 1,
        size_at_dep::<C>(1) == 512,
        size_at_dep::<C>(2) == 262144,
        size_at_dep::<C>(3) == 134217728,
        size_at_dep::<C>(4) == 68719476736,
{
    reveal(pow);
    assert(size_at_dep::<C>(0) == 1) by (compute_only);
    assert(size_at_dep::<C>(1) == 512) by (compute_only);
    assert(size_at_dep::<C>(2) == 262144) by (compute_only);
    assert(size_at_dep::<C>(3) == 134217728) by (compute_only);
    assert(size_at_dep::<C>(4) == 68719476736) by (compute_only);
}

/// Returns the size of the tree with nodes at most `max_dep` depth.
#[verifier::memoize]
pub closed spec fn tree_size_spec<C: PageTableConfig>(max_dep: int) -> nat
    recommends
        0 <= max_dep < C::NR_LEVELS_SPEC(),
    decreases max_dep,
    when max_dep >= 0
{
    let cur_dep = max_dep as nat;
    if max_dep == 0 {
        1
    } else {
        512 * tree_size_spec::<C>(max_dep - 1) + 1
    }
}

pub proof fn lemma_tree_size_spec_table<C: PageTableConfig>()
    ensures
        tree_size_spec::<C>(0) == 1,
        tree_size_spec::<C>(1) == 513,
        tree_size_spec::<C>(2) == 262657,
        tree_size_spec::<C>(3) == 134480385,
        tree_size_spec::<C>(4) == 68853957121,
{
    assert(tree_size_spec::<C>(0) == 1) by (compute_only);
    assert(tree_size_spec::<C>(1) == 513) by (compute_only);
    assert(tree_size_spec::<C>(2) == 262657) by (compute_only);
    assert(tree_size_spec::<C>(3) == 134480385) by (compute_only);
    assert(tree_size_spec::<C>(4) == 68853957121) by (compute_only);
}

pub open spec fn tree_size_weighted_spec<C: PageTableConfig>(k: int) -> nat
    recommends
        1 <= k < C::NR_LEVELS_SPEC(),
{
    511 * tree_size_spec::<C>(k) + 1
}

pub open spec fn tree_size_weighted_sum_spec<C: PageTableConfig>(k: int) -> nat
    recommends
        0 <= k < C::NR_LEVELS_SPEC(),
    decreases k,
{
    if k <= 0 {
        0
    } else {
        tree_size_weighted_spec::<C>(k - 1) + tree_size_weighted_sum_spec::<C>(k - 1)
    }
}

pub open spec fn tree_size_relation_spec<C: PageTableConfig>(k: int) -> bool {
    tree_size_weighted_sum_spec::<C>(k) + 1 == tree_size_spec::<C>(k)
}

pub proof fn lemma_tree_size_relation<C: PageTableConfig>()
    ensures
        tree_size_relation_spec::<C>(0),
        tree_size_relation_spec::<C>(1),
        tree_size_relation_spec::<C>(2),
        tree_size_relation_spec::<C>(3),
        tree_size_relation_spec::<C>(4),
{
    assert(tree_size_relation_spec::<C>(0)) by (compute_only);
    assert(tree_size_relation_spec::<C>(1)) by (compute_only);
    assert(tree_size_relation_spec::<C>(2)) by (compute_only);
    assert(tree_size_relation_spec::<C>(3)) by (compute_only);
    assert(tree_size_relation_spec::<C>(4)) by (compute_only);
}

/// The total size of the tree with C::NR_LEVELS_SPEC() levels.
pub open spec fn total_size<C: PageTableConfig>() -> nat {
    tree_size_spec::<C>(C::NR_LEVELS_SPEC() - 1)
}

// Do not inline this function, it serves as a trigger.
pub open spec fn valid_nid<C: PageTableConfig>(nid: NodeId) -> bool {
    0 <= nid < total_size::<C>()
}

#[verifier::inline]
pub open spec fn root_id<C: PageTableConfig>() -> NodeId {
    0
}

pub proof fn lemma_root_id<C: PageTableConfig>()
    ensures
        valid_nid::<C>(root_id::<C>()),
{
    assert(0 < total_size::<C>()) by {
        assert(C::NR_LEVELS_SPEC() >= 1) by {
            C::lemma_consts_properties();
        };
    };
}

// Lemmas about trace.
// A trace is a sequence of offsets from the root to a node.
// The length of the trace is at most C::NR_LEVELS_SPEC() - 1.
pub open spec fn valid_trace<C: PageTableConfig>(trace: Seq<nat>) -> bool {
    &&& 0 <= trace.len() < C::NR_LEVELS_SPEC()
    &&& trace.all(|offset: nat| 0 <= offset < 512)
}

/// The set of all valid node ids.
pub open spec fn valid_nid_set<C: PageTableConfig>() -> Set<NodeId> {
    Set::new(|nid: NodeId| valid_nid::<C>(nid))
}

/// The set of all valid traces.
pub open spec fn valid_trace_set<C: PageTableConfig>() -> Set<Seq<nat>> {
    Set::new(|trace: Seq<nat>| valid_trace::<C>(trace))
}

pub open spec fn trace_lt<C: PageTableConfig>(t1: Seq<nat>, t2: Seq<nat>) -> bool
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
            trace_lt::<C>(t1.drop_first(), t2.drop_first())
        }
    }
}

/// Returns the trace from cur_rt to the node with id `nid`.
pub closed spec fn nid_to_trace_rec<C: PageTableConfig>(
    nid: NodeId,
    cur_level: nat,
    cur_rt: NodeId,
) -> Seq<nat>
    decreases cur_level,
{
    if cur_level == 0 {
        seq![]
    } else {
        let child_size = tree_size_spec::<C>(cur_level - 1);
        let offset = ((nid - cur_rt - 1) / child_size as int) as nat;
        let child_root = cur_rt + offset * child_size + 1;
        if child_root == nid {
            seq![offset]
        } else {
            seq![offset].add(nid_to_trace_rec::<C>(nid, (cur_level - 1) as nat, child_root))
        }
    }
}

/// Returns the trace from root to the node with id `nid`.
pub open spec fn nid_to_trace<C: PageTableConfig>(nid: NodeId) -> Seq<nat>
    recommends
        valid_nid::<C>(nid),
{
    if nid == root_id::<C>() {
        Seq::empty()
    } else {
        nid_to_trace_rec::<C>(nid, (C::NR_LEVELS_SPEC() - 1) as nat, root_id::<C>())
    }
}

pub proof fn lemma_nid_to_trace_basic<C: PageTableConfig>()
    ensures
        nid_to_trace::<C>(root_id::<C>()) =~= Seq::empty(),
{
}

/// Returns the node id from the trace.
#[verifier::opaque]
pub open spec fn trace_to_nid_rec<C: PageTableConfig>(
    trace: Seq<nat>,
    cur_rt: NodeId,
    cur_level: int,
) -> NodeId
    recommends
        valid_trace::<C>(trace),
        valid_nid::<C>(cur_rt),
        trace.len() <= cur_level <= C::NR_LEVELS_SPEC() - 1,
{
    trace.fold_left_alt(
        (cur_rt, cur_level as int),
        |param: (NodeId, int), offset: nat|
            {
                let nid = param.0;
                let cur_level = param.1;
                let sz = tree_size_spec::<C>(cur_level - 1);
                (nid + offset * sz + 1, cur_level - 1)
            },
    ).0
}

/// Returns the node id from the trace starting from root.
pub open spec fn trace_to_nid<C: PageTableConfig>(trace: Seq<nat>) -> NodeId
    recommends
        valid_trace::<C>(trace),
{
    trace_to_nid_rec::<C>(trace, 0, C::NR_LEVELS_SPEC() - 1)
}

pub proof fn lemma_trace_to_nid_basic<C: PageTableConfig>()
    ensures
        trace_to_nid::<C>(Seq::empty()) == root_id::<C>(),
{
    admit();
}

/// Returns the child node id from the trace and offset.
pub open spec fn child_nid_from_trace_offset<C: PageTableConfig>(
    trace: Seq<nat>,
    offset: nat,
) -> NodeId
    recommends
        valid_trace::<C>(trace),
        0 <= offset < 512,
        trace.len() < C::NR_LEVELS_SPEC() - 1,
{
    let nid1 = trace_to_nid::<C>(trace);
    let level = C::NR_LEVELS_SPEC() - 1 - trace.len();
    let sz = tree_size_spec::<C>(level - 1);
    nid1 + offset * sz + 1
}

/// Returns true is the node is not a leaf
pub open spec fn is_not_leaf<C: PageTableConfig>(nid: NodeId) -> bool
    recommends
        valid_nid::<C>(nid),
{
    nid_to_dep::<C>(nid) < C::NR_LEVELS_SPEC() - 1
}

/// Returns the child node id from the node id and offset.
pub open spec fn get_child<C: PageTableConfig>(nid: NodeId, offset: nat) -> NodeId
    recommends
        valid_nid::<C>(nid),
        nid_to_dep::<C>(nid) < C::NR_LEVELS_SPEC() - 1,
        0 <= offset < 512,
{
    trace_to_nid::<C>(nid_to_trace::<C>(nid).push(offset))
}

/// Returns the parent node id from the node id.
/// If the node id is root, the result is arbitrary.
pub open spec fn get_parent<C: PageTableConfig>(nid: NodeId) -> NodeId
    recommends
        valid_nid::<C>(nid),
        nid != root_id::<C>(),
{
    trace_to_nid::<C>(nid_to_trace::<C>(nid).drop_last())
}

/// Returns true if `ch` is a child of `pa (the trace of 'pa' is equal to the drooping last element trace of 'ch').
pub open spec fn is_child<C: PageTableConfig>(pa: NodeId, ch: NodeId) -> bool
    recommends
        valid_nid::<C>(pa),
        valid_nid::<C>(ch),
{
    &&& nid_to_trace::<C>(pa) == nid_to_trace::<C>(ch).drop_last()
    &&& ch != root_id::<C>()
}

/// Returns the offset of the node id from its parent.
pub open spec fn get_offset<C: PageTableConfig>(nid: NodeId) -> nat
    recommends
        valid_nid::<C>(nid),
        nid != root_id::<C>(),
{
    let trace = nid_to_trace::<C>(nid);
    trace.last()
}

pub open spec fn nid_to_dep<C: PageTableConfig>(nid: NodeId) -> nat
    recommends
        valid_nid::<C>(nid),
{
    nid_to_trace::<C>(nid).len()
}

pub open spec fn nid_to_level<C: PageTableConfig>(nid: NodeId) -> nat
    recommends
        valid_nid::<C>(nid),
{
    dep_to_level::<C>(nid_to_dep::<C>(nid))
}

/// Returns the size of the subtree rooted at `nid`.
pub open spec fn sub_tree_size<C: PageTableConfig>(nid: NodeId) -> nat
    recommends
        valid_nid::<C>(nid),
{
    let level = nid_to_level::<C>(nid);
    tree_size_spec::<C>(level - 1)
}

/// The next node id outside the subtree rooted at `nid`.
pub open spec fn next_outside_subtree<C: PageTableConfig>(nid: NodeId) -> NodeId
    recommends
        valid_nid::<C>(nid),
{
    nid + sub_tree_size::<C>(nid)
}

/// Returns 'true' if 'nd' is in the subtree of 'rt' (the trace of 'rt' is a prefix of the trace of 'nd' and 'nd' is valid).
pub open spec fn in_subtree<C: PageTableConfig>(rt: NodeId, nd: NodeId) -> bool
    recommends
        valid_nid::<C>(rt),
        valid_nid::<C>(nd),
{
    &&& nid_to_trace::<C>(rt).is_prefix_of(nid_to_trace::<C>(nd))
    &&& valid_nid::<C>(nd)
}

pub open spec fn in_subtree_range<C: PageTableConfig>(rt: NodeId, nd: NodeId) -> bool
    recommends
        valid_nid::<C>(rt),
{
    rt <= nd < next_outside_subtree::<C>(rt)
}

/// Returns the NodeIds in the path from the trace.
pub open spec fn trace_to_tree_path<C: PageTableConfig>(trace: Seq<nat>) -> Seq<NodeId>
    recommends
        valid_trace::<C>(trace),
    decreases trace.len(),
{
    let ids = trace.map(|i: int, offset: nat| trace_to_nid::<C>(trace.subrange(0, i + 1)));
    seq![root_id::<C>()] + ids
}

/// Returns the traces in the subtree of the given trace.
pub open spec fn get_subtree_traces<C: PageTableConfig>(trace: Seq<nat>) -> Set<Seq<nat>>
    recommends
        valid_trace::<C>(trace),
{
    valid_trace_set::<C>().filter(|subtree_trace| trace.is_prefix_of(subtree_trace))
}

pub open spec fn get_ancestor_at_level<C: PageTableConfig>(nid: NodeId, level: nat) -> NodeId
    recommends
        valid_nid::<C>(nid),
        nid_to_level::<C>(nid) <= level <= C::NR_LEVELS_SPEC(),
{
    let trace = nid_to_trace::<C>(nid);
    let dep = dep_to_level::<C>(level);
    let ancestor_trace = trace.subrange(0, dep as int);
    trace_to_nid::<C>(ancestor_trace)
}

proof fn lemma_trace_to_nid_rec_inductive<C: PageTableConfig>(
    trace: Seq<nat>,
    cur_rt: NodeId,
    cur_level: int,
)
    ensures
        trace.len() > 0 ==> trace_to_nid_rec::<C>(trace, cur_rt, cur_level) == trace_to_nid_rec::<
            C,
        >(
            trace.drop_first(),
            cur_rt + trace[0] * tree_size_spec::<C>(cur_level - 1) + 1,
            cur_level - 1,
        ),
{
    reveal(trace_to_nid_rec);
}

pub open spec fn trace_to_nid_upperbound_spec<C: PageTableConfig>(max_dep: nat) -> nat
    decreases max_dep,
{
    let cur_dep = max_dep;
    let level = dep_to_level::<C>(max_dep);
    if cur_dep == 0 {
        0
    } else {
        tree_size_weighted_spec::<C>(level - 1) + trace_to_nid_upperbound_spec::<C>(
            (max_dep - 1) as nat,
        )
    }
}

pub proof fn lemma_trace_to_nid_upperbound_spec<C: PageTableConfig>(max_dep: nat)
    requires
        0 <= max_dep < C::NR_LEVELS_SPEC(),
    ensures
        trace_to_nid_upperbound_spec::<C>(max_dep) == tree_size_spec::<C>(C::NR_LEVELS_SPEC() - 1)
            - tree_size_spec::<C>(C::NR_LEVELS_SPEC() - 1 - max_dep),
    decreases max_dep,
{
    lemma_tree_size_relation::<C>();
    if max_dep > 0 {
        lemma_trace_to_nid_upperbound_spec::<C>((max_dep - 1) as nat);
    }
}

proof fn lemma_trace_to_nid_inner<C: PageTableConfig>(trace: Seq<nat>)
    requires
        valid_trace::<C>(trace),
    ensures
        trace.fold_left_alt(
            (0, C::NR_LEVELS_SPEC() - 1),
            |param: (NodeId, int), offset: nat|
                {
                    let nid = param.0;
                    let cur_level = param.1;
                    let sz = tree_size_spec::<C>(cur_level - 1);
                    (nid + offset * sz + 1, cur_level - 1)
                },
        ).0 <= trace_to_nid_upperbound_spec::<C>(trace.len()),
        trace.fold_left_alt(
            (0, C::NR_LEVELS_SPEC() - 1),
            |param: (NodeId, int), offset: nat|
                {
                    let nid = param.0;
                    let cur_level = param.1;
                    let sz = tree_size_spec::<C>(cur_level - 1);
                    (nid + offset * sz + 1, cur_level - 1)
                },
        ).1 == C::NR_LEVELS_SPEC() - 1 - trace.len(),
    decreases trace.len(),
{
    let func = |param: (NodeId, int), offset: nat|
        {
            let nid = param.0;
            let cur_level = param.1;
            let sz = tree_size_spec::<C>(cur_level - 1);
            (nid + offset * sz + 1, cur_level - 1)
        };

    if trace.len() != 0 {
        let new_trace = trace.drop_last();
        lemma_trace_to_nid_inner::<C>(new_trace);
        lemma_mul_inequality(
            trace.last() as int,
            511,
            tree_size_spec::<C>(C::NR_LEVELS_SPEC() - 1 - trace.len()) as int,
        );
        trace.lemma_fold_left_alt((0, C::NR_LEVELS_SPEC() - 1), func);
        new_trace.lemma_fold_left_alt((0, C::NR_LEVELS_SPEC() - 1), func);
    }
}

proof fn lemma_trace_to_nid_rec_lower_bound<C: PageTableConfig>(
    trace: Seq<nat>,
    root: NodeId,
    level: int,
)
    ensures
        trace.len() > 0 ==> trace_to_nid_rec::<C>(trace, root, level) > root,
        trace.len() == 0 ==> trace_to_nid_rec::<C>(trace, root, level) == root,
    decreases trace.len(),
{
    reveal(trace_to_nid_rec);
    if trace.len() != 0 {
        let new_trace = trace.subrange(1, trace.len() as int);
        let new_rt = root + trace[0] * tree_size_spec::<C>(level - 1) + 1;
        if new_trace.len() > 0 {
            lemma_trace_to_nid_rec_lower_bound::<C>(new_trace, new_rt, level - 1);
        }
    }
}

proof fn lemma_trace_to_nid_rec_upper_bound<C: PageTableConfig>(
    trace: Seq<nat>,
    root: NodeId,
    level: int,
)
    requires
        valid_trace::<C>(trace),
        trace.len() <= level,
    ensures
        trace_to_nid_rec::<C>(trace, root, level) < root + tree_size_spec::<C>(level),
    decreases trace.len(),
{
    reveal(trace_to_nid_rec);
    lemma_tree_size_spec_table::<C>();
    if trace.len() != 0 {
        let new_trace = trace.subrange(1, trace.len() as int);
        let new_rt = root + trace[0] * tree_size_spec::<C>(level - 1) + 1;
        assert(new_rt + tree_size_spec::<C>(level - 1) <= root + tree_size_spec::<C>(level))
            by (nonlinear_arith)
            requires
                trace[0] < 512,
                tree_size_spec::<C>(level - 1) >= 0,
                tree_size_spec::<C>(level) == tree_size_spec::<C>(level - 1) * 512 + 1,
                new_rt == root + trace[0] * tree_size_spec::<C>(level - 1) + 1,
        ;
        lemma_trace_to_nid_rec_upper_bound::<C>(new_trace, new_rt, level - 1);
    }
}

pub proof fn lemma_trace_to_nid_increasing<C: PageTableConfig>(trace1: Seq<nat>, trace2: Seq<nat>)
    requires
        trace_lt::<C>(trace1, trace2),
        valid_trace::<C>(trace1),
        valid_trace::<C>(trace2),
    ensures
        trace_to_nid::<C>(trace1) < trace_to_nid::<C>(trace2),
{
    lemma_trace_to_nid_rec_increasing::<C>(trace1, trace2, 0, C::NR_LEVELS_SPEC() - 1);
}

proof fn lemma_trace_to_nid_rec_increasing<C: PageTableConfig>(
    trace1: Seq<nat>,
    trace2: Seq<nat>,
    root: NodeId,
    level: int,
)
    requires
        trace_lt::<C>(trace1, trace2),
        valid_trace::<C>(trace1),
        valid_trace::<C>(trace2),
        trace2.len() <= level,
        trace1.len() <= level,
    ensures
        trace_to_nid_rec::<C>(trace1, root, level) < trace_to_nid_rec::<C>(trace2, root, level),
    decreases trace1.len(),
{
    reveal(trace_to_nid_rec);
    if trace1.len() == 0 {
        if trace2.len() != 0 {
            lemma_trace_to_nid_rec_lower_bound::<C>(trace2, root, level);
        }
    } else {
        if trace2.len() != 0 {
            let new_trace1 = trace1.subrange(1, trace1.len() as int);
            let new_trace2 = trace2.subrange(1, trace2.len() as int);
            if trace1[0] == trace2[0] {
                let new_rt = root + trace1[0] * tree_size_spec::<C>(level - 1) + 1;
                lemma_trace_to_nid_rec_increasing::<C>(new_trace1, new_trace2, new_rt, level - 1);
            } else if trace1[0] < trace2[0] {
                let new_rt1 = root + trace1[0] * tree_size_spec::<C>(level - 1) + 1;
                let new_rt2 = root + trace2[0] * tree_size_spec::<C>(level - 1) + 1;
                assert(trace_to_nid_rec::<C>(trace1, root, level) < new_rt1 + tree_size_spec::<C>(
                    level - 1,
                )) by {
                    lemma_trace_to_nid_rec_upper_bound::<C>(new_trace1, new_rt1, level - 1);
                }
                assert(trace_to_nid_rec::<C>(trace2, root, level) >= new_rt2) by {
                    lemma_trace_to_nid_rec_lower_bound::<C>(new_trace2, new_rt2, level - 1);
                }
                assert(trace1[0] * tree_size_spec::<C>(level - 1) + tree_size_spec::<C>(level - 1)
                    <= trace2[0] * tree_size_spec::<C>(level - 1)) by (nonlinear_arith)
                    requires
                        0 <= trace1[0] < trace2[0],
                ;
            }
        }
    }
}

/// `child_nid_from_trace_offset` correctly returns the child node id from the trace and offset,
/// i.e. `child_nid_from_trace_offset(trace, offset) == trace_to_nid(trace.push(offset))`.
pub proof fn lemma_child_nid_from_trace_offset_sound<C: PageTableConfig>(
    trace: Seq<nat>,
    offset: nat,
)
    requires
        0 <= offset < 512,
        valid_trace::<C>(trace),
    ensures
        child_nid_from_trace_offset::<C>(trace, offset) == trace_to_nid::<C>(trace.push(offset)),
{
    reveal(trace_to_nid_rec);
    let func = |param: (NodeId, int), offset: nat|
        {
            let nid = param.0;
            let cur_level = param.1;
            let sz = tree_size_spec::<C>(cur_level - 1);
            (nid + offset * sz + 1, cur_level - 1)
        };

    assert(trace.push(offset).drop_last() == trace);
    assert(func(trace.fold_left_alt((0, C::NR_LEVELS_SPEC() - 1), func), offset) == trace.push(
        offset,
    ).fold_left_alt((0, C::NR_LEVELS_SPEC() - 1), func)) by {
        trace.lemma_fold_left_alt((0, C::NR_LEVELS_SPEC() - 1), func);
        trace.push(offset).lemma_fold_left_alt((0, C::NR_LEVELS_SPEC() - 1), func);
    };
    assert(trace.fold_left_alt((0, C::NR_LEVELS_SPEC() - 1), func).1 == C::NR_LEVELS_SPEC() - 1
        - trace.len()) by {
        lemma_trace_to_nid_inner::<C>(trace);
    };
}

/// The result of `trace_to_nid` is the same as splitting the trace into two parts
/// and calling `trace_to_nid_rec` on the second part.
pub proof fn lemma_trace_to_nid_split<C: PageTableConfig>(
    trace1: Seq<nat>,
    trace2: Seq<nat>,
    cur_rt: NodeId,
    cur_level: int,
)
    requires
        valid_trace::<C>(trace1.add(trace2)),
        cur_rt == trace_to_nid::<C>(trace1),
        cur_level == level_to_dep::<C>(trace1.len()) - 1,
    ensures
        trace_to_nid::<C>(trace1.add(trace2)) == trace_to_nid_rec::<C>(trace2, cur_rt, cur_level),
    decreases trace2.len(),
{
    reveal(trace_to_nid_rec);
    if trace2.len() == 0 {
        assert(trace1.add(trace2) == trace1);
    } else {
        // Induction step: use `lemma_child_nid_from_trace_offset_sound` to move the first element
        // of `trace2` to the end of `trace1` and then use the inductive hypothesis on the rest of `trace2`.
        let new_trace1 = trace1.push(trace2[0]);
        let new_trace2 = trace2.subrange(1, trace2.len() as int);
        assert(new_trace1.add(new_trace2) == trace1.add(trace2));
        let new_rt = cur_rt + trace2[0] * tree_size_spec::<C>(cur_level - 1) + 1;
        assert(new_rt == trace_to_nid::<C>(new_trace1)) by {
            lemma_child_nid_from_trace_offset_sound::<C>(trace1, trace2[0]);
        };
        lemma_trace_to_nid_split::<C>(new_trace1, new_trace2, new_rt, cur_level - 1)
    }
}

/// `nid_to_trace_rec` correcly returns a trace from `cur_rt` to the node id `nid`.
/// By applying `trace_to_nid_rec' to the trace produced by `nid_to_trace_rec`, we can
/// reconstruct the original node id.
pub proof fn lemma_nid_to_trace_rec_sound<C: PageTableConfig>(
    nid: NodeId,
    cur_level: nat,
    cur_rt: NodeId,
)
    requires
        valid_nid::<C>(nid),
        cur_level <= C::NR_LEVELS_SPEC() - 1,
        cur_rt < nid < cur_rt + tree_size_spec::<C>(cur_level as int),
    ensures
        nid_to_trace_rec::<C>(nid, cur_level, cur_rt).len() <= cur_level,
        valid_trace::<C>(nid_to_trace_rec::<C>(nid, cur_level, cur_rt)),
        nid == trace_to_nid_rec::<C>(
            nid_to_trace_rec::<C>(nid, cur_level, cur_rt),
            cur_rt,
            cur_level as int,
        ),
    decreases cur_level,
{
    if cur_level == 0 {
    } else {
        let sz = tree_size_spec::<C>(cur_level - 1);
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
            reveal(trace_to_nid_rec);
            assert(trace_to_nid_rec::<C>(trace, cur_rt, cur_level as int) == nid) by {
                lemma_trace_to_nid_rec_inductive::<C>(trace, cur_rt, cur_level as int);
            };
        } else {
            lemma_nid_to_trace_rec_sound::<C>(nid, (cur_level - 1) as nat, new_rt);
            let _trace = nid_to_trace_rec::<C>(nid, (cur_level - 1) as nat, new_rt);
            let trace = seq![offset].add(_trace);
            assert(trace_to_nid_rec::<C>(trace, cur_rt, cur_level as int) == nid) by {
                lemma_trace_to_nid_rec_inductive::<C>(trace, cur_rt, cur_level as int);
                assert(_trace == trace.subrange(1, trace.len() as int));
            };
        }
    }
}

/// `nid_to_trace` correctly returns a trace of the node id `nid` starting from the root.
/// By applying `nid_to_trace` to the trace produced by `nid_to_trace`, we can
/// reconstruct the original node id.
pub broadcast proof fn lemma_nid_to_trace_sound<C: PageTableConfig>(nid: NodeId)
    requires
        valid_nid::<C>(nid),
    ensures
        valid_trace::<C>(#[trigger] nid_to_trace::<C>(nid)),
        trace_to_nid::<C>(nid_to_trace::<C>(nid)) == nid,
{
    reveal(trace_to_nid_rec);
    assert(C::NR_LEVELS_SPEC() >= 1) by {
        C::lemma_consts_properties();
    };
    if nid != root_id::<C>() {
        lemma_nid_to_trace_rec_sound::<C>(nid, (C::NR_LEVELS_SPEC() - 1) as nat, 0)
    }
}

/// 'trace_to_nid` is the left inverse of `nid_to_trace` between the valid node id set and the valid trace set.
pub proof fn lemma_nid_to_trace_left_inverse<C: PageTableConfig>()
    ensures
        left_inverse_on(
            |nid| nid_to_trace::<C>(nid),
            |trace| trace_to_nid::<C>(trace),
            valid_nid_set::<C>(),
            valid_trace_set::<C>(),
        ),
{
    assert forall|nid| #[trigger] valid_nid_set::<C>().contains(nid) implies valid_trace_set::<
        C,
    >().contains(nid_to_trace::<C>(nid)) && trace_to_nid::<C>(nid_to_trace::<C>(nid)) == nid by {
        lemma_nid_to_trace_sound::<C>(nid);
    };
}

/// `trace_to_nid_rec` correctly returns a node id from the trace starting from `cur_rt`.
/// We can reconstruct the trace using `nid_to_trace_rec` with the trace given by `trace_to_nid_rec`.
#[verifier::spinoff_prover]
pub proof fn lemma_trace_to_nid_rec_sound<C: PageTableConfig>(
    trace: Seq<nat>,
    cur_rt: NodeId,
    cur_level: int,
)
    requires
        valid_trace::<C>(trace),
        cur_rt + tree_size_spec::<C>(cur_level) <= total_size::<C>(),
        trace.len() <= cur_level,
    ensures
        cur_rt <= trace_to_nid_rec::<C>(trace, cur_rt, cur_level) < cur_rt + tree_size_spec::<C>(
            cur_level,
        ),
        trace_to_nid_rec::<C>(trace, cur_rt, cur_level) == cur_rt <==> trace.len() == 0,
        trace.len() != 0 ==> trace == nid_to_trace_rec::<C>(
            trace_to_nid_rec::<C>(trace, cur_rt, cur_level),
            cur_level as nat,
            cur_rt,
        ),
    decreases trace.len(),
{
    reveal(trace_to_nid_rec);
    if trace.len() == 0 {
    } else {
        let new_rt = cur_rt + trace[0] * tree_size_spec::<C>(cur_level - 1) + 1;
        assert(new_rt + tree_size_spec::<C>(cur_level - 1) <= total_size::<C>()) by {
            lemma_mul_is_distributive_sub_other_way(
                tree_size_spec::<C>(cur_level - 1) as int,
                512,
                trace[0] as int,
            );
            lemma_mul_inequality(1, 512 - trace[0], tree_size_spec::<C>(cur_level - 1) as int);
        };

        let new_level = cur_level - 1;

        lemma_trace_to_nid_rec_sound::<C>(trace.drop_first(), new_rt, new_level);
        let nid = trace_to_nid_rec::<C>(trace, cur_rt, cur_level);

        let sz = tree_size_spec::<C>(cur_level - 1);
        reveal(trace_to_nid_rec);
        assert(new_rt + sz <= cur_rt + tree_size_spec::<C>(cur_level)) by {
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
pub broadcast proof fn lemma_trace_to_nid_sound<C: PageTableConfig>(trace: Seq<nat>)
    requires
        valid_trace::<C>(trace),
    ensures
        valid_nid::<C>(#[trigger] trace_to_nid::<C>(trace)),
        trace =~= nid_to_trace::<C>(trace_to_nid::<C>(trace)),
{
    lemma_trace_to_nid_rec_sound::<C>(trace, 0, C::NR_LEVELS_SPEC() - 1)
}

/// `nid_to_trace` is the right inverse of `trace_to_nid` between the valid node id set and the valid trace set.
pub proof fn lemma_nid_to_trace_right_inverse<C: PageTableConfig>()
    ensures
        right_inverse_on(
            |trace| nid_to_trace::<C>(trace),
            |nid| trace_to_nid::<C>(nid),
            valid_nid_set::<C>(),
            valid_trace_set::<C>(),
        ),
{
    assert forall|trace| #[trigger] valid_trace_set::<C>().contains(trace) implies valid_nid_set::<
        C,
    >().contains(trace_to_nid::<C>(trace)) && nid_to_trace::<C>(trace_to_nid::<C>(trace))
        == trace by {
        lemma_trace_to_nid_sound::<C>(trace);
    };
}

/// The function `nid_to_trace` is bijective between the valid node id set and the valid trace set.
pub proof fn lemma_nid_to_trace_bijective<C: PageTableConfig>()
    ensures
        bijective_on(|nid| nid_to_trace::<C>(nid), valid_nid_set::<C>(), valid_trace_set::<C>()),
{
    lemma_nid_to_trace_left_inverse::<C>();
    lemma_nid_to_trace_right_inverse::<C>();
}

/// The function `trace_to_nid` is bijective between the valid trace set and the valid node id set.
pub proof fn lemma_trace_to_nid_bijective<C: PageTableConfig>()
    ensures
        bijective_on(
            |trace| trace_to_nid::<C>(trace),
            valid_trace_set::<C>(),
            valid_nid_set::<C>(),
        ),
{
    lemma_nid_to_trace_bijective::<C>();
    lemma_nid_to_trace_left_inverse::<C>();
    lemma_inverse_of_bijection_is_bijective(
        |nid| nid_to_trace::<C>(nid),
        |trace| trace_to_nid::<C>(trace),
        valid_nid_set::<C>(),
        valid_trace_set::<C>(),
    );
}

// Helper lemma: prove that the result length of nid_to_trace_rec does not exceed cur_level
proof fn lemma_trace_rec_len_le_level<C: PageTableConfig>(
    nid: NodeId,
    cur_level: nat,
    cur_rt: NodeId,
)
    ensures
        nid_to_trace_rec::<C>(nid, cur_level, cur_rt).len() <= cur_level,
    decreases cur_level,
// Induction proof on cur_level

{
    if cur_level == 0 {
        assert(nid_to_trace_rec::<C>(nid, 0, cur_rt).len() == 0);
    } else {
        let sz = tree_size_spec::<C>(cur_level - 1);
        let offset = ((nid - cur_rt - 1) / sz as int) as nat;
        let new_rt = cur_rt + offset * sz + 1;

        if new_rt == nid {
        } else {
            lemma_trace_rec_len_le_level::<C>(nid, (cur_level - 1) as nat, new_rt);
        }
    }
}

/// `nid_to_depth` correctly returns a depth of C::NR_LEVELS_SPEC() - 1 or less.
pub proof fn lemma_nid_to_dep_up_bound<C: PageTableConfig>(nid: NodeId)
    ensures
        nid_to_dep::<C>(nid) <= C::NR_LEVELS_SPEC() - 1,
{
    C::lemma_consts_properties();
    if nid != root_id::<C>() {
        lemma_trace_rec_len_le_level::<C>(nid, (C::NR_LEVELS_SPEC() - 1) as nat, root_id::<C>());
    }
}

/// The relation between nid_to_level and nid_to_dep.
pub proof fn lemma_level_dep_relation<C: PageTableConfig>(nid: NodeId)
    ensures
        nid_to_level::<C>(nid) == C::NR_LEVELS_SPEC() - nid_to_dep::<C>(nid),
{
    lemma_nid_to_dep_up_bound::<C>(nid);
}

/// A valid node's descendant's id is less than or equal to the total size.
pub proof fn lemma_valid_level_to_node<C: PageTableConfig>(nid: NodeId)
    requires
        valid_nid::<C>(nid),
    ensures
        nid + tree_size_spec::<C>(nid_to_level::<C>(nid) - 1) <= total_size::<C>(),
{
    let trace = nid_to_trace::<C>(nid);
    lemma_nid_to_trace_sound::<C>(nid);
    reveal(trace_to_nid_rec);
    lemma_trace_to_nid_inner::<C>(trace);
    lemma_trace_to_nid_upperbound_spec::<C>(trace.len());
}

/// A valid node's subtree size is at least 1.
pub proof fn lemma_sub_tree_size_lower_bound<C: PageTableConfig>(nid: NodeId)
    requires
        valid_nid::<C>(nid),
    ensures
        sub_tree_size::<C>(nid) >= 1,
{
    lemma_nid_to_trace_sound::<C>(nid);
}

/// A valid node plus its subtree size is less than or equal to the total size.
pub broadcast proof fn lemma_next_outside_subtree_bounded<C: PageTableConfig>(nid: NodeId)
    requires
        valid_nid::<C>(nid),
    ensures
        nid < #[trigger] next_outside_subtree::<C>(nid) <= total_size::<C>(),
{
    lemma_valid_level_to_node::<C>(nid);
    lemma_sub_tree_size_lower_bound::<C>(nid);
}

/// A node is in its own subtree.
pub proof fn lemma_in_subtree_self<C: PageTableConfig>(nid: NodeId)
    requires
        valid_nid::<C>(nid),
    ensures
        in_subtree::<C>(nid, nid),
{
}

/// A child is in the subtree of its parent.
pub proof fn lemma_is_child_implies_in_subtree<C: PageTableConfig>(pa: NodeId, ch: NodeId)
    requires
        is_child::<C>(pa, ch),
        valid_nid::<C>(ch),
    ensures
        in_subtree::<C>(pa, ch),
        nid_to_dep::<C>(pa) + 1 == nid_to_dep::<C>(ch),
{
    C::lemma_consts_properties();
}

pub proof fn lemma_is_child_bound<C: PageTableConfig>(pa: NodeId, ch: NodeId)
    requires
        valid_nid::<C>(pa),
        valid_nid::<C>(ch),
        is_child::<C>(pa, ch),
    ensures
        next_outside_subtree::<C>(ch) <= next_outside_subtree::<C>(pa),
{
    broadcast use {lemma_nid_to_trace_sound, lemma_trace_to_nid_sound};

    let dep_pa = nid_to_dep::<C>(pa);
    let sz_pa = sub_tree_size::<C>(pa);
    let sz_ch = sub_tree_size::<C>(ch);
    let trace_pa = nid_to_trace::<C>(pa);
    let trace_ch = nid_to_trace::<C>(ch);
    lemma_is_child_implies_in_subtree::<C>(pa, ch);

    assert((ch as int) + (sz_ch as int) <= (pa as int) + (sz_pa as int)) by {
        if ch == pa {
        } else {
            let offset = trace_ch.last();
            let pa_level = dep_to_level::<C>(dep_pa);
            let sz = tree_size_spec::<C>(pa_level - 2);
            lemma_child_nid_from_trace_offset_sound::<C>(trace_pa, offset);
            assert(ch == pa + offset * sz + 1) by {
                assert(trace_ch.drop_last() == trace_pa);
                assert(trace_ch.last() == offset) by {
                    assert(trace_ch == trace_pa.push(offset));
                    assert(trace_to_nid::<C>(trace_ch) == trace_to_nid::<C>(trace_pa.push(offset)));
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

pub proof fn lemma_is_child_implies_same_pa<C: PageTableConfig>(
    pa1: NodeId,
    pa2: NodeId,
    ch: NodeId,
)
    requires
        valid_nid::<C>(pa1),
        valid_nid::<C>(pa2),
        valid_nid::<C>(ch),
        is_child::<C>(pa1, ch),
        is_child::<C>(pa2, ch),
    ensures
        pa1 == pa2,
{
    admit();
}

// If 'nd' is in the subtree of 'rt', then `next_outside_subtree(nd)` (the next node id outside the subtree of 'nd') is less than or equal to
// `next_outside_subtree(rt)`.
pub proof fn lemma_in_subtree_bounded<C: PageTableConfig>(rt: NodeId, nd: NodeId)
    requires
        valid_nid::<C>(rt),
        in_subtree::<C>(rt, nd),
    ensures
        next_outside_subtree::<C>(nd) <= next_outside_subtree::<C>(rt),
    decreases nid_to_trace::<C>(nd).len() - nid_to_trace::<C>(rt).len(),
{
    broadcast use lemma_nid_to_trace_sound;

    if rt == nd {
    } else {
        // Induction step: use `lemma_is_child_bound` to prove the relationship between `nd` and its parent,
        // and then use the induction hypothesis between `rt` and `nd`'s parent.
        let parent = get_parent::<C>(nd);
        assert(nid_to_trace::<C>(rt).len() < nid_to_trace::<C>(nd).len()) by {
            if nid_to_trace::<C>(rt).len() == nid_to_trace::<C>(nd).len() {
                assert(nid_to_trace::<C>(rt) == nid_to_trace::<C>(nd));
                assert(rt == nd);
            }
        }
        lemma_get_parent_sound::<C>(nd);
        assert(nid_to_trace::<C>(rt).is_prefix_of(nid_to_trace::<C>(parent)));
        lemma_in_subtree_bounded::<C>(rt, parent);
        lemma_is_child_bound::<C>(parent, nd);
    }
}

/// `get_parent` correctly returns the parent of a node.
/// The result indeed satisfies `is_child(get_parent(nid), nid)`.
pub broadcast proof fn lemma_get_parent_sound<C: PageTableConfig>(nid: NodeId)
    requires
        valid_nid::<C>(nid),
        nid != root_id::<C>(),
    ensures
        valid_nid::<C>(#[trigger] get_parent::<C>(nid)),
        is_child::<C>(get_parent::<C>(nid), nid),
{
    broadcast use {lemma_nid_to_trace_sound, lemma_trace_to_nid_sound};

}

/// `get_offset` returns the offset in a correct range.
pub broadcast proof fn lemma_get_offset_sound<C: PageTableConfig>(nid: NodeId)
    requires
        valid_nid::<C>(nid),
        nid != root_id::<C>(),
    ensures
        0 <= #[trigger] get_offset::<C>(nid) < 512,
{
    lemma_nid_to_trace_sound::<C>(nid);
}

pub proof fn lemma_parent_offset_uniqueness<C: PageTableConfig>(nid1: NodeId, nid2: NodeId)
    requires
        valid_nid::<C>(nid1),
        valid_nid::<C>(nid2),
        nid1 != root_id::<C>(),
        nid2 != root_id::<C>(),
        nid1 != nid2,
    ensures
        !(get_parent::<C>(nid1) == get_parent::<C>(nid2) && get_offset::<C>(nid1) == get_offset::<
            C,
        >(nid2)),
{
    broadcast use {lemma_nid_to_trace_sound, lemma_trace_to_nid_sound};

    if get_parent::<C>(nid1) == get_parent::<C>(nid2) && get_offset::<C>(nid1) == get_offset::<C>(
        nid2,
    ) {
        let trace1 = nid_to_trace::<C>(nid1);
        let trace2 = nid_to_trace::<C>(nid2);

        lemma_nid_to_trace_left_inverse::<C>();

        assert(trace_to_nid::<C>(trace1.drop_last()) == trace_to_nid::<C>(trace2.drop_last()));

        assert(trace1 == trace2) by {
            assert(trace2 == trace1.drop_last().push(trace1.last()));
        };

        // But since nid_to_trace is bijective (left inverse to trace_to_nid)
        // and trace1 == trace2, we must have nid1 == nid2
        lemma_nid_to_trace_right_inverse::<C>();
        assert(nid1 == nid2);  // contradiction with nid1 != nid2
    }
}

/// `get_child` correctly returns the child of a node.
/// The result indeed satisfies `is_child(nid, get_child::<C>(nid, offset))`.
pub broadcast proof fn lemma_get_child_sound<C: PageTableConfig>(nid: NodeId, offset: nat)
    requires
        valid_nid::<C>(nid),
        nid_to_dep::<C>(nid) < C::NR_LEVELS_SPEC() - 1,
        0 <= offset < nr_subpage_per_huge::<C>(),
    ensures
        valid_nid::<C>(#[trigger] get_child::<C>(nid, offset)),
        nid == get_parent::<C>(get_child::<C>(nid, offset)),
        offset == get_offset::<C>(get_child::<C>(nid, offset)),
        is_child::<C>(nid, get_child::<C>(nid, offset)),
{
    assert(offset < 512) by {
        C::lemma_nr_subpage_per_huge_is_512();
    };
    lemma_nid_to_trace_sound::<C>(nid);
    lemma_trace_to_nid_sound::<C>(nid_to_trace::<C>(nid).push(offset));
    assert(nid_to_trace::<C>(nid).push(offset).drop_last() == nid_to_trace::<C>(nid));
}

pub proof fn lemma_leaf_get_child_wrong<C: PageTableConfig>(nid: NodeId, offset: nat)
    requires
        valid_nid::<C>(nid),
        nid_to_dep::<C>(nid) == C::NR_LEVELS_SPEC() - 1,
        0 <= offset < 512,
    ensures
        !valid_nid::<C>(get_child::<C>(nid, offset)),
{
    admit();
}

/// The valid nid set's cardinality is `total_size`.
pub proof fn lemma_valid_nid_set_cardinality<C: PageTableConfig>()
    ensures
        valid_nid_set::<C>().finite(),
        valid_nid_set::<C>().len() == total_size::<C>(),
{
    assert(valid_nid_set::<C>() == Set::new(|nid: nat| 0 <= nid < total_size::<C>()));
    lemma_nat_range_finite(0, total_size::<C>());
}

/// The valid trace set's cardinality is `total_size`.
pub proof fn lemma_valid_trace_set_cardinality<C: PageTableConfig>()
    ensures
        valid_trace_set::<C>().finite(),
        valid_trace_set::<C>().len() == total_size::<C>(),
{
    lemma_valid_nid_set_cardinality::<C>();
    lemma_nid_to_trace_bijective::<C>();
    lemma_bijective_cardinality(
        |nid| nid_to_trace::<C>(nid),
        valid_nid_set::<C>(),
        valid_trace_set::<C>(),
    );
}

/// `get_subtree_traces` returns a finite set of traces.
pub proof fn lemma_get_subtree_traces_finite<C: PageTableConfig>(trace: Seq<nat>)
    ensures
        get_subtree_traces::<C>(trace).finite(),
{
    lemma_valid_trace_set_cardinality::<C>();
}

/// `get_subtree_traces` contains the input trace.
pub proof fn lemma_get_subtree_traces_contains_self<C: PageTableConfig>(trace: Seq<nat>)
    requires
        valid_trace::<C>(trace),
    ensures
        get_subtree_traces::<C>(trace).contains(trace),
        get_subtree_traces::<C>(trace).len() > 0,
{
    lemma_get_subtree_traces_finite::<C>(trace);
    axiom_set_contains_len(get_subtree_traces::<C>(trace), trace);
}

/// `get_subtree_traces` is injective
pub proof fn lemma_get_subtree_traces_injective<C: PageTableConfig>()
    ensures
        injective_on(|trace| get_subtree_traces::<C>(trace), valid_trace_set::<C>()),
{
    assert forall|x, y|
        #![trigger get_subtree_traces::<C>(x), get_subtree_traces::<C>(y)]
        valid_trace_set::<C>().contains(x) && valid_trace_set::<C>().contains(y)
            && get_subtree_traces::<C>(x) == get_subtree_traces::<C>(y) implies x == y by {
        lemma_get_subtree_traces_contains_self::<C>(x);
        lemma_get_subtree_traces_contains_self::<C>(y);
    }

}

/// The cardinality of the subtree traces is equal to the tree size specification.
pub proof fn lemma_get_subtree_traces_cardinality<C: PageTableConfig>(trace: Seq<nat>)
    requires
        valid_trace::<C>(trace),
    ensures
        get_subtree_traces::<C>(trace).len() == tree_size_spec::<C>(
            C::NR_LEVELS_SPEC() - 1 - trace.len(),
        ),
    decreases C::NR_LEVELS_SPEC() - 1 - trace.len(),
{
    let subtree_trace_set = get_subtree_traces::<C>(trace);
    assert(subtree_trace_set.contains(trace));
    lemma_valid_trace_set_cardinality::<C>();
    if trace.len() == C::NR_LEVELS_SPEC() - 1 {
        assert(forall|subtree_trace| #[trigger]
            subtree_trace_set.contains(subtree_trace) ==> subtree_trace == trace);
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
        let trace_singleton_set = subtree_trace_set.filter(|child_trace: Seq<nat>| !f(child_trace));
        assert(trace_singleton_set.is_singleton()) by {
            assert(trace_singleton_set.contains(trace));
            assert forall|x, y|
                #![trigger trace_singleton_set.contains(x), trace_singleton_set.contains(y)]
                trace_singleton_set.contains(x) && trace_singleton_set.contains(y) implies x
                == y by {
                assert(x == trace);
                assert(y == trace);
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
            lemma_injective_map_cardinality(|offset| trace.push(offset), offset_set, offset_set);
        }
        assert(child_traces <= valid_trace_set::<C>());
        // The set of each child trace's subtree traces set
        let child_subtree_trace_set = child_traces.map(
            |child_trace| get_subtree_traces::<C>(child_trace),
        );
        // Use induction hypothesis here, prove that each child trace's subtree traces set has the size of tree with a
        // height of C::NR_LEVELS_SPEC() - 2 - trace.len()
        assert forall|child_trace| #[trigger]
            child_traces.contains(child_trace) implies get_subtree_traces::<C>(child_trace).len()
            == tree_size_spec::<C>(C::NR_LEVELS_SPEC() - 2 - trace.len()) by {
            lemma_get_subtree_traces_cardinality::<C>(child_trace);
        };
        assert(child_subtree_trace_set.len() == 512 && child_subtree_trace_set.finite()) by {
            lemma_get_subtree_traces_injective::<C>();
            lemma_injective_map_cardinality(
                |child_trace| get_subtree_traces::<C>(child_trace),
                valid_trace_set::<C>(),
                child_traces,
            );
        }

        // Show that the child traces are disjoint
        assert(pairwise_disjoint(child_subtree_trace_set));
        // Show that the flatten of the child_subtree_trace_set is equal to the child_trace_set
        assert(child_trace_set == child_subtree_trace_set.flatten()) by {
            assert forall|child_trace: Seq<nat>| #[trigger]
                child_trace_set.contains(child_trace) == child_subtree_trace_set.flatten().contains(
                    child_trace,
                ) by {
                if child_trace_set.contains(child_trace) {
                    assert(trace.is_prefix_of(child_trace));
                    let trace_child = child_trace.subrange(0, (trace.len() + 1) as int);
                    let offset = child_trace[trace.len() as int];
                    assert(trace_child == trace.push(offset));
                    assert(offset_set.contains(offset));
                    // Definition of flatten
                    assert(child_traces.contains(trace_child));
                    assert(child_subtree_trace_set.contains(get_subtree_traces::<C>(trace_child)));
                }
                if child_subtree_trace_set.flatten().contains(child_trace) {
                    let child_subtree_trace = choose|t: Set<Seq<nat>>|
                        child_subtree_trace_set.contains(t) && t.contains(child_trace);
                    let trace_child = choose|t: Seq<nat>| #[trigger]
                        child_traces.contains(t) && get_subtree_traces::<C>(t)
                            == child_subtree_trace;
                    assert(trace.is_prefix_of(trace_child));
                    assert(trace_child.is_prefix_of(child_trace));
                }
            }
        }

        assert(child_trace_set.len() == 512 * tree_size_spec::<C>(
            C::NR_LEVELS_SPEC() - 2 - trace.len(),
        )) by {
            lemma_flatten_cardinality_under_disjointness_same_length(
                child_subtree_trace_set,
                tree_size_spec::<C>(C::NR_LEVELS_SPEC() - 2 - trace.len()),
            );
        }
    }
}

/// The cardinality of nodes in subtree is `sub_tree_size`
pub proof fn lemma_in_subtree_cardinality<C: PageTableConfig>(nid: NodeId)
    requires
        valid_nid::<C>(nid),
    ensures
        valid_nid_set::<C>().filter(|id| in_subtree::<C>(nid, id)).len() == sub_tree_size::<C>(nid),
{
    broadcast use lemma_trace_to_nid_sound;

    let nid_trace = nid_to_trace::<C>(nid);
    let subtree_traces = get_subtree_traces::<C>(nid_trace);
    let subtree_ids = valid_nid_set::<C>().filter(|id| in_subtree::<C>(nid, id));
    lemma_nid_to_trace_sound::<C>(nid);
    lemma_valid_nid_set_cardinality::<C>();
    assert(subtree_traces.len() == sub_tree_size::<C>(nid) && subtree_traces.finite()) by {
        lemma_get_subtree_traces_cardinality::<C>(nid_trace);
        lemma_get_subtree_traces_finite::<C>(nid_trace);
    }
    assert(bijective_on(|id| nid_to_trace::<C>(id), subtree_ids, subtree_traces)) by {
        lemma_nid_to_trace_bijective::<C>();
        // Prove subtree_traces == subtree_ids.map(nid_to_trace)
        assert forall|trace| #[trigger]
            subtree_traces.contains(trace) == subtree_ids.map(|id| nid_to_trace::<C>(id)).contains(
                trace,
            ) by {
            if subtree_traces.contains(trace) {
                let trace_id = trace_to_nid::<C>(trace);
                assert(subtree_ids.contains(trace_id) && nid_to_trace::<C>(trace_id) == trace);
            }
        }
        assert(subtree_traces == subtree_ids.map(|id| nid_to_trace::<C>(id)));
    }
    lemma_bijective_cardinality(|id| nid_to_trace::<C>(id), subtree_ids, subtree_traces);
}

/// If a node id is in the subtree, than it falls in the range of [rt, next_outside_subtree(rt)).
proof fn lemma_in_subtree_implies_in_subtree_range<C: PageTableConfig>(rt: NodeId, nd: NodeId)
    requires
        valid_nid::<C>(rt),
        in_subtree::<C>(rt, nd),
    ensures
        in_subtree_range::<C>(rt, nd),
{
    broadcast use {lemma_nid_to_trace_sound, lemma_trace_to_nid_sound};

    assert(rt <= nd < next_outside_subtree::<C>(rt)) by {
        assert(next_outside_subtree::<C>(nd) <= next_outside_subtree::<C>(rt)) by {
            lemma_in_subtree_bounded::<C>(rt, nd);
        };
        assert(nd < next_outside_subtree::<C>(nd)) by {
            lemma_sub_tree_size_lower_bound::<C>(nd);
        };
        assert(rt <= nd) by {
            let rt_trace = nid_to_trace::<C>(rt);
            let nd_trace = nid_to_trace::<C>(nd);

            if rt_trace.len() == 0 {
            } else {
                if rt == nd {
                } else {
                    let suffix = nd_trace.subrange(rt_trace.len() as int, nd_trace.len() as int);

                    let cur_level = C::NR_LEVELS_SPEC() - 1 - rt_trace.len();
                    assert(valid_trace::<C>(suffix)) by {
                        assert(forall|i: int|
                            #![trigger suffix[i]]
                            0 <= i < suffix.len() ==> 0 <= suffix[i] < 512) by {
                            assert(forall|i: int|
                                #![trigger nd_trace[i + rt_trace.len()]]
                                0 <= i < suffix.len() ==> 0 <= nd_trace[i + rt_trace.len()] < 512);
                        }
                    }

                    // Apply trace_to_nid_rec_sound directly using our key insights:
                    // 1. rt = trace_to_nid(rt_trace)
                    // 2. nd = trace_to_nid(rt_trace.add(suffix))
                    // 3. Using lemma_trace_to_nid_rec_sound, we know:
                    //    cur_rt <= trace_to_nid_rec(trace, cur_rt, level)

                    assert(rt + tree_size_spec::<C>(cur_level) <= total_size::<C>()) by {
                        lemma_next_outside_subtree_bounded::<C>(rt);
                    }

                    assert(nd == trace_to_nid_rec::<C>(suffix, rt, cur_level)) by {
                        assert(rt_trace.add(suffix) == nd_trace) by {
                            assert(rt_trace.is_prefix_of(nd_trace));
                            assert(rt_trace == nd_trace.subrange(0, rt_trace.len() as int));
                        }

                        assert(nid_to_trace::<C>(nd) == rt_trace.add(suffix)) by {
                            assert(nid_to_trace::<C>(nd) == nd_trace);
                            assert(nd_trace == rt_trace.add(suffix));
                        }
                        lemma_nid_to_trace_bijective::<C>();

                        assert(trace_to_nid::<C>(nid_to_trace::<C>(nd)) == trace_to_nid::<C>(
                            rt_trace.add(suffix),
                        )) by {
                            lemma_nid_to_trace_right_inverse::<C>();
                        }
                        assert(nd == trace_to_nid::<C>(rt_trace.add(suffix)));

                        lemma_trace_to_nid_split::<C>(rt_trace, suffix, rt, cur_level);
                    }
                    assert(rt <= trace_to_nid_rec::<C>(suffix, rt, cur_level)) by {
                        lemma_trace_to_nid_rec_sound::<C>(suffix, rt, cur_level);
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
proof fn lemma_in_subtree_range_implies_in_subtree<C: PageTableConfig>(rt: NodeId, nd: NodeId)
    requires
        valid_nid::<C>(rt),
        rt <= nd < next_outside_subtree::<C>(rt),
    ensures
        in_subtree::<C>(rt, nd),
{
    // Showing every node id in the range is valid and the range is `sub_tree_size::<C>(rt)`
    let nid_set = Set::new(|nid: nat| rt <= nid < next_outside_subtree::<C>(rt));
    assert(nid_set.len() == sub_tree_size::<C>(rt) && nid_set.finite()) by {
        lemma_nat_range_finite(rt, next_outside_subtree::<C>(rt));
    }
    assert(nid_set == nid_set.filter(|id| valid_nid::<C>(id))) by {
        assert forall|id| #[trigger] nid_set.contains(id) implies valid_nid::<C>(id) by {
            lemma_next_outside_subtree_bounded::<C>(rt);
        }
    }
    assert(nid_set == valid_nid_set::<C>().filter(|id| rt <= id < next_outside_subtree::<C>(rt)));

    // Shhowing there are exactly `sub_tree_size(rt)` node ids that are in the subtree
    let child_set = valid_nid_set::<C>().filter(|id| in_subtree::<C>(rt, id));
    assert(child_set.len() == sub_tree_size::<C>(rt)) by {
        lemma_in_subtree_cardinality::<C>(rt);
    };
    // Every node id in the subtree falls in the range
    assert(child_set == child_set.filter(|id| rt <= id < next_outside_subtree::<C>(rt))) by {
        assert forall|id| #[trigger] child_set.contains(id) implies rt <= id
            < next_outside_subtree::<C>(rt) by {
            lemma_in_subtree_implies_in_subtree_range::<C>(rt, id);
        }
    }
    // So we can find exactly `sub_tree_size(rt)` node ids in the range that are in the subtree
    assert(child_set == nid_set.filter(|id| in_subtree::<C>(rt, id)));
    assert(nid_set.len() == nid_set.filter(|id| in_subtree::<C>(rt, id)).len());
    // Therefore, every node id in the range is in the subtree
    assert(nid_set == nid_set.filter(|id| in_subtree::<C>(rt, id))) by {
        lemma_filter_len_unchanged_implies_equal(nid_set, |id| in_subtree::<C>(rt, id));
    }
    assert(nid_set.contains(nd));
}

/// 'in_subtree' is equivalent to 'in_subtree_range' (nd in [rt, next_outside_subtree(rt)))
pub broadcast proof fn lemma_in_subtree_iff_in_subtree_range<C: PageTableConfig>(
    rt: NodeId,
    nd: NodeId,
)
    requires
        valid_nid::<C>(rt),
    ensures
        #![trigger in_subtree::<C>(rt, nd)]
        #![trigger in_subtree_range::<C>(rt, nd)]
        in_subtree::<C>(rt, nd) <==> in_subtree_range::<C>(rt, nd),
{
    if in_subtree::<C>(rt, nd) {
        lemma_in_subtree_implies_in_subtree_range::<C>(rt, nd);
    }
    if rt <= nd < next_outside_subtree::<C>(rt) {
        lemma_next_outside_subtree_bounded::<C>(rt);
        lemma_in_subtree_range_implies_in_subtree::<C>(rt, nd);
    }
}

/// If `ch` is a child of `pa`, `ch` is in the subtree of `rt`, and `rt` is not equal to `ch`,
/// then `pa` is in the subtree of `rt`.
pub proof fn lemma_child_in_subtree_implies_in_subtree<C: PageTableConfig>(
    rt: NodeId,
    pa: NodeId,
    ch: NodeId,
)
    requires
        valid_nid::<C>(rt),
        valid_nid::<C>(pa),
        in_subtree::<C>(rt, ch),
        is_child::<C>(pa, ch),
        rt != ch,
    ensures
        in_subtree::<C>(rt, pa),
{
    broadcast use {lemma_nid_to_trace_sound, lemma_trace_to_nid_sound};

    if (nid_to_trace::<C>(ch).len() == nid_to_trace::<C>(rt).len()) {
        assert(nid_to_trace::<C>(ch) == nid_to_trace::<C>(rt));
    }
}

/// Similar to `lemma_child_in_subtree_implies_in_subtree`, but for descendants.
pub proof fn lemma_decendant_in_subtree_implies_in_subtree<C: PageTableConfig>(
    rt: NodeId,
    anc: NodeId,
    dec: NodeId,
)
    requires
        valid_nid::<C>(rt),
        valid_nid::<C>(anc),
        in_subtree::<C>(rt, dec),
        in_subtree::<C>(anc, dec),
        nid_to_level::<C>(anc) < nid_to_level::<C>(rt),
    ensures
        in_subtree::<C>(rt, anc),
{
    broadcast use {lemma_nid_to_trace_sound, lemma_trace_to_nid_sound};

    let rt_trace = nid_to_trace::<C>(rt);
    let anc_trace = nid_to_trace::<C>(anc);
    let dec_trace = nid_to_trace::<C>(dec);

    assert(rt_trace.len() < anc_trace.len()) by {
        if rt_trace.len() == anc_trace.len() {
            assert(rt_trace == anc_trace);
            assert(rt == anc);
        }
    };
    assert(anc_trace.is_prefix_of(dec_trace));
    assert(rt_trace.is_prefix_of(dec_trace));

    assert(rt_trace.is_prefix_of(anc_trace));
}

/// If `pa` is not in the subtree of `rt`, `ch` is a child of `pa`, and `rt` is not equal to `ch`,
/// then `ch` is not in the subtree of `rt`.
pub proof fn lemma_not_in_subtree_range_implies_child_not_in_subtree_range<C: PageTableConfig>(
    rt: NodeId,
    pa: NodeId,
    ch: NodeId,
)
    requires
        valid_nid::<C>(rt),
        valid_nid::<C>(pa),
        is_child::<C>(pa, ch),
        rt != ch,
        !in_subtree_range::<C>(rt, pa),
    ensures
        !in_subtree_range::<C>(rt, ch),
{
    broadcast use lemma_in_subtree_iff_in_subtree_range;

    if in_subtree_range::<C>(rt, ch) {
        lemma_next_outside_subtree_bounded::<C>(rt);
        lemma_child_in_subtree_implies_in_subtree::<C>(rt, pa, ch);
    }
}

/// If `pa` is in the subtree of `rt`, `ch` is a child of `pa`, then `ch` is in the subtree of `rt`.
pub proof fn lemma_in_subtree_is_child_in_subtree<C: PageTableConfig>(
    rt: NodeId,
    nd: NodeId,
    ch: NodeId,
)
    requires
        in_subtree::<C>(rt, nd),
        valid_nid::<C>(ch),
        is_child::<C>(nd, ch),
    ensures
        in_subtree::<C>(rt, ch),
{
}

/// If `pa` is the parent of `ch`, then `pa` is less than `ch`.
pub broadcast proof fn lemma_is_child_nid_increasing<C: PageTableConfig>(pa: NodeId, ch: NodeId)
    requires
        valid_nid::<C>(pa),
        valid_nid::<C>(ch),
        #[trigger] is_child::<C>(pa, ch),
    ensures
        pa < ch,
{
    lemma_is_child_implies_in_subtree::<C>(pa, ch);
    lemma_in_subtree_iff_in_subtree_range::<C>(pa, ch);
}

pub proof fn lemma_brother_nid_increasing<C: PageTableConfig>(
    pa: NodeId,
    offset1: nat,
    offset2: nat,
)
    requires
        valid_nid::<C>(pa),
        is_not_leaf::<C>(pa),
        0 <= offset1 < offset2 < 512,
    ensures
        get_child::<C>(pa, offset1) < get_child::<C>(pa, offset2),
{
    lemma_parent_child_algebraic_relation::<C>(pa, offset1);
    lemma_parent_child_algebraic_relation::<C>(pa, offset2);
    let tree_size = tree_size_spec::<C>(nid_to_level::<C>(pa) - 2);
    assert(offset1 * tree_size < offset2 * tree_size) by (nonlinear_arith)
        requires
            0 <= offset1 < offset2,
            tree_size > 0,
    ;
}

pub proof fn lemma_is_child_level_relation<C: PageTableConfig>(pa: NodeId, ch: NodeId)
    requires
        valid_nid::<C>(pa),
        valid_nid::<C>(ch),
        is_child::<C>(pa, ch),
    ensures
        nid_to_level::<C>(pa) == nid_to_level::<C>(ch) + 1,
{
    lemma_is_child_implies_in_subtree::<C>(pa, ch);
    lemma_level_dep_relation::<C>(pa);
    lemma_level_dep_relation::<C>(ch);
}

pub proof fn lemma_in_subtree_level_relation<C: PageTableConfig>(rt: NodeId, nd: NodeId)
    requires
        valid_nid::<C>(rt),
        valid_nid::<C>(nd),
        in_subtree::<C>(rt, nd),
        rt != nd,
    ensures
        nid_to_level::<C>(nd) < nid_to_level::<C>(rt),
{
    broadcast use lemma_nid_to_trace_sound;

    let rt_trace = nid_to_trace::<C>(rt);
    let nd_trace = nid_to_trace::<C>(nd);

    assert(rt_trace.len() < nd_trace.len()) by {
        if rt_trace.len() > nd_trace.len() {
            assert(!(rt_trace.is_prefix_of(nd_trace)));
        } else if rt_trace.len() == nd_trace.len() {
            assert(rt_trace == nd_trace);
            assert(rt == nd);
        }
    };
    lemma_level_dep_relation::<C>(rt);
    lemma_level_dep_relation::<C>(nd);
}

proof fn lemma_trace_to_nid_rec_push<C: PageTableConfig>(
    trace: Seq<nat>,
    offset: nat,
    rt: NodeId,
    level: int,
)
    requires
        valid_trace::<C>(trace),
        trace.len() < level,
    ensures
        trace_to_nid_rec::<C>(trace.push(offset), rt, level) == trace_to_nid_rec::<C>(
            trace,
            rt,
            level,
        ) + offset * tree_size_spec::<C>(level - trace.len() - 1) + 1,
    decreases trace.len(),
{
    reveal(trace_to_nid_rec);
    let pushed_trace = trace.push(offset);
    lemma_trace_to_nid_rec_inductive::<C>(pushed_trace, rt, level);
    if trace.len() == 0 {
        assert(pushed_trace.drop_first() == Seq::<nat>::empty());
    } else {
        let new_rt = rt + trace[0] * tree_size_spec::<C>(level - 1) + 1;
        lemma_trace_to_nid_rec_push::<C>(trace.drop_first(), offset, new_rt, level - 1);
        assert(pushed_trace.drop_first() == trace.drop_first().push(offset));
    }
}

pub proof fn lemma_trace_to_nid_push<C: PageTableConfig>(trace: Seq<nat>, offset: nat)
    requires
        valid_trace::<C>(trace),
        trace.len() < C::NR_LEVELS_SPEC() - 1,
    ensures
        trace_to_nid::<C>(trace.push(offset)) == trace_to_nid::<C>(trace) + offset
            * tree_size_spec::<C>(C::NR_LEVELS_SPEC() - 1 - trace.len() - 1) + 1,
{
    lemma_trace_to_nid_rec_push::<C>(trace, offset, 0, C::NR_LEVELS_SPEC() - 1);
}

pub proof fn lemma_parent_child_algebraic_relation<C: PageTableConfig>(nid: NodeId, offset: nat)
    requires
        valid_nid::<C>(nid),
        is_not_leaf::<C>(nid),
        0 <= offset < 512,
    ensures
        get_child::<C>(nid, offset) == nid + offset * tree_size_spec::<C>(
            nid_to_level::<C>(nid) - 2,
        ) + 1,
{
    lemma_nid_to_trace_sound::<C>(nid);
    lemma_trace_to_nid_push::<C>(nid_to_trace::<C>(nid), offset);
}

pub proof fn lemma_brother_algebraic_relation<C: PageTableConfig>(nid: NodeId, offset: nat)
    requires
        valid_nid::<C>(nid),
        is_not_leaf::<C>(nid),
        0 <= offset < 511,
    ensures
        next_outside_subtree::<C>(get_child::<C>(nid, offset)) == get_child::<C>(nid, offset + 1),
{
    C::lemma_nr_subpage_per_huge_is_512();
    lemma_parent_child_algebraic_relation::<C>(nid, offset);
    lemma_parent_child_algebraic_relation::<C>(nid, offset + 1);
    lemma_get_child_sound::<C>(nid, offset);
    lemma_get_child_sound::<C>(nid, offset + 1);
    let tree_size = tree_size_spec::<C>(nid_to_level::<C>(nid) - 2);
    assert(offset * tree_size + tree_size == (offset + 1) * tree_size) by (nonlinear_arith);
}

pub proof fn lemma_brother_sub_tree_range_disjoint<C: PageTableConfig>(
    nid: NodeId,
    offset1: nat,
    offset2: nat,
)
    requires
        valid_nid::<C>(nid),
        is_not_leaf::<C>(nid),
        0 <= offset1 < offset2 < 512,
    ensures
        next_outside_subtree::<C>(get_child::<C>(nid, offset1)) <= get_child::<C>(nid, offset2),
    decreases offset2 - offset1,
{
    assert(511 < nr_subpage_per_huge::<C>()) by {
        C::lemma_nr_subpage_per_huge_is_512();
    };

    if offset2 == offset1 + 1 {
        lemma_brother_algebraic_relation::<C>(nid, offset1);
    } else {
        lemma_brother_sub_tree_range_disjoint::<C>(nid, (offset1 + 1) as nat, offset2);
        lemma_brother_algebraic_relation::<C>(nid, offset1);
        let ch = get_child::<C>(nid, (offset1 + 1) as nat);
        assert(ch < next_outside_subtree::<C>(ch)) by {
            lemma_get_child_sound::<C>(nid, (offset1 + 1) as nat);
            lemma_sub_tree_size_lower_bound::<C>(ch);
        };
    }
}

pub proof fn lemma_last_child_next_outside_subtree<C: PageTableConfig>(nid: NodeId)
    requires
        valid_nid::<C>(nid),
        is_not_leaf::<C>(nid),
    ensures
        next_outside_subtree::<C>(get_child::<C>(nid, 511)) == next_outside_subtree::<C>(nid),
{
    assert(511 < nr_subpage_per_huge::<C>()) by {
        C::lemma_nr_subpage_per_huge_is_512();
    }
    lemma_parent_child_algebraic_relation::<C>(nid, 511);
    lemma_get_child_sound::<C>(nid, 511);
}

pub proof fn lemma_get_parent_get_offset_sound<C: PageTableConfig>(nid: NodeId)
    requires
        valid_nid::<C>(nid),
        nid != root_id::<C>(),
    ensures
        get_child::<C>(get_parent::<C>(nid), get_offset::<C>(nid)) == nid,
{
    broadcast use {lemma_nid_to_trace_sound, lemma_trace_to_nid_sound};

    let trace = nid_to_trace::<C>(nid);
    assert(trace.drop_last().push(trace.last()) == trace);
}

pub proof fn lemma_brothers_have_different_offset<C: PageTableConfig>(nid1: NodeId, nid2: NodeId)
    requires
        valid_nid::<C>(nid1),
        nid1 != root_id::<C>(),
        valid_nid::<C>(nid2),
        nid2 != root_id::<C>(),
        nid1 != nid2,
        get_parent::<C>(nid1) == get_parent::<C>(nid2),
    ensures
        get_offset::<C>(nid1) != get_offset::<C>(nid2),
{
    lemma_get_parent_get_offset_sound::<C>(nid1);
    lemma_get_parent_get_offset_sound::<C>(nid2);
}

pub proof fn lemma_get_ancestor_at_level_implies_in_subtree<C: PageTableConfig>(
    nid: NodeId,
    level: nat,
)
    requires
        valid_nid::<C>(nid),
        nid_to_level::<C>(nid) <= level <= C::NR_LEVELS_SPEC(),
    ensures
        in_subtree::<C>(get_ancestor_at_level::<C>(nid, level), nid),
{
    assert(1 <= nid_to_level::<C>(nid)) by {
        lemma_nid_to_dep_up_bound::<C>(nid);
    };

    let nid_trace = nid_to_trace::<C>(nid);
    assert(valid_trace::<C>(nid_trace)) by {
        lemma_nid_to_trace_sound::<C>(nid);
    };
    let dep = level_to_dep::<C>(level);
    assert(0 <= dep as int <= nid_trace.len() as int) by {
        lemma_level_dep_relation::<C>(nid);
    };
    let ancestor_trace = nid_trace.subrange(0, dep as int);
    assert(valid_trace::<C>(ancestor_trace));
    let anc = trace_to_nid::<C>(ancestor_trace);
    assert(valid_nid::<C>(anc)) by {
        lemma_trace_to_nid_sound::<C>(ancestor_trace);
    };
    assert(get_ancestor_at_level::<C>(nid, level) == anc);
    assert(in_subtree::<C>(anc, nid)) by {
        assert(ancestor_trace =~= nid_to_trace::<C>(anc)) by {
            lemma_trace_to_nid_sound::<C>(ancestor_trace);
        };
        assert(ancestor_trace.is_prefix_of(nid_trace));
    };
}

pub proof fn lemma_get_ancestor_at_level_uniqueness<C: PageTableConfig>(nid: NodeId, level: nat)
    requires
        valid_nid::<C>(nid),
        nid_to_level::<C>(nid) <= level <= C::NR_LEVELS_SPEC(),
    ensures
        forall|anc: NodeId|
            {
                &&& #[trigger] valid_nid::<C>(anc)
                &&& #[trigger] nid_to_level::<C>(anc) == level
                &&& #[trigger] in_subtree::<C>(anc, nid)
            } ==> anc == #[trigger] get_ancestor_at_level::<C>(nid, level),
{
    assert forall|anc: NodeId|
        {
            &&& #[trigger] valid_nid::<C>(anc)
            &&& #[trigger] nid_to_level::<C>(anc) == level
            &&& #[trigger] in_subtree::<C>(anc, nid)
        } implies anc == get_ancestor_at_level::<C>(nid, level) by {
        let nid_trace = nid_to_trace::<C>(nid);
        lemma_nid_to_trace_sound::<C>(nid);
        let dep = level_to_dep::<C>(level);
        let ancestor_trace = nid_trace.subrange(0, dep as int);
        let expected_anc = trace_to_nid::<C>(ancestor_trace);

        lemma_nid_to_trace_sound::<C>(anc);
        let anc_trace = nid_to_trace::<C>(anc);

        assert(ancestor_trace =~= anc_trace) by {
            assert(ancestor_trace.is_prefix_of(nid_trace));
            assert(anc_trace.is_prefix_of(nid_trace));
            assert(ancestor_trace.len() == anc_trace.len());
        };
        lemma_trace_to_nid_sound::<C>(ancestor_trace);
        assert(expected_anc == anc);
    };
}

pub proof fn lemma_in_subtree_implies_in_subtree_of_one_child<C: PageTableConfig>(
    nid1: NodeId,
    nid2: NodeId,
)
    requires
        valid_nid::<C>(nid1),
        valid_nid::<C>(nid2),
        in_subtree::<C>(nid1, nid2),
        nid1 != nid2,
    ensures
        exists|offset: nat|
            #![trigger get_child::<C>(nid1, offset)]
            0 <= offset < nr_subpage_per_huge::<C>() && in_subtree::<C>(
                get_child::<C>(nid1, offset),
                nid2,
            ),
{
    assert(is_not_leaf::<C>(nid1)) by {
        admit();
    };
    admit();
}

} // verus!
