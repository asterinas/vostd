use std::{io::Write, path, result};

use vstd::{prelude::*, seq::*};
use vstd_extra::{ghost_tree::Node, seq_extra::*};

use crate::spec::{common::*, utils::*};

verus! {

pub open spec fn wf_tree_path(path: Seq<NodeId>) -> bool {
    if path.len() == 0 {
        true
    } else {
        &&& path[0] == NodeHelper::root_id()
        &&& forall|i: int|
            1 <= i < path.len() ==> NodeHelper::is_child(#[trigger] path[i - 1], path[i])
        &&& path.all(|nid| NodeHelper::valid_nid(nid))
    }
}

pub proof fn lemma_wf_tree_path_inc(path: Seq<NodeId>, nid: NodeId)
    requires
        wf_tree_path(path),
        NodeHelper::valid_nid(nid),
        path.len() > 0 ==> NodeHelper::is_child(path.last(), nid),
        path.len() == 0 ==> nid == NodeHelper::root_id(),
    ensures
        wf_tree_path(path.push(nid)),
{
}

} // verus!
verus! {

broadcast use {
    vstd_extra::seq_extra::group_forall_seq_lemmas,
    crate::spec::utils::group_node_helper_lemmas,
};

pub proof fn lemma_wf_tree_path_nid_increasing(path: Seq<NodeId>)
    requires
        wf_tree_path(path),
    ensures
        forall|i: int, j: int|
            #![trigger path[i],path[j]]
            0 <= i < j < path.len() ==> path[i] < path[j],
    decreases path.len(),
{
    if path.len() == 0 {
    } else if path.len() == 1 {
    } else {
        assert forall|i: int, j: int| 0 <= i < j < path.len() implies path[i] < path[j] by {
            lemma_wf_tree_path_nid_increasing(path.drop_last());
            assert(path[i] == path.drop_last()[i]);
            if j < path.len() - 1 {
                assert(path[j] == path.drop_last()[j]);
            } else {
                assert(path[j] == path.last());
                NodeHelper::lemma_is_child_nid_increasing(path.drop_last().last(), path[j]);
            }
        }
    }
}

pub proof fn lemma_wf_tree_path_inversion(path: Seq<NodeId>)
    requires
        wf_tree_path(path),
    ensures
        path.len() > 0 ==> {
            &&& path[0] == NodeHelper::root_id()
            &&& wf_tree_path(path.drop_last())
            &&& !path.drop_last().contains(path.last())
        },
{
    if path.len() == 0 {
    } else {
        lemma_wf_tree_path_nid_increasing(path);
    }
}

pub proof fn lemma_wf_tree_path_push_inversion(path: Seq<NodeId>, nid: NodeId)
    requires
        wf_tree_path(path.push(nid)),
    ensures
        wf_tree_path(path),
        path.len() > 0 ==> NodeHelper::is_child(path.last(), nid),
        !path.contains(nid),
{
    lemma_wf_tree_path_inversion(path.push(nid));
    if (path.len() > 0) {
        assert(path.push(nid).drop_last() =~= path);
    }
}

pub proof fn lemma_wf_tree_path_nid_to_trace_len(path: Seq<NodeId>)
    requires
        wf_tree_path(path),
    ensures
        forall_seq(path, |i: int, nid: NodeId| NodeHelper::nid_to_trace(nid).len() == i),
    decreases path.len(),
{
    if path.len() == 0 {
    } else if path.len() == 1 {
    } else {
        let last = path.last();
        let rest_last = path.drop_last().last();
        lemma_wf_tree_path_nid_to_trace_len(path.drop_last());
        assert(NodeHelper::nid_to_trace(rest_last).len() + 1 == NodeHelper::nid_to_trace(
            last,
        ).len()) by { NodeHelper::lemma_is_child_implies_in_subtree(rest_last, last) };

    }
}

pub proof fn lemma_wf_tree_path_nid_index(path: Seq<NodeId>, nid: NodeId)
    requires
        wf_tree_path(path),
        path.contains(nid),
    ensures
        path[NodeHelper::nid_to_trace(nid).len() as int] == nid,
        NodeHelper::nid_to_trace(nid).len() < path.len(),
{
    lemma_wf_tree_path_nid_to_trace_len(path);
}

pub proof fn lemma_wf_tree_path_in_subtree_range(path: Seq<NodeId>)
    requires
        wf_tree_path(path),
    ensures
        forall|i: int, j: int|
            0 <= i <= j < path.len() ==> #[trigger] NodeHelper::in_subtree_range(path[i], path[j]),
    decreases path.len(),
{
    if path.len() == 0 {
    } else if path.len() == 1 {
    } else {
        let last = path.last();
        let rest = path.drop_last();
        let rest_last = rest.last();
        assert forall|i: int, j: int|
            #![trigger path[i],path[j]]
            0 <= i <= j < path.len() implies NodeHelper::in_subtree_range(path[i], path[j]) by {
            lemma_wf_tree_path_in_subtree_range(rest);
            if j < rest.len() {
                assert(path[i] == rest[i]);
                assert(path[j] == rest[j]);
            } else {
                assert(path[j] == last);
                if (i == j) {
                } else {
                    assert(path[i] == rest[i]);
                    NodeHelper::lemma_in_subtree_is_child_in_subtree(path[i], rest_last, last);
                }
            }
        }
    }
}

pub proof fn lemma_wf_tree_path_contains_descendant_implies_contains_ancestor(
    path: Seq<NodeId>,
    ancestor: NodeId,
    descendant: NodeId,
)
    requires
        wf_tree_path(path),
        NodeHelper::valid_nid(ancestor),
        NodeHelper::in_subtree(ancestor, descendant),
        path.contains(descendant),
    ensures
        path.contains(ancestor),
{
    let descendant_path = NodeHelper::nid_to_trace(descendant);
    let ancestor_path = NodeHelper::nid_to_trace(ancestor);
    let descendant_dep = descendant_path.len() as int;
    let ancestor_dep = ancestor_path.len() as int;
    let ancestor_in_path = path[ancestor_dep];
    let ancestor_in_path_path = NodeHelper::nid_to_trace(ancestor_in_path);

    lemma_wf_tree_path_nid_index(path, descendant);
    lemma_wf_tree_path_nid_index(path, ancestor_in_path);

    assert(NodeHelper::in_subtree(ancestor_in_path, descendant)) by {
        lemma_wf_tree_path_in_subtree_range(path);
    }
    assert(ancestor_in_path_path.len() == ancestor_dep) by {
        lemma_wf_tree_path_nid_to_trace_len(path);
    }
    assert(ancestor_path =~= ancestor_in_path_path);
    assert(ancestor == ancestor_in_path);
}

} // verus!
