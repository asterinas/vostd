use std::{io::Write, path, result};

use vstd::{prelude::*, seq::*};
use vstd_extra::{ghost_tree::Node, seq_extra::*};

use crate::spec::{common::NodeId, node_helper};

use crate::mm::page_table::PageTableConfig;

verus! {

pub open spec fn wf_tree_path<C: PageTableConfig>(path: Seq<NodeId>) -> bool {
    if path.len() == 0 {
        true
    } else {
        &&& path[0] == node_helper::root_id::<C>()
        &&& forall|i: int|
            1 <= i < path.len() ==> node_helper::is_child::<C>(#[trigger] path[i - 1], path[i])
        &&& path.all(|nid| node_helper::valid_nid::<C>(nid))
    }
}

pub proof fn lemma_wf_tree_path_inc<C: PageTableConfig>(path: Seq<NodeId>, nid: NodeId)
    requires
        wf_tree_path::<C>(path),
        node_helper::valid_nid::<C>(nid),
        path.len() > 0 ==> node_helper::is_child::<C>(path.last(), nid),
        path.len() == 0 ==> nid == node_helper::root_id::<C>(),
    ensures
        wf_tree_path::<C>(path.push(nid)),
{
}

} // verus!
verus! {

broadcast use {
    vstd_extra::seq_extra::group_forall_seq_lemmas,
    crate::spec::node_helper::group_node_helper_lemmas,
};

pub proof fn lemma_wf_tree_path_nid_increasing<C: PageTableConfig>(path: Seq<NodeId>)
    requires
        wf_tree_path::<C>(path),
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
            lemma_wf_tree_path_nid_increasing::<C>(path.drop_last());
            assert(path[i] == path.drop_last()[i]);
            if j < path.len() - 1 {
                assert(path[j] == path.drop_last()[j]);
            } else {
                assert(path[j] == path.last());
                node_helper::lemma_is_child_nid_increasing::<C>(path.drop_last().last(), path[j]);
            }
        }
    }
}

pub proof fn lemma_wf_tree_path_inversion<C: PageTableConfig>(path: Seq<NodeId>)
    requires
        wf_tree_path::<C>(path),
    ensures
        path.len() > 0 ==> {
            &&& path[0] == node_helper::root_id::<C>()
            &&& wf_tree_path::<C>(path.drop_last())
            &&& !path.drop_last().contains(path.last())
        },
{
    if path.len() == 0 {
    } else {
        lemma_wf_tree_path_nid_increasing::<C>(path);
    }
}

pub proof fn lemma_wf_tree_path_push_inversion<C: PageTableConfig>(path: Seq<NodeId>, nid: NodeId)
    requires
        wf_tree_path::<C>(path.push(nid)),
    ensures
        wf_tree_path::<C>(path),
        path.len() > 0 ==> node_helper::is_child::<C>(path.last(), nid),
        !path.contains(nid),
{
    lemma_wf_tree_path_inversion::<C>(path.push(nid));
    if (path.len() > 0) {
        assert(path.push(nid).drop_last() =~= path);
    }
}

pub proof fn lemma_wf_tree_path_nid_to_trace_len<C: PageTableConfig>(path: Seq<NodeId>)
    requires
        wf_tree_path::<C>(path),
    ensures
        forall_seq(path, |i: int, nid: NodeId| node_helper::nid_to_trace::<C>(nid).len() == i),
    decreases path.len(),
{
    if path.len() == 0 {
    } else if path.len() == 1 {
    } else {
        let last = path.last();
        let rest_last = path.drop_last().last();
        lemma_wf_tree_path_nid_to_trace_len::<C>(path.drop_last());
        assert(node_helper::nid_to_trace::<C>(rest_last).len() + 1 == node_helper::nid_to_trace::<C>(
            last,
        ).len()) by { node_helper::lemma_is_child_implies_in_subtree::<C>(rest_last, last) };

    }
}

pub proof fn lemma_wf_tree_path_nid_index<C: PageTableConfig>(path: Seq<NodeId>, nid: NodeId)
    requires
        wf_tree_path::<C>(path),
        path.contains(nid),
    ensures
        path[node_helper::nid_to_trace::<C>(nid).len() as int] == nid,
        node_helper::nid_to_trace::<C>(nid).len() < path.len(),
{
    lemma_wf_tree_path_nid_to_trace_len::<C>(path);
}

pub proof fn lemma_wf_tree_path_in_subtree_range<C: PageTableConfig>(path: Seq<NodeId>)
    requires
        wf_tree_path::<C>(path),
    ensures
        forall|i: int, j: int|
            0 <= i <= j < path.len() ==> #[trigger] node_helper::in_subtree_range::<C>(path[i], path[j]),
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
            0 <= i <= j < path.len() implies node_helper::in_subtree_range::<C>(path[i], path[j]) by {
            lemma_wf_tree_path_in_subtree_range::<C>(rest);
            if j < rest.len() {
                assert(path[i] == rest[i]);
                assert(path[j] == rest[j]);
            } else {
                assert(path[j] == last);
                if (i == j) {
                } else {
                    assert(path[i] == rest[i]);
                    node_helper::lemma_in_subtree_is_child_in_subtree::<C>(path[i], rest_last, last);
                }
            }
        }
    }
}

pub proof fn lemma_wf_tree_path_contains_descendant_implies_contains_ancestor<C: PageTableConfig>(
    path: Seq<NodeId>,
    ancestor: NodeId,
    descendant: NodeId,
)
    requires
        wf_tree_path::<C>(path),
        node_helper::valid_nid::<C>(ancestor),
        node_helper::in_subtree::<C>(ancestor, descendant),
        path.contains(descendant),
    ensures
        path.contains(ancestor),
{
    let descendant_path = node_helper::nid_to_trace::<C>(descendant);
    let ancestor_path = node_helper::nid_to_trace::<C>(ancestor);
    let descendant_dep = descendant_path.len() as int;
    let ancestor_dep = ancestor_path.len() as int;
    let ancestor_in_path = path[ancestor_dep];
    let ancestor_in_path_path = node_helper::nid_to_trace::<C>(ancestor_in_path);

    lemma_wf_tree_path_nid_index::<C>(path, descendant);
    lemma_wf_tree_path_nid_index::<C>(path, ancestor_in_path);

    assert(node_helper::in_subtree::<C>(ancestor_in_path, descendant)) by {
        lemma_wf_tree_path_in_subtree_range::<C>(path);
    }
    assert(ancestor_in_path_path.len() == ancestor_dep) by {
        lemma_wf_tree_path_nid_to_trace_len::<C>(path);
    }
    assert(ancestor_path =~= ancestor_in_path_path);
    assert(ancestor == ancestor_in_path);
}

} // verus!
