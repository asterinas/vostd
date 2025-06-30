use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::spec::{utils::*, common::*};
use super::common::*;

verus! {

pub struct NodeHelperExec;

impl NodeHelperExec {
    pub fn dep_to_level_exec(dep: usize) -> (res: PagingLevel)
        requires
            0 <= dep < 4,
        ensures
            res as nat == NodeHelper::dep_to_level(dep as nat),
            1 <= res <= 4,
    {
        4 - dep
    }

    #[verifier::external_body]
    pub fn tree_size_exec(max_dep: usize) -> (res: usize)
        requires
            0 <= max_dep < 4,
        ensures
            res as nat == NodeHelper::tree_size_spec(max_dep as int),
    {
        match max_dep {
            0 => Some(1),
            1 => Some(513),
            2 => Some(262657),
            3 => Some(134480385),
            _ => None,
        }.unwrap()
    }

    pub open spec fn exec_trace_to_ghost(trace: Vec<usize>) -> Seq<nat> {
        Seq::new(trace.len() as nat, |i| trace[i] as nat)
    }

    #[verifier::external_body]
    pub fn nid_to_trace_exec(nid: usize) -> (res: Vec<usize>)
        requires
            NodeHelper::valid_nid(nid as NodeId),
        ensures
            Self::exec_trace_to_ghost(res) =~= NodeHelper::nid_to_trace(nid as NodeId),
    {
        Vec::new()
    }

    pub fn nid_to_dep_exec(nid: usize) -> (res: usize)
        requires
            NodeHelper::valid_nid(nid as NodeId),
        ensures
            res as nat == NodeHelper::nid_to_dep(nid as nat),
    {
        let trace = Self::nid_to_trace_exec(nid);
        trace.len() as usize
    }

    #[verifier::external_body]
    pub fn get_child_exec(nid: usize, offset: usize) -> (child: usize)
        requires
            NodeHelper::valid_nid(nid as NodeId),
            NodeHelper::is_not_leaf(nid as NodeId),
        ensures
            child as nat == NodeHelper::get_child(nid as NodeId, offset as nat),
            NodeHelper::valid_nid(child as nat),
            nid < child,
            NodeHelper::in_subtree(nid as nat, child as nat),
    {
        let dep = Self::nid_to_dep_exec(nid);
        let level = Self::dep_to_level_exec(dep);
        assert(level >= 2);
        let sz = Self::tree_size_exec(level - 2);

        assert(0 <= offset < 512) by { admit(); };
        assert(0 <= sz <= NodeHelper::total_size()) by { admit(); };
        nid + offset * sz + 1
    }

    pub fn is_not_leaf_exec(nid: usize) -> (res: bool)
        requires
            NodeHelper::valid_nid(nid as NodeId),
        ensures
            res == NodeHelper::is_not_leaf(nid as NodeId),
    {
        Self::nid_to_dep_exec(nid) < 3
    }

}

}
