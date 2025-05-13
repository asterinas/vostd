use builtin::*;
use builtin_macros::*;
use state_machines_macros::tokenized_state_machine;
use vstd::prelude::*;

use super::common::*;
use super::utils::*;

verus! {

tokenized_state_machine!{

ConcreteSpec {

fields {
    #[sharding(constant)]
    pub cpu_num: CpuId,

    #[sharding(map)]
    pub nodes: Map<NodeId, NodeState>,

    #[sharding(map)]
    pub cursors: Map<CpuId, CursorState>,
}

#[invariant]
pub fn inv_nodes(&self) -> bool {
    &&& forall |nid| #![auto] self.nodes.contains_key(nid) <==> NodeHelper::valid_nid(nid)
}

#[invariant]
pub fn inv_cursors(&self) -> bool {
    &&& forall |cpu| #![auto] self.cursors.contains_key(cpu) <==> valid_cpu(self.cpu_num, cpu)

    &&& forall |cpu: CpuId| #![auto] self.cursors.contains_key(cpu) ==> {
        &&& self.cursors[cpu].inv()
        &&& match self.cursors[cpu] {
            CursorState::Empty => true,
            CursorState::Creating(st, en, _) | CursorState::Hold(st, en) | CursorState::Destroying(st, en, _) => {
                &&& 0 <= st < en <= NodeHelper::total_size()
                &&& en == NodeHelper::next_outside_subtree(st)
            },
        }
    }

    &&& forall |cpu1: CpuId, cpu2: CpuId|
        cpu1 != cpu2 && self.cursors.contains_key(cpu1) && self.cursors.contains_key(cpu2) ==>
            self.cursors[cpu1].no_overlap(&self.cursors[cpu2])
}

pub open spec fn is_locked(&self, st: NodeId, en: NodeId) -> bool {
    forall |nid| st <= nid < en ==> (self.nodes[nid] is EmptyLocked || self.nodes[nid] is Locked)
}

#[invariant]
pub fn inv_cursors_nodes_relation(&self) -> bool {
    &&& forall |cpu| self.cursors.contains_key(cpu) ==> match self.cursors[cpu] {
        CursorState::Empty => true,
        CursorState::Creating(st, _, en) | CursorState::Hold(st, en) | CursorState::Destroying(st, _, en) => {
            self.is_locked(st, en)
        },
    }
}


init!{
    initialize(cpu_num: CpuId) {
        require(cpu_num > 0);

        init cpu_num = cpu_num;
        init nodes = Map::new(
            |nid| NodeHelper::valid_nid(nid),
            |nid| if nid == NodeHelper::root_id() {
                NodeState::Free
            } else {
                NodeState::Empty
            },
        );
        init cursors = Map::new(
            |cpu| valid_cpu(cpu_num, cpu),
            |cpu| CursorState::Empty,
        );
    }
}

transition!{
    node_acquire_outside_cursor(nid: NodeId) {
        require(NodeHelper::valid_nid(nid));

        remove nodes -= [ nid => NodeState::Free ];
        add nodes += [ nid => NodeState::LockedOutside ];
    }
}

transition!{
    node_release_outside_cursor(nid: NodeId) {
        require(NodeHelper::valid_nid(nid));

        remove nodes -= [ nid => NodeState::LockedOutside ];
        add nodes += [ nid => NodeState::Free ];
    }
}

transition!{
    node_create_in_cursor(cpu: CpuId, nid: NodeId) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(NodeHelper::valid_nid(nid));
        require(nid != NodeHelper::root_id());

        remove nodes -= [ nid => NodeState::EmptyLocked ];
        add nodes += [ nid => NodeState::Locked ];

        have cursors >= [ cpu => let CursorState::Hold(st, en) ];
        require(st <= nid < en);
    }
}

transition!{
    node_create_outside_cursor(nid: NodeId) {
        require(NodeHelper::valid_nid(nid));
        require(nid != NodeHelper::root_id());

        remove nodes -= [ nid => NodeState::Empty ];
        have nodes >= [ NodeHelper::get_parent(nid) => NodeState::LockedOutside ];
        add nodes += [ nid => NodeState::LockedOutside ];
    }
}

transition!{
    cursor_create_start(cpu: CpuId, nid: NodeId) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(NodeHelper::valid_nid(nid));

        remove cursors -= [ cpu => CursorState::Empty ];
        add cursors += [ cpu => CursorState::Creating(nid, NodeHelper::next_outside_subtree(nid), nid) ];
    }
}

transition!{
    node_acquire(cpu: CpuId, nid: NodeId) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(NodeHelper::valid_nid(nid));

        remove nodes -= [ nid => NodeState::Free ];
        add nodes += [ nid => NodeState::Locked ];

        remove cursors -= [ cpu => let CursorState::Creating(st, en, cur_nid) ];
        require(nid == cur_nid && nid < en);
        add cursors += [ cpu => CursorState::Creating(st, en, nid + 1) ];
    }
}

transition!{
    node_acquire_skip(cpu: CpuId, nid: NodeId) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(NodeHelper::valid_nid(nid));

        remove nodes -= (Map::new(
            |_nid| NodeHelper::in_subtree(nid, _nid),
            |_nid| NodeState::Empty,
        ));
        add nodes += (Map::new(
            |_nid| NodeHelper::in_subtree(nid, _nid),
            |_nid| NodeState::EmptyLocked,
        ));

        remove cursors -= [ cpu => let CursorState::Creating(st, en, cur_nid) ];
        require(nid == cur_nid && nid < en);
        add cursors += [ cpu => CursorState::Creating(st, en, NodeHelper::next_outside_subtree(nid)) ];
    }
}

transition!{
    cursor_create_end(cpu: CpuId) {
        require(valid_cpu(pre.cpu_num, cpu));

        remove cursors -= [ cpu => let CursorState::Creating(st, en, cur_nid) ];
        require(en == cur_nid);
        add cursors += [ cpu => CursorState::Hold(st, en) ];
    }
}

transition!{
    cursor_destroy_start(cpu: CpuId) {
        require(valid_cpu(pre.cpu_num, cpu));

        remove cursors -= [ cpu => let CursorState::Hold(st, en) ];
        add cursors += [ cpu => CursorState::Destroying(st, en, en) ];
    }
}

transition!{
    node_release(cpu: CpuId, nid: NodeId) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(NodeHelper::valid_nid(nid));

        remove nodes -= [ nid => NodeState::Locked ];
        add nodes += [ nid => NodeState::Free ];

        remove cursors -= [ cpu => let CursorState::Destroying(st, en, cur_nid) ];
        require(nid + 1 == cur_nid && nid >= st);
        add cursors += [ cpu => CursorState::Destroying(st, en, nid) ];
    }
}

transition!{
    node_release_skip(cpu: CpuId, nid: NodeId) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(NodeHelper::valid_nid(nid));

        remove nodes -= (Map::new(
            |_nid| NodeHelper::in_subtree(nid, _nid),
            |_nid| NodeState::EmptyLocked,
        ));
        add nodes += (Map::new(
            |_nid| NodeHelper::in_subtree(nid, _nid),
            |_nid| NodeState::Empty,
        ));

        remove cursors -= [ cpu => let CursorState::Destroying(st, en, cur_nid) ];
        require(NodeHelper::next_outside_subtree(nid) == cur_nid && nid >= st);
        add cursors += [ cpu => CursorState::Destroying(st, en, nid) ];
    }
}

transition!{
    cursor_destroy_end(cpu: CpuId) {
        require(valid_cpu(pre.cpu_num, cpu));

        remove cursors -= [ cpu => let CursorState::Destroying(st, en, cur_nid) ];
        require(st == cur_nid);
        add cursors += [ cpu => CursorState::Empty ];
    }
}

#[inductive(initialize)]
fn initialize_inductive(post: Self, cpu_num: CpuId) {}

#[inductive(node_acquire_outside_cursor)]
fn node_acquire_outside_cursor_inductive(pre: Self, post: Self, nid: NodeId) {
    assert forall |cpu| post.cursors.contains_key(cpu) implies {
        match post.cursors[cpu] {
            CursorState::Empty => true,
            CursorState::Creating(st, _, en) | CursorState::Hold(st, en) | CursorState::Destroying(st, _, en) => {
                post.is_locked(st, en)
            },
        }
    } by {
        assert(pre.cursors[cpu] =~= post.cursors[cpu]);
        if pre.cursors[cpu] !is Empty {
            let (st, en) = pre.cursors[cpu].get_locked_range();
            assert forall |_nid| st <= _nid < en implies {
                post.nodes[_nid] is EmptyLocked || post.nodes[_nid] is Locked
            } by {
                assert(NodeHelper::valid_nid(_nid));
                if _nid != nid {
                    assert(post.nodes[_nid] =~= pre.nodes[_nid]);
                } else {
                    assert(post.nodes[nid] is LockedOutside);
                }
            };
        }
    };
}

#[inductive(node_release_outside_cursor)]
fn node_release_outside_cursor_inductive(pre: Self, post: Self, nid: NodeId) {
    assert forall |cpu| post.cursors.contains_key(cpu) implies {
        match post.cursors[cpu] {
            CursorState::Empty => true,
            CursorState::Creating(st, _, en) | CursorState::Hold(st, en) | CursorState::Destroying(st, _, en) => {
                post.is_locked(st, en)
            },
        }
    } by {
        assert(pre.cursors[cpu] =~= post.cursors[cpu]);
        if pre.cursors[cpu] !is Empty {
            let (st, en) = pre.cursors[cpu].get_locked_range();
            assert forall |_nid| st <= _nid < en implies {
                post.nodes[_nid] is EmptyLocked || post.nodes[_nid] is Locked
            } by {
                assert(NodeHelper::valid_nid(_nid));
                if _nid != nid {
                    assert(post.nodes[_nid] =~= pre.nodes[_nid]);
                } else {
                    assert(post.nodes[nid] is Free);
                }
            };
        }
    };
}

#[inductive(node_create_in_cursor)]
fn node_create_in_cursor_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {
    assert forall |_cpu| _cpu != cpu && post.cursors.contains_key(_cpu) implies {
        match post.cursors[_cpu] {
            CursorState::Empty => true,
            CursorState::Creating(st, _, en) | CursorState::Hold(st, en) | CursorState::Destroying(st, _, en) => {
                post.is_locked(st, en)
            },
        }
    } by {
        assert(pre.cursors[_cpu] =~= post.cursors[_cpu]);
        assert(pre.cursors[cpu].no_overlap(&pre.cursors[_cpu]));
        if pre.cursors[_cpu] !is Empty {
            let (st, en) = pre.cursors[_cpu].get_locked_range();
            assert forall |_nid| st <= _nid < en implies {
                post.nodes[_nid] is EmptyLocked || post.nodes[_nid] is Locked
            } by {
                assert(NodeHelper::valid_nid(_nid));
                assert(post.nodes[_nid] =~= pre.nodes[_nid]);
            };
        }
    };

    assert(post.cursors[cpu] is Hold);
    let st = post.cursors[cpu]->Hold_0;
    let en = post.cursors[cpu]->Hold_1;
    assert forall |_nid| st <= _nid < en implies {
        post.nodes[_nid] is EmptyLocked || post.nodes[_nid] is Locked
    } by {
        if _nid == nid { assert(post.nodes[nid] is Locked); }
        else {
            assert(NodeHelper::valid_nid(_nid));
            assert(post.nodes[_nid] =~= pre.nodes[_nid]);
        }
    };
}

#[inductive(node_create_outside_cursor)]
fn node_create_outside_cursor_inductive(pre: Self, post: Self, nid: NodeId) {
    assert forall |cpu| post.cursors.contains_key(cpu) implies {
        match post.cursors[cpu] {
            CursorState::Empty => true,
            CursorState::Creating(st, _, en) | CursorState::Hold(st, en) | CursorState::Destroying(st, _, en) => {
                post.is_locked(st, en)
            },
        }
    } by {
        assert(pre.cursors[cpu] =~= post.cursors[cpu]);
        if pre.cursors[cpu] !is Empty {
            let (st, en) = pre.cursors[cpu].get_locked_range();
            assert forall |_nid| st <= _nid < en implies {
                post.nodes[_nid] is EmptyLocked || post.nodes[_nid] is Locked
            } by {
                assert(NodeHelper::valid_nid(_nid));
                if _nid != nid {
                    assert(post.nodes[_nid] =~= pre.nodes[_nid]);
                } else {
                    assert(post.nodes[nid] is Locked);
                }
            };
        }
    };
}

#[inductive(cursor_create_start)]
fn cursor_create_start_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {
    assert(post.cursors[cpu] is Creating);
    let st = post.cursors[cpu]->Creating_0;
    let en = post.cursors[cpu]->Creating_1;
    let cur_nid = post.cursors[cpu]->Creating_2;
    assert(st == cur_nid);
    assert(en == st + NodeHelper::sub_tree_size(st));
    assert(en <= NodeHelper::total_size()) by {
        NodeHelper::lemma_next_outside_subtree_bounded(st);
    };
    assert(st < en) by { NodeHelper::lemma_sub_tree_size_lowerbound(st) };
    assert(post.cursors[cpu].inv());
}

#[inductive(node_acquire)]
fn node_acquire_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {
    assert(pre.nodes[nid] is Free);
    assert forall |_cpu| _cpu != cpu && #[trigger] post.cursors.contains_key(_cpu) implies {
        post.cursors[cpu].no_overlap(&post.cursors[_cpu])
    } by {
        assert(pre.cursors[cpu].no_overlap(&pre.cursors[_cpu]));
        assert(pre.cursors[_cpu].node_is_not_held(nid));
        match post.cursors[_cpu] {
            CursorState::Empty => (),
            CursorState::Creating(st, _, en) | CursorState::Hold(st, en) | CursorState::Destroying(st, _, en) => {
                assert(nid < st || nid >= en);
            }
        }
    };

    assert forall |_cpu| _cpu != cpu && post.cursors.contains_key(_cpu) implies {
        match post.cursors[_cpu] {
            CursorState::Empty => true,
            CursorState::Creating(st, _, en) | CursorState::Hold(st, en) | CursorState::Destroying(st, _, en) => {
                post.is_locked(st, en)
            },
        }
    } by {
        assert(pre.cursors[_cpu] =~= post.cursors[_cpu]);
        assert(pre.cursors[cpu].no_overlap(&pre.cursors[_cpu]));
        if pre.cursors[_cpu] !is Empty {
            let (st, en) = pre.cursors[_cpu].get_locked_range();
            assert forall |_nid| st <= _nid < en implies {
                post.nodes[_nid] is EmptyLocked || post.nodes[_nid] is Locked
            } by {
                assert(NodeHelper::valid_nid(_nid));
                assert(post.nodes[_nid] =~= pre.nodes[_nid]);
            };
        }
    };

    assert(post.cursors[cpu] is Creating);
    let st = post.cursors[cpu]->Creating_0;
    let en = post.cursors[cpu]->Creating_2;
    assert forall |_nid| st <= _nid < en implies {
        post.nodes[_nid] is EmptyLocked || post.nodes[_nid] is Locked
    } by {
        if _nid == nid { assert(post.nodes[nid] is Locked); }
        else {
            assert(NodeHelper::valid_nid(_nid));
            assert(post.nodes[_nid] =~= pre.nodes[_nid]);
        }
    }
}

#[inductive(node_acquire_skip)]
fn node_acquire_skip_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {
    let _nodes = Map::new(
        |_nid| NodeHelper::in_subtree(nid, _nid),
        |_nid| NodeState::Empty,
    );
    assert(_nodes.submap_of(pre.nodes));
    assert forall |_nid| #[trigger] NodeHelper::in_subtree(nid, _nid) implies {
        pre.nodes[_nid] is Empty
    } by {
        assert(_nodes.dom().contains(_nid));
        assert(pre.nodes.dom().contains(_nid));
    };
    assert(forall |_nid| #[trigger] NodeHelper::in_subtree(nid, _nid) ==>
        post.nodes[_nid] is EmptyLocked
    );
    assert(forall |_nid| NodeHelper::in_subtree(nid, _nid) <==>
        nid <= _nid < NodeHelper::next_outside_subtree(nid)
    );
    assert(post.cursors[cpu] is Creating);
    let st = post.cursors[cpu]->Creating_0;
    let en = post.cursors[cpu]->Creating_1;
    let cur_nid = post.cursors[cpu]->Creating_2;
    assert(cur_nid <= en) by {
        assert(en == NodeHelper::next_outside_subtree(st));
        assert(cur_nid == NodeHelper::next_outside_subtree(nid));
        NodeHelper::lemma_in_subtree_bounded(st, nid);
    };
    assert forall |_cpu| _cpu != cpu && #[trigger] post.cursors.contains_key(_cpu) implies {
        post.cursors[cpu].no_overlap(&post.cursors[_cpu])
    } by {
        assert(pre.cursors[cpu].no_overlap(&pre.cursors[_cpu]));
        assert forall |_nid| NodeHelper::in_subtree(nid, _nid) implies {
            match post.cursors[_cpu] {
                CursorState::Empty => true,
                CursorState::Creating(st, _, en) | CursorState::Hold(st, en) | CursorState::Destroying(st, _, en) => {
                    _nid < st || _nid >= en
                },
            }
        } by {
            assert(pre.nodes[_nid] is Empty);
            assert(pre.cursors[_cpu].node_is_not_held(_nid));
        };
        match post.cursors[_cpu] {
            CursorState::Empty => (),
            CursorState::Creating(st, _, en) | CursorState::Hold(st, en) | CursorState::Destroying(st, _, en) => {
                let nid_tail = (NodeHelper::next_outside_subtree(nid) - 1) as nat;
                assert(nid_tail < st || nid >= en || st == en) by {
                    assert(nid < st || nid >= en) by {
                        assert(NodeHelper::in_subtree(nid, nid)) by {
                            NodeHelper::lemma_in_subtree_0(nid);
                        };
                    };
                    assert(nid_tail < st || nid_tail >= en) by {
                        assert(NodeHelper::in_subtree(nid, nid_tail)) by {
                            NodeHelper::lemma_sub_tree_size_lowerbound(nid);
                        };
                    };
                    if nid < st && nid_tail >= en && st != en {
                        assert(NodeHelper::in_subtree(nid, st));
                    }
                };
            },
        };
    };

    assert forall |_cpu| _cpu != cpu && post.cursors.contains_key(_cpu) implies {
        match post.cursors[_cpu] {
            CursorState::Empty => true,
            CursorState::Creating(st, _, en) | CursorState::Hold(st, en) | CursorState::Destroying(st, _, en) => {
                post.is_locked(st, en)
            },
        }
    } by {
        assert(pre.cursors[_cpu] =~= post.cursors[_cpu]);
        assert(pre.cursors[cpu].no_overlap(&pre.cursors[_cpu]));
        if pre.cursors[_cpu] !is Empty {
            let (st, en) = pre.cursors[_cpu].get_locked_range();
            assert forall |_nid| st <= _nid < en implies {
                post.nodes[_nid] is EmptyLocked || post.nodes[_nid] is Locked
            } by {
                assert(NodeHelper::valid_nid(_nid));
                assert(post.nodes[_nid] =~= pre.nodes[_nid]);
            };
        }
    };
    assert forall |_nid| st <= _nid < cur_nid implies {
        post.nodes[_nid] is EmptyLocked || post.nodes[_nid] is Locked
    } by {
        if _nid < nid {
            assert(NodeHelper::valid_nid(_nid));
            assert(pre.nodes[_nid] =~= post.nodes[_nid]);
        } else {
            assert(post.nodes[_nid] is EmptyLocked);
        }
    };
}

#[inductive(cursor_create_end)]
fn cursor_create_end_inductive(pre: Self, post: Self, cpu: CpuId) {
    assert(forall |_cpu| #![auto] _cpu != cpu && post.cursors.contains_key(_cpu) ==> {
        pre.cursors[cpu].no_overlap(&pre.cursors[_cpu]) <==>
        post.cursors[cpu].no_overlap(&post.cursors[_cpu])
    });
}

#[inductive(cursor_destroy_start)]
fn cursor_destroy_start_inductive(pre: Self, post: Self, cpu: CpuId) {
    assert(forall |_cpu| #![auto] _cpu != cpu && post.cursors.contains_key(_cpu) ==> {
        pre.cursors[cpu].no_overlap(&pre.cursors[_cpu]) <==>
        post.cursors[cpu].no_overlap(&post.cursors[_cpu])
    });
}

#[inductive(node_release)]
fn node_release_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {
    assert(pre.nodes[nid] is Locked);
    assert(pre.cursors[cpu].node_is_held(nid));
    assert forall |_cpu| _cpu != cpu && #[trigger] post.cursors.contains_key(_cpu) implies {
        post.cursors[cpu].no_overlap(&post.cursors[_cpu])
    } by {
        assert(pre.cursors[cpu].no_overlap(&pre.cursors[_cpu]));
        assert(pre.cursors[_cpu].node_is_not_held(nid));
        match post.cursors[_cpu] {
            CursorState::Empty => (),
            CursorState::Creating(st, _, en) | CursorState::Hold(st, en) | CursorState::Destroying(st, _, en) => {
                assert(nid < st || nid >= en);
            }
        }
    };

    assert forall |_cpu| _cpu != cpu && post.cursors.contains_key(_cpu) implies {
        match post.cursors[_cpu] {
            CursorState::Empty => true,
            CursorState::Creating(st, _, en) | CursorState::Hold(st, en) | CursorState::Destroying(st, _, en) => {
                post.is_locked(st, en)
            },
        }
    } by {
        assert(pre.cursors[_cpu] =~= post.cursors[_cpu]);
        assert(pre.cursors[cpu].no_overlap(&pre.cursors[_cpu]));
        if pre.cursors[_cpu] !is Empty {
            let (st, en) = pre.cursors[_cpu].get_locked_range();
            assert forall |_nid| st <= _nid < en implies {
                post.nodes[_nid] is EmptyLocked || post.nodes[_nid] is Locked
            } by {
                assert(NodeHelper::valid_nid(_nid));
                assert(post.nodes[_nid] =~= pre.nodes[_nid]);
            };
        }
    };

    assert(post.cursors[cpu]is Destroying);
    let st = post.cursors[cpu]->Destroying_0;
    let en = post.cursors[cpu]->Destroying_2;
    assert forall |_nid| st <= _nid < en implies {
        post.nodes[_nid] is EmptyLocked || post.nodes[_nid] is Locked
    } by {
        assert(NodeHelper::valid_nid(_nid));
        assert(post.nodes[_nid] =~= pre.nodes[_nid]);
    };
}

#[inductive(node_release_skip)]
fn node_release_skip_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {
    let _nodes = Map::new(
        |_nid| NodeHelper::in_subtree(nid, _nid),
        |_nid| NodeState::EmptyLocked,
    );
    assert(_nodes.submap_of(pre.nodes));
    assert forall |_nid| #[trigger] NodeHelper::in_subtree(nid, _nid) implies {
        pre.nodes[_nid] is EmptyLocked
    } by {
        assert(_nodes.dom().contains(_nid));
        assert(pre.nodes.dom().contains(_nid));
    };
    assert(forall |_nid| #[trigger] NodeHelper::in_subtree(nid, _nid) ==>
        post.nodes[_nid] is Empty
    );
    assert(forall |_nid| NodeHelper::in_subtree(nid, _nid) <==>
        nid <= _nid < NodeHelper::next_outside_subtree(nid)
    );

    assert forall |_cpu| _cpu != cpu && #[trigger] post.cursors.contains_key(_cpu) implies {
        post.cursors[cpu].no_overlap(&post.cursors[_cpu])
    } by {
        assert(pre.cursors[cpu].no_overlap(&pre.cursors[_cpu]));
        assert forall |_nid| NodeHelper::in_subtree(nid, _nid) implies {
            match post.cursors[_cpu] {
                CursorState::Empty => true,
                CursorState::Creating(st, _, en) | CursorState::Hold(st, en) | CursorState::Destroying(st, _, en) => {
                    _nid < st || _nid >= en
                },
            }
        } by {
            assert(pre.nodes[_nid] is EmptyLocked);
            assert(pre.cursors[_cpu].node_is_not_held(_nid));
        };
        match post.cursors[_cpu] {
            CursorState::Empty => (),
            CursorState::Creating(st, _, en) | CursorState::Hold(st, en) | CursorState::Destroying(st, _, en) => {
                let nid_tail = (NodeHelper::next_outside_subtree(nid) - 1) as nat;
                assert(nid_tail < st || nid >= en || st == en) by {
                    assert(nid < st || nid >= en) by {
                        assert(NodeHelper::in_subtree(nid, nid)) by {
                            NodeHelper::lemma_in_subtree_0(nid);
                        };
                    };
                    assert(nid_tail < st || nid_tail >= en) by {
                        assert(NodeHelper::in_subtree(nid, nid_tail)) by {
                            NodeHelper::lemma_sub_tree_size_lowerbound(nid);
                        };
                    };
                    if nid < st && nid_tail >= en && st != en {
                        assert(NodeHelper::in_subtree(nid, st));
                    }
                };
            },
        };
    };

    let st = post.cursors[cpu]->Destroying_0;
    let en = post.cursors[cpu]->Destroying_1;
    let cur_nid = post.cursors[cpu]->Destroying_2;
    assert forall |_cpu| _cpu != cpu && post.cursors.contains_key(_cpu) implies {
        match post.cursors[_cpu] {
            CursorState::Empty => true,
            CursorState::Creating(st, _, en) | CursorState::Hold(st, en) | CursorState::Destroying(st, _, en) => {
                post.is_locked(st, en)
            },
        }
    } by {
        assert(pre.cursors[_cpu] =~= post.cursors[_cpu]);
        assert(pre.cursors[cpu].no_overlap(&pre.cursors[_cpu]));
        if pre.cursors[_cpu] !is Empty {
            let (st, en) = pre.cursors[_cpu].get_locked_range();
            assert forall |_nid| st <= _nid < en implies {
                post.nodes[_nid] is EmptyLocked || post.nodes[_nid] is Locked
            } by {
                assert(NodeHelper::valid_nid(_nid));
                assert(post.nodes[_nid] =~= pre.nodes[_nid]);
            };
        }
    };
    assert forall |_nid| st <= _nid < cur_nid implies {
        post.nodes[_nid] is EmptyLocked || post.nodes[_nid] is Locked
    } by {
        if _nid < nid {
            assert(NodeHelper::valid_nid(_nid));
            assert(pre.nodes[_nid] =~= post.nodes[_nid]);
        } else {
            assert(post.nodes[_nid] is EmptyLocked);
        }
    };
}

#[inductive(cursor_destroy_end)]
fn cursor_destroy_end_inductive(pre: Self, post: Self, cpu: CpuId) {}

}

}

} // verus!
