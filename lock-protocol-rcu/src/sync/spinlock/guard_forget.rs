use vstd::prelude::*;

use crate::spec::{common::*, utils::*, rcu::*};
use super::{PageTablePageSpinLock, SpinGuardGhostInner};
use crate::mm::page_table::PageTableConfig;
// use crate::configs::{};

verus! {

pub tracked struct SubTreeForgotGuard<C: PageTableConfig> {
    pub inner: Map<NodeId, (SpinGuardGhostInner<C>, Ghost<PageTablePageSpinLock<C>>)>,
}

impl<C: PageTableConfig> SubTreeForgotGuard<C> {
    pub open spec fn get_guard_inner(&self, nid: NodeId) -> SpinGuardGhostInner<C> {
        self.inner[nid].0
    }

    pub open spec fn get_lock(&self, nid: NodeId) -> PageTablePageSpinLock<C> {
        self.inner[nid].1@
    }

    pub open spec fn wf(&self) -> bool {
        // NIDs match the guards.
        &&& forall|nid: NodeId| #[trigger]
            self.inner.dom().contains(nid) ==> {
                &&& NodeHelper::valid_nid(nid)
                &&& self.get_guard_inner(nid).relate_nid(nid)
                &&& self.get_guard_inner(nid).wf(&self.get_lock(nid))
                &&& self.get_guard_inner(nid).stray_perm.value() == false
                &&& self.get_guard_inner(nid).in_protocol == true
            }
            // Children are contained.
        &&& forall|nid: NodeId| #[trigger]
            self.inner.dom().contains(nid) ==> self.children_are_contained(
                nid,
                self.get_guard_inner(nid).pte_token->Some_0.value(),
            )
        // If a node has an ancestor, it has a parent.
        // &&& forall|nid1: NodeId, nid2: NodeId|
        //     {
        //         &&& #[trigger] self.inner.dom().contains(nid1)
        //         &&& #[trigger] self.inner.dom().contains(nid2)
        //         &&& #[trigger] NodeHelper::in_subtree_range(nid1, nid2)
        //         &&& nid1 != nid2
        //     } ==> {
        //         let parent = NodeHelper::get_parent(nid2);
        //         let idx = NodeHelper::get_offset(nid2);
        //         (nid1 == parent || self.inner.dom().contains(parent)) && self.get_guard_inner(
        //             parent,
        //         ).pte_token->Some_0.value().is_alive(idx)
        //     }
    }

    pub open spec fn is_root(&self, nid: NodeId) -> bool {
        forall|_nid: NodeId| #[trigger]
            self.inner.dom().contains(_nid) ==> NodeHelper::in_subtree_range(nid, _nid)
    }

    pub open spec fn is_root_and_contained(&self, nid: NodeId) -> bool {
        &&& self.inner.dom().contains(nid)
        &&& self.is_root(nid)
    }

    pub open spec fn is_sub_root(&self, nid: NodeId) -> bool {
        forall|_nid: NodeId| #[trigger]
            self.inner.dom().contains(_nid) && _nid != nid ==> !NodeHelper::in_subtree_range(
                _nid,
                nid,
            )
    }

    pub open spec fn is_sub_root_and_contained(&self, nid: NodeId) -> bool {
        &&& self.inner.dom().contains(nid)
        &&& self.is_sub_root(nid)
    }

    // If the node specified by NID is not a leaf, all its alive children are contained in the map.
    pub open spec fn children_are_contained(&self, nid: NodeId, pte_array: PteArrayState) -> bool {
        &&& NodeHelper::is_not_leaf(nid) ==> forall|i: nat|
            0 <= i < 512 ==> {
                #[trigger] pte_array.is_alive(i) <==> self.inner.dom().contains(
                    NodeHelper::get_child(nid, i),
                )
            }
        &&& !NodeHelper::is_not_leaf(nid) ==> pte_array =~= PteArrayState::empty()
    }

    pub open spec fn childs_are_contained_constrained(
        &self,
        nid: NodeId,
        pte_array: PteArrayState,
        idx: nat,
    ) -> bool {
        &&& NodeHelper::is_not_leaf(nid) ==> forall|i: nat|
            0 <= i < idx ==> {
                #[trigger] pte_array.is_alive(i) <==> self.inner.dom().contains(
                    NodeHelper::get_child(nid, i),
                )
            }
        &&& !NodeHelper::is_not_leaf(nid) ==> pte_array =~= PteArrayState::empty()
    }

    pub open spec fn sub_tree_not_contained(&self, nid: NodeId) -> bool {
        forall|_nid: NodeId| #[trigger]
            self.inner.dom().contains(_nid) ==> !NodeHelper::in_subtree_range(nid, _nid)
    }
}

impl<C: PageTableConfig> SubTreeForgotGuard<C> {
    pub open spec fn empty_spec() -> Self {
        Self { inner: Map::empty() }
    }

    pub proof fn empty() -> (tracked res: Self)
        ensures
            res =~= Self::empty_spec(),
    {
        Self { inner: Map::tracked_empty() }
    }

    pub open spec fn put_spec(
        self,
        nid: NodeId,
        guard: SpinGuardGhostInner<C>,
        spin_lock: PageTablePageSpinLock<C>,
    ) -> Self {
        Self { inner: self.inner.insert(nid, (guard, Ghost(spin_lock))) }
    }

    // Put the sub tree root.
    pub proof fn tracked_put(
        tracked &mut self,
        nid: NodeId,
        tracked guard: SpinGuardGhostInner<C>,
        spin_lock: PageTablePageSpinLock<C>,
    )
        requires
            old(self).wf(),
            !old(self).inner.dom().contains(nid),
            NodeHelper::valid_nid(nid),
            guard.relate_nid(nid),
            guard.wf(&spin_lock),
            guard.stray_perm.value() == false,
            guard.in_protocol == true,
            old(self).is_sub_root(nid),
            old(self).children_are_contained(nid, guard.pte_token->Some_0.value()),
        ensures
            *self =~= old(self).put_spec(nid, guard, spin_lock),
            self.wf(),
            self.inner.dom().contains(nid),
            self.is_sub_root_and_contained(nid),
    {
        self.inner.tracked_insert(nid, (guard, Ghost(spin_lock)));
        assert(self.wf()) by {
            assert forall |_nid: NodeId| 
                #[trigger] self.inner.dom().contains(_nid) 
            implies {
                self.children_are_contained(
                    _nid,
                    self.get_guard_inner(_nid).pte_token->Some_0.value(),
                )
            } by {
                if _nid == nid {
                    let pte_array = guard.pte_token->Some_0.value();
                    if NodeHelper::is_not_leaf(nid) {
                        assert forall|i: nat|
                            0 <= i < 512 
                        implies {
                            #[trigger] pte_array.is_alive(i) <==> 
                                self.inner.dom().contains(NodeHelper::get_child(nid, i))
                        } by {
                            assert(NodeHelper::get_child(nid, i) != nid) by {
                                let ch = NodeHelper::get_child(nid, i);
                                NodeHelper::lemma_get_child_sound(nid, i);
                                NodeHelper::lemma_is_child_nid_increasing(nid, ch);
                            };
                        };
                    }
                } else {
                    assert(old(self).inner.dom().contains(_nid));
                    assert forall |idx: nat|
                        0 <= idx < 512
                    implies {
                        nid != NodeHelper::get_child(_nid, idx)
                    } by {
                        assert(old(self).is_sub_root(nid));
                        assert(NodeHelper::valid_nid(_nid));
                        assert(1 <= NodeHelper::nid_to_level(_nid) <= 4) by {
                            NodeHelper::lemma_nid_to_dep_le_3(_nid);
                            NodeHelper::lemma_level_dep_relation(_nid);
                        };
                        if NodeHelper::nid_to_level(_nid) == 1 {
                            assert(NodeHelper::valid_nid(nid));
                            assert(!NodeHelper::valid_nid(NodeHelper::get_child(_nid, idx))) by {
                                NodeHelper::lemma_level_dep_relation(_nid);
                                NodeHelper::lemma_leaf_get_child_wrong(_nid, idx);
                            };
                        } else if nid == NodeHelper::get_child(_nid, idx) {
                            assert(NodeHelper::nid_to_level(_nid) > 1);
                            assert(NodeHelper::in_subtree_range(_nid, nid)) by {
                                NodeHelper::lemma_level_dep_relation(_nid);
                                NodeHelper::lemma_get_child_sound(_nid, idx);
                                NodeHelper::lemma_is_child_implies_in_subtree(_nid, nid);
                                NodeHelper::lemma_in_subtree_iff_in_subtree_range(_nid, nid);
                            }
                        }
                    }
                }
            }
        };
    }

    pub open spec fn take_spec(self, nid: NodeId) -> Self {
        Self { inner: self.inner.remove(nid) }
    }

    // Take the sub tree root.
    pub proof fn tracked_take(tracked &mut self, nid: NodeId) -> (tracked res: SpinGuardGhostInner<
        C,
    >)
        requires
            old(self).wf(),
            NodeHelper::valid_nid(nid),
            old(self).is_sub_root_and_contained(nid),
        ensures
            *self =~= old(self).take_spec(nid),
            res =~= old(self).get_guard_inner(nid),
            self.wf(),
            res.relate_nid(nid),
            res.wf(&old(self).get_lock(nid)),
            res.stray_perm.value() == false,
            res.in_protocol == true,
            !self.inner.dom().contains(nid),
            self.is_sub_root(nid),
            self.children_are_contained(nid, res.pte_token->Some_0.value()),
    {
        let tracked res = self.inner.tracked_remove(nid);
        assert forall|_nid: NodeId| #[trigger] self.inner.dom().contains(_nid) implies {
            self.children_are_contained(_nid, self.get_guard_inner(_nid).pte_token->Some_0.value())
        } by {
            if NodeHelper::is_not_leaf(_nid) {
                assert forall|i: nat|
                    0 <= i < 512 && #[trigger] self.get_guard_inner(
                        _nid,
                    ).pte_token->Some_0.value().is_alive(i) implies {
                    self.inner.dom().contains(NodeHelper::get_child(_nid, i))
                } by {
                    if _nid != nid {
                        assert(old(self).inner.dom().contains(NodeHelper::get_child(_nid, i)));
                        assert(!NodeHelper::in_subtree_range(_nid, nid));
                        assert(NodeHelper::get_child(_nid, i) != nid) by {
                            NodeHelper::lemma_get_child_sound(_nid, i);
                            NodeHelper::lemma_is_child_nid_increasing(
                                _nid,
                                NodeHelper::get_child(_nid, i),
                            );
                            NodeHelper::lemma_is_child_implies_in_subtree(
                                _nid,
                                NodeHelper::get_child(_nid, i),
                            );
                            NodeHelper::lemma_in_subtree_iff_in_subtree_range(
                                _nid,
                                NodeHelper::get_child(_nid, i),
                            );
                        };
                    }
                }
            }
        };
        if NodeHelper::is_not_leaf(nid) {
            assert forall|i: nat|
                0 <= i < 512 && #[trigger] res.0.pte_token->Some_0.value().is_alive(i) implies {
                self.inner.dom().contains(NodeHelper::get_child(nid, i))
            } by {
                assert(old(self).inner.dom().contains(NodeHelper::get_child(nid, i)));
                assert(NodeHelper::get_child(nid, i) != nid) by {
                    NodeHelper::lemma_get_child_sound(nid, i);
                    NodeHelper::lemma_is_child_nid_increasing(nid, NodeHelper::get_child(nid, i));
                };
            };
        }
        res.0
    }

    pub proof fn lemma_take_put(self, nid: NodeId)
        requires
            self.wf(),
            NodeHelper::valid_nid(nid),
            self.is_sub_root_and_contained(nid),
        ensures
            self =~= self.take_spec(nid).put_spec(
                nid,
                self.get_guard_inner(nid),
                self.get_lock(nid),
            ),
    {
        admit();
    }

    pub open spec fn union_spec(self, other: Self) -> Self {
        Self { inner: self.inner.union_prefer_right(other.inner) }
    }

    pub proof fn tracked_union(
        tracked &mut self, 
        tracked other: Self,
        pa: NodeId,
        ch: NodeId,
        offset: nat,
        pte_array: PteArrayState,
    )
        requires
            old(self).wf(),
            other.wf(),
            old(self).inner.dom().disjoint(other.inner.dom()),
            NodeHelper::valid_nid(pa),
            NodeHelper::is_not_leaf(pa),
            NodeHelper::valid_nid(ch),
            0 <= offset < 512,
            pte_array.wf(),
            pte_array.is_alive(offset),
            ch == NodeHelper::get_child(pa, offset),
            !old(self).inner.dom().contains(pa),
            old(self).is_root(pa),
            old(self).childs_are_contained_constrained(pa, pte_array, offset),
            old(self).sub_tree_not_contained(ch),
            other.is_root_and_contained(ch),
        ensures
            *self =~= old(self).union_spec(other),
            self.wf(),
            !self.inner.dom().contains(pa),
            self.is_root(pa),
            self.childs_are_contained_constrained(pa, pte_array, (offset + 1) as nat),
    {
        self.inner.tracked_union_prefer_right(other.inner);
        assert(self.wf()) by {
            assert forall |nid: NodeId| 
                #[trigger] self.inner.dom().contains(nid)
            implies { 
                self.children_are_contained(
                    nid,
                    self.get_guard_inner(nid).pte_token->Some_0.value(),
                )
            } by {
                if old(self).inner.dom().contains(nid) {
                    let pte_array = self.get_guard_inner(nid).pte_token->Some_0.value();
                    if NodeHelper::is_not_leaf(nid) {
                        assert(!other.inner.dom().contains(nid));
                        assert forall|i: nat|
                            0 <= i < 512
                        implies {
                            #[trigger] pte_array.is_alive(i) <==> self.inner.dom().contains(
                                NodeHelper::get_child(nid, i),
                            )
                        } by {
                            if pte_array.is_alive(i) {
                                assert(self.inner.dom().contains(
                                    NodeHelper::get_child(nid, i),
                                ));
                            }
                            if self.inner.dom().contains(NodeHelper::get_child(nid, i)) {
                                assert(pte_array.is_alive(i)) by {
                                    let _ch = NodeHelper::get_child(nid, i);
                                    assert(old(self).inner.dom().contains(_ch)) by {
                                        assert(other.is_root(ch));
                                        assert(_ch != ch) by {
                                            if _ch == ch {
                                                assert(nid == pa) by {
                                                    NodeHelper::lemma_get_child_sound(pa, offset);
                                                    assert(pa == NodeHelper::get_parent(ch));
                                                    NodeHelper::lemma_get_child_sound(nid, i);
                                                    assert(nid == NodeHelper::get_parent(_ch));
                                                };
                                            }
                                        };
                                        assert(!NodeHelper::in_subtree_range(ch, nid));
                                        NodeHelper::lemma_get_child_sound(nid, i);
                                        NodeHelper::lemma_not_in_subtree_range_implies_child_not_in_subtree_range(ch, nid, _ch);
                                    };
                                };
                            }
                        }
                    }
                } else {
                    let pte_array = self.get_guard_inner(nid).pte_token->Some_0.value();
                    assert(other.inner.dom().contains(nid));
                    if NodeHelper::is_not_leaf(nid) {
                        assert forall|i: nat|
                            0 <= i < 512
                        implies {
                            #[trigger] pte_array.is_alive(i) <==> self.inner.dom().contains(
                                NodeHelper::get_child(nid, i),
                            )
                        } by {
                            if pte_array.is_alive(i) {
                                assert(self.inner.dom().contains(
                                    NodeHelper::get_child(nid, i),
                                ));
                            }
                            if self.inner.dom().contains(NodeHelper::get_child(nid, i)) {
                                assert(pte_array.is_alive(i)) by {
                                    let _ch = NodeHelper::get_child(nid, i);
                                    assert(other.inner.dom().contains(_ch)) by {
                                        assert(NodeHelper::in_subtree_range(ch, nid));
                                        NodeHelper::lemma_in_subtree_iff_in_subtree_range(ch, nid);
                                        NodeHelper::lemma_get_child_sound(nid, i);
                                        NodeHelper::lemma_in_subtree_is_child_in_subtree(ch, nid, _ch);
                                        NodeHelper::lemma_in_subtree_iff_in_subtree_range(ch, _ch);
                                    };
                                };
                            }
                        };
                    }
                }
            }
        };
        assert(!self.inner.dom().contains(pa)) by {
            assert(!old(self).inner.dom().contains(pa));
            assert(!other.inner.dom().contains(pa)) by {
                assert forall |nid: NodeId|
                    #[trigger] other.inner.dom().contains(nid)
                implies {
                    nid != pa
                } by {
                    assert(NodeHelper::in_subtree_range(ch, nid));
                    NodeHelper::lemma_get_child_sound(pa, offset);
                    NodeHelper::lemma_is_child_nid_increasing(pa, ch);
                };
            };
        };
        assert(self.is_root(pa)) by {
            assert forall |nid: NodeId|
                #[trigger] self.inner.dom().contains(nid)
            implies {
                NodeHelper::in_subtree_range(pa, nid)
            } by {
                if other.inner.dom().contains(nid) {
                    assert(NodeHelper::in_subtree_range(ch, nid));
                    NodeHelper::lemma_get_child_sound(pa, offset);
                    NodeHelper::lemma_is_child_bound(pa, ch);
                    NodeHelper::lemma_is_child_nid_increasing(pa, ch);
                }
            };
        };
        assert(self.childs_are_contained_constrained(pa, pte_array, (offset + 1) as nat)) by {
            assert forall |i: nat|
                0 <= i < offset + 1
            implies {
                #[trigger] pte_array.is_alive(i) <==> 
                    self.inner.dom().contains(NodeHelper::get_child(pa, i))
            } by {
                if 0 <= i < offset {
                    if pte_array.is_alive(i) {
                        assert(self.inner.dom().contains(NodeHelper::get_child(pa, i)));
                    }
                    if self.inner.dom().contains(NodeHelper::get_child(pa, i)) {
                        assert(pte_array.is_alive(i)) by {
                            let _ch = NodeHelper::get_child(pa, i);
                            assert(_ch < ch) by {
                                NodeHelper::lemma_brother_nid_increasing(pa, i, offset);
                            };
                        };
                    }
                }
            }
        };
    }

    pub open spec fn get_sub_tree_dom(&self, nid: NodeId) -> Set<NodeId> {
        self.inner.dom().intersect(Set::new(|_nid: NodeId| NodeHelper::in_subtree_range(nid, _nid)))
    }

    pub proof fn tracked_take_sub_tree(tracked &mut self, nid: NodeId) -> (tracked res: Self)
        requires
            old(self).wf(),
            NodeHelper::valid_nid(nid),
            old(self).is_sub_root_and_contained(nid),
        ensures
            self.inner =~= old(self).inner.remove_keys(old(self).get_sub_tree_dom(nid)),
            res.inner =~= old(self).inner.restrict(old(self).get_sub_tree_dom(nid)),
            self.wf(),
            res.wf(),
            res.is_root_and_contained(nid),
    {
        let tracked out_inner = self.inner.tracked_remove_keys(old(self).get_sub_tree_dom(nid));
        assert forall|_nid: NodeId| #[trigger] self.inner.dom().contains(_nid) implies {
            self.children_are_contained(_nid, self.get_guard_inner(_nid).pte_token->Some_0.value())
        } by {
            assert(!NodeHelper::in_subtree_range(nid, _nid));
            if NodeHelper::is_not_leaf(_nid) {
                assert forall|i: nat|
                    0 <= i < 512 && #[trigger] self.get_guard_inner(
                        _nid,
                    ).pte_token->Some_0.value().is_alive(i) implies {
                    self.inner.dom().contains(NodeHelper::get_child(_nid, i))
                } by {
                    let child_nid = NodeHelper::get_child(_nid, i);
                    NodeHelper::lemma_get_child_sound(_nid, i);
                    assert(nid != child_nid) by {
                        assert(self.is_sub_root(nid));
                        if nid == child_nid {
                            assert(NodeHelper::in_subtree_range(_nid, nid)) by {
                                NodeHelper::lemma_is_child_implies_in_subtree(_nid, nid);
                                NodeHelper::lemma_in_subtree_iff_in_subtree_range(_nid, nid);
                            };
                        }
                    };
                    assert(!NodeHelper::in_subtree_range(nid, child_nid)) by {
                        NodeHelper::lemma_get_child_sound(_nid, i);
                        NodeHelper::lemma_not_in_subtree_range_implies_child_not_in_subtree_range(
                            nid,
                            _nid,
                            child_nid,
                        );
                    };
                };
            }
        };
        let tracked res = Self { inner: out_inner };
        assert forall|_nid: NodeId| #[trigger] res.inner.dom().contains(_nid) implies {
            res.children_are_contained(_nid, res.get_guard_inner(_nid).pte_token->Some_0.value())
        } by {
            assert(NodeHelper::in_subtree_range(nid, _nid));
            if NodeHelper::is_not_leaf(_nid) {
                assert forall|i: nat|
                    0 <= i < 512 && #[trigger] res.get_guard_inner(
                        _nid,
                    ).pte_token->Some_0.value().is_alive(i) implies {
                    res.inner.dom().contains(NodeHelper::get_child(_nid, i))
                } by {
                    let child_nid = NodeHelper::get_child(_nid, i);
                    NodeHelper::lemma_get_child_sound(_nid, i);
                    assert(NodeHelper::in_subtree_range(nid, child_nid)) by {
                        NodeHelper::lemma_in_subtree_iff_in_subtree_range(nid, _nid);
                        NodeHelper::lemma_in_subtree_is_child_in_subtree(nid, _nid, child_nid);
                        NodeHelper::lemma_in_subtree_iff_in_subtree_range(nid, child_nid);
                    };
                };
            }
        };
        assert(res.inner.dom().contains(nid)) by {
            assert(NodeHelper::in_subtree_range(nid, nid)) by {
                NodeHelper::lemma_sub_tree_size_lower_bound(nid);
            };
        };
        res
    }
}

} // verus!
