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
        &&& forall|nid: NodeId| #[trigger]
            self.inner.dom().contains(nid) ==> {
                &&& NodeHelper::valid_nid(nid)
                &&& self.get_guard_inner(nid).relate_nid(nid)
                &&& self.get_guard_inner(nid).wf(&self.get_lock(nid))
            }
        &&& forall|nid: NodeId| #[trigger]
            self.inner.dom().contains(nid) ==> {
                &&& self.get_guard_inner(nid).stray_perm.value() == false
                &&& self.get_guard_inner(nid).in_protocol == true
                &&& self.childs_are_contained(
                    nid,
                    self.get_guard_inner(nid).pte_token->Some_0.value(),
                )
            }
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
            self.inner.dom().contains(_nid) && _nid != nid ==> 
                !NodeHelper::in_subtree_range(_nid, nid)
    }

    pub open spec fn is_sub_root_and_contained(&self, nid: NodeId) -> bool {
        &&& self.inner.dom().contains(nid)
        &&& self.is_sub_root(nid)
    }

    pub open spec fn childs_are_contained(&self, nid: NodeId, pte_array: PteArrayState) -> bool {
        &&& NodeHelper::is_not_leaf(nid) ==> forall|i: nat|
            0 <= i < 512 ==> {
                #[trigger] pte_array.is_alive(i) ==> self.inner.dom().contains(
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
                #[trigger] pte_array.is_alive(i) ==> self.inner.dom().contains(
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
            old(self).childs_are_contained(nid, guard.pte_token->Some_0.value()),
        ensures
            *self =~= old(self).put_spec(nid, guard, spin_lock),
            self.wf(),
            self.inner.dom().contains(nid),
            self.is_sub_root_and_contained(nid),
    {
        self.inner.tracked_insert(nid, (guard, Ghost(spin_lock)));
    }

    pub open spec fn take_spec(self, nid: NodeId) -> Self {
        Self { inner: self.inner.remove(nid) }
    }

    // Take the sub tree root.
    pub proof fn tracked_take(
        tracked &mut self, 
        nid: NodeId,
    ) -> (tracked res: SpinGuardGhostInner<C>)
        requires
            old(self).wf(),
            NodeHelper::valid_nid(nid),
            old(self).is_sub_root_and_contained(nid),
        ensures
            *self =~= old(self).take_spec(nid),
            self.wf(),
            res.relate_nid(nid),
            res.wf(&old(self).get_lock(nid)),
            res.stray_perm.value() == false,
            res.in_protocol == true,
            !self.inner.dom().contains(nid),
            self.is_sub_root(nid),
            self.childs_are_contained(nid, res.pte_token->Some_0.value()),
    {
        let tracked res = self.inner.tracked_remove(nid);
        assert forall|_nid: NodeId| #[trigger] self.inner.dom().contains(_nid) implies {
            self.childs_are_contained(_nid, self.get_guard_inner(_nid).pte_token->Some_0.value())
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

    pub open spec fn union_spec(self, other: Self) -> Self {
        Self { inner: self.inner.union_prefer_right(other.inner) }
    }

    pub proof fn tracked_union(tracked &mut self, tracked other: Self)
        requires
            old(self).wf(),
            other.wf(),
            old(self).inner.dom().disjoint(other.inner.dom()),
        ensures
            *self =~= old(self).union_spec(other),
            self.wf(),
    {
        self.inner.tracked_union_prefer_right(other.inner)
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
            self.childs_are_contained(_nid, self.get_guard_inner(_nid).pte_token->Some_0.value())
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
            res.childs_are_contained(_nid, res.get_guard_inner(_nid).pte_token->Some_0.value())
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
