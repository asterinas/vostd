use vstd::prelude::*;

use common::{
    mm::nr_subpage_per_huge,
    mm::page_table::{PageTableConfig, PagingConstsTrait},
    spec::{common::NodeId, node_helper},
};

use crate::{mm::page_table::pte, spec::rcu::PteArrayState};

use super::{PageTablePageSpinLock, SpinGuardGhostInner};

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
                &&& node_helper::valid_nid::<C>(nid)
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
        //         &&& #[trigger] node_helper::in_subtree_range::<C>(nid1, nid2)
        //         &&& nid1 != nid2
        //     } ==> {
        //         let parent = node_helper::get_parent::<C>(nid2);
        //         let idx = node_helper::get_offset::<C>(nid2);
        //         (nid1 == parent || self.inner.dom().contains(parent)) && self.get_guard_inner(
        //             parent,
        //         ).pte_token->Some_0.value().is_alive(idx)
        //     }

    }

    pub open spec fn is_root(&self, nid: NodeId) -> bool {
        forall|_nid: NodeId| #[trigger]
            self.inner.dom().contains(_nid) ==> node_helper::in_subtree_range::<C>(nid, _nid)
    }

    pub open spec fn is_root_and_contained(&self, nid: NodeId) -> bool {
        &&& self.inner.dom().contains(nid)
        &&& self.is_root(nid)
    }

    pub open spec fn is_sub_root(&self, nid: NodeId) -> bool {
        forall|_nid: NodeId| #[trigger]
            self.inner.dom().contains(_nid) && _nid != nid ==> !node_helper::in_subtree_range::<C>(
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
        &&& node_helper::is_not_leaf::<C>(nid) ==> {
            &&& forall|i: nat|
                0 <= i < nr_subpage_per_huge::<C>() ==> {
                    #[trigger] pte_array.is_alive(i) <==> self.inner.dom().contains(
                        node_helper::get_child::<C>(nid, i),
                    )
                }
            &&& forall|i: nat|
                0 <= i < nr_subpage_per_huge::<C>() ==> {
                    #[trigger] pte_array.is_void(i) ==> self.sub_tree_not_contained(
                        node_helper::get_child::<C>(nid, i),
                    )
                }
        }
        &&& !node_helper::is_not_leaf::<C>(nid) ==> pte_array =~= PteArrayState::empty()
    }

    pub open spec fn childs_are_contained_constrained(
        &self,
        nid: NodeId,
        pte_array: PteArrayState,
        idx: nat,
    ) -> bool {
        &&& node_helper::is_not_leaf::<C>(nid) ==> {
            &&& forall|i: nat|
                0 <= i < idx ==> {
                    #[trigger] pte_array.is_alive(i) <==> self.inner.dom().contains(
                        node_helper::get_child::<C>(nid, i),
                    )
                }
            &&& forall|i: nat|
                0 <= i < idx ==> {
                    #[trigger] pte_array.is_void(i) ==> self.sub_tree_not_contained(
                        node_helper::get_child::<C>(nid, i),
                    )
                }
        }
        &&& !node_helper::is_not_leaf::<C>(nid) ==> pte_array =~= PteArrayState::empty()
    }

    pub open spec fn sub_tree_not_contained(&self, nid: NodeId) -> bool {
        forall|_nid: NodeId| #[trigger]
            self.inner.dom().contains(_nid) ==> !node_helper::in_subtree_range::<C>(nid, _nid)
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
            node_helper::valid_nid::<C>(nid),
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
        C::lemma_consts_properties();
        C::lemma_nr_subpage_per_huge_is_512();

        self.inner.tracked_insert(nid, (guard, Ghost(spin_lock)));
        assert(self.wf()) by {
            assert forall|_nid: NodeId| #[trigger] self.inner.dom().contains(_nid) implies {
                self.children_are_contained(
                    _nid,
                    self.get_guard_inner(_nid).pte_token->Some_0.value(),
                )
            } by {
                if _nid == nid {
                    let pte_array = guard.pte_token->Some_0.value();
                    if node_helper::is_not_leaf::<C>(nid) {
                        assert forall|i: nat| 0 <= i < 512 implies {
                            #[trigger] pte_array.is_alive(i) <==> self.inner.dom().contains(
                                node_helper::get_child::<C>(nid, i),
                            )
                        } by {
                            assert(node_helper::get_child::<C>(nid, i) != nid) by {
                                let ch = node_helper::get_child::<C>(nid, i);
                                node_helper::lemma_get_child_sound::<C>(nid, i);
                                node_helper::lemma_is_child_nid_increasing::<C>(nid, ch);
                            };
                        };
                        assert forall|i: nat| 0 <= i < 512 implies {
                            #[trigger] pte_array.is_void(i) ==> self.sub_tree_not_contained(
                                node_helper::get_child::<C>(nid, i),
                            )
                        } by {
                            let ch = node_helper::get_child::<C>(nid, i);
                            assert(node_helper::get_child::<C>(nid, i) != nid) by {
                                let ch = node_helper::get_child::<C>(nid, i);
                                node_helper::lemma_get_child_sound::<C>(nid, i);
                                node_helper::lemma_is_child_nid_increasing::<C>(nid, ch);
                            };
                            if pte_array.is_void(i) {
                                assert forall|__nid: NodeId| #[trigger]
                                    self.inner.dom().contains(__nid) implies {
                                    !node_helper::in_subtree_range::<C>(ch, __nid)
                                } by {
                                    if __nid == nid {
                                        node_helper::lemma_get_child_sound::<C>(nid, i);
                                        node_helper::lemma_is_child_nid_increasing::<C>(nid, ch);
                                    } else {
                                    }
                                }
                            }
                        };
                    }
                } else {
                    assert(old(self).inner.dom().contains(_nid));
                    assert forall|idx: nat| 0 <= idx < 512 implies {
                        nid != node_helper::get_child::<C>(_nid, idx)
                    } by {
                        assert(old(self).is_sub_root(nid));
                        assert(node_helper::valid_nid::<C>(_nid));
                        assert(1 <= node_helper::nid_to_level::<C>(_nid) <= C::NR_LEVELS_SPEC())
                            by {
                            node_helper::lemma_nid_to_dep_up_bound::<C>(_nid);
                            node_helper::lemma_level_dep_relation::<C>(_nid);
                        };
                        if node_helper::nid_to_level::<C>(_nid) == 1 {
                            assert(node_helper::valid_nid::<C>(nid));
                            assert(!node_helper::valid_nid::<C>(
                                node_helper::get_child::<C>(_nid, idx),
                            )) by {
                                node_helper::lemma_level_dep_relation::<C>(_nid);
                                node_helper::lemma_leaf_get_child_wrong::<C>(_nid, idx);
                            };
                        } else if nid == node_helper::get_child::<C>(_nid, idx) {
                            assert(node_helper::nid_to_level::<C>(_nid) > 1);
                            assert(node_helper::in_subtree_range::<C>(_nid, nid)) by {
                                node_helper::lemma_level_dep_relation::<C>(_nid);
                                node_helper::lemma_get_child_sound::<C>(_nid, idx);
                                node_helper::lemma_is_child_implies_in_subtree::<C>(_nid, nid);
                                node_helper::lemma_in_subtree_iff_in_subtree_range::<C>(_nid, nid);
                            }
                        }
                    }
                    if node_helper::is_not_leaf::<C>(_nid) {
                        let pte_array = self.get_guard_inner(_nid).pte_token->Some_0.value();
                        assert forall|i: nat| 0 <= i < 512 implies {
                            #[trigger] pte_array.is_void(i) ==> self.sub_tree_not_contained(
                                node_helper::get_child::<C>(_nid, i),
                            )
                        } by {
                            let ch = node_helper::get_child::<C>(_nid, i);
                            if pte_array.is_void(i) {
                                assert forall|__nid: NodeId| #[trigger]
                                    self.inner.dom().contains(__nid) implies {
                                    !node_helper::in_subtree_range::<C>(ch, __nid)
                                } by {
                                    if __nid == nid {
                                        assert(!node_helper::in_subtree_range::<C>(ch, nid)) by {
                                            if node_helper::in_subtree_range::<C>(nid, _nid) {
                                                assert(node_helper::in_subtree_range::<C>(nid, ch))
                                                    by {
                                                    node_helper::lemma_get_child_sound::<C>(
                                                        _nid,
                                                        i,
                                                    );
                                                    node_helper::lemma_in_subtree_iff_in_subtree_range::<
                                                        C,
                                                    >(nid, _nid);
                                                    node_helper::lemma_in_subtree_is_child_in_subtree::<
                                                        C,
                                                    >(nid, _nid, ch);
                                                    node_helper::lemma_in_subtree_iff_in_subtree_range::<
                                                        C,
                                                    >(nid, ch);
                                                }
                                            } else {
                                                assert(!node_helper::in_subtree_range::<C>(
                                                    _nid,
                                                    nid,
                                                ));
                                                if node_helper::in_subtree_range::<C>(ch, nid) {
                                                    assert(node_helper::in_subtree_range::<C>(
                                                        _nid,
                                                        nid,
                                                    )) by {
                                                        assert(node_helper::in_subtree_range::<C>(
                                                            _nid,
                                                            ch,
                                                        )) by {
                                                            node_helper::lemma_get_child_sound::<C>(
                                                                _nid,
                                                                i,
                                                            );
                                                            node_helper::lemma_is_child_implies_in_subtree::<
                                                                C,
                                                            >(_nid, ch);
                                                            node_helper::lemma_in_subtree_iff_in_subtree_range::<
                                                                C,
                                                            >(_nid, ch);
                                                        };
                                                        node_helper::lemma_in_subtree_iff_in_subtree_range::<
                                                            C,
                                                        >(_nid, ch);
                                                        node_helper::lemma_in_subtree_bounded::<C>(
                                                            _nid,
                                                            ch,
                                                        );
                                                    }
                                                }
                                            }
                                        };
                                    }
                                };
                            }
                        };
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
            node_helper::valid_nid::<C>(nid),
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
            if node_helper::is_not_leaf::<C>(_nid) {
                assert forall|i: nat|
                    0 <= i < nr_subpage_per_huge::<C>() && #[trigger] self.get_guard_inner(
                        _nid,
                    ).pte_token->Some_0.value().is_alive(i) implies {
                    self.inner.dom().contains(node_helper::get_child::<C>(_nid, i))
                } by {
                    if _nid != nid {
                        assert(old(self).inner.dom().contains(
                            node_helper::get_child::<C>(_nid, i),
                        ));
                        assert(!node_helper::in_subtree_range::<C>(_nid, nid));
                        assert(node_helper::get_child::<C>(_nid, i) != nid) by {
                            node_helper::lemma_get_child_sound::<C>(_nid, i);
                            node_helper::lemma_is_child_nid_increasing::<C>(
                                _nid,
                                node_helper::get_child::<C>(_nid, i),
                            );
                            node_helper::lemma_is_child_implies_in_subtree::<C>(
                                _nid,
                                node_helper::get_child::<C>(_nid, i),
                            );
                            node_helper::lemma_in_subtree_iff_in_subtree_range::<C>(
                                _nid,
                                node_helper::get_child::<C>(_nid, i),
                            );
                        };
                    }
                }
            }
        };
        if node_helper::is_not_leaf::<C>(nid) {
            assert forall|i: nat|
                0 <= i < nr_subpage_per_huge::<C>()
                    && #[trigger] res.0.pte_token->Some_0.value().is_alive(i) implies {
                self.inner.dom().contains(node_helper::get_child::<C>(nid, i))
            } by {
                assert(old(self).inner.dom().contains(node_helper::get_child::<C>(nid, i)));
                assert(node_helper::get_child::<C>(nid, i) != nid) by {
                    node_helper::lemma_get_child_sound::<C>(nid, i);
                    node_helper::lemma_is_child_nid_increasing::<C>(
                        nid,
                        node_helper::get_child::<C>(nid, i),
                    );
                };
            };
        }
        res.0
    }

    pub proof fn lemma_take_put(self, nid: NodeId)
        requires
            self.wf(),
            node_helper::valid_nid::<C>(nid),
            self.is_sub_root_and_contained(nid),
        ensures
            self =~= self.take_spec(nid).put_spec(
                nid,
                self.get_guard_inner(nid),
                self.get_lock(nid),
            ),
    {
        let taken = self.take_spec(nid);
        let put_back = taken.put_spec(nid, self.get_guard_inner(nid), self.get_lock(nid));
        assert(self.inner =~= put_back.inner);
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
            node_helper::valid_nid::<C>(pa),
            node_helper::is_not_leaf::<C>(pa),
            node_helper::valid_nid::<C>(ch),
            0 <= offset < 512,
            pte_array.wf(),
            pte_array.is_alive(offset),
            ch == node_helper::get_child::<C>(pa, offset),
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
        C::lemma_consts_properties();
        C::lemma_nr_subpage_per_huge_is_512();

        self.inner.tracked_union_prefer_right(other.inner);
        assert(self.wf()) by {
            assert forall|nid: NodeId| #[trigger] self.inner.dom().contains(nid) implies {
                self.children_are_contained(
                    nid,
                    self.get_guard_inner(nid).pte_token->Some_0.value(),
                )
            } by {
                if old(self).inner.dom().contains(nid) {
                    let pte_array = self.get_guard_inner(nid).pte_token->Some_0.value();
                    if node_helper::is_not_leaf::<C>(nid) {
                        assert(!other.inner.dom().contains(nid));
                        assert forall|i: nat| 0 <= i < 512 implies {
                            #[trigger] pte_array.is_alive(i) <==> self.inner.dom().contains(
                                node_helper::get_child::<C>(nid, i),
                            )
                        } by {
                            if pte_array.is_alive(i) {
                                assert(self.inner.dom().contains(
                                    node_helper::get_child::<C>(nid, i),
                                ));
                            }
                            if self.inner.dom().contains(node_helper::get_child::<C>(nid, i)) {
                                assert(pte_array.is_alive(i)) by {
                                    let _ch = node_helper::get_child::<C>(nid, i);
                                    assert(old(self).inner.dom().contains(_ch)) by {
                                        assert(other.is_root(ch));
                                        assert(_ch != ch) by {
                                            if _ch == ch {
                                                assert(nid == pa) by {
                                                    node_helper::lemma_get_child_sound::<C>(
                                                        pa,
                                                        offset,
                                                    );
                                                    assert(pa == node_helper::get_parent::<C>(ch));
                                                    node_helper::lemma_get_child_sound::<C>(nid, i);
                                                    assert(nid == node_helper::get_parent::<C>(
                                                        _ch,
                                                    ));
                                                };
                                            }
                                        };
                                        assert(!node_helper::in_subtree_range::<C>(ch, nid));
                                        node_helper::lemma_get_child_sound::<C>(nid, i);
                                        node_helper::lemma_not_in_subtree_range_implies_child_not_in_subtree_range::<
                                            C,
                                        >(ch, nid, _ch);
                                    };
                                };
                            }
                        }
                        assert forall|i: nat| 0 <= i < 512 implies {
                            #[trigger] pte_array.is_void(i) ==> self.sub_tree_not_contained(
                                node_helper::get_child::<C>(nid, i),
                            )
                        } by {
                            if nid == pa {
                            } else {
                                if other.inner.dom().contains(nid) {
                                } else {
                                    assert(nid != pa);
                                    assert(old(self).inner.dom().contains(nid));
                                    let _ch = node_helper::get_child::<C>(nid, i);
                                    assert(old(self).inner.dom().contains(nid));
                                    assert forall|_nid: NodeId| #[trigger]
                                        other.inner.dom().contains(_nid) implies {
                                        !node_helper::in_subtree_range::<C>(_ch, _nid)
                                    } by {
                                        assert(node_helper::in_subtree_range::<C>(ch, _nid));
                                        assert(node_helper::in_subtree_range::<C>(pa, nid));
                                        node_helper::lemma_in_subtree_iff_in_subtree_range::<C>(
                                            pa,
                                            nid,
                                        );
                                        node_helper::lemma_in_subtree_implies_in_subtree_of_one_child::<
                                            C,
                                        >(pa, nid);
                                        let _offset = choose|_offset: nat|
                                            #![trigger node_helper::get_child::<C>(pa, _offset)]
                                            0 <= _offset < nr_subpage_per_huge::<C>()
                                                && node_helper::in_subtree::<C>(
                                                node_helper::get_child::<C>(pa, _offset),
                                                nid,
                                            );
                                        let __ch = node_helper::get_child::<C>(pa, _offset);
                                        node_helper::lemma_get_child_sound::<C>(pa, _offset);
                                        node_helper::lemma_in_subtree_iff_in_subtree_range::<C>(
                                            __ch,
                                            nid,
                                        );
                                        assert(_offset != offset);
                                        assert(__ch != ch);
                                        if node_helper::in_subtree_range::<C>(_ch, _nid) {
                                            assert(node_helper::in_subtree_range::<C>(__ch, _nid))
                                                by {
                                                assert(node_helper::in_subtree_range::<C>(
                                                    __ch,
                                                    _ch,
                                                )) by {
                                                    node_helper::lemma_get_child_sound::<C>(nid, i);
                                                    node_helper::lemma_in_subtree_iff_in_subtree_range::<
                                                        C,
                                                    >(__ch, nid);
                                                    node_helper::lemma_in_subtree_is_child_in_subtree::<
                                                        C,
                                                    >(__ch, nid, _ch);
                                                    node_helper::lemma_in_subtree_iff_in_subtree_range::<
                                                        C,
                                                    >(__ch, _ch);
                                                };
                                                node_helper::lemma_in_subtree_iff_in_subtree_range::<
                                                    C,
                                                >(__ch, _ch);
                                                node_helper::lemma_in_subtree_bounded::<C>(
                                                    __ch,
                                                    _ch,
                                                );
                                            };
                                            assert(node_helper::in_subtree_range::<C>(ch, _nid));
                                            if _offset < offset {
                                                node_helper::lemma_brother_sub_tree_range_disjoint::<
                                                    C,
                                                >(pa, _offset, offset);
                                            } else {
                                                node_helper::lemma_brother_sub_tree_range_disjoint::<
                                                    C,
                                                >(pa, offset, _offset);
                                            }
                                        }
                                    }
                                }
                            }
                        };
                    }
                } else {
                    let pte_array = self.get_guard_inner(nid).pte_token->Some_0.value();
                    assert(other.inner.dom().contains(nid));
                    if node_helper::is_not_leaf::<C>(nid) {
                        assert forall|i: nat| 0 <= i < 512 implies {
                            #[trigger] pte_array.is_alive(i) <==> self.inner.dom().contains(
                                node_helper::get_child::<C>(nid, i),
                            )
                        } by {
                            if pte_array.is_alive(i) {
                                assert(self.inner.dom().contains(
                                    node_helper::get_child::<C>(nid, i),
                                ));
                            }
                            if self.inner.dom().contains(node_helper::get_child::<C>(nid, i)) {
                                assert(pte_array.is_alive(i)) by {
                                    let _ch = node_helper::get_child::<C>(nid, i);
                                    assert(other.inner.dom().contains(_ch)) by {
                                        assert(node_helper::in_subtree_range::<C>(ch, nid));
                                        node_helper::lemma_in_subtree_iff_in_subtree_range::<C>(
                                            ch,
                                            nid,
                                        );
                                        node_helper::lemma_get_child_sound::<C>(nid, i);
                                        node_helper::lemma_in_subtree_is_child_in_subtree::<C>(
                                            ch,
                                            nid,
                                            _ch,
                                        );
                                        node_helper::lemma_in_subtree_iff_in_subtree_range::<C>(
                                            ch,
                                            _ch,
                                        );
                                    };
                                };
                            }
                        };
                        assert forall|i: nat| 0 <= i < 512 implies {
                            #[trigger] pte_array.is_void(i) ==> self.sub_tree_not_contained(
                                node_helper::get_child::<C>(nid, i),
                            )
                        } by {
                            if nid == pa {
                                assert(node_helper::in_subtree_range::<C>(ch, pa));
                                node_helper::lemma_get_child_sound::<C>(pa, offset);
                                node_helper::lemma_is_child_nid_increasing::<C>(pa, ch);
                            } else {
                                if other.inner.dom().contains(nid) {
                                    let _ch = node_helper::get_child::<C>(nid, i);
                                    assert forall|_nid: NodeId| #[trigger]
                                        old(self).inner.dom().contains(_nid) implies {
                                        !node_helper::in_subtree_range::<C>(_ch, _nid)
                                    } by {
                                        assert(node_helper::in_subtree_range::<C>(ch, _ch)) by {
                                            node_helper::lemma_get_child_sound::<C>(nid, i);
                                            node_helper::in_subtree_range::<C>(ch, nid);
                                            node_helper::lemma_in_subtree_iff_in_subtree_range::<C>(
                                                ch,
                                                nid,
                                            );
                                            node_helper::lemma_in_subtree_is_child_in_subtree::<C>(
                                                ch,
                                                nid,
                                                _ch,
                                            );
                                            node_helper::lemma_in_subtree_iff_in_subtree_range::<C>(
                                                ch,
                                                _ch,
                                            );
                                        };
                                        if node_helper::in_subtree_range::<C>(_ch, _nid) {
                                            node_helper::lemma_in_subtree_iff_in_subtree_range::<C>(
                                                ch,
                                                _ch,
                                            );
                                            node_helper::lemma_in_subtree_bounded::<C>(ch, _ch);
                                            assert(node_helper::in_subtree_range::<C>(ch, _nid));
                                        }
                                    }
                                }
                            }
                        };
                    }
                }
            }
        };
        assert(!self.inner.dom().contains(pa)) by {
            assert(!old(self).inner.dom().contains(pa));
            assert(!other.inner.dom().contains(pa)) by {
                assert forall|nid: NodeId| #[trigger] other.inner.dom().contains(nid) implies {
                    nid != pa
                } by {
                    assert(node_helper::in_subtree_range::<C>(ch, nid));
                    node_helper::lemma_get_child_sound::<C>(pa, offset);
                    node_helper::lemma_is_child_nid_increasing::<C>(pa, ch);
                };
            };
        };
        assert(self.is_root(pa)) by {
            assert forall|nid: NodeId| #[trigger] self.inner.dom().contains(nid) implies {
                node_helper::in_subtree_range::<C>(pa, nid)
            } by {
                if other.inner.dom().contains(nid) {
                    assert(node_helper::in_subtree_range::<C>(ch, nid));
                    node_helper::lemma_get_child_sound::<C>(pa, offset);
                    node_helper::lemma_is_child_bound::<C>(pa, ch);
                    node_helper::lemma_is_child_nid_increasing::<C>(pa, ch);
                }
            };
        };
        assert(self.childs_are_contained_constrained(pa, pte_array, (offset + 1) as nat)) by {
            assert forall|i: nat| 0 <= i < offset + 1 implies {
                #[trigger] pte_array.is_alive(i) <==> self.inner.dom().contains(
                    node_helper::get_child::<C>(pa, i),
                )
            } by {
                if 0 <= i < offset {
                    if pte_array.is_alive(i) {
                        assert(self.inner.dom().contains(node_helper::get_child::<C>(pa, i)));
                    }
                    if self.inner.dom().contains(node_helper::get_child::<C>(pa, i)) {
                        assert(pte_array.is_alive(i)) by {
                            let _ch = node_helper::get_child::<C>(pa, i);
                            assert(_ch < ch) by {
                                node_helper::lemma_brother_nid_increasing::<C>(pa, i, offset);
                            };
                        };
                    }
                }
            }
            assert forall|i: nat| 0 <= i < offset + 1 implies {
                #[trigger] pte_array.is_void(i) ==> self.sub_tree_not_contained(
                    node_helper::get_child::<C>(pa, i),
                )
            } by {
                if 0 <= i < offset {
                    let ch = node_helper::get_child::<C>(pa, i);
                    assert forall|_nid: NodeId| #[trigger]
                        other.inner.dom().contains(_nid) implies {
                        !node_helper::in_subtree_range::<C>(ch, _nid)
                    } by {
                        let _ch = node_helper::get_child::<C>(pa, offset);
                        assert(node_helper::in_subtree_range::<C>(_ch, _nid));
                        node_helper::lemma_brother_sub_tree_range_disjoint::<C>(pa, i, offset);
                    };
                }
            };
        };
    }

    pub open spec fn get_sub_tree_dom(&self, nid: NodeId) -> Set<NodeId> {
        self.inner.dom().intersect(
            Set::new(|_nid: NodeId| node_helper::in_subtree_range::<C>(nid, _nid)),
        )
    }

    pub proof fn tracked_take_sub_tree(tracked &mut self, nid: NodeId) -> (tracked res: Self)
        requires
            old(self).wf(),
            node_helper::valid_nid::<C>(nid),
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
            assert(!node_helper::in_subtree_range::<C>(nid, _nid));
            if node_helper::is_not_leaf::<C>(_nid) {
                assert forall|i: nat|
                    0 <= i < nr_subpage_per_huge::<C>() && #[trigger] self.get_guard_inner(
                        _nid,
                    ).pte_token->Some_0.value().is_alive(i) implies {
                    self.inner.dom().contains(node_helper::get_child::<C>(_nid, i))
                } by {
                    let child_nid = node_helper::get_child::<C>(_nid, i);
                    node_helper::lemma_get_child_sound::<C>(_nid, i);
                    assert(nid != child_nid) by {
                        assert(self.is_sub_root(nid));
                        if nid == child_nid {
                            assert(node_helper::in_subtree_range::<C>(_nid, nid)) by {
                                node_helper::lemma_is_child_implies_in_subtree::<C>(_nid, nid);
                                node_helper::lemma_in_subtree_iff_in_subtree_range::<C>(_nid, nid);
                            };
                        }
                    };
                    assert(!node_helper::in_subtree_range::<C>(nid, child_nid)) by {
                        node_helper::lemma_get_child_sound::<C>(_nid, i);
                        node_helper::lemma_not_in_subtree_range_implies_child_not_in_subtree_range::<
                            C,
                        >(nid, _nid, child_nid);
                    };
                };
            }
        };
        let tracked res = Self { inner: out_inner };
        assert forall|_nid: NodeId| #[trigger] res.inner.dom().contains(_nid) implies {
            res.children_are_contained(_nid, res.get_guard_inner(_nid).pte_token->Some_0.value())
        } by {
            assert(node_helper::in_subtree_range::<C>(nid, _nid));
            if node_helper::is_not_leaf::<C>(_nid) {
                assert forall|i: nat|
                    0 <= i < nr_subpage_per_huge::<C>() && #[trigger] res.get_guard_inner(
                        _nid,
                    ).pte_token->Some_0.value().is_alive(i) implies {
                    res.inner.dom().contains(node_helper::get_child::<C>(_nid, i))
                } by {
                    let child_nid = node_helper::get_child::<C>(_nid, i);
                    node_helper::lemma_get_child_sound::<C>(_nid, i);
                    assert(node_helper::in_subtree_range::<C>(nid, child_nid)) by {
                        node_helper::lemma_in_subtree_iff_in_subtree_range::<C>(nid, _nid);
                        node_helper::lemma_in_subtree_is_child_in_subtree::<C>(
                            nid,
                            _nid,
                            child_nid,
                        );
                        node_helper::lemma_in_subtree_iff_in_subtree_range::<C>(nid, child_nid);
                    };
                };
                assert forall|i: nat|
                    0 <= i < nr_subpage_per_huge::<C>() && #[trigger] res.get_guard_inner(
                        _nid,
                    ).pte_token->Some_0.value().is_void(i) implies {
                    res.sub_tree_not_contained(node_helper::get_child::<C>(_nid, i))
                } by {
                    let child_nid = node_helper::get_child::<C>(_nid, i);
                    node_helper::lemma_get_child_sound::<C>(_nid, i);
                    assert(node_helper::in_subtree_range::<C>(nid, child_nid)) by {
                        node_helper::lemma_in_subtree_iff_in_subtree_range::<C>(nid, _nid);
                        node_helper::lemma_in_subtree_is_child_in_subtree::<C>(
                            nid,
                            _nid,
                            child_nid,
                        );
                        node_helper::lemma_in_subtree_iff_in_subtree_range::<C>(nid, child_nid);
                    };
                };
            }
        };
        assert(res.inner.dom().contains(nid)) by {
            assert(node_helper::in_subtree_range::<C>(nid, nid)) by {
                node_helper::lemma_sub_tree_size_lower_bound::<C>(nid);
            };
        };
        res
    }
}

impl<C: PageTableConfig> SubTreeForgotGuard<C> {
    pub proof fn lemma_replace_with_equal_guard_hold_wf(
        &self,
        nid: NodeId,
        new_guard: SpinGuardGhostInner<C>,
        new_spin_lock: PageTablePageSpinLock<C>,
    )
        requires
            self.wf(),
            self.inner.dom().contains(nid),
            node_helper::valid_nid::<C>(nid),
            new_guard.relate_nid(nid),
            new_guard.wf(&new_spin_lock),
            new_guard.stray_perm.value() == false,
            new_guard.in_protocol == true,
            new_guard.pte_token->Some_0.value() =~= self.get_guard_inner(
                nid,
            ).pte_token->Some_0.value(),
            new_spin_lock =~= self.get_lock(nid),
        ensures
            self.put_spec(nid, new_guard, new_spin_lock).wf(),
    {
    }

    pub proof fn lemma_alloc_hold_wf(
        &self,
        pa: NodeId,
        ch: NodeId,
        offset: nat,
        new_pa_guard: SpinGuardGhostInner<C>,
        new_pa_spin_lock: PageTablePageSpinLock<C>,
        new_ch_guard: SpinGuardGhostInner<C>,
        new_ch_spin_lock: PageTablePageSpinLock<C>,
    )
        requires
            self.wf(),
            node_helper::valid_nid::<C>(pa),
            node_helper::valid_nid::<C>(ch),
            node_helper::is_not_leaf::<C>(pa),
            0 <= offset < 512,
            ch == node_helper::get_child::<C>(pa, offset),
            self.inner.dom().contains(pa),
            !self.inner.dom().contains(ch),
            new_pa_guard.relate_nid(pa),
            new_pa_guard.wf(&new_pa_spin_lock),
            new_pa_guard.stray_perm.value() == false,
            new_pa_guard.in_protocol == true,
            new_pa_spin_lock =~= self.get_lock(pa),
            self.get_guard_inner(pa).pte_token->Some_0.value().is_void(offset),
            new_pa_guard.pte_token->Some_0.value().is_alive(offset),
            new_ch_guard.relate_nid(ch),
            new_ch_guard.wf(&new_ch_spin_lock),
            new_ch_guard.stray_perm.value() == false,
            new_ch_guard.in_protocol == true,
            new_ch_guard.pte_token->Some_0.value() =~= PteArrayState::empty(),
        ensures
            self.put_spec(pa, new_pa_guard, new_pa_spin_lock).put_spec(
                ch,
                new_ch_guard,
                new_ch_spin_lock,
            ).wf(),
    {
        let put_parent = self.put_spec(pa, new_pa_guard, new_pa_spin_lock);
        let put_child = put_parent.put_spec(ch, new_ch_guard, new_ch_spin_lock);
        // NIDs match the guards.
        assert forall|nid: NodeId| #[trigger] put_child.inner.dom().contains(nid) implies {
            &&& node_helper::valid_nid::<C>(nid)
            &&& put_child.get_guard_inner(nid).relate_nid(nid)
            &&& put_child.get_guard_inner(nid).wf(&put_child.get_lock(nid))
            &&& put_child.get_guard_inner(nid).stray_perm.value() == false
            &&& put_child.get_guard_inner(nid).in_protocol == true
        } by {};
        // Children are contained.
        assert forall|nid: NodeId| #[trigger] put_child.inner.dom().contains(nid) implies {
            put_child.children_are_contained(
                nid,
                put_child.get_guard_inner(nid).pte_token->Some_0.value(),
            )
        } by {
            let pte_array = put_child.get_guard_inner(nid).pte_token->Some_0.value();
            let old_pte_array = self.get_guard_inner(nid).pte_token->Some_0.value();
            assert(!node_helper::is_not_leaf::<C>(nid) ==> pte_array =~= PteArrayState::empty());

            if node_helper::is_not_leaf::<C>(nid) {
                if nid != pa && nid != ch {
                    assert(pte_array =~= old_pte_array);
                    assert forall|i: nat| 0 <= i < nr_subpage_per_huge::<C>() implies {
                        #[trigger] pte_array.is_alive(i) <==> put_child.inner.dom().contains(
                            node_helper::get_child::<C>(nid, i),
                        )
                    } by {
                        let child_nid = node_helper::get_child::<C>(nid, i);
                        assert(self.inner.dom().contains(child_nid) <==> put_child.inner.dom().contains(child_nid)) by {
                            if !self.inner.dom().contains(child_nid) {
                                assert(child_nid != ch) by {
                                    admit();
                                }
                                assert(!put_child.inner.dom().contains(child_nid));
                            }
                        };
                        if pte_array.is_alive(i) {
                            assert(self.inner.dom().contains(child_nid)) by {
                                assert(self.wf());
                            }
                            assert(put_child.inner.dom().contains(child_nid));
                        }
                        if put_child.inner.dom().contains(child_nid) {
                            assert(old_pte_array.is_alive(i)) by {
                                assert(self.wf());
                            }
                            assert(pte_array.is_alive(i));
                        }
                    };
                    assert forall|i: nat| 0 <= i < nr_subpage_per_huge::<C>() implies {
                        #[trigger] pte_array.is_void(i) ==> put_child.sub_tree_not_contained(
                            node_helper::get_child::<C>(nid, i),
                        )
                    } by {
                        let child_nid = node_helper::get_child::<C>(nid, i);
                        assert(self.sub_tree_not_contained(child_nid) <==> put_child.sub_tree_not_contained(child_nid)) by {
                            admit();
                        };
                        if pte_array.is_void(i) {
                            assert(put_child.sub_tree_not_contained(child_nid)) by {
                                admit();
                            };
                        }
                    };
                } else {
                    admit();
                }
            }
        };
    }
}

} // verus!
