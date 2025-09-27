use vstd::prelude::*;

use crate::spec::{common::*, utils::*, rcu::*};
use super::super::{common::*, cpu::*};
use super::SpinGuardGhostInner;

verus! {

pub tracked struct SubTreeForgotGuard<C: PageTableConfig> {
    pub guards: Map<NodeId, SpinGuardGhostInner<C>>,
}

impl<C: PageTableConfig> SubTreeForgotGuard<C> {
    pub open spec fn wf(&self) -> bool {
        &&& forall|nid: NodeId|
            self.guards.dom().contains(nid) ==> {
                &&& NodeHelper::valid_nid(nid)
                &&& self.guards[nid].relate_nid(nid)
            }
    }

    pub open spec fn put_spec(self, nid: NodeId, guard: SpinGuardGhostInner<C>) -> Self {
        Self { guards: self.guards.insert(nid, guard) }
    }

    pub proof fn tracked_put(tracked &mut self, nid: NodeId, tracked guard: SpinGuardGhostInner<C>)
        requires
            old(self).wf(),
            !self.guards.dom().contains(nid),
            NodeHelper::valid_nid(nid),
            guard.relate_nid(nid),
        ensures
            self =~= old(self).put_spec(nid, guard),
            self.wf(),
    {
        self.guards.tracked_insert(nid, guard)
    }

    pub open spec fn take_spec(self, nid: NodeId) -> Self {
        Self { guards: self.guards.remove(nid) }
    }

    pub proof fn tracked_take(tracked &mut self, nid: NodeId) -> (tracked guard:
        SpinGuardGhostInner<C>)
        requires
            old(self).wf(),
            self.guards.dom().contains(nid),
            NodeHelper::valid_nid(nid),
        ensures
            self =~= old(self).take_spec(nid),
            self.wf(),
            guard.relate_nid(nid),
    {
        self.guards.tracked_remove(nid)
    }
}

} // verus!
