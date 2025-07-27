use vstd::prelude::*;

use crate::spec::{common::*, utils::*, rcu::*};
use super::{common::*, types::*};

verus! {

pub tracked struct LockProtocolModel {
    pub cpu: CpuId,
    pub token: CursorToken,
    pub inst: SpecInstance,
}

impl LockProtocolModel {
    pub open spec fn inst_id(&self) -> InstanceId {
        self.inst.id()
    }

    pub open spec fn state(&self) -> CursorState {
        self.token.value()
    }

    pub open spec fn sub_tree_rt(&self) -> NodeId
        recommends
            !(self.state() is Void),
    {
        match self.state() {
            CursorState::Void => arbitrary(),
            CursorState::Locking(rt, _) => rt,
            CursorState::Locked(rt) => rt,
            // CursorState::UnLocking(rt, _) => rt,
        }
    }

    pub open spec fn cur_node(&self) -> NodeId
        recommends
            !(self.state() is Void),
            !(self.state() is Locked),
    {
        match self.state() {
            CursorState::Void => arbitrary(),
            CursorState::Locking(_, nid) => nid,
            CursorState::Locked(_) => arbitrary(),
            // CursorState::UnLocking(_, nid) => nid,
        }
    }

    pub open spec fn inv(&self) -> bool {
        &&& valid_cpu(GLOBAL_CPU_NUM, self.cpu)
        &&& self.token.instance_id() == self.inst.id()
        &&& self.token.key() == self.cpu
        &&& self.inst.cpu_num() == GLOBAL_CPU_NUM
        &&& self.state().wf()
    }

    pub open spec fn node_is_locked(&self, nid: NodeId) -> bool
        recommends
            !(self.state() is Void),
    {
        match self.state() {
            CursorState::Void => arbitrary(),
            CursorState::Locking(rt, _nid) => rt <= nid < _nid,
            CursorState::Locked(rt) => NodeHelper::in_subtree_range(rt, nid),
        }
    }
}

} // verus!
