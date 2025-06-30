use vstd::prelude::*;

use crate::spec::common::*;
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

    pub open spec fn path(&self) -> Seq<NodeId> {
        match self.state() {
            CursorState::Void => Seq::empty(),
            CursorState::ReadLocking(_) => self.state()->ReadLocking_0,
            CursorState::WriteLocked(_) => self.state()->WriteLocked_0,
        }
    }

    pub open spec fn inv(&self) -> bool {
        &&& valid_cpu(GLOBAL_CPU_NUM, self.cpu)
        &&& self.token.instance_id() == self.inst.id()
        &&& self.token.key() == self.cpu
        &&& self.inst.cpu_num() == GLOBAL_CPU_NUM
        &&& wf_tree_path(self.path())
    }
}

} // verus!
