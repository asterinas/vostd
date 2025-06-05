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

    pub open spec fn inv(&self) -> bool {
        &&& valid_cpu(GLOBAL_CPU_NUM, self.cpu)
        &&& self.token.instance_id() == self.inst.id()
        &&& self.token.key() == self.cpu
        &&& self.inst.cpu_num() == GLOBAL_CPU_NUM
    }

    pub open spec fn pred_cursor_Void(&self) -> bool {
        self.state() is Void
    }

    pub open spec fn pred_cursor_ReadLocking(&self, path: Seq<NodeId>) -> bool {
        &&& self.state() is ReadLocking
        &&& self.state()->ReadLocking_0 =~= path
    }

    pub open spec fn pred_cursor_WriteLocked(&self, path: Seq<NodeId>) -> bool {
        &&& self.state() is WriteLocked
        &&& self.state()->WriteLocked_0 =~= path
    }
}

} // verus!
