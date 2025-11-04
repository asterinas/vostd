use vstd::prelude::*;

use core::marker::PhantomData;

use common::{
    mm::page_table::PageTableConfig,
    spec::{
        common::{valid_cpu, CpuId, NodeId},
        node_helper,
    },
    configs::GLOBAL_CPU_NUM,
};

use crate::spec::rw::{CursorState, CursorToken, SpecInstance};
use crate::spec::rw::wf_tree_path;

verus! {

pub tracked struct LockProtocolModel<C: PageTableConfig> {
    pub cpu: CpuId,
    pub token: CursorToken<C>,
    pub inst: SpecInstance<C>,
}

impl<C: PageTableConfig> LockProtocolModel<C> {
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
        &&& wf_tree_path::<C>(self.path())
    }

    pub open spec fn sub_tree_rt(&self) -> NodeId
        recommends
            self.state() is WriteLocked,
    {
        self.path().last()
    }

    pub open spec fn cur_node(&self) -> NodeId
        recommends
            self.path().len() > 0,
    {
        self.path().last()
    }

    pub open spec fn node_is_locked(&self, nid: NodeId) -> bool
        recommends
            self.state() is WriteLocked,
    {
        node_helper::in_subtree::<C>(self.sub_tree_rt(), nid)
    }
}

} // verus!
