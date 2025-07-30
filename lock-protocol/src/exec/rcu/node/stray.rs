use vstd::prelude::*;
use vstd::cell::{CellId, PCell, PointsTo};

use crate::spec::{common::*, utils::*, rcu::*};
use super::super::{common::*, types::*, cpu::*};
use super::PageTableGuard;

verus! {

pub struct StrayFlag {
    pub inner: PCell<bool>,
}

impl StrayFlag {
    pub open spec fn id(&self) -> CellId {
        self.inner.id()
    }

    pub fn read(&self, perm: Tracked<&StrayPerm>) -> (res: bool)
        requires
            perm@.wf_with_cell_id(self.id()),
            perm@.perm.is_init(),
        ensures
            res == perm@.perm.value(),
    {
        let tracked perm = perm.get();
        *self.inner.borrow(Tracked(&perm.perm))
    }
}

pub tracked struct StrayPerm {
    pub perm: PointsTo<bool>,
    pub token: StrayToken,
}

impl StrayPerm {
    pub open spec fn wf(&self) -> bool {
        self.perm.value() == self.token.value()
    }

    pub open spec fn wf_with_cell_id(&self, id: CellId) -> bool {
        &&& self.wf()
        &&& self.perm.id() == id
    }

    pub open spec fn wf_with_node_info(
        &self,
        inst_id: InstanceId,
        nid: NodeId,
        paddr: Paddr,
    ) -> bool {
        &&& self.wf()
        &&& self.inst_id() == inst_id
        &&& self.nid() == nid
        &&& self.paddr() == paddr
    }

    pub open spec fn inst_id(&self) -> InstanceId {
        self.token.instance_id()
    }

    pub open spec fn nid(&self) -> NodeId {
        self.token.key().0
    }

    pub open spec fn paddr(&self) -> Paddr {
        self.token.key().1
    }

    pub open spec fn cell_id(&self) -> CellId {
        self.perm.id()
    }

    pub open spec fn value(&self) -> bool {
        self.perm.value()
    }
}

} // verus!
