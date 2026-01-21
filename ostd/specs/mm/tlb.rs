use vstd::prelude::*;

use crate::specs::mm::cpu::*;

verus! {

pub struct TlbModel {
    pub mappings: Set<Mapping>
}

impl Inv for TlbModel {
    open spec fn inv(self) -> bool {
        &&& forall|m: Mapping| m in self.mappings ==> m.inv()
        &&& forall|m: Mapping| m in self.mappings ==> m.va % m.page_size == 0
        &&& forall|m: Mapping| m in self.mappings ==> m.pa % m.page_size == 0
        &&& forall|m: Mapping| m in self.mappings ==> set![4096, 2097152, 1073741824].contains(m.page_size)
        &&& forall|m: Mapping| forall|n: Mapping|
            m in self.mappings ==>
            n in self.mappings ==> {
                &&& m.va + m.page_size <= n.va || n.va + n.page_size <= m.va
                &&& m.pa + m.page_size <= n.pa || n.pa + n.page_size <= m.pa
            }
    }
}

impl TlbModel {
    pub open spec fn update(self, mapping: Mapping) -> Self
    {
        let va = mapping.va;
        let filtered = self.mappings.filter(|m: Mapping| m.va != va);
    }
}

}