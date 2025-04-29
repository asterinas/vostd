use vstd::prelude::*;
use super::{part_idx_spec, cpu_to_bit_spec};
use super::super::CPU_NUM_SPEC;

verus! {

pub tracked struct CpuSetModel {
    pub ghost bits: Seq<u64>,
}

impl CpuSetModel {
    pub open spec fn is_empty_spec(&self) -> bool {
        forall|i: int| #![auto] 0 <= i < self.bits.len() ==> { self.bits[i] == 0 }
    }

    pub open spec fn contains_spec(&self, cpu: nat) -> bool {
        (self.bits[part_idx_spec(cpu) as int] | (cpu_to_bit_spec(cpu) as u64)) != 0
    }

    pub open spec fn to_set_spec(&self) -> Set<nat> {
        Set::new(
            |cpu: nat|
                {
                    &&& 0 <= cpu < CPU_NUM_SPEC()
                    &&& self.contains_spec(cpu)
                },
        )
    }

    pub open spec fn to_set_inv_spec(&self) -> Set<nat> {
        Set::new(
            |cpu: nat|
                {
                    &&& 0 <= cpu < CPU_NUM_SPEC()
                    &&& !self.to_set_spec().contains(cpu)
                },
        )
    }
}

} // verus!
