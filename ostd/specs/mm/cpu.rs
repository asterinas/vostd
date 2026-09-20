use crate::cpu::CpuSet;
use vstd::prelude::*;

verus! {

pub struct AtomicCpuSet;

impl AtomicCpuSet {
    #[verifier::external_body]
    pub fn new(_initial: CpuSet) -> Self {
        unimplemented!()
    }
}

pub trait PinCurrentCpu {

}

} // verus!
