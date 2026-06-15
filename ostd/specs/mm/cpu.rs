use core::sync::atomic::Ordering;

use vstd::prelude::*;

verus! {

pub struct CpuId(u32);

impl CpuId {
    #[verifier::external_body]
    pub fn current() -> Self {
        unimplemented!()
    }
}

pub struct AtomicCpuSet;

impl AtomicCpuSet {
    #[verifier::external_body]
    pub fn new(_initial: CpuSet) -> Self {
        unimplemented!()
    }

    #[verifier::external_body]
    pub fn load(&self, _ordering: Ordering) -> CpuSet
        no_unwind
    {
        unimplemented!()
    }

    pub fn store(&self, _value: &CpuSet, _ordering: Ordering)
        no_unwind
    {
    }

    pub fn add(&self, _cpu: CpuId, _ordering: Ordering)
        no_unwind
    {
    }
}

pub struct CpuSet {
    pub cpus: Set<CpuId>,
}

impl CpuSet {
    pub open spec fn new_empty_spec() -> Self {
        Self { cpus: Set::empty() }
    }

    #[verifier::external_body]
    #[verifier::when_used_as_spec(new_empty_spec)]
    pub fn new_empty() -> Self
        returns
            Self::new_empty_spec(),
        no_unwind
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub fn is_full(&self) -> bool
        no_unwind
    {
        unimplemented!()
    }
}

pub trait PinCurrentCpu {

}

} // verus!
