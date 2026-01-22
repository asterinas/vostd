use vstd::prelude::*;

verus! {

pub struct CpuId(u32);

pub struct AtomicCpuSet;

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
        returns Self::new_empty_spec()
    {
        unimplemented!()
    }
}

pub trait PinCurrentCpu { }

} // verus!
