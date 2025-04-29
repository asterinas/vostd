pub mod set;

use vstd::prelude::*;
use vstd_extra::prelude::*;
use crate::task::DisabledPreemptGuard;

extern_const!(
pub CPU_NUM [CPU_NUM_SPEC, CONST_CPU_NUM]: usize = 128);

verus! {

#[derive(Clone, Copy)]
pub struct CpuId(u32);

impl CpuId {
    /// Returns the CPU ID of the bootstrap processor (BSP).
    pub const fn bsp() -> Self {
        CpuId(0)
    }

    /// Converts the CPU ID to an `usize`.
    pub const fn as_usize(self) -> (res: usize)
        requires
            valid_cpu(self@),
        ensures
            res == self@,
    {
        self.0 as usize
    }
}

impl View for CpuId {
    type V = nat;

    closed spec fn view(&self) -> Self::V {
        self.0 as nat
    }
}

} // verus!
verus! {

pub open spec fn valid_cpu(cpu: nat) -> bool {
    0 <= cpu < CPU_NUM_SPEC()
}

} // verus!
verus! {

// Verus doen't support unsafe trait.
pub trait PinCurrentCpu {
    /// Returns the number of the current CPU.
    fn current_cpu(&self) -> (res: CpuId)
        ensures
            valid_cpu(res@),
    {
        // let id = CURRENT_CPU.load();
        // debug_assert_ne!(id, u32::MAX, "This CPU is not initialized");
        // CpuId(id)
        CpuId(0)
    }
}

impl PinCurrentCpu for DisabledPreemptGuard {

}

} // verus!
