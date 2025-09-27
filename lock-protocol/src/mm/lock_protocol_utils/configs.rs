use vstd::prelude::*;

verus! {

// Configurations
// Cpu
pub spec const GLOBAL_CPU_NUM: nat = 2;

// Frame
pub spec const GLOBAL_FRAME_NUM: nat = 1024;

pub spec const FRAME_SIZE: nat = 4096;

// Pte
pub exec const PTE_NUM: usize = 512;

} // verus!
