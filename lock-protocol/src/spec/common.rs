use std::{io::Write, path, result};

use vstd::{prelude::*, seq::*};
use vstd_extra::{ghost_tree::Node, seq_extra::*};

use crate::spec::utils::*;

verus! {

pub type CpuId = nat;

pub type NodeId = nat;

pub open spec fn valid_cpu(cpu_num: CpuId, cpu: CpuId) -> bool {
    0 <= cpu < cpu_num
}

pub open spec fn valid_pte_offset(offset: nat) -> bool {
    0 <= offset < 512
}

} // verus!
