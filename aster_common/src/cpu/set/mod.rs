pub mod atomic;
mod bit;
pub mod model;

use vstd::prelude::*;
use vstd_extra::prelude::*;
use super::{CpuId, valid_cpu, CONST_CPU_NUM};
// use atomic::AtomicU64;
use model::CpuSetModel;

extern_const!(
pub BITS_PER_PART [BITS_PER_PART_SPEC, CONST_BITS_PER_PART]: usize = 64);

extern_const!(
pub NR_PARTS_NO_ALLOC [NR_PARTS_NO_ALLOC_SPEC, CONST_NR_PARTS_NO_ALLOC]: usize
    = CONST_CPU_NUM / CONST_BITS_PER_PART
);

verus! {

pub open spec fn part_idx_spec(cpu_id: nat) -> nat {
    cpu_id / BITS_PER_PART_SPEC() as nat
}

#[verifier::external_body]
const fn part_idx(cpu_id: CpuId) -> (res: usize)
    requires
        valid_cpu(cpu_id@),
    ensures
        res == part_idx_spec(cpu_id@),
        0 <= res < NR_PARTS_NO_ALLOC_SPEC(),
{
    cpu_id.as_usize() / BITS_PER_PART()
}

pub open spec fn bit_idx_spec(cpu_id: nat) -> nat {
    cpu_id % BITS_PER_PART_SPEC() as nat
}

#[verifier::external_body]
const fn bit_idx(cpu_id: CpuId) -> (res: usize)
    requires
        valid_cpu(cpu_id@),
    ensures
        res == bit_idx_spec(cpu_id@),
        0 <= res < BITS_PER_PART_SPEC(),
{
    cpu_id.as_usize() % BITS_PER_PART()
}

pub open spec fn cpu_to_bit_spec(cpu_id: nat) -> (res: nat) {
    ((1 as u64) << (bit_idx_spec(cpu_id) as u64)) as nat
}

#[verifier::external_body]
const fn cpu_to_bit(cpu_id: CpuId) -> (res: u64)
    requires
        valid_cpu(cpu_id@),
    ensures
        res == cpu_to_bit_spec(cpu_id@),
{
    1 << bit_idx(cpu_id)
}

}

verus! {

#[derive(Clone)]
pub struct CpuSet {
    // A bitset representing the CPUs in the system.
    pub bits: Vec<u64>,
}

impl CpuSet {
    pub open spec fn invariants(&self) -> bool {
        &&& self.bits@.len() == NR_PARTS_NO_ALLOC_SPEC()
    }

    pub fn new() -> (res: Self)
        ensures
            res.invariants(),
    {
        Self { bits: vec![0, 0] }
    }

    pub fn clone(&self) -> (res: Self)
        requires
            self.invariants(),
        ensures
            self@ =~= res@,
            res.invariants(),
    {
        Self {
            bits: self.bits.clone(),
        }
    }

    pub open spec fn is_empty_spec(&self) -> bool {
        forall |i: int| #![auto] 0 <= i < self.bits@.len() ==> {
            self.bits@[i] == 0
        }
    }

    /// Returns true if the set is empty.
    #[verifier::external_body]
    pub fn is_empty(&self) -> (res: bool)
        requires
            self.invariants(),
        ensures
            self.invariants(),
            res == self.is_empty_spec(),
    {
        let mut flag = true;
        let mut i = 0;
        while i < self.bits.len()
            invariant_except_break
                flag == true,
                0 <= i <= self.bits@.len(),
                forall |j: int| #![auto] 0 <= j < i ==> {
                    self.bits@[j] == 0
                },
            ensures
                forall |j: int| #![auto] 0 <= j < i ==> {
                    self.bits@[j] == 0
                } || (flag == false),
        {
            if self.bits[i] != 0 {
                flag = false;
                break;
            }
            i += 1;
        }
        flag
    }

    pub open spec fn contains_spec(&self, cpu: nat) -> bool {
        (self.bits[part_idx_spec(cpu) as int] | (cpu_to_bit_spec(cpu) as u64)) != 0
    }

    pub open spec fn not_contains_spec(&self, cpu: nat) -> bool {
        !self.contains_spec(cpu)
    }

    pub fn contains(&self, cpu: CpuId) -> (res: bool)
        requires
            self.invariants(),
            valid_cpu(cpu@),
        ensures
            res == self.contains_spec(cpu@),
    {
        let part_idx = part_idx(cpu);
        (self.bits[part_idx] | cpu_to_bit(cpu)) != 0
    }

    #[verifier::external_body]
    pub fn insert(&mut self, cpu: CpuId)
        requires
            old(self).invariants(),
            valid_cpu(cpu@),
        ensures
            self.invariants(),
            self.contains_spec(cpu@),
    {
        let part_idx = part_idx(cpu);
        self.bits[part_idx] |= cpu_to_bit(cpu);
    }
}

impl View for CpuSet {
    type V = CpuSetModel;

    open spec fn view(&self) -> Self::V {
        CpuSetModel { bits: self.bits@ }
    }
}

}

// verus! {

// pub struct AtomicCpuSet {
//     pub bits: Vec<AtomicU64>,
// }

// impl AtomicCpuSet {
//     pub open spec fn invariants(&self) -> bool {
//         &&& self.bits@.len() == NR_PARTS_NO_ALLOC_SPEC()
//         &&& forall |i: int| #![auto] 0 <= i < self.bits@.len() ==> {
//             self.bits[i].invariants()
//         }
//     }

//     pub open spec fn is_same(&self, cpu_set: CpuSetModel) -> bool {
//         self@.bits =~= cpu_set.bits
//     }

//     #[verifier::external_body]
//     pub fn new(cpu_set: CpuSet) -> (res: Self)
//         ensures
//             res.invariants(),
//             res.is_same(cpu_set@),
//     {
//         let mut bits = Vec::<AtomicU64>::new();
//         for i in 0..cpu_set.bits.len()
//             invariant
//                 0 <= i <= cpu_set.bits.len(),
//                 bits.len() == i,
//                 forall |j: int| #![auto] 0 <= j < i ==> {
//                     bits[j]@ == cpu_set.bits[j]
//                 }
//         {
//             bits.push(AtomicU64::new(cpu_set.bits[i]));
//         }

//         Self { bits }
//     }

//     #[verifier::external_body]
//     pub fn load(&self) -> (res: CpuSet)
//         requires
//             self.invariants(),
//         ensures
//             self.is_same(res@),
//             res.invariants(),
//     {
//         let mut bits = Vec::<u64>::new();
//         for i in 0..self.bits.len()
//             invariant
//                 0 <= i <= self.bits.len(),
//                 bits.len() == i,
//                 forall |j: int| #![auto] 0 <= j < i ==> {
//                     bits[j] == self.bits[j]@
//                 }
//         {
//             bits.push(self.bits[i].load());
//         }

//         CpuSet { bits }
//     }

//     #[verifier::external_body]
//     pub fn remove(&self, cpu_id: CpuId)
//         requires
//             self.invariants(),
//             valid_cpu(cpu_id@),
//         ensures
//             !self.contains_spec(cpu_id@),
//     {
//         let part_idx = part_idx(cpu_id);
//         let bit_idx = bit_idx(cpu_id);
//         self.bits[part_idx].fetch_and(!(1 << bit_idx));
//     }

//     // pub open spec fn contains_spec(&self, cpu_id: nat) -> bool {
//     //     bit_and_spec(self.bits[part_idx_spec(cpu_id) as int].load() as nat, cpu_to_bit_spec(cpu_id)) != 0
//     // }
//     pub open spec fn contains_spec(&self, cpu_id: nat) -> bool;

//     #[verifier::external_body]
//     pub fn contains(&self, cpu_id: CpuId) -> (res: bool)
//         requires
//             self.invariants(),
//             valid_cpu(cpu_id@),
//         ensures
//             res == self.contains_spec(cpu_id@),
//     {
//         let part_idx = part_idx(cpu_id);
//         let bit_idx = bit_idx(cpu_id);
//         self.bits[part_idx].load() & (1 << bit_idx) != 0
//     }
// }

// impl View for AtomicCpuSet {
//     type V = CpuSetModel;

//     open spec fn view(&self) -> Self::V {
//         CpuSetModel { bits: self.bits@.map_values(|atomic: AtomicU64| { atomic.load() }) }
//     }
// }

// }
