// SPDX-License-Identifier: MPL-2.0
//! This module contains the implementation of the CPU set and atomic CPU set.
use super::cpu_count;
use vstd::{
    arithmetic::div_mod::lemma_fundamental_div_mod, assert_seqs_equal, layout::size_of, prelude::*,
    set::Set, std_specs::iter::IteratorSpec,
};
use vstd_extra::{
    bits::{
        group_u64_bit_algebra, lemma_u64_allones_bit, lemma_u64_and_zero, lemma_u64_masked_bit_keep,
    },
    external::{
        bits::{lemma_u64_set_bits_nonzero, u64_set_bits},
        smallvec::{group_smallvec_models, smallvec_view},
    },
    ownership::Inv,
};

use core::sync::atomic::{AtomicU64, Ordering};

use smallvec::SmallVec;

use super::{CpuId, num_cpus};
use crate::const_assert;

/// A subset of all CPUs in the system.
#[derive(Clone, Debug, Default)]
#[verifier::allow(autoderive_clone_without_spec)]
#[verus_verify]
pub struct CpuSet {
    // A bitset representing the CPUs in the system.
    bits: SmallVec<[InnerPart; NR_PARTS_NO_ALLOC]>,
}

type InnerPart = u64;

verus! {

// Original exec: `const BITS_PER_PART: usize = core::mem::size_of::<InnerPart>() * 8;`
// literalized to `64` inside `verus!` so Verus sees a known value (exec `% BITS_PER_PART` ↔ spec `% 64`).
const BITS_PER_PART: usize = 64;

const NR_PARTS_NO_ALLOC: usize = 2;

} // verus!
#[verus_verify]
#[verus_spec(
    returns part_idx_spec(cpu_id@),
)]
const fn part_idx(cpu_id: CpuId) -> usize {
    proof! {
        reveal(part_idx_spec);
    }
    cpu_id.as_usize() / BITS_PER_PART
}

#[verus_verify]
#[verus_spec(
    returns bit_idx_spec(cpu_id@),
)]
const fn bit_idx(cpu_id: CpuId) -> usize {
    proof! {
        reveal(bit_idx_spec);
    }
    cpu_id.as_usize() % BITS_PER_PART
}

#[verus_verify]
#[verifier::when_used_as_spec(parts_for_cpus_spec)]
#[verus_spec(
    returns parts_for_cpus_spec(num_cpus),
)]
const fn parts_for_cpus(num_cpus: usize) -> usize {
    proof! {
        reveal(parts_for_cpus_spec);
        if num_cpus == 0 {
            assert(parts_for_cpus_spec(0) == 0);
        } else {
            assert(num_cpus as int > 0);
            assert(parts_for_cpus_spec(num_cpus) as int == ((num_cpus as int) + 63) / 64);
        }
    }
    num_cpus.div_ceil(BITS_PER_PART)
}

verus! {

broadcast use {
    group_smallvec_models,
    lemma_u64_set_bits_nonzero,
    group_u64_bit_algebra,
    crate::cpu::axiom_cpu_count_bounds,
    vstd::layout::layout_of_primitives,
    vstd::set::group_set_lemmas,
    vstd::set_lib::range_set_properties,
};

/// `div_ceil(n, BITS_PER_PART)`: the number of 64-bit words needed to hold `n` bits.
pub closed spec fn parts_for_cpus_spec(n: usize) -> usize {
    if n == 0 {
        0
    } else {
        ((n + 63) / 64) as usize
    }
}

/// The 64-bit word holding bit `i`.
pub closed spec fn part_idx_spec(i: int) -> usize {
    (i / 64) as usize
}

/// The position of bit `i` within its 64-bit word.
pub closed spec fn bit_idx_spec(i: int) -> usize {
    (i % 64) as usize
}

/// Number of set bits in all words of `seq`.
pub open spec fn count_set_bits(seq: Seq<u64>) -> int {
    seq.fold_left(0, |count: int, word: u64| count + u64_set_bits(word))
}

/// Expected value of word `idx` in a full CPU set.
spec fn full_set_word(num_cpus: int, len: int, idx: int) -> u64 {
    if idx == len - 1 && bit_idx_spec(num_cpus) != 0 {
        ((1u64 << bit_idx_spec(num_cpus)) - 1) as u64
    } else {
        !0u64
    }
}

/// Bit `i` is set in the bit sequence `seq`.
pub open spec fn bit_at(seq: Seq<u64>, i: int) -> bool {
    if 0 <= i < 64 * seq.len() as int {
        (seq[part_idx_spec(i) as int] & (1u64 << bit_idx_spec(i))) != 0
    } else {
        false
    }
}

impl View for CpuSet {
    type V = Set<int>;

    /// The set of CPU ids whose bit is set in `bits` (and below `cpu_count()`).
    closed spec fn view(&self) -> Set<int> {
        Set::range(0, cpu_count()).filter(|i: int| bit_at(smallvec_view(&self.bits), i))
    }
}

impl CpuSet {
    /// Number of set bits in the backing words.
    pub closed spec fn count_spec(&self) -> int {
        count_set_bits(smallvec_view(&self.bits))
    }
}

impl Inv for CpuSet {
    /// The backing vector holds exactly `parts_for_cpus(cpu_count)` words, the view
    /// is bounded by `cpu_count`, and the unused tail bits (>= `cpu_count`) are clear.
    closed spec fn inv(self) -> bool {
        &&& smallvec_view(&self.bits).len() == parts_for_cpus_spec(cpu_count() as usize)
        &&& forall|j: int|
            #![trigger bit_at(smallvec_view(&self.bits), j)]
            cpu_count() <= j < 64 * smallvec_view(&self.bits).len() as int ==> !bit_at(
                smallvec_view(&self.bits),
                j,
            )
    }
}

} // verus!
#[verus_verify]
impl CpuSet {
    /// Creates a new `CpuSet` with all CPUs in the system.
    #[verus_spec(ret =>
        ensures
            ret@ == Set::range(0, cpu_count()),
            ret.inv(),
    )]
    pub fn new_full() -> Self {
        proof! { lemma_cpucount_fits(); }
        let mut ret = Self::with_capacity_val(num_cpus(), !0);
        proof! {
            let seq0 = smallvec_view(&ret.bits);
            assert(forall|k: int|
                #![trigger smallvec_view(&ret.bits)[k]]
                0 <= k < smallvec_view(&ret.bits).len() as int ==> smallvec_view(&ret.bits)[k]
                    == !0u64);
            assert forall|j: int| 0 <= j < cpu_count() implies bit_at(seq0, j) by {
                lemma_bit_at_uniform(seq0, !0, j);
            }
        }
        ret.clear_nonexistent_cpu_bits();
        proof! {
            let seq = smallvec_view(&ret.bits);
            let n = cpu_count();
            assert forall|a: int|
                #![trigger ret@.contains(a)]
                ret@.contains(a) == Set::range(0, n).contains(a) by {
                assert(ret@.contains(a) == (0 <= a < n && bit_at(seq, a)));
            }
            assert(ret@ == Set::range(0, n));
        }
        ret
    }

    /// Creates a new `CpuSet` with no CPUs in the system.
    #[verus_spec(ret =>
        ensures
            ret@ == Set::empty(),
            ret.inv(),
    )]
    pub fn new_empty() -> Self {
        proof! { lemma_cpucount_fits(); }
        let ret = Self::with_capacity_val(num_cpus(), 0);
        proof! {
            lemma_empty_bits_imply_empty_set(&ret);
            assert forall|j: int|
                cpu_count() <= j < 64 * smallvec_view(&ret.bits).len() as int implies !bit_at(
                    smallvec_view(&ret.bits),
                    j,
                ) by {
                lemma_u64_and_zero(1u64 << bit_idx_spec(j));
            }
        }
        ret
    }

    /// Adds a CPU to the set.
    #[verus_spec(
        requires
            self.inv(),
        ensures
            final(self)@ == old(self)@.insert(cpu_id@),
            final(self).inv(),
    )]
    pub fn add(&mut self, cpu_id: CpuId) {
        proof! {
            use_type_invariant(&cpu_id);
        }
        let part_idx = part_idx(cpu_id);
        let bit_idx = bit_idx(cpu_id);
        proof! {
            // The growth branch is dead under `self.inv()` and the `CpuId` type invariant
            // (kept for the original out-of-contract behavior).
            let id = cpu_id@;
            let n = cpu_count();
            let p = part_idx as int;
            let b = bit_idx as int;
            assert(id < n);
            assert(p == id / 64);
            lemma_fundamental_div_mod(id, 64);
            lemma_fundamental_div_mod(n - 1, 64);
            assert(id / 64 <= (n - 1) / 64);
            assert((n + 63) / 64 >= (n - 1) / 64 + 1);
            reveal(parts_for_cpus_spec);
            assert(smallvec_view(&self.bits).len() == (n + 63) / 64);
            assert(p < smallvec_view(&self.bits).len());
            assert(0 <= b < 64);
        }
        if part_idx >= self.bits.len() {
            self.bits.resize(part_idx + 1, 0);
        }
        // Original exec: `self.bits[part_idx] |= 1 << bit_idx;`
        // routed via `as_mut_slice()` — SmallVec's own `IndexMut` impl has no Verus model.
        self.bits.as_mut_slice()[part_idx] |= 1 << bit_idx;
        proof! {
            let id = cpu_id@;
            let n = cpu_count();
            let p = (part_idx as int) - 0;
            let b = bit_idx as int;
            let old_seq = smallvec_view(&old(self).bits);
            let new_seq = smallvec_view(&self.bits);
            let len = old_seq.len() as int;
            assert(new_seq.len() == old_seq.len());
            assert(new_seq == old_seq.update(p, old_seq[p] | (1u64 << (b as usize))));
            assert forall|a: int|
                #![trigger self@.contains(a)]
                self@.contains(a) == old(self)@.insert(id).contains(a) by {
                assert(self@.contains(a) == (0 <= a < n && bit_at(new_seq, a)));
                assert(old(self)@.contains(a) == (0 <= a < n && bit_at(old_seq, a)));
                if a == id {
                    assert(a / 64 == p);
                }
            }
            assert(self@ == old(self)@.insert(id));
            assert forall|j: int| n <= j < 64 * len implies !bit_at(new_seq, j) by {
                assert(bit_at(new_seq, j) == bit_at(old_seq, j));
            }
        }
    }

    /// Removes a CPU from the set.
    #[verus_spec(
        requires
            self.inv(),
        ensures
            final(self)@ == old(self)@.remove(cpu_id@),
            final(self).inv(),
    )]
    pub fn remove(&mut self, cpu_id: CpuId) {
        proof! {
            use_type_invariant(&cpu_id);
        }
        let part_idx = part_idx(cpu_id);
        let bit_idx = bit_idx(cpu_id);
        if part_idx < self.bits.len() {
            // Original exec: `self.bits[part_idx] &= !(1 << bit_idx);`
            // routed via `as_mut_slice()` — SmallVec's own `IndexMut` impl has no Verus model.
            self.bits.as_mut_slice()[part_idx] &= !(1 << bit_idx);
            proof! {
                let id = cpu_id@;
                let n = cpu_count();
                let p = part_idx as int;
                let b = bit_idx as int;
                let old_seq = smallvec_view(&old(self).bits);
                let new_seq = smallvec_view(&self.bits);
                assert(new_seq.len() == old_seq.len());
                assert(new_seq == old_seq.update(p, old_seq[p] & (!(1u64 << (b as usize)))));
                assert forall|a: int|
                    #![trigger self@.contains(a)]
                    self@.contains(a) == old(self)@.remove(id).contains(a) by {
                    assert(self@.contains(a) == (0 <= a < n && bit_at(new_seq, a)));
                    if a == id {
                        assert(a / 64 == p);
                    }
                }
                assert forall|j: int| n <= j < 64 * old_seq.len() as int implies !bit_at(
                    new_seq,
                    j,
                ) by {
                    assert(bit_at(new_seq, j) == bit_at(old_seq, j));
                }
            }
        }
    }

    /// Returns true if the set contains the specified CPU.
    #[verus_spec(ret =>
        requires
            self.inv(),
        returns self@.contains(cpu_id@),
    )]
    pub fn contains(&self, cpu_id: CpuId) -> bool {
        proof! {
            use_type_invariant(&cpu_id);
        }
        let part_idx = part_idx(cpu_id);
        let bit_idx = bit_idx(cpu_id);
        // Original exec: `self.bits[part_idx]`
        // routed via `as_slice()` — SmallVec's own `Index` impl has no Verus model.
        part_idx < self.bits.len() && (self.bits.as_slice()[part_idx] & (1 << bit_idx)) != 0
    }

    /// Returns the number of CPUs in the set.
    #[verus_spec(
        requires
            self.inv(),
        returns self.count_spec() as usize,
    )]
    pub fn count(&self) -> usize {
        /* `Iterator::sum` has no model in the active vstd, so use an indexed loop with a
         * prefix-sum invariant while preserving the same word order and arithmetic.
         * Origin Rust: self.bits
         *     .iter()
         *     .map(|part| part.count_ones() as usize)
         *     .sum()
         */
        let mut count = 0usize;
        let mut idx = 0usize;
        proof! {
            lemma_count_fits();
            reveal(CpuSet::count_spec);
        }
        #[verus_spec(
            invariant
                self.inv(),
                idx <= smallvec_view(&self.bits).len(),
                count == smallvec_view(&self.bits).subrange(0, idx as int).fold_left(
                    0,
                    |count: int, word: u64| count + u64_set_bits(word),
                ),
                count <= 64 * idx,
            decreases
                smallvec_view(&self.bits).len() - idx,
        )]
        while idx < self.bits.len() {
            let part = self.bits.as_slice()[idx];
            let part_count = part.count_ones() as usize;
            proof! {
                assert(0 <= u64_set_bits(part) <= 64);
                assert(count + part_count <= usize::MAX);
                let seq = smallvec_view(&self.bits);
                assert_seqs_equal!(
                    seq.subrange(0, idx + 1).drop_last() == seq.subrange(0, idx as int)
                );
                assert(seq.subrange(0, idx + 1).last() == seq[idx as int]);
                reveal_with_fuel(Seq::fold_left, 1);
            }
            count += part_count;
            idx += 1;
        }
        count
    }

    /// Returns true if the set is empty.
    #[verus_spec(ret =>
        requires
            self.inv(),
        returns self@ == Set::empty(),
    )]
    pub fn is_empty(&self) -> bool {
        /* `Iterator::all` on a temporary receiver does not expose its initial `remaining()`
         * sequence to the caller's proof, so name the iterator and retain a ghost snapshot.
         * Origin Rust: self.bits.iter().all(|part| *part == 0)
         */
        let mut iter = self.bits.iter();
        proof_decl! {
            let ghost initial_iter = iter;
        }
        let ret = iter.all(
            #[verus_spec(ret: bool => ensures ret == (*part == 0u64))]
            |part| *part == 0,
        );
        proof! {
            if ret {
                assert(IteratorSpec::remaining(&initial_iter)
                    == smallvec_view(&self.bits).as_ref());
                assert forall|i: int|
                    0 <= i < smallvec_view(&self.bits).len() implies
                        smallvec_view(&self.bits)[i] == 0u64 by {
                    assert(*IteratorSpec::remaining(&initial_iter)[i] == 0u64);
                }
                lemma_empty_bits_imply_empty_set(self);
            } else {
                let seq = smallvec_view(&self.bits);
                let initial = IteratorSpec::remaining(&initial_iter);
                let idx = initial.len() - IteratorSpec::remaining(&iter).len() - 1;
                assert(initial == seq.as_ref());
                assert(initial[idx] != 0u64);
                lemma_u64_nonzero_has_set_bit(*initial[idx]);
                let b = choose|b: u32| b < 64 && #[trigger] (*initial[idx]
                    & (1u64 << b)) != 0;
                let j = 64 * idx + b as int;
                assert(0 <= idx < seq.len());
                assert(j / 64 == idx);
                assert(j % 64 == b as int);
                assert((j % 64) as usize == b as usize);
                assert(bit_at(seq, j));
                assert(j < cpu_count());
                assert(self@.contains(j));
            }
        }
        ret
    }

    /// Returns true if the set is full.
    #[verus_spec(ret =>
        requires
            self.inv(),
        ensures
            ret ==> self@ == Set::range(0, cpu_count()),
    )]
    pub fn is_full(&self) -> bool {
        /* `Enumerate` has no `IteratorSpecImpl` in the active vstd, so use an indexed loop
         * with the same ascending word order and the same first-mismatch short circuit.
         * Origin Rust: let num_cpus = num_cpus();
         * self.bits.iter().enumerate().all(|(idx, part)| {
         *     if idx == self.bits.len() - 1 && num_cpus % BITS_PER_PART != 0 {
         *         *part == (1 << (num_cpus % BITS_PER_PART)) - 1
         *     } else {
         *         *part == !0
         *     }
         * })
         */
        let num_cpus = num_cpus();
        let mut idx = 0usize;
        #[verus_spec(
            invariant
                self.inv(),
                num_cpus == cpu_count(),
                idx <= smallvec_view(&self.bits).len(),
                forall|i: int|
                    #![trigger smallvec_view(&self.bits)[i]]
                    0 <= i < idx ==> smallvec_view(&self.bits)[i]
                        == full_set_word(
                            cpu_count(),
                            smallvec_view(&self.bits).len() as int,
                            i,
                        ),
            decreases
                smallvec_view(&self.bits).len() - idx,
        )]
        while idx < self.bits.len() {
            let expected = if idx == self.bits.len() - 1 && num_cpus % BITS_PER_PART != 0 {
                (1 << (num_cpus % BITS_PER_PART)) - 1
            } else {
                !0
            };
            if self.bits.as_slice()[idx] != expected {
                return false;
            }
            idx += 1;
        }
        proof! {
            lemma_full_bits_imply_full_set(self);
        }
        true
    }

    /// Adds all CPUs to the set.
    #[verus_spec(
        requires
            self.inv(),
        ensures
            final(self)@ == Set::range(0, cpu_count()),
            final(self).inv(),
    )]
    pub fn add_all(&mut self) {
        self.bits.fill(!0);
        self.clear_nonexistent_cpu_bits();
    }

    /// Removes all CPUs from the set.
    #[verus_spec(
        requires
            self.inv(),
        ensures
            final(self)@ == Set::empty(),
            final(self).inv(),
    )]
    pub fn clear(&mut self) {
        self.bits.fill(0);
        proof! {
            let seq = smallvec_view(&self.bits);
            assert(forall|k: int| 0 <= k < seq.len() ==> seq[k] == 0u64);
            lemma_empty_bits_imply_empty_set(self);
            assert forall|j: int|
                cpu_count() <= j < 64 * smallvec_view(&self.bits).len() as int implies !bit_at(
                    smallvec_view(&self.bits),
                    j,
                ) by {
                lemma_u64_and_zero(1u64 << bit_idx_spec(j));
            }
        }
    }

    /// Iterates over the CPUs in the set.
    ///
    /// The order of the iteration is guaranteed to be in ascending order.
    #[verus_spec(ret =>
        requires
            self.inv(),
        ensures
            IteratorSpec::obeys_prophetic_iter_laws(&ret),
            IteratorSpec::decrease(&ret) is Some,
    )]
    pub fn iter(&self) -> impl Iterator<Item = CpuId> + '_ {
        /* `Enumerate`, `FlatMap`, and `FilterMap` are not modeled by the active vstd, so scan
         * the same bit positions with modeled `Filter` and `Map` adapters. The position order
         * and selected CPU IDs are unchanged.
         * Origin Rust: self.bits.iter().enumerate().flat_map(|(part_idx, &part)| {
         *     (0..BITS_PER_PART).filter_map(move |bit_idx| {
         *         if (part & (1 << bit_idx)) != 0 {
         *             let id = part_idx * BITS_PER_PART + bit_idx;
         *             Some(CpuId(id as u32))
         *         } else {
         *             None
         *         }
         *     })
         * })
         */
        proof! {
            lemma_count_fits();
        }
        let end = self.bits.len() * BITS_PER_PART;
        (0..end)
            .filter(
                #[verus_spec(ret: bool =>
                    requires
                        *id < end,
                    ensures
                        ret == bit_at(smallvec_view(&self.bits), *id as int),
                )]
                move |id| {
                    let part_idx = *id / BITS_PER_PART;
                    let bit_idx = *id % BITS_PER_PART;
                    proof! {
                        assert((*id as int) / 64 == part_idx as int);
                        assert((*id as int) % 64 == bit_idx as int);
                    }
                    (self.bits.as_slice()[part_idx] & (1 << bit_idx)) != 0
                },
            )
            .map(
                #[verus_spec(ret: CpuId =>
                    requires
                        bit_at(smallvec_view(&self.bits), id as int),
                    ensures
                        ret == CpuId(id as u32),
                )]
                move |id| {
                    proof! {
                        assert(id < cpu_count());
                    }
                    CpuId(id as u32)
                },
            )
    }

    /// Only for internal use. Build a vector of `num_cpus`-covering words, all equal to `val`.
    #[verus_spec(ret =>
        requires
            (num_cpus as int) == cpu_count(),
            2 * (parts_for_cpus_spec(num_cpus) as int) * (size_of::<u64>() as int)
                <= isize::MAX as int,
        ensures
            smallvec_view(&ret.bits).len() == parts_for_cpus_spec(num_cpus),
        forall|i: int|
            #![trigger smallvec_view(&ret.bits)[i]]
            0 <= i < smallvec_view(&ret.bits).len() as int ==> smallvec_view(&ret.bits)[i]
                == val,
    )]
    fn with_capacity_val(num_cpus: usize, val: InnerPart) -> Self {
        let num_parts = parts_for_cpus(num_cpus);
        let mut bits = SmallVec::with_capacity(num_parts);
        bits.resize(num_parts, val);
        Self { bits }
    }

    #[verus_spec(
        requires
            smallvec_view(&self.bits).len() == parts_for_cpus_spec(cpu_count() as usize),
            forall|j: int|
                #![trigger bit_at(smallvec_view(&self.bits), j)]
                0 <= j < cpu_count() ==> bit_at(smallvec_view(&self.bits), j),
        ensures
            final(self).inv(),
            forall|j: int|
                #![trigger bit_at(smallvec_view(&final(self).bits), j)]
                0 <= j < cpu_count() ==> bit_at(smallvec_view(&final(self).bits), j),
    )]
    fn clear_nonexistent_cpu_bits(&mut self) {
        let num_cpus = num_cpus();
        if num_cpus % BITS_PER_PART != 0 {
            let num_parts = parts_for_cpus(num_cpus);
            proof! {
                let n = cpu_count();
                assert((num_cpus as int) == n);
                assert(1 <= n);
                assert((num_parts as int) == (n + 63) / 64);
                lemma_fundamental_div_mod(n + 63, 64);
                assert(n + 63 >= 64);
                assert(0 <= (n + 63) % 64 < 64);
                assert((num_parts as int) >= 1);
                reveal(parts_for_cpus_spec);
                assert(parts_for_cpus_spec(n as usize) as int == (n + 63) / 64);
                assert(((num_parts as int) - 1) < smallvec_view(&self.bits).len());
                lemma_fundamental_div_mod(n - 1, 64);
                assert(64 * ((n - 1) / 64) < n);
            }
            // Original exec: `self.bits[num_parts - 1] &= (1 << (num_cpus % BITS_PER_PART)) - 1;`
            // routed via `as_mut_slice()` — SmallVec's own `IndexMut` impl has no Verus model.
            self.bits.as_mut_slice()[num_parts - 1] &= (1 << (num_cpus % BITS_PER_PART)) - 1;
            proof! {
                let n = cpu_count();
                let old_seq = smallvec_view(&old(self).bits);
                let new_seq = smallvec_view(&self.bits);
                let len = old_seq.len() as int;
                let idx = (num_parts as int) - 1;
                let k = n % 64;
                let mask: u64 = ((1u64 << (k as usize)) - 1) as u64;
                assert((num_cpus as int) == n);
                assert((num_cpus % BITS_PER_PART) as int == k);
                assert((num_parts as int) == (n + 63) / 64);
                assert(len == (n + 63) / 64);
                assert(idx == len - 1);
                assert(64 * (len - 1) < n);
                assert(0 <= k < 64);
                assert(new_seq.len() == old_seq.len());
                assert(new_seq == old_seq.update(idx, old_seq[idx] & mask));
                assert(mask == (1u64 << (k as usize)) - 1);
                assert forall|j: int| n <= j < 64 * len implies !bit_at(new_seq, j) by {
                    assert(j / 64 == len - 1);
                    assert(j % 64 >= k);
                }
                assert forall|j: int| 0 <= j < n implies
                    bit_at(new_seq, j) == bit_at(old_seq, j) by {
                    if j / 64 < len - 1 {
                        assert(new_seq[j / 64] == old_seq[j / 64]);
                    } else {
                        assert(j / 64 == len - 1);
                        assert(j % 64 < k);
                    }
                }
            }
        }
    }
}

/* impl From<CpuId> for CpuSet {
    fn from(cpu_id: CpuId) -> Self {
        let mut set = Self::new_empty();
        set.add(cpu_id);
        set
    }
} */

/// A subset of all CPUs in the system with atomic operations.
///
/// It provides atomic operations for each CPU in the system. When the
/// operation contains multiple CPUs, the ordering is not guaranteed.
#[derive(Debug)]
pub struct AtomicCpuSet {
    bits: SmallVec<[AtomicInnerPart; NR_PARTS_NO_ALLOC]>,
}

type AtomicInnerPart = AtomicU64;
/* const_assert!(core::mem::size_of::<AtomicInnerPart>() * 8 == BITS_PER_PART); */

impl AtomicCpuSet {
    /// Creates a new `AtomicCpuSet` with an initial value.
    pub fn new(value: CpuSet) -> Self {
        let bits = value.bits.into_iter().map(AtomicU64::new).collect();
        Self { bits }
    }

    /// Loads the value of the set with the given ordering.
    ///
    /// This operation is not atomic. When racing with a [`Self::store`]
    /// operation, this load may return a set that contains a portion of the
    /// new value and a portion of the old value. Load on each specific
    /// word is atomic, and follows the specified ordering.
    ///
    /// Note that load with [`Ordering::Release`] is a valid operation, which
    /// is different from the normal atomic operations. When coupled with
    /// [`Ordering::Release`], it actually performs `fetch_or(0, Release)`.
    pub fn load(&self, ordering: Ordering) -> CpuSet {
        let bits = self
            .bits
            .iter()
            .map(|part| match ordering {
                Ordering::Release => part.fetch_or(0, ordering),
                _ => part.load(ordering),
            })
            .collect();
        CpuSet { bits }
    }

    /// Stores a new value to the set with the given ordering.
    ///
    /// This operation is not atomic. When racing with a [`Self::load`]
    /// operation, that load may return a set that contains a portion of the
    /// new value and a portion of the old value. Load on each specific
    /// word is atomic, and follows the specified ordering.
    pub fn store(&self, value: &CpuSet, ordering: Ordering) {
        for (part, new_part) in self.bits.iter().zip(value.bits.iter()) {
            part.store(*new_part, ordering);
        }
    }

    /// Atomically adds a CPU with the given ordering.
    pub fn add(&self, cpu_id: CpuId, ordering: Ordering) {
        let part_idx = part_idx(cpu_id);
        let bit_idx = bit_idx(cpu_id);
        if part_idx < self.bits.len() {
            self.bits[part_idx].fetch_or(1 << bit_idx, ordering);
        }
    }

    /// Atomically removes a CPU with the given ordering.
    pub fn remove(&self, cpu_id: CpuId, ordering: Ordering) {
        let part_idx = part_idx(cpu_id);
        let bit_idx = bit_idx(cpu_id);
        if part_idx < self.bits.len() {
            self.bits[part_idx].fetch_and(!(1 << bit_idx), ordering);
        }
    }

    /// Atomically checks if the set contains the specified CPU.
    pub fn contains(&self, cpu_id: CpuId, ordering: Ordering) -> bool {
        let part_idx = part_idx(cpu_id);
        let bit_idx = bit_idx(cpu_id);
        part_idx < self.bits.len() && (self.bits[part_idx].load(ordering) & (1 << bit_idx)) != 0
    }
}

// Private auxiliary proof lemmas backing the implementations above. They are
// collected at the end of the file so that the APIs and critical proofs stay in focus.

verus! {

/// If every word of `seq` equals `val`, `bit_at(seq, j)` is just `val & (1<<b) != 0`.
proof fn lemma_bit_at_uniform(seq: Seq<u64>, val: u64, j: int)
    requires
        forall|k: int| 0 <= k < seq.len() ==> seq[k] == val,
        0 <= j < 64 * seq.len() as int,
    ensures
        bit_at(seq, j) == ((val & (1u64 << bit_idx_spec(j))) != 0),
{
    reveal(bit_at);
    assert(seq[part_idx_spec(j) as int] == val);
}

proof fn lemma_u64_nonzero_has_set_bit_aux(word: u64, n: u32)
    requires
        word != 0,
        n <= 64,
        word >> n == 0,
    ensures
        exists|b: u32| b < n && #[trigger] (word & (1u64 << b)) != 0,
    decreases n,
{
    if n == 0 {
        assert(word >> n == word) by (bit_vector)
            requires
                n == 0,
        ;
    } else if word & 1u64 != 0 {
        assert((word & (1u64 << 0u32)) != 0) by (bit_vector)
            requires
                word & 1u64 != 0,
        ;
        assert(exists|b: u32| b < n && #[trigger] (word & (1u64 << b)) != 0);
    } else {
        let shifted = word >> 1u32;
        assert(shifted != 0) by (bit_vector)
            requires
                shifted == word >> 1u32,
                word != 0,
                word & 1u64 == 0,
        ;
        let prev: u32 = (n - 1) as u32;
        assert(prev + 1 == n);
        assert(shifted >> prev == word >> n) by (bit_vector)
            requires
                shifted == word >> 1u32,
                n == prev + 1,
                n <= 64,
        ;
        assert(shifted >> prev == 0);
        lemma_u64_nonzero_has_set_bit_aux(shifted, prev);
        let b = choose|b: u32| b < n - 1 && #[trigger] (shifted & (1u64 << b)) != 0;
        assert(b < 63);
        let next: u32 = (b + 1) as u32;
        assert(next < n);
        assert((word & (1u64 << next)) != 0) by (bit_vector)
            requires
                shifted == word >> 1u32,
                (shifted & (1u64 << b)) != 0,
                next == b + 1,
                b < 63,
        ;
        assert(exists|b: u32| b < n && #[trigger] (word & (1u64 << b)) != 0);
    }
}

proof fn lemma_u64_nonzero_has_set_bit(word: u64)
    requires
        word != 0,
    ensures
        exists|b: u32| b < 64 && #[trigger] (word & (1u64 << b)) != 0,
{
    assert(word >> 64u32 == 0) by (bit_vector);
    lemma_u64_nonzero_has_set_bit_aux(word, 64);
}

proof fn lemma_cpucount_fits()
    ensures
        2 * (parts_for_cpus_spec(cpu_count() as usize) as int) * (size_of::<u64>() as int)
            <= isize::MAX as int,
{
    if cpu_count() > 0 {
        assert(parts_for_cpus_spec(cpu_count() as usize) as int == (cpu_count() + 63) / 64) by {
            reveal(parts_for_cpus_spec)
        };
    }
}

proof fn lemma_count_fits()
    ensures
        64 * parts_for_cpus_spec(cpu_count() as usize) <= usize::MAX,
{
    if cpu_count() > 0 {
        assert(parts_for_cpus_spec(cpu_count() as usize) as int == (cpu_count() + 63) / 64) by {
            reveal(parts_for_cpus_spec)
        };
    }
}

/// A CPU set whose backing words are all zero has an empty abstract view.
proof fn lemma_empty_bits_imply_empty_set(set: &CpuSet)
    requires
        smallvec_view(&set.bits).all(|w: u64| w == 0u64),
    ensures
        set@ == Set::empty(),
{
    let seq = smallvec_view(&set.bits);
    assert forall|k: int| 0 <= k < seq.len() implies seq[k] == 0u64 by {
        let p = |w: u64| w == 0u64;
        assert(p(seq[k]));
    }
    assert forall|j: int| !set@.contains(j) by {
        if 0 <= j < cpu_count() && j < 64 * seq.len() {
            lemma_bit_at_uniform(seq, 0u64, j);
            lemma_u64_and_zero(1u64 << bit_idx_spec(j));
        }
    }
    assert(set@ =~= Set::empty());
}

/// If every backing word has the full-set value, every existing CPU bit is set.
proof fn lemma_full_bits_imply_full_set(set: &CpuSet)
    requires
        set.inv(),
        forall|i: int|
            #![trigger smallvec_view(&set.bits)[i]]
            0 <= i < smallvec_view(&set.bits).len() ==> smallvec_view(&set.bits)[i]
                == full_set_word(cpu_count(), smallvec_view(&set.bits).len() as int, i),
    ensures
        set@ == Set::range(0, cpu_count()),
{
    let seq = smallvec_view(&set.bits);
    let n = cpu_count();
    let len = seq.len() as int;
    assert(n > 0);
    reveal(parts_for_cpus_spec);
    assert(parts_for_cpus_spec(n as usize) as int == (n + 63) / 64);
    assert(len == (n + 63) / 64);
    assert forall|a: int|
        #![trigger set@.contains(a)]
        set@.contains(a) == Set::range(0, n).contains(a) by {
        if 0 <= a < n {
            lemma_fundamental_div_mod(a, 64);
            lemma_fundamental_div_mod(n, 64);
            assert(0 <= a / 64 < len);
            assert(seq[a / 64] == full_set_word(n, len, a / 64));
            let p = a / 64;
            let b = a % 64;
            if a / 64 == len - 1 && n % 64 != 0 {
                assert(a % 64 < n % 64);
                let k = n % 64;
                let mask = seq[p];
                assert(0 < k < 64);
                assert(mask == ((1u64 << (k as usize)) - 1) as u64);
                lemma_u64_masked_bit_keep(!0u64, mask, k, b);
                lemma_u64_allones_bit(b);
                assert(!0u64 & mask == mask) by (bit_vector);
                assert((mask & (1u64 << (b as usize))) != 0);
            } else {
                assert(seq[p] == !0u64);
                lemma_u64_allones_bit(b);
            }
            assert(bit_at(seq, a));
        }
    }
    assert(set@ == Set::range(0, n));
}

} // verus!
#[cfg(ktest)]
mod test {
    use super::*;
    use crate::{cpu::all_cpus, prelude::*};

    #[ktest]
    fn test_full_cpu_set_iter_is_all() {
        let set = CpuSet::new_full();
        let num_cpus = num_cpus();
        let all_cpus = all_cpus().collect::<Vec<_>>();
        let set_cpus = set.iter().collect::<Vec<_>>();

        assert!(set_cpus.len() == num_cpus);
        assert_eq!(set_cpus, all_cpus);
    }

    #[ktest]
    fn test_full_cpu_set_contains_all() {
        let set = CpuSet::new_full();
        for cpu_id in all_cpus() {
            assert!(set.contains(cpu_id));
        }
    }

    #[ktest]
    fn test_empty_cpu_set_iter_is_empty() {
        let set = CpuSet::new_empty();
        let set_cpus = set.iter().collect::<Vec<_>>();
        assert!(set_cpus.is_empty());
    }

    #[ktest]
    fn test_empty_cpu_set_contains_none() {
        let set = CpuSet::new_empty();
        for cpu_id in all_cpus() {
            assert!(!set.contains(cpu_id));
        }
    }

    #[ktest]
    fn test_atomic_cpu_set_multiple_sizes() {
        for test_num_cpus in [1usize, 3, 12, 64, 96, 99, 128, 256, 288, 1024] {
            let test_all_iter = || (0..test_num_cpus).map(|id| CpuId(id as u32));

            let set = CpuSet::with_capacity_val(test_num_cpus, 0);
            let atomic_set = AtomicCpuSet::new(set);

            for cpu_id in test_all_iter() {
                assert!(!atomic_set.contains(cpu_id, Ordering::Relaxed));
                if cpu_id.as_usize() % 3 == 0 {
                    atomic_set.add(cpu_id, Ordering::Relaxed);
                }
            }

            let loaded = atomic_set.load(Ordering::Relaxed);
            for cpu_id in loaded.iter() {
                if cpu_id.as_usize() % 3 == 0 {
                    assert!(loaded.contains(cpu_id));
                } else {
                    assert!(!loaded.contains(cpu_id));
                }
            }

            atomic_set.store(
                &CpuSet::with_capacity_val(test_num_cpus, 0),
                Ordering::Relaxed,
            );

            for cpu_id in test_all_iter() {
                assert!(!atomic_set.contains(cpu_id, Ordering::Relaxed));
                atomic_set.add(cpu_id, Ordering::Relaxed);
            }
        }
    }
}
