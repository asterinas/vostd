// SPDX-License-Identifier: MPL-2.0
//! This module contains the implementation of the CPU set and atomic CPU set.
use super::cpu_count;
use vstd::{
    assert_seqs_equal, layout::size_of, prelude::*, set::Set, std_specs::iter::IteratorSpec,
};
use vstd_extra::{
    bits::{group_u64_bit_algebra, lemma_u64_and_zero, u64_bit_is_set},
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
    cpu_id.as_usize() / BITS_PER_PART
}

#[verus_verify]
#[verus_spec(
    returns bit_idx_spec(cpu_id@),
)]
const fn bit_idx(cpu_id: CpuId) -> usize {
    cpu_id.as_usize() % BITS_PER_PART
}

#[verus_verify]
#[verifier::when_used_as_spec(parts_for_cpus_spec)]
#[verus_spec(
    returns parts_for_cpus_spec(num_cpus),
)]
const fn parts_for_cpus(num_cpus: usize) -> usize {
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
spec fn parts_for_cpus_spec(n: usize) -> usize {
    if n == 0 {
        0
    } else {
        ((n + 63) / 64) as usize
    }
}

/// The 64-bit word holding bit `i`.
spec fn part_idx_spec(i: int) -> usize {
    (i / 64) as usize
}

/// The position of bit `i` within its 64-bit word.
spec fn bit_idx_spec(i: int) -> usize {
    (i % 64) as usize
}

/// Number of set bits in all words of `seq`.
spec fn count_set_bits(seq: Seq<u64>) -> int {
    seq.fold_left(0, |count: int, word: u64| count + u64_set_bits(word))
}

/// Bit `i` is set in the bit sequence `seq`.
spec fn bit_at(seq: Seq<u64>, i: int) -> bool {
    if 0 <= i < 64 * seq.len() as int {
        u64_bit_is_set(seq[part_idx_spec(i) as int], i % 64)
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
        let mut ret = Self::with_capacity_val(num_cpus(), !0);
        ret.clear_nonexistent_cpu_bits();
        ret
    }

    /// Creates a new `CpuSet` with no CPUs in the system.
    #[verus_spec(ret =>
        ensures
            ret@ == Set::empty(),
            ret.inv(),
    )]
    pub fn new_empty() -> Self {
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
        if part_idx >= self.bits.len() {
            self.bits.resize(part_idx + 1, 0);
        }
        self.bits[part_idx] |= 1 << bit_idx;
        proof! {
            let n = cpu_count();
            let old_seq = smallvec_view(&old(self).bits);
            let new_seq = smallvec_view(&self.bits);
            let len = old_seq.len() as int;
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
        let part_idx = part_idx(cpu_id);
        let bit_idx = bit_idx(cpu_id);
        if part_idx < self.bits.len() {
            self.bits[part_idx] &= !(1 << bit_idx);
            proof! {
                let n = cpu_count();
                let old_seq = smallvec_view(&old(self).bits);
                let new_seq = smallvec_view(&self.bits);
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
        part_idx < self.bits.len() && (self.bits[part_idx] & (1 << bit_idx)) != 0
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
            let part = self.bits[idx];
            let part_count = part.count_ones() as usize;
            proof! {
                let seq = smallvec_view(&self.bits);
                assert_seqs_equal!(
                    seq.subrange(0, idx + 1).drop_last() == seq.subrange(0, idx as int)
                );
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
                lemma_u64_nonzero_has_set_bit(*initial[idx]);
                let b = choose|b: int| 0 <= b < 64 && #[trigger] u64_bit_is_set(*initial[idx], b);
                let j = 64 * idx + b;
                assert(bit_at(seq, j));
                assert(self@.contains(j));
            }
        }
        ret
    }

    /// Returns true if the set is full.
    #[verus_spec(ret =>
        requires
            self.inv(),
        returns self@ == Set::range(0, cpu_count()),
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
            if self.bits[idx] != expected {
                proof! {
                    lemma_mismatched_word_imply_not_full_set(self, idx as int);
                }
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
                    (self.bits[part_idx] & (1 << bit_idx)) != 0
                },
            )
            .map(
                #[verus_spec(ret: CpuId =>
                    requires
                        bit_at(smallvec_view(&self.bits), id as int),
                    ensures
                        ret == CpuId(id as u32),
                )]
                move |id| CpuId(id as u32),
            )
    }

    /// Only for internal use. Build a vector of `num_cpus`-covering words, all equal to `val`.
    #[verus_spec(ret =>
        requires
            num_cpus == cpu_count(),
            2 * parts_for_cpus_spec(num_cpus) * size_of::<u64>() <= isize::MAX,
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
            self.bits[num_parts - 1] &= (1 << (num_cpus % BITS_PER_PART)) - 1;
            proof! {
                let n = cpu_count();
                let old_seq = smallvec_view(&old(self).bits);
                let new_seq = smallvec_view(&self.bits);
                assert forall|j: int| 0 <= j < n implies
                    bit_at(new_seq, j) == bit_at(old_seq, j) by {}
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

/// Expected value of word `idx` in a full CPU set.
spec fn full_set_word(num_cpus: int, len: int, idx: int) -> u64 {
    if idx == len - 1 && bit_idx_spec(num_cpus) != 0 {
        ((1u64 << bit_idx_spec(num_cpus)) - 1) as u64
    } else {
        !0u64
    }
}

proof fn lemma_u64_nonzero_has_set_bit_aux(word: u64, n: int)
    requires
        word != 0,
        0 <= n <= 64,
        word >> (n as u32) == 0,
    ensures
        exists|b: int| 0 <= b < n && #[trigger] u64_bit_is_set(word, b),
    decreases n,
{
    if n == 0 {
        assert(word >> (0u32) == word) by (bit_vector);
    } else if u64_bit_is_set(word, 0) {
        assert(u64_bit_is_set(word, 0));
    } else {
        let shifted = word >> 1u32;
        assert((word & (1u64 << 0usize)) == 0u64);
        assert(shifted != 0) by (bit_vector)
            requires
                shifted == word >> 1u32,
                word != 0,
                (word & (1u64 << 0usize)) == 0u64,
        ;
        let prev: int = n - 1;
        let nu: u32 = n as u32;
        let prevu: u32 = (n - 1) as u32;
        assert(shifted >> prevu == word >> nu) by (bit_vector)
            requires
                shifted == word >> 1u32,
                nu == prevu + 1,
                nu <= 64,
        ;
        lemma_u64_nonzero_has_set_bit_aux(shifted, prev);
        let b = choose|b: int| 0 <= b < n - 1 && #[trigger] u64_bit_is_set(shifted, b);
        let bu: u32 = b as u32;
        let next: u32 = (b + 1) as u32;
        assert(u64_bit_is_set(word, b + 1)) by {
            assert((word & (1u64 << next)) != 0) by (bit_vector)
                requires
                    shifted == word >> 1u32,
                    (shifted & (1u64 << bu)) != 0,
                    next == bu + 1,
                    bu < 63,
            ;
        };
        assert(0 <= b + 1 < n && u64_bit_is_set(word, b + 1));
    }
}

proof fn lemma_u64_nonzero_has_set_bit(word: u64)
    requires
        word != 0,
    ensures
        exists|b: int| 0 <= b < 64 && #[trigger] u64_bit_is_set(word, b),
{
    assert(word >> 64u32 == 0) by (bit_vector);
    lemma_u64_nonzero_has_set_bit_aux(word, 64);
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
            lemma_u64_and_zero(1u64 << bit_idx_spec(j));
        }
    }
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
    assert forall|a: int|
        #![trigger set@.contains(a)]
        set@.contains(a) == Set::range(0, n).contains(a) by {
        if 0 <= a < n {
            let p = a / 64;
            if a / 64 == len - 1 && n % 64 != 0 {
                let mask = seq[p];
                // Materialize the `!0u64 & mask` term: the broadcast masked-bit lemmas
                // then chain (with `!0u64` as the word) to show that every in-range bit
                // of the partial last word is set.
                assert(!0u64 & mask == mask) by (bit_vector);
            }
        }
    }
}

/// Two distinct `u64` words differ at some unit bit.
proof fn lemma_u64_distinct_bits_differ(x: u64, y: u64)
    requires
        x != y,
    ensures
        exists|b: int|
            0 <= b < 64 && (#[trigger] (x & (1u64 << (b as usize)))) != (y & (1u64 << (
            b as usize))),
{
    let diff: u64 = x ^ y;
    assert(diff != 0u64) by (bit_vector)
        requires
            diff == x ^ y,
            x != y,
    ;
    lemma_u64_nonzero_has_set_bit(diff);
    let b = choose|b: int| 0 <= b < 64 && #[trigger] u64_bit_is_set(diff, b);
    let bu: u32 = b as u32;
    assert((x & (1u64 << bu)) != (y & (1u64 << bu))) by (bit_vector)
        requires
            (diff & (1u64 << bu)) != 0,
            diff == x ^ y,
    ;
}

/// ANDing with the unit bit at `b` yields `0` or the unit bit itself.
proof fn lemma_u64_unit_bit_projection(x: u64, b: int)
    requires
        0 <= b < 64,
    ensures
        !u64_bit_is_set(x, b) || ((x & (1u64 << (b as usize))) == (1u64 << (b as usize))),
{
    let bu: u32 = b as u32;
    assert((x & (1u64 << bu)) == 0u64 || (x & (1u64 << bu)) == (1u64 << bu)) by (bit_vector);
}

/// If some backing word differs from its full-set value, the abstract view is not
/// the full CPU range: the differing bit is either a missing CPU bit (below
/// `cpu_count`), or a set nonexistent bit, which `inv` rules out.
proof fn lemma_mismatched_word_imply_not_full_set(set: &CpuSet, p: int)
    requires
        set.inv(),
        0 <= p < smallvec_view(&set.bits).len() as int,
        smallvec_view(&set.bits)[p] != full_set_word(
            cpu_count(),
            smallvec_view(&set.bits).len() as int,
            p,
        ),
    ensures
        set@ != Set::range(0, cpu_count()),
{
    let seq = smallvec_view(&set.bits);
    let n = cpu_count();
    let len = seq.len() as int;
    let k = n % 64;
    if k != 0 {
    } else {
    }
    // A bit where the word differs from its full-set value.
    let word = seq[p];
    let expected = full_set_word(n, len, p);
    lemma_u64_distinct_bits_differ(word, expected);
    let b = choose|b: int|
        0 <= b < 64 && (#[trigger] (word & (1u64 << (b as usize)))) != (expected & (1u64 << (
        b as usize)));
    lemma_u64_unit_bit_projection(word, b);
    lemma_u64_unit_bit_projection(expected, b);
    let j = 64 * p + b;
    assert(set@.contains(j) == (0 <= j < n && bit_at(seq, j)));
    if p == len - 1 && k != 0 {
        if u64_bit_is_set(expected, b) {
            // The mask only keeps bits below `k`, so `j` is a missing CPU bit.
            if b >= k {
                assert(!0u64 & expected == expected) by (bit_vector);
                assert(false);
            }
        } else {
            // A set bit at or above `n` would violate the clear-tail invariant.
            if b < k {
                assert(!0u64 & expected == expected) by (bit_vector);
                assert(false);
            }
            assert(bit_at(seq, j));
            assert(false);
        }
    } else {
        if p < len - 1 {
        } else {
        }
    }
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
