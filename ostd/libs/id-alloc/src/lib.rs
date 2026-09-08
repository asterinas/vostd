// SPDX-License-Identifier: MPL-2.0
#![cfg_attr(not(test), no_std)]
#![deny(unsafe_code)]
#![feature(proc_macro_hygiene)]
#![expect(internal_features)]

use ::bitvec::prelude::BitVec;
use vstd::prelude::*;
use vstd_extra::{debug_assert, prelude::*};

use core::{fmt::Debug, ops::Range};

verus! {

/// The index of the first `false` bit in `s`, or `s.len()` if every bit is `true`.
pub open spec fn is_first_zero(s: Seq<bool>, i: int) -> bool {
    &&& 0 <= i <= s.len()
    &&& (forall|j: int| #![trigger s.index(j)] 0 <= j < i ==> s.index(j))
    &&& (i < s.len() ==> !s.index(i))
}

/// Index of the first `false` bit, or `s.len()` if every bit is `true`. Defined
/// recursively so it is deterministic and the SMT solver can unfold it.
pub open spec fn first_zero_seq(s: Seq<bool>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else if !s.index(0) {
        0
    } else {
        1 + first_zero_seq(s.subrange(1, s.len() as int))
    }
}

// Bring the bitvec bridge's broadcast axioms into scope so they fire at call sites.
broadcast use {
    group_bitvec_models,
    axiom_bitvec_index_usize,
    axiom_bitvec_index_req,
    axiom_bitslice_get_range,
    axiom_bitvec_len_bound,
};

} // verus!
/// An id allocator implemented by the bitmap.
/// The true bit implies that the id is allocated, and vice versa.
///
/// # Verified Invariant
///
/// `first_available_id == first_zero_seq(self@)`: it is the index of the first
/// free (`false`) bit, or the length when the bitmap is full. Consequently every
/// bit before `first_available_id` is `true` and (unless full) the bit at
/// `first_available_id` is `false`.
#[derive(Clone)]
#[verifier::allow(autoderive_clone_without_spec)]
#[verus_verify]
pub struct IdAlloc {
    bitset: BitVec<u8>,
    first_available_id: usize,
}

verus! {

impl View for IdAlloc {
    type V = Seq<bool>;

    closed spec fn view(&self) -> Seq<bool> {
        bitvec_view(&self.bitset)
    }
}

impl Inv for IdAlloc {
    /// The well-formedness invariant: `first_available_id` is the first free bit.
    closed spec fn inv(self) -> bool {
        &&& 0 <= self.first_available_id <= self@.len()
        &&& self.first_available_id == first_zero_seq(self@)
    }
}

/// `is_first_zero` is uniquely satisfied. Broadcast so it auto-fires whenever two
/// `is_first_zero` facts arise.
pub broadcast proof fn lemma_is_first_zero_unique(s: Seq<bool>, i: int, j: int)
    requires
        is_first_zero(s, i),
        is_first_zero(s, j),
    ensures
        #![auto]
        i == j,
{
    if i < j {
        assert(false);
    } else if j < i {
        assert(false);
    }
}

/// `first_zero_seq(s)` itself satisfies `is_first_zero` (induction on `s.len()`).
proof fn lemma_first_zero_seq_char(s: Seq<bool>)
    ensures
        is_first_zero(s, first_zero_seq(s)),
    decreases s.len(),
{
    if s.len() == 0 {
    } else if !s.index(0) {
    } else {
        let sub = s.subrange(1, s.len() as int);
        lemma_first_zero_seq_char(sub);
        let i2 = first_zero_seq(sub);
        assert(is_first_zero(s, 1 + i2)) by {
            assert forall|j: int| 0 <= j < 1 + i2 implies s.index(j) by {
                if j == 0 {
                } else {
                    assert(s.index(j) == sub.index(j - 1));
                }
            }
            if 1 + i2 < s.len() {
            }
        }
    }
}

/// If the prefix `[0, k)` of `s` is all `true`, then the first zero of `s` is
/// `k` plus the first zero of the remainder (induction on `s.len()`).
proof fn lemma_first_zero_seq_prefix_all_true(s: Seq<bool>, k: int)
    requires
        0 <= k <= s.len(),
        forall|j: int| #![trigger s.index(j)] 0 <= j < k ==> s.index(j),
    ensures
        first_zero_seq(s) == k + first_zero_seq(s.subrange(k, s.len() as int)),
    decreases s.len(),
{
    if k == 0 {
        assert(s.subrange(0, s.len() as int) =~= s) by {}
    } else if s.len() == 0 {
    } else {
        let sub = s.subrange(1, s.len() as int);
        lemma_first_zero_seq_prefix_all_true(sub, k - 1);
        assert(sub.subrange(k - 1, sub.len() as int) =~= s.subrange(k, s.len() as int)) by {}
    }
}

/// Setting the bit at `k - 1` (the current first zero) to `true`, when the prefix
/// `[0, k - 1)` is all `true`, advances the first zero to
/// `k + first_zero_seq(s.subrange(k, len))`.
proof fn lemma_first_zero_seq_advance_after_set(s: Seq<bool>, k: int)
    requires
        0 < k <= s.len(),
        forall|j: int| 0 <= j < k - 1 ==> s.index(j),
        k - 1 < s.len() ==> !s.index(k - 1),
    ensures
        first_zero_seq(s.update(k - 1, true)) == k + first_zero_seq(s.subrange(k, s.len() as int)),
{
    let t = s.update(k - 1, true);
    lemma_first_zero_seq_prefix_all_true(t, k);
    assert(t.subrange(k, s.len() as int) =~= s.subrange(k, s.len() as int)) by {}
}

/// Element-wise-equal sequences have the same `first_zero_seq`.
proof fn lemma_first_zero_seq_ext_equal(a: Seq<bool>, b: Seq<bool>)
    requires
        a =~= b,
    ensures
        first_zero_seq(a) == first_zero_seq(b),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(b.len() == 0);
    } else if !a.index(0) {
        assert(!b.index(0));
    } else {
        lemma_first_zero_seq_ext_equal(
            a.subrange(1, a.len() as int),
            b.subrange(1, b.len() as int),
        );
    }
}

/// Clearing a `true` bit at `i` moves the first zero to `min(first_zero_seq(s), i)`.
proof fn lemma_first_zero_seq_clear(s: Seq<bool>, i: int)
    requires
        0 <= i < s.len(),
        s.index(i),
    ensures
        first_zero_seq(s.update(i, false)) == if first_zero_seq(s) <= i {
            first_zero_seq(s)
        } else {
            i
        },
    decreases s.len(),
{
    let fz = first_zero_seq(s);
    lemma_first_zero_seq_char(s);
    let t = s.update(i, false);
    lemma_first_zero_seq_char(t);
    if fz <= i {
        assert(is_first_zero(t, fz)) by {
            if fz < s.len() {
                assert(!t.index(fz)) by {
                    if fz == i {
                        assert(t.index(fz) == false);
                    } else {
                        assert(t.index(fz) == s.index(fz));
                        assert(!s.index(fz));
                    }
                }
            }
            assert(forall|j: int| 0 <= j < fz ==> t.index(j)) by {
                assert(forall|j: int| 0 <= j < fz ==> s.index(j));
            }
        }
        lemma_is_first_zero_unique(t, first_zero_seq(t), fz);
    } else {
        assert(is_first_zero(t, i)) by {
            assert(!t.index(i));
            assert(forall|j: int| 0 <= j < i ==> t.index(j)) by {
                assert(forall|j: int| 0 <= j < i ==> s.index(j));
            }
        }
        lemma_is_first_zero_unique(t, first_zero_seq(t), i);
    }
}

/// Clearing all bits in `[start, end)` moves the first zero to
/// `min(first_zero_seq(s), start)`.
proof fn lemma_first_zero_seq_clear_range(s: Seq<bool>, t: Seq<bool>, start: int, end: int)
    requires
        s.len() == t.len(),
        0 <= start < end <= s.len(),
        forall|j: int| #![trigger t.index(j)] 0 <= j < start ==> t.index(j) == s.index(j),
        forall|j: int| #![trigger t.index(j)] start <= j < end ==> !t.index(j),
        forall|j: int| #![trigger t.index(j)] end <= j < s.len() ==> t.index(j) == s.index(j),
    ensures
        first_zero_seq(t) == if first_zero_seq(s) <= start {
            first_zero_seq(s)
        } else {
            start
        },
{
    let fz = first_zero_seq(s);
    lemma_first_zero_seq_char(s);
    lemma_first_zero_seq_char(t);
    if fz <= start {
        assert(is_first_zero(t, fz)) by {
            if fz < s.len() {
                assert(!t.index(fz)) by {
                    if fz < start {
                        assert(t.index(fz) == s.index(fz));
                        assert(!s.index(fz));
                    }
                }
            }
            assert(forall|j: int| 0 <= j < fz ==> t.index(j)) by {
                assert(forall|j: int| 0 <= j < fz ==> s.index(j));
                assert(forall|j: int| 0 <= j < fz ==> t.index(j) == s.index(j));
            }
        }
        lemma_is_first_zero_unique(t, first_zero_seq(t), fz);
    } else {
        assert(is_first_zero(t, start)) by {
            assert(!t.index(start));
            assert(forall|j: int| 0 <= j < start ==> t.index(j)) by {
                assert(forall|j: int| 0 <= j < start ==> s.index(j));
            }
        }
        lemma_is_first_zero_unique(t, first_zero_seq(t), start);
    }
}

/// Setting a `false` bit at `i` that is strictly past the first zero leaves the
/// first zero unchanged.
proof fn lemma_first_zero_seq_set_after_first_zero(s: Seq<bool>, i: int)
    requires
        0 <= i < s.len(),
        first_zero_seq(s) < i,
        !s.index(i),
    ensures
        first_zero_seq(s.update(i, true)) == first_zero_seq(s),
{
    let fz = first_zero_seq(s);
    lemma_first_zero_seq_char(s);
    let t = s.update(i, true);
    lemma_first_zero_seq_char(t);
    assert(is_first_zero(t, fz)) by {
        if fz < s.len() {
            assert(!t.index(fz)) by {
                assert(fz < i);
                assert(t.index(fz) == s.index(fz));
                assert(!s.index(fz));
            }
        }
        assert forall|j: int| 0 <= j < fz implies t.index(j) by {
            assert(t.index(j) == s.index(j));
            assert(s.index(j));
        }
    }
    lemma_is_first_zero_unique(t, first_zero_seq(t), fz);
}

} // verus!
#[verus_verify]
impl IdAlloc {
    /// Constructs a new id allocator with a maximum capacity.
    #[verus_spec(ret =>
        requires
            capacity <= usize::MAX / 8,
        ensures
            ret@ == Seq::new(capacity as nat, |i: int| false),
            ret.inv(),
    )]
    pub fn with_capacity(capacity: usize) -> Self {
        let mut bitset = BitVec::with_capacity(capacity);
        bitset.resize(capacity, false);
        Self {
            bitset,
            first_available_id: 0,
        }
    }

    /// Allocates and returns a new `id`.
    ///
    /// If allocation is not possible, it returns `None`.
    #[verus_spec(res =>
        requires
            old(self).inv(),
        ensures
            res matches Some(id) ==> {
                &&& id == first_zero_seq(old(self)@)
                &&& first_zero_seq(old(self)@) < old(self)@.len()
                &&& final(self)@ == old(self)@.update(first_zero_seq(old(self)@), true)
                &&& final(self).inv()
            },
            res is None ==> {
                &&& first_zero_seq(old(self)@) == old(self)@.len()
                &&& final(self)@ == old(self)@
                &&& final(self).inv()
            },
    )]
    pub fn alloc(&mut self) -> Option<usize> {
        if self.first_available_id < self.bitset.len() {
            let id = self.first_available_id;
            proof! {
                lemma_first_zero_seq_char(self@);
            }
            self.bitset.set(id, true);
            self.update_first_available_id(id + 1);
            Some(id)
        } else {
            None
        }
    }

    /// Allocates a consecutive range of new `id`s.
    ///
    /// The `count` is the number of consecutive `id`s to allocate. If it is 0, return `None`.
    ///
    /// If allocation is not possible, it returns `None`.
    ///
    /// TODO: Choose a more efficient strategy.
    #[verus_spec(res =>
        requires
            old(self).inv(),
        ensures
            res matches Some(r) ==> {
                &&& r.end - r.start == count
                &&& 0 <= r.start
                &&& r.end <= old(self)@.len()
                &&& (forall|i: int| #![trigger old(self)@[i]] r.start <= i < r.end ==> !old(self)@[i])
                &&& (forall|i: int| #![trigger final(self)@[i]] r.start <= i < r.end ==> final(self)@[i])
                &&& (forall|i: int| 0 <= i < final(self)@.len() && !(r.start <= i < r.end) ==> final(self)@[i] == old(self)@[i])
                &&& final(self)@.len() == old(self)@.len()
                &&& final(self).inv()
            },
            res is None ==> {
                &&& final(self)@ == old(self)@
                &&& final(self).inv()
            },
    )]
    pub fn alloc_consecutive(&mut self, count: usize) -> Option<Range<usize>> {
        if count == 0 {
            return None;
        }

        let end = self.first_available_id.checked_add(count)?;
        if end > self.bitset.len() {
            return None;
        }

        let allocated_range = {
            let mut curr_range = self.first_available_id..self.first_available_id + 1;
            proof! {
                lemma_first_zero_seq_char(self@);
            }
            #[verus_spec(invariant
                count > 0,
                self@ == old(self)@,
                self.first_available_id == old(self).first_available_id,
                self.first_available_id <= curr_range.start,
                curr_range.start <= curr_range.end,
                curr_range.end <= self@.len(),
                range_usize_len_spec(&curr_range) <= count,
                forall|j: int| #![trigger self@[j]] curr_range.start as int <= j < curr_range.end as int ==> !self@[j],
                decreases self@.len() as int - curr_range.end as int,
            )]
            /* `Range::len` is unspecced by vstd.
             * Origin Rust: while curr_range.len() < count && curr_range.end < self.bitset.len() {
             */
            while range_usize_len(&curr_range) < count && curr_range.end < self.bitset.len() {
                if !self.is_allocated(curr_range.end) {
                    curr_range.end += 1;
                } else {
                    curr_range = curr_range.end + 1..curr_range.end + 1;
                }
            }

            if range_usize_len(&curr_range) < count {
                return None;
            }

            curr_range
        };

        #[verus_spec(invariant
            self@.len() == old(self)@.len(),
            0 <= allocated_range.start,
            allocated_range.end <= self@.len(),
            allocated_range.start <= id,
            id <= allocated_range.end,
            forall|j: int| #![trigger self@[j]] allocated_range.start as int <= j < id as int ==> self@[j],
            forall|j: int| 0 <= j < self@.len() && !(allocated_range.start as int <= j < id as int) ==> self@[j] == old(self)@[j],
        )]
        /* `Range::clone` is unspecced; iterate `start..end` directly.
         * Origin Rust: for id in allocated_range.clone()
         */
        for id in allocated_range.start..allocated_range.end {
            self.bitset.set(id, true);
        }

        if self.is_allocated(self.first_available_id) {
            self.update_first_available_id(allocated_range.end);
        }

        proof! {
            let faid = old(self).first_available_id as int;
            if faid < allocated_range.start as int {
                lemma_first_zero_seq_char(self@);
            }
        }

        Some(allocated_range)
    }

    /// Releases the consecutive range of allocated `id`s.
    ///
    /// # Panics
    ///
    /// If the `range` is out of bounds, this method will panic.
    #[verus_spec(
        requires
            old(self).inv(),
            range.end <= self@.len(),
            forall|i: int| range.start <= i < self@.len() && i < range.end ==> self@[i],
        ensures
            final(self)@.len() == old(self)@.len(),
            forall|i: int| #![trigger final(self)@[i]] range.start <= i < range.end ==> !final(self)@[i],
            forall|i: int|
                0 <= i < final(self)@.len() && !(range.start <= i < range.end) ==> final(self)@[i] == old(self)@[i],
            final(self).inv(),
    )]
    pub fn free_consecutive(&mut self, range: Range<usize>) {
        /* `Range::is_empty` is unspecced by vstd.
         * Origin Rust: if range.is_empty() {
         */
        if range_usize_is_empty(&range) {
            return;
        }

        let range_start = range.start;
        #[verus_spec(invariant
            self@.len() == old(self)@.len(),
            0 <= range.start,
            range.end <= self@.len(),
            range.start <= id,
            id <= range.end,
            forall|j: int| #![trigger self@[j]] range.start as int <= j < id as int ==> !self@[j],
            forall|j: int| 0 <= j < self@.len() && !(range.start as int <= j < id as int) ==> self@[j] == old(self)@[j],
        )]
        /* Drop `.clone()` (range unused after) and the in-loop `debug_assert` (already required).
         * Origin Rust: for id in range.clone() { debug_assert!(self.is_allocated(id));
         */
        for id in range {
            self.bitset.set(id, false);
        }

        if range_start < self.first_available_id {
            self.first_available_id = range_start
        }
        proof! {
            lemma_first_zero_seq_clear_range(
                old(self)@,
                self@,
                range.start as int,
                range.end as int,
            );
        }
    }

    /// Releases the allocated `id`.
    ///
    /// # Panics
    ///
    /// If the `id` is out of bounds, this method will panic.
    #[verus_spec(
        requires
            old(self).inv(),
            id < self@.len(),
            self@[id as int],
        ensures
            final(self)@ == old(self)@.update(id as int, false),
            final(self).inv(),
    )]
    pub fn free(&mut self, id: usize) {
        debug_assert!(self.is_allocated(id));

        self.bitset.set(id, false);
        proof! {
            lemma_first_zero_seq_clear(old(self)@, id as int);
        }
        if id < self.first_available_id {
            self.first_available_id = id;
        }
    }

    /// Allocates a specific ID.
    ///
    /// If the ID is already allocated, it returns `None`, otherwise it
    /// returns the allocated ID.
    ///
    /// # Panics
    ///
    /// If the `id` is out of bounds, this method will panic.
    #[verus_spec(res =>
        requires
            old(self).inv(),
            id < self@.len(),
        ensures
            res is Some ==> {
                &&& final(self)@ == old(self)@.update(id as int, true)
                &&& res == (if old(self)@[id as int] { None } else { Some(id) })
                &&& final(self).inv()
            },
            res is None ==> final(self)@ == old(self)@ && final(self).inv(),
    )]
    pub fn alloc_specific(&mut self, id: usize) -> Option<usize> {
        if self.bitset[id] {
            return None;
        }
        self.bitset.set(id, true);
        if id == self.first_available_id {
            proof! {
                lemma_first_zero_seq_char(old(self)@);
            }
            self.update_first_available_id(id + 1);
        }
        proof! {
            if id != old(self).first_available_id {
                lemma_first_zero_seq_char(old(self)@);
                lemma_first_zero_seq_set_after_first_zero(old(self)@, id as int);
            }
        }
        Some(id)
    }

    /// Returns true if the `id` is allocated.
    ///
    /// # Panics
    ///
    /// If the `id` is out of bounds, this method will panic.
    #[verus_spec(ret =>
        requires
            id < self@.len(),
        ensures
            ret == self@[id as int],
    )]
    pub fn is_allocated(&self, id: usize) -> bool {
        self.bitset[id]
    }

    /// Updates the `first_available_id` field to the first zero index at or after `start`.
    #[verus_spec(
        requires
            0 <= self.first_available_id <= self@.len(),
            0 <= start <= self@.len(),
            forall|i: int| #![trigger self@[i]] 0 <= i < start ==> self@[i],
        ensures
            final(self)@ == old(self)@,
            final(self).first_available_id == first_zero_seq(final(self)@),
            final(self).inv(),
    )]
    fn update_first_available_id(&mut self, start: usize) {
        let bit_slice = self
            .bitset
            .get(start..self.bitset.len())
            .expect("start is guaranteed to be valid by the caller");
        /* Bind the bounded `first_zero` result (avoid closure overflow + enable proof).
         * Origin Rust: self.first_available_id = bit_slice.first_zero().map(|offset| start + offset).unwrap_or(len);
         */
        self.first_available_id = match bit_slice.first_zero() {
            Some(offset) => start + offset,
            None => self.bitset.len(),
        };
        proof! {
            lemma_first_zero_seq_prefix_all_true(self@, start as int);
            let tail = self@.subrange(start as int, self@.len() as int);
            lemma_first_zero_seq_char(self@);
            assert(is_first_zero(bitslice_view(bit_slice), first_zero_seq(tail)));
        }
    }
}

impl Debug for IdAlloc {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("IdAlloc")
            .field("len", &self.bitset.len())
            .field("first_available_id", &self.first_available_id)
            .finish()
    }
}

#[cfg(test)]
mod test {
    use super::IdAlloc;

    #[test]
    fn bitmap_alloc_out_of_bounds() {
        let capacity = 16;
        let mut bitmap = IdAlloc::with_capacity(capacity);

        for _ in 0..capacity {
            assert!(bitmap.alloc().is_some());
        }

        // Allocating one more ID should fail since the
        // bitmap's `first_available_id` + `count` is out of bounds.
        assert!(bitmap.alloc_consecutive(1).is_none());
    }
}
