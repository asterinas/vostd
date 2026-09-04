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
    /// `closed` so the (private-field-referencing) body is not exposed across the
    /// crate boundary; proofs reveal it locally.
    closed spec fn inv(self) -> bool {
        &&& 0 <= self.first_available_id <= self@.len()
        &&& self.first_available_id == first_zero_seq(self@)
    }
}

/// `is_first_zero` is uniquely satisfied. Broadcast so it auto-fires whenever two
/// `is_first_zero` facts arise (e.g. connecting an exec `first_zero` result to
/// `first_zero_seq`).
pub broadcast proof fn lemma_is_first_zero_unique(s: Seq<bool>, i: int, j: int)
    requires
        is_first_zero(s, i),
        is_first_zero(s, j),
    ensures
        #![auto]
        i == j,
{
    if i < j {
        assert(s.index(i));
        assert(false);
    } else if j < i {
        assert(s.index(j));
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
        assert(is_first_zero(s, 0));
    } else {
        let sub = s.subrange(1, s.len() as int);
        lemma_first_zero_seq_char(sub);
        let i2 = first_zero_seq(sub);
        assert(is_first_zero(s, 1 + i2)) by {
            assert(0 < 1 + i2 <= s.len()) by {
                assert(i2 <= sub.len());
                assert(sub.len() == s.len() - 1);
            }
            assert forall|j: int| 0 <= j < 1 + i2 implies s.index(j) by {
                if j == 0 {
                    assert(s.index(0));
                } else {
                    assert(s.index(j) == sub.index(j - 1));
                }
            }
            if 1 + i2 < s.len() {
                assert(!s.index(1 + i2)) by {
                    assert(s.index(1 + i2) == sub.index(i2));
                }
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
        assert(s.subrange(0, s.len() as int) =~= s) by {
            assert forall|j: int| #![auto] 0 <= j < s.len() implies s.subrange(
                0,
                s.len() as int,
            ).index(j) == s.index(j) by {
                assert(s.subrange(0, s.len() as int).index(j) == s.index(0 + j));
            }
        }
    } else if s.len() == 0 {
        assert(k == 0);
    } else {
        let sub = s.subrange(1, s.len() as int);
        lemma_first_zero_seq_prefix_all_true(sub, k - 1);
        assert(sub.subrange(k - 1, sub.len() as int) =~= s.subrange(k, s.len() as int)) by {
            assert forall|j: int| 0 <= j < s.len() - k implies sub.subrange(
                k - 1,
                sub.len() as int,
            ).index(j) == s.subrange(k, s.len() as int).index(j) by {
                assert(sub.subrange(k - 1, sub.len() as int).index(j) == sub.index(k - 1 + j));
                assert(sub.index(k - 1 + j) == s.index(k + j));
                assert(s.subrange(k, s.len() as int).index(j) == s.index(k + j));
            }
        }
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
    // The prefix [0, k) of `t` is all true (the changed bit at k-1 is set).
    assert(forall|j: int| #![trigger t.index(j)] 0 <= j < k ==> t.index(j)) by {
        assert forall|j: int| 0 <= j < k implies t.index(j) by {
            if j == k - 1 {
                assert(t.index(j));
            } else {
                assert(t.index(j) == s.index(j));
            }
        }
    }
    lemma_first_zero_seq_prefix_all_true(t, k);
    // The suffix [k, len) is unchanged by the update at k-1, so the subranges agree.
    assert(t.subrange(k, s.len() as int) =~= s.subrange(k, s.len() as int)) by {
        assert forall|j: int| 0 <= j < s.len() - k implies t.subrange(k, s.len() as int).index(j)
            == s.subrange(k, s.len() as int).index(j) by {
            assert(t.subrange(k, s.len() as int).index(j) == t.index(k + j));
            assert(s.subrange(k, s.len() as int).index(j) == s.index(k + j));
            assert(t.index(k + j) == s.index(k + j));
        }
    }
    assert(first_zero_seq(t.subrange(k, s.len() as int)) == first_zero_seq(
        s.subrange(k, s.len() as int),
    )) by {
        lemma_first_zero_seq_ext_equal(
            t.subrange(k, s.len() as int),
            s.subrange(k, s.len() as int),
        );
    }
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
        // The first zero is at or before `i`; clearing bit `i` (at or after `fz`) does
        // not move it.
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
        // `fz > i`: clearing bit `i` makes `i` the first zero (prefix [0, i) is true).
        assert(is_first_zero(t, i)) by {
            assert(!t.index(i));
            assert(forall|j: int| 0 <= j < i ==> t.index(j)) by {
                assert(forall|j: int| 0 <= j < i ==> s.index(j));
            }
        }
        lemma_is_first_zero_unique(t, first_zero_seq(t), i);
    }
}

/// Clearing all bits in `[start, end)` moves the first zero to `min(first_zero_seq(s), start)`:
/// clearing can only introduce a new first zero at `start` (the earliest cleared index).
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

/// Setting a `false` bit at `i` that is strictly past the first zero leaves the first
/// zero unchanged.
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
                reveal(<IdAlloc as Inv>::inv);
                lemma_first_zero_seq_char(self@);
                assert(id == first_zero_seq(self@));
                assert(id < self@.len());
                assert(!self@[id as int]);
            }
            self.bitset.set(id, true);
            proof! {
                assert(id < self@.len());
                assert(self@ == old(self)@.update(id as int, true));
                assert(id + 1 <= self@.len());
                assert(id < usize::MAX);
                assert(forall|i: int| 0 <= i < (id + 1) as int ==> self@[i]) by {
                    assert forall|i: int| 0 <= i < (id + 1) as int implies self@[i] by {
                        if i == id as int {
                            assert(self@[id as int]);
                        } else {
                            assert(self@[i] == old(self)@[i]);
                        }
                    }
                }
            }
            self.update_first_available_id(id + 1);
            proof! {
                assert(self@ == old(self)@.update(id as int, true));
                assert(id == first_zero_seq(old(self)@));
                assert(first_zero_seq(old(self)@) < old(self)@.len());
            }
            Some(id)
        } else {
            proof! {
                lemma_first_zero_seq_char(self@);
                assert(first_zero_seq(old(self)@) == old(self)@.len());
            }
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

        // Scan the bitmap from the position `first_available_id`
        // for the first `count` number of consecutive 0's.
        let allocated_range = {
            // Invariance: all bits within `curr_range` are 0's
            let mut curr_range = self.first_available_id..self.first_available_id + 1;
            proof! {
                reveal(<IdAlloc as Inv>::inv);
                lemma_first_zero_seq_char(self@);
                assert(self.first_available_id == first_zero_seq(self@));
                assert(end == self.first_available_id + count);
                assert(end <= self@.len());
                assert(self.first_available_id + count <= self@.len());
                assert(count > 0);
                assert(self.first_available_id < self@.len());
                assert(self.first_available_id + 1 <= self@.len());
                assert(!self@[self.first_available_id as int]);
                assert(1 <= count);
                assert(range_usize_len_spec(&curr_range) <= count);
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

        // Set every bit to 1 within the allocated range
        proof! {
            assert(allocated_range.start <= allocated_range.end);
            assert(0 <= allocated_range.start);
            assert(self@ == old(self)@);
            assert(self@.len() == old(self)@.len());
        }
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
            proof! {
                assert(id < self@.len());
            }
            self.bitset.set(id, true);
            proof! {
                // `set` changed only bit `id` (to true); carry the invariant to `id + 1`.
                assert(self@[id as int]);
                assert forall|j: int| 0 <= j < self@.len() && !(allocated_range.start as int <= j < (id + 1) as int) implies self@[j] == old(self)@[j] by {
                    assert(j != id as int);
                }
            }
        }

        // In case we need to update first_available_id
        if self.is_allocated(self.first_available_id) {
            proof! {
                // The prefix `[0, allocated_range.end)` is now all `true`: `[0, start)`
                // was true (old invariant, start == old first_available_id) and
                // `[start, end)` was just set true by the loop.
                reveal(<IdAlloc as Inv>::inv);
                lemma_first_zero_seq_char(old(self)@);
                assert forall|i: int| 0 <= i < (allocated_range.end as int) implies self@[i] by {
                    if i < allocated_range.start as int {
                        assert(self@[i] == old(self)@[i]);
                    }
                }
                assert(0 <= allocated_range.end <= self@.len());
            }
            self.update_first_available_id(allocated_range.end);
        }

        proof! {
            reveal(<IdAlloc as Inv>::inv);
            lemma_first_zero_seq_char(old(self)@);
            let faid = old(self).first_available_id as int;
            // `self@` is `old(self)@` with `[allocated_range.start, allocated_range.end)` set true.
            // Establish the postcondition facts from the while/for-loop exit invariants.
            if faid < allocated_range.start as int {
                // The first zero was before the allocated range, so it is unchanged.
                assert(is_first_zero(self@, faid)) by {
                    assert forall|j: int| 0 <= j < faid implies self@[j] by {
                        assert(self@[j] == old(self)@[j]);
                    }
                    if faid < self@.len() {
                        assert(!self@[faid]) by {
                            assert(self@[faid] == old(self)@[faid]);
                        }
                    }
                }
                lemma_first_zero_seq_char(self@);
                lemma_is_first_zero_unique(self@, first_zero_seq(self@), faid);
                assert(self.first_available_id as int == faid);
                assert(self.first_available_id == first_zero_seq(self@));
            }
            assert(0 <= self.first_available_id <= self@.len());
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
        proof! {
            // The early return above guarantees the range is non-empty.
            assert(range.start < range.end);
            assert(range.start <= range.end);
            assert(self@.len() == old(self)@.len());
        }
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
            proof! {
                assert(id < self@.len());
            }
            self.bitset.set(id, false);
            proof! {
                // `set` changed only bit `id` (to false); carry the invariant to `id + 1`.
                assert(!self@[id as int]);
                assert forall|j: int| 0 <= j < self@.len() && !(range.start as int <= j < (id + 1) as int) implies self@[j] == old(self)@[j] by {
                    assert(j != id as int);
                }
            }
        }

        if range_start < self.first_available_id {
            self.first_available_id = range_start
        }
        proof! {
            // The for-loop cleared `[range.start, range.end)` and left the rest equal to
            // `old(self)@`; the field update above only touched `first_available_id`.
            lemma_first_zero_seq_clear_range(
                old(self)@,
                self@,
                range.start as int,
                range.end as int,
            );
            lemma_first_zero_seq_char(old(self)@);
            reveal(<IdAlloc as Inv>::inv);
            assert(self.first_available_id == first_zero_seq(self@)) by {
                if range_start < old(self).first_available_id {
                    assert(self.first_available_id == range_start);
                    assert(first_zero_seq(old(self)@) > range.start as int);
                    assert(first_zero_seq(self@) == range.start as int);
                } else {
                    assert(self.first_available_id == old(self).first_available_id);
                    assert(first_zero_seq(old(self)@) <= range.start as int);
                    assert(first_zero_seq(self@) == first_zero_seq(old(self)@));
                }
            }
            assert(0 <= self.first_available_id <= self@.len());
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
        proof! {
            reveal(<IdAlloc as Inv>::inv);
            assert(self@[id as int]);
            assert(id < self@.len());
        }

        self.bitset.set(id, false);
        proof! {
            assert(id < self@.len());
            assert(self@ == old(self)@.update(id as int, false));
            lemma_first_zero_seq_clear(old(self)@, id as int);
        }
        if id < self.first_available_id {
            self.first_available_id = id;
        }
        proof! {
            // `first_available_id` is now `min(old first_available_id, id)`, which the
            // clear lemma shows equals `first_zero_seq(self@)`.
            assert(self.first_available_id == first_zero_seq(self@)) by {
                if id < old(self).first_available_id {
                    assert(first_zero_seq(old(self)@) > id as int);
                    assert(self.first_available_id == id);
                    assert(first_zero_seq(self@) == id as int);
                } else {
                    assert(first_zero_seq(old(self)@) <= id as int);
                    assert(self.first_available_id == old(self).first_available_id);
                    assert(first_zero_seq(self@) == first_zero_seq(old(self)@));
                }
            }
            assert(0 <= self.first_available_id <= self@.len());
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
            proof! {
                assert(self@[id as int]);
            }
            return None;
        }
        proof! {
            assert(!self@[id as int]);
            assert(id < self@.len());
        }
        self.bitset.set(id, true);
        proof! {
            assert(id < self@.len());
            assert(self@ == old(self)@.update(id as int, true));
            assert(self@.len() <= usize::MAX as int);
            assert(id < usize::MAX);
        }
        if id == self.first_available_id {
            proof! {
                reveal(<IdAlloc as Inv>::inv);
                // `id` is the current first zero; setting it advances the first zero.
                lemma_first_zero_seq_char(old(self)@);
                assert(old(self).first_available_id == first_zero_seq(old(self)@));
                assert(id as int == first_zero_seq(old(self)@));
                lemma_first_zero_seq_advance_after_set(old(self)@, (id + 1) as int);
                assert(id + 1 <= self@.len());
                assert(forall|i: int| 0 <= i < (id + 1) as int ==> self@[i]) by {
                    assert forall|i: int| 0 <= i < (id + 1) as int implies self@[i] by {
                        if i == id as int {
                            assert(self@[id as int]);
                        } else {
                            assert(self@[i] == old(self)@[i]);
                        }
                    }
                }
            }
            self.update_first_available_id(id + 1);
        }
        proof! {
            assert(self@ == old(self)@.update(id as int, true));
            // `inv(final)` either follows from `update_first_available_id` (when it ran)
            // or holds because the first zero was unaffected by setting a bit past it.
            if id != old(self).first_available_id {
                lemma_first_zero_seq_char(old(self)@);
                assert(first_zero_seq(old(self)@) == old(self).first_available_id);
                assert(!old(self)@[id as int]);
                // `id` is a zero that is not the first zero, so it is past the first zero.
                assert(first_zero_seq(old(self)@) < id as int) by {
                    assert(first_zero_seq(old(self)@) != id as int);
                    assert forall|j: int| 0 <= j < first_zero_seq(old(self)@) implies old(self)@[j] by {}
                }
                lemma_first_zero_seq_set_after_first_zero(old(self)@, id as int);
                assert(first_zero_seq(self@) == first_zero_seq(old(self)@));
                assert(self.first_available_id == old(self).first_available_id);
                assert(self.first_available_id == first_zero_seq(self@));
            }
            assert(0 <= self.first_available_id <= self@.len());
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
    ///
    /// The invariant's `first_available_id == first_zero_seq(self@)` equation need NOT
    /// hold on entry: callers invoke this right after a `set` that has advanced the
    /// first zero, so only the prefix-all-`true` fact (which lets the tail scan agree
    /// with the global first zero) and the field bounds are required.
    #[verus_spec(
        requires
            0 <= self.first_available_id <= self@.len(),
            0 <= start <= self@.len(),
            // The caller has just made the prefix [0, start) all `true`.
            forall|i: int| #![trigger self@[i]] 0 <= i < start ==> self@[i],
        ensures
            final(self)@ == old(self)@,
            final(self).first_available_id == first_zero_seq(final(self)@),
            final(self).inv(),
    )]
    fn update_first_available_id(&mut self, start: usize) {
        let len = self.bitset.len();
        proof! {
            assert(bitvec_view(&self.bitset) == self@);
            assert(len == self@.len());
            assert(0 <= start <= len);
        }
        let bit_slice = self
            .bitset
            .get(start..len)
            .expect("start is guaranteed to be valid by the caller");
        proof! {
            // The deref ties the tail slice's view to `self@`; the `get` axiom ties
            // it to the sub-range.
            assert(0 <= start as int <= self@.len());
            assert(bitslice_view(bit_slice) == self@.subrange(start as int, self@.len() as int));
            // The tail's length is `len - start`, bounding a `first_zero` offset so
            // that `start + offset` cannot overflow.
            assert(bitslice_view(bit_slice).len() == self@.len() - start as int);
            assert(start as int + bitslice_view(bit_slice).len() <= self@.len());
        }
        /* Bind the bounded `first_zero` result (avoid closure overflow + enable proof).
         * Origin Rust: self.first_available_id = bit_slice.first_zero().map(|offset| start + offset).unwrap_or(len);
         */
        self.first_available_id = match bit_slice.first_zero() {
            Some(offset) => start + offset,
            None => len,
        };
        proof! {
            // `first_zero` on the tail gives the offset of the first zero in the tail
            // (or `None` when the tail is all `true`). Translate to the global first
            // zero using the all-`true` prefix [0, start). The exec `first_zero` spec
            // plus the broadcast `is_first_zero` uniqueness connect the anonymous
            // `Some(j)` to `first_zero_seq(tail)` automatically.
            lemma_first_zero_seq_prefix_all_true(self@, start as int);
            let tail = self@.subrange(start as int, self@.len() as int);
            assert(tail == bitslice_view(bit_slice));
            lemma_first_zero_seq_char(tail);
            lemma_first_zero_seq_char(self@);
            assert(first_zero_seq(self@) == start as int + first_zero_seq(tail));
            assert(is_first_zero(bitslice_view(bit_slice), first_zero_seq(tail)));
            assert(self.first_available_id == first_zero_seq(self@));
            assert(0 <= self.first_available_id <= self@.len());
            reveal(<IdAlloc as Inv>::inv);
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
