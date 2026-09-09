// SPDX-License-Identifier: MPL-2.0
#![cfg_attr(not(test), no_std)]
#![deny(unsafe_code)]
#![feature(proc_macro_hygiene)]

use vstd::prelude::*;
use vstd_extra::{debug_assert, prelude::*};

use core::{fmt::Debug, ops::Range};

use bitvec::prelude::BitVec;

verus! {

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
/// `first_available_id == first_zero_index(self@)`: it is the index of the first
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
        &&& self.first_available_id == first_zero_index(self@)
    }
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
                &&& id == first_zero_index(old(self)@)
                &&& first_zero_index(old(self)@) < old(self)@.len()
                &&& final(self)@ == old(self)@.update(first_zero_index(old(self)@), true)
                &&& final(self).inv()
            },
            res is None ==> {
                &&& first_zero_index(old(self)@) == old(self)@.len()
                &&& final(self)@ == old(self)@
                &&& final(self).inv()
            },
    )]
    pub fn alloc(&mut self) -> Option<usize> {
        if self.first_available_id < self.bitset.len() {
            let id = self.first_available_id;
            proof! {
                lemma_first_zero_index_is_first_zero(self@);
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
                lemma_first_zero_index_is_first_zero(self@);
            }
            #[verus_spec(invariant
                count > 0,
                self@ == old(self)@,
                self.first_available_id == old(self).first_available_id,
                self.first_available_id <= curr_range.start <= curr_range.end <= self@.len(),
                range_usize_len_spec(&curr_range) <= count,
                forall|j: int| #![trigger self@[j]] curr_range.start as int <= j < curr_range.end as int ==> !self@[j],
                decreases self@.len() as int - curr_range.end as int,
            )]
            /* `Range::len` is trait method, cannot be `assume_specification`.
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
            allocated_range.end <= self@.len(),
            allocated_range.start <= id <= allocated_range.end,
            forall|j: int| #![trigger self@[j]] allocated_range.start as int <= j < id as int ==> self@[j],
            forall|j: int| 0 <= j < self@.len() && !(allocated_range.start as int <= j < id as int) ==> self@[j] == old(self)@[j],
        )]
        // Set every bit to 1 within the allocated range
        for id in allocated_range.clone() {
            self.bitset.set(id, true);
        }

        // In case we need to update first_available_id
        if self.is_allocated(self.first_available_id) {
            self.update_first_available_id(allocated_range.end);
        }

        proof! {
            let faid = old(self).first_available_id as int;
            if faid < allocated_range.start as int {
                lemma_first_zero_index_is_first_zero(self@);
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
        if range.is_empty() {
            return;
        }

        let range_start = range.start;
        #[verus_spec(invariant
            self@.len() == old(self)@.len(),
            range.end <= self@.len(),
            range.start <= id <= range.end,
            forall|j: int| #![trigger self@[j]] range.start as int <= j < id as int ==> !self@[j],
            forall|j: int| #![trigger self@[j]] id as int <= j < range.end as int ==> self@[j],
            forall|j: int| 0 <= j < self@.len() && !(range.start as int <= j < id as int) ==> self@[j] == old(self)@[j],
        )]
        for id in range {
            debug_assert!(self.is_allocated(id));
            self.bitset.set(id, false);
        }

        if range_start < self.first_available_id {
            self.first_available_id = range_start
        }
        proof! {
            lemma_first_zero_index_clear_range(
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
            lemma_first_zero_index_clear(old(self)@, id as int);
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
                &&& !old(self)@[id as int]
                &&& res == Some(id)
                &&& final(self).inv()
            },
            res is None ==> {
                &&& old(self)@[id as int]
                &&& final(self)@ == old(self)@
                &&& final(self).inv()
            },
    )]
    pub fn alloc_specific(&mut self, id: usize) -> Option<usize> {
        if self.bitset[id] {
            return None;
        }
        self.bitset.set(id, true);
        if id == self.first_available_id {
            proof! {
                lemma_first_zero_index_is_first_zero(old(self)@);
            }
            self.update_first_available_id(id + 1);
        }
        proof! {
            if id != old(self).first_available_id {
                lemma_first_zero_index_is_first_zero(old(self)@);
                lemma_first_zero_index_set_after_first_zero(old(self)@, id as int);
            }
        }
        Some(id)
    }

    /// Returns true if the `id` is allocated.
    ///
    /// # Panics
    ///
    /// If the `id` is out of bounds, this method will panic.
    #[verus_spec(
        requires
            id < self@.len(),
        returns
            self@[id as int],
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
            final(self).first_available_id == first_zero_index(final(self)@),
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
            lemma_first_zero_index_after_true_prefix(self@, start as int);
            let tail = self@.subrange(start as int, self@.len() as int);
            lemma_first_zero_index_is_first_zero(self@);
            assert(is_first_zero(bitslice_view(bit_slice), first_zero_index(tail)));
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
