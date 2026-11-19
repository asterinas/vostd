// SPDX-License-Identifier: MPL-2.0
//! Trusted models: Rust 1.100.0 (0ef1bc386059596dada8fb65b50425aab2ea637a),
//! library/core/src/mem/maybe_uninit.rs. Returned slices alias the receiver.
use vstd::{
    prelude::*, raw_ptr::MemContents, std_specs::maybe_uninit::MaybeUninitAdditionalSpecFns,
};

use core::mem::MaybeUninit;

verus! {

/// Copies equal-length slices; a length mismatch panics.
pub assume_specification<'a, T: Copy>[ <[MaybeUninit<T>]>::write_copy_of_slice ](
    dst: &'a mut [MaybeUninit<T>],
    src: &[T],
) -> (ret: &'a mut [T])
    requires
        old(dst)@.len() == src@.len(),
    ensures
        ret@ == src@,
        final(dst)@.len() == old(dst)@.len(),
        forall|i: int|
            0 <= i < final(dst)@.len() ==> #[trigger] final(dst)@[i].mem_contents()
                == MemContents::Init(final(ret)@[i]),
    opens_invariants none
    no_unwind when old(dst)@.len() == src@.len()
;

/// Clones into the prefix and moves `value` into the last slot; cloning may panic.
pub assume_specification<T: Clone>[ <[MaybeUninit<T>]>::write_filled ](
    dst: &mut [MaybeUninit<T>],
    value: T,
) -> (ret: &mut [T])
    ensures
        ret@.len() == old(dst)@.len(),
        forall|i: int|
            0 <= i < ret@.len() ==> if i + 1 == ret@.len() {
                #[trigger] ret@[i] == value
            } else {
                cloned(value, ret@[i])
            },
        final(dst)@.len() == old(dst)@.len(),
        forall|i: int|
            0 <= i < final(dst)@.len() ==> #[trigger] final(dst)@[i].mem_contents()
                == MemContents::Init(final(ret)@[i]),
;

} // verus!
