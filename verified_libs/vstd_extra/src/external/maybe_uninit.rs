// SPDX-License-Identifier: MPL-2.0
//! Trusted models: Rust 1.100.0 (0ef1bc386059596dada8fb65b50425aab2ea637a),
//! library/core/src/mem/maybe_uninit.rs. Returned slices alias the receiver.
use vstd::{prelude::*, std_specs::maybe_uninit::MaybeUninitAdditionalSpecFns};

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
        final(dst)@.all(|slot: MaybeUninit<T>| slot.mem_contents().is_init()),
        final(ret)@ == final(dst)@.map_values(|slot: MaybeUninit<T>| slot.mem_contents().value()),
    opens_invariants none
    no_unwind when old(dst)@.len() == src@.len()
;

/// Cloning into the prefix may panic. The last slot receives the original value.
pub assume_specification<T: Clone>[ <[MaybeUninit<T>]>::write_filled ](
    dst: &mut [MaybeUninit<T>],
    value: T,
) -> (ret: &mut [T])
    ensures
        ret@.len() == old(dst)@.len(),
        ret@.all(|x| cloned(value, x)),
        ret@.len() > 0 ==> ret@.last() == value,
        final(dst)@.len() == old(dst)@.len(),
        final(dst)@.all(|slot: MaybeUninit<T>| slot.mem_contents().is_init()),
        final(ret)@ == final(dst)@.map_values(|slot: MaybeUninit<T>| slot.mem_contents().value()),
;

} // verus!
