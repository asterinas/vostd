// SPDX-License-Identifier: MPL-2.0
use vstd::prelude::*;

use core::mem::MaybeUninit;

verus! {

/// Rust 1.100.0 `library/core/src/mem/maybe_uninit.rs` reborrows a fully initialized slice.
/// See <https://doc.rust-lang.org/1.100.0/core/primitive.slice.html#method.assume_init_ref>.
///
/// TODO: Upstream this model; remove it when equivalent vstd support is available.
pub assume_specification<'a, T>[ <[MaybeUninit<T>]>::assume_init_ref ](
    values: &'a [MaybeUninit<T>],
) -> (ret: &'a [T])
    requires
        values@.all(|slot: MaybeUninit<T>| slot.mem_contents().is_init()),
    ensures
        ret@ == values@.map_values(|slot: MaybeUninit<T>| slot.mem_contents().value()),
    opens_invariants none
    no_unwind
;

} // verus!
