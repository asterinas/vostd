// SPDX-License-Identifier: MPL-2.0
//! Trusted contract for bytemuck 1.25.2's `bytes_of`.
use vstd::prelude::*;

verus! {

#[verifier::external_trait_specification]
pub unsafe trait ExNoUninit: Sized + Copy + 'static {
    type ExternalTraitSpecificationFor: ::bytemuck::NoUninit;
}

/// The initialized object representation of a NoUninit value.
pub uninterp spec fn object_bytes<T: ::bytemuck::NoUninit>(value: T) -> Seq<u8>;

pub assume_specification<T: ::bytemuck::NoUninit>[ ::bytemuck::bytes_of::<T> ](value: &T) -> (bytes:
    &[u8])
    ensures
        bytes@ == object_bytes(*value),
        bytes@.len() == vstd::layout::size_of::<T>(),
    opens_invariants none
    no_unwind
;

} // verus!
