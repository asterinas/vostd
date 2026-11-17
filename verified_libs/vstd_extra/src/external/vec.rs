//! Trusted specifications for standard-library `Vec` operations missing from `vstd`.
use alloc::vec::Vec;
use core::{
    alloc::Allocator,
    ops::{Index, IndexMut},
    slice::SliceIndex,
};
use vstd::prelude::*;

verus! {

/// `Vec` delegates mutable indexing to its element slice. Reuse the slice
/// index's contract, including its bounds and updates to the borrowed elements.
pub assume_specification<T, I: SliceIndex<[T]>, A: Allocator>[ <Vec<T, A> as IndexMut<
    I,
>>::index_mut ](vec: &mut Vec<T, A>, index: I) -> (output: &mut <Vec<T, A> as Index<I>>::Output)
    ensures
        exists|slice: &mut [T]| #[trigger]
            slice@ == old(vec)@ && final(slice)@ == final(vec)@ && call_ensures(
                <I as SliceIndex<[T]>>::index_mut,
                (index, slice),
                output,
            ),
;

} // verus!
