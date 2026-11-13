//! Trusted specifications for standard-library `Vec` operations missing from `vstd`.
use alloc::vec::Vec;
use core::{
    alloc::Allocator,
    ops::{Index, IndexMut},
    slice::SliceIndex,
};
use vstd::{prelude::*, slice::SliceIndexSpec};

verus! {

/// `Vec` delegates mutable indexing to its element slice. Reuse the slice
/// index's contract, including its bounds and updates to the borrowed elements.
pub assume_specification<T, I: SliceIndex<[T]>, A: Allocator>[ <Vec<T, A> as IndexMut<
    I,
>>::index_mut ](vec: &mut Vec<T, A>, index: I) -> (output: &mut <Vec<T, A> as Index<I>>::Output)
    ensures
        exists|old_slice: &[T], final_slice: &[T]|
            old_slice@ == old(vec)@ && final_slice@ == final(vec)@ && index.index_mut_postcondition(
                old_slice,
                final_slice,
                output,
                &*final(output),
            ),
;

} // verus!
