//! External type specifications for `core::alloc` types and related intrinsics.
use core::alloc::{AllocError, Layout};
use vstd::prelude::*;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExLayout(Layout);

#[verifier::external_type_specification]
pub struct ExAllocError(AllocError);

pub assume_specification[ Layout::size ](layout: &Layout) -> usize
;

pub assume_specification[ Layout::align ](layout: &Layout) -> (res: usize)
    ensures
        res != 0,
;

pub assume_specification[ core::intrinsics::abort ]() -> !
;

} // verus!
