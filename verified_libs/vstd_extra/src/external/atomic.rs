use core::sync::atomic::AtomicUsize;
use vstd::prelude::*;

verus! {

/// Specification for `AtomicUsize::from_ptr`.
pub assume_specification<'a>[ AtomicUsize::from_ptr ](ptr: *mut usize) -> &'a AtomicUsize
;

} // verus!
