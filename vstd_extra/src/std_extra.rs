use vstd::prelude::*;

verus! {

#[verifier::when_used_as_spec(as_ptr_spec)]
pub assume_specification<T>[ <[T]>::as_ptr ](s: &[T]) -> (r: *const T)
    ensures
        r == as_ptr_spec(s),
;

pub uninterp spec fn as_ptr_spec<T>(s: &[T]) -> *const T;

} // verus!
