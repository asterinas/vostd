use core::ptr::NonNull;
use vstd::prelude::*;

verus! {

#[verifier::external_type_specification]
#[verifier::reject_recursive_types(T)]
#[verifier::external_body]
pub struct ExNonNull<T: std::marker::PointeeSized>(NonNull<T>);

} // verus!
