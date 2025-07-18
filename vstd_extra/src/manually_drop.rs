use vstd::prelude::*;
use core::mem::ManuallyDrop;
use core::ops::Deref;

verus! {

pub uninterp spec fn manually_drop_deref_spec<T: ?Sized>(v: &ManuallyDrop<T>) -> &T;

pub uninterp spec fn manually_drop_new_spec<T>(v: T) -> ManuallyDrop<T>;

pub open spec fn manually_drop_unwrap<T>(v: ManuallyDrop<T>) -> T {
    *manually_drop_deref_spec(&v)
}

#[verifier::when_used_as_spec(manually_drop_new_spec)]
pub assume_specification<T>[ ManuallyDrop::new ](v: T) -> (res: ManuallyDrop<T>)
    ensures
        manually_drop_deref_spec(&res) == &v,
    returns
        manually_drop_new_spec(v),
;

#[verifier::when_used_as_spec(manually_drop_deref_spec)]
pub assume_specification<T: ?Sized>[ <ManuallyDrop<T> as Deref>::deref ](
    v: &ManuallyDrop<T>,
) -> (res: &T)
    ensures
        res == manually_drop_deref_spec(v),
;

#[verifier::when_used_as_spec(manually_drop_unwrap)]
pub assume_specification<T>[ ManuallyDrop::<T>::into_inner ](v: ManuallyDrop<T>) -> T
    returns
        manually_drop_unwrap(v),
;

} // verus!
