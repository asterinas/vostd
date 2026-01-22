use core::mem::ManuallyDrop;
use core::ops::Deref;
use vstd::prelude::*;

verus! {

pub uninterp spec fn manually_drop_deref_spec<T: ?Sized>(v: &ManuallyDrop<T>) -> &T;

pub uninterp spec fn manually_drop_new_spec<T>(v: T) -> ManuallyDrop<T>;

pub open spec fn manually_drop_unwrap<T>(v: ManuallyDrop<T>) -> T {
    *manually_drop_deref_spec(&v)
}

} // verus!
