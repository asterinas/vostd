use core::mem::ManuallyDrop;
use core::ops::Deref;
use vstd::prelude::*;

verus! {

pub uninterp spec fn manually_drop_deref_spec<T: ?Sized>(v: &ManuallyDrop<T>) -> &T;

pub uninterp spec fn manually_drop_new_spec<T>(v: T) -> ManuallyDrop<T>;

pub open spec fn manually_drop_unwrap<T>(v: ManuallyDrop<T>) -> T {
    *manually_drop_deref_spec(&v)
}

pub axiom fn manually_drop_into_inner_spec<T>(v: ManuallyDrop<T>)
    ensures
        forall |output| #[trigger] call_ensures(ManuallyDrop::into_inner, (v,), output) ==> output == manually_drop_unwrap(v),
;

pub axiom fn manually_drop_new_deref_spec<T>(v: T)
    ensures
        forall |output| #[trigger] call_ensures(ManuallyDrop::new, (v,), output)
            ==> manually_drop_deref_spec(&output) == &v,
;

} // verus!
