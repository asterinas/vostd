use vstd::prelude::*;

use core::ops::Deref;
use core::mem::ManuallyDrop;

verus! {

pub struct RcuDrop<T> {
    pub inner: ManuallyDrop<T>,
}

impl<T> RcuDrop<T> {
    pub fn new(inner: T) -> (res: Self)
        ensures
            *res.inner.deref() =~= inner,
    {
        RcuDrop { inner: ManuallyDrop::new(inner) }
    }
}

impl<T> Deref for RcuDrop<T> {
    type Target = T;

    #[verifier::when_used_as_spec(rcu_drop_deref)]
    fn deref(&self) -> &Self::Target
        returns
            rcu_drop_deref(self),
    {
        self.inner.deref()
    }
}

pub open spec fn rcu_drop_deref<T>(x: &RcuDrop<T>) -> &T {
    &x.inner
}

} // verus!
