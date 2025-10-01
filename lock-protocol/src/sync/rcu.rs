use core::ops::Deref;
use core::mem::ManuallyDrop;

use vstd::prelude::*;

use crate::mm::{
    page_table::{node_concurrent::PageTableNode, pte::Pte, PageTableConfig},
    Vaddr,
};

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

#[verifier::external_body]
pub fn rcu_load_pte<C: PageTableConfig>(
    // ptr: *const Pte,
    va: Vaddr,
    idx: usize,
    node: Ghost<PageTableNode<C>>,
    offset: Ghost<nat>,
) -> (res: Pte<C>)
    ensures
        res.wf_with_node(node@, offset@),
{
    unimplemented!()
}

} // verus!
