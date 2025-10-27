use vstd::atomic::*;
use vstd::cell;
use vstd::prelude::*;
use vstd::simple_pptr::{self, *};

use std::marker::PhantomData;
use std::ops::Range;

verus! {

pub trait Inv {
    spec fn inv(&self) -> bool;
}

pub trait InvView: Inv {
    type V: Inv;

    spec fn view(&self) -> Self::V
        recommends
            self.inv(),
    ;

    proof fn view_preserves_inv(&self)
        requires
            self.inv(),
        ensures
            self.view().inv(),
    ;
}

pub trait OwnerOf {
    /// The owner of the concrete type.
    /// The Owner must implement `Inv`, indicating that it must
    /// has a consistent state.
    type Owner: InvView;

    spec fn wf(&self, owner: &Self::Owner) -> bool
        recommends
            owner.inv(),
    ;
}

pub trait ModelOf: OwnerOf {
    open spec fn model(&self, owner: &Self::Owner) -> <Self::Owner as InvView>::V
        recommends
            self.wf(owner),
    {
        owner.view()
    }
}

} // verus!
