use vstd::atomic::*;
use vstd::cell;
use vstd::prelude::*;

use core::marker::PhantomData;
use core::ops::Range;

verus! {

pub trait Inv {
    spec fn inv(self) -> bool;
}

impl<T: Inv> Inv for Option<T> {
    open spec fn inv(self) -> bool {
        match self {
            Some(t) => t.inv(),
            None => true,
        }
    }
}

pub trait InvView: Inv + View where <Self as View>::V: Inv {
    proof fn view_preserves_inv(self)
        requires
            self.inv(),
        ensures
            self.view().inv(),
    ;
}

pub trait OwnerOf where <<Self as OwnerOf>::Owner as View>::V: Inv {
    /// The owner of the concrete type.
    /// The Owner must implement `Inv`, indicating that it must
    /// has a consistent state.
    type Owner: InvView + Sized;

    spec fn wf(self, owner: Self::Owner) -> bool
        recommends
            owner.inv(),
    ;
}

pub trait ModelOf: OwnerOf + Sized {
    open spec fn model(self, owner: Self::Owner) -> <Self::Owner as View>::V
        recommends
            self.wf(owner),
    {
        owner.view()
    }
}

} // verus!
