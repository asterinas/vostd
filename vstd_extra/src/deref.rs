use vstd::prelude::*;
use core::ops::Deref;

verus!{
/// This is a workaround to add an uninterpreted specification of Deref trait, as Deref is included in Verus but does not have spec functions.
/// It may change if Verus adds native support for spec functions in the Deref trait.
pub trait DerefSpec:Deref {
    spec fn deref_spec(&self) -> &<Self as Deref>::Target;

    proof fn deref_spec_eq(&self) 
        ensures
            forall |output| call_ensures(Self::deref,(self,),output) ==> self.deref_spec() == output;
}

impl<T:Deref> DerefSpec for T {
    uninterp spec fn deref_spec(&self) -> &<Self as Deref>::Target;
    axiom fn deref_spec_eq(&self);
}

// Special Cases
pub broadcast axiom fn ref_deref_spec<T>(r:&T) 
    ensures
        #[trigger] r.deref_spec() == r;

}