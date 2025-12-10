use super::manually_drop::manually_drop_deref_spec;
use core::hint::spin_loop;
use core::mem::ManuallyDrop;
use core::ops::Deref;
use vstd::prelude::*;

// Assumptions about external functions

verus! {

/// This is a workaround to add an uninterpreted specification of Deref trait, as Deref is included in Verus but does not have spec functions.
/// It may change if Verus adds native support for spec functions in the Deref trait.
pub trait DerefSpec: Deref {
    spec fn deref_spec(&self) -> &<Self as Deref>::Target;

    proof fn deref_spec_eq(&self)
        ensures
            forall|output|
                call_ensures(Self::deref, (self,), output) ==> self.deref_spec() == output,
    ;
}

impl<T: Deref> DerefSpec for T {
    uninterp spec fn deref_spec(&self) -> &<Self as Deref>::Target;

    axiom fn deref_spec_eq(&self);
}

// Special Cases
pub broadcast axiom fn ref_deref_spec<T>(r: &T)
    ensures
        #[trigger] r.deref_spec() == r,
;

pub broadcast axiom fn manually_drop_deref_spec_eq<T: ?Sized>(v: &ManuallyDrop<T>)
    ensures
        #[trigger] &**v == manually_drop_deref_spec(v),
;

} // verus!
verus! {

pub assume_specification[ core::hint::spin_loop ]()
    opens_invariants none
    no_unwind
;

} // verus!
