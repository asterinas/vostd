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
        #[trigger] *(r.deref_spec()) == *r,
;

pub broadcast axiom fn box_deref_spec<T>(b: Box<T>)
    ensures
        #[trigger] *(b.deref_spec()) == *b,
;

pub broadcast axiom fn rc_deref_spec<T>(r: std::rc::Rc<T>)
    ensures
        #[trigger] *(r.deref_spec()) == *r,
;

pub broadcast axiom fn arc_deref_spec<T>(a: std::sync::Arc<T>)
    ensures
        #[trigger] *(a.deref_spec()) == *a,
;

pub broadcast axiom fn manually_drop_deref_spec_eq<T: ?Sized>(v: &ManuallyDrop<T>)
    ensures
        #[trigger] &**v == manually_drop_deref_spec(v),
;

pub broadcast group group_deref_spec {
    ref_deref_spec,
    box_deref_spec,
    rc_deref_spec,
    arc_deref_spec,
}

} // verus!
verus! {

pub assume_specification[ core::hint::spin_loop ]()
    opens_invariants none
    no_unwind
;


#[verifier::external_type_specification]
#[verifier::reject_recursive_types(T)]
#[verifier::external_body]
pub struct ExNonNull<T: std::marker::PointeeSized>(core::ptr::NonNull<T>);

} // verus!
