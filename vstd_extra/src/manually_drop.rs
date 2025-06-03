use vstd::prelude::*;
use core::mem::ManuallyDrop;
use core::ops::Deref;

verus! {

pub uninterp spec fn ex_manually_drop_new_spec<T>(value: T) -> ManuallyDrop<T>;

pub uninterp spec fn ex_manually_drop_deref_spec<V: ?Sized>(slot: &ManuallyDrop<V>) -> &V;

pub open spec fn manually_drop_unwrap<V>(slot: ManuallyDrop<V>) -> V {
    *ex_manually_drop_deref_spec(&slot)
}

#[verifier::when_used_as_spec(ex_manually_drop_new_spec)]
pub assume_specification<T>[ std::mem::ManuallyDrop::<T>::new ](value: T) -> ManuallyDrop<T>
    returns
        ex_manually_drop_new_spec(value),
;

#[verifier::when_used_as_spec(ex_manually_drop_deref_spec)]
pub assume_specification<V: ?Sized>[ std::mem::ManuallyDrop::<V>::deref ](
    slot: &ManuallyDrop<V>,
) -> &V
    returns
        ex_manually_drop_deref_spec(slot),
;

#[verifier::when_used_as_spec(manually_drop_unwrap)]
pub assume_specification<V>[ std::mem::ManuallyDrop::<V>::into_inner ](slot: ManuallyDrop<V>) -> V
    returns
        *ex_manually_drop_deref_spec(&slot),
;

pub broadcast axiom fn ex_manually_drop_value_axiom<V: Sized>(value: V)
    ensures
        #[trigger] *ex_manually_drop_deref_spec(&ManuallyDrop::new(value)) == value,
;

pub proof fn ex_manually_drop_value_properties<V: Sized>(value: V)
    ensures
        ManuallyDrop::into_inner(ManuallyDrop::new(value)) == value,
        forall|other: V|
            #![trigger ManuallyDrop::new(value), ManuallyDrop::new(other)]
            value == other ==> ManuallyDrop::new(value) == ManuallyDrop::new(other),
{
    ex_manually_drop_value_axiom(value);
}

pub proof fn ex_manually_drop_ref_properties<V: Sized>(r: &V)
    ensures
        #[trigger] ex_manually_drop_deref_spec(&ManuallyDrop::new(*r)) == r,
{
    ex_manually_drop_value_axiom(*r);
}

/* ///Seems wrong
pub broadcast axiom fn ex_manually_drop_properties<V: Sized>(slot: ManuallyDrop<V>)
    ensures
        #[trigger] ManuallyDrop::new(*slot) == slot,
        #[trigger] ManuallyDrop::into_inner(ManuallyDrop::new(*slot)) == slot;
*/
} // verus!
