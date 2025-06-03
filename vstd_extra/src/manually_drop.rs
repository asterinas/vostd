use vstd::prelude::*;
use core::mem::ManuallyDrop;
use core::ops::Deref;

verus! {

pub uninterp spec fn ex_manually_drop_new_spec<V>(value: V) -> ManuallyDrop<V>;

pub uninterp spec fn ex_manually_drop_into_inner_spec<V>(slot: ManuallyDrop<V>) -> V;

pub uninterp spec fn ex_manually_drop_deref_spec<V: ?Sized>(slot: &ManuallyDrop<V>) -> &V;

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(ex_manually_drop_new_spec)]
pub fn ex_manually_drop_new<V>(value: V) -> ManuallyDrop<V> {
    ManuallyDrop::new(value)
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(ex_manually_drop_into_inner_spec)]
pub fn ex_manually_drop_into_inner<V>(slot: ManuallyDrop<V>) -> V {
    ManuallyDrop::into_inner(slot)
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(ex_manually_drop_deref_spec)]
pub fn ex_manually_drop_deref<V: ?Sized>(slot: &ManuallyDrop<V>) -> &V {
    slot.deref()
}

pub broadcast proof fn ex_manually_drop_value_properties<V: Sized>(value: V)
    ensures
        #[trigger] ManuallyDrop::into_inner(ManuallyDrop::new(value)) == value,
        *ManuallyDrop::new(value) == value,
        forall|other: V| value == other ==> ManuallyDrop::new(value) == ManuallyDrop::new(other),
{
    admit();
}

pub broadcast proof fn ex_manually_drop_ref_properties<V: Sized>(r: &V)
    ensures
        #[trigger] *ManuallyDrop::new(*r) == r,
{
    admit();
}

pub broadcast proof fn ex_manually_drop_properties<V: Sized>(slot: ManuallyDrop<V>)
    ensures
        #[trigger] ManuallyDrop::new(*slot) == slot,
{
    admit();
}

} // verus!
