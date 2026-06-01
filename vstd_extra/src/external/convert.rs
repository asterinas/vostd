use vstd::prelude::*;

use core::marker::PointeeSized;

verus! {

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(AsRefSpec via AsRefSpecImpl)]
pub trait ExAsRef<T: PointeeSized>: PointeeSized {
    type ExternalTraitSpecificationFor: core::convert::AsRef<T>;

    spec fn as_ref_spec(&self) -> &T;

    spec fn obeys_as_ref_spec() -> bool;

    fn as_ref(&self) -> (r: &T)
        ensures
            Self::obeys_as_ref_spec() ==> r == self.as_ref_spec(),
    ;
}

} // verus!
