// SPDX-License-Identifier: MPL-2.0
//! Logged `u32` accesses for [`::volatile`](https://docs.rs/volatile).
//! Each adapter records one access at the borrowed reference's address in the supplied history.
//! A read records the sampled word without constraining it to a previous read or write.
use vstd::prelude::*;

use ::volatile::{
    VolatileRef,
    access::{Access, ReadWrite, Writable},
};

verus! {

#[verifier::external_type_specification]
pub struct ExWriteOnly(::volatile::access::WriteOnly);

#[verifier::external_type_specification]
pub struct ExReadWrite(::volatile::access::ReadWrite);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(A)]
pub struct ExVolatileRef<'a, T: ?Sized, A>(::volatile::VolatileRef<'a, T, A>);

#[verifier::external_trait_specification]
#[verifier::external_trait_private_bound(volatile::access::private::Sealed)]
pub trait ExAccess: Copy + Default {
    type ExternalTraitSpecificationFor: Access;
}

#[verifier::external_trait_specification]
pub trait ExWritable: Access {
    type ExternalTraitSpecificationFor: Writable;
}

pub uninterp spec fn volatile_ref_addr<A>(vref: &VolatileRef<'_, u32, A>) -> usize;

pub ghost enum VolatileAccess {
    Read { addr: usize, sample: u32 },
    Write { addr: usize, value: u32 },
}

pub ghost struct AccessLog {
    events: Seq<VolatileAccess>,
}

impl View for AccessLog {
    type V = Seq<VolatileAccess>;

    closed spec fn view(&self) -> Seq<VolatileAccess> {
        self.events
    }
}

pub open spec fn accesses(log: &Option<AccessLog>) -> Seq<VolatileAccess> {
    match log {
        None => Seq::empty(),
        Some(history) => history@,
    }
}

} // verus!
/* Trusted: the volatile primitive needs an extra tracked log argument.
 * Origin Rust: <none; new executable wrapper>
 */
#[verus_verify(external_body)]
#[verus_spec(value =>
    with Tracked(log): Tracked<&mut Option<AccessLog>>
    ensures accesses(final(log)) == accesses(old(log)).push(VolatileAccess::Read { addr: volatile_ref_addr(vref), sample: value }),
    opens_invariants none
    no_unwind
)]
pub fn read_u32(vref: &VolatileRef<'_, u32, ReadWrite>) -> u32 {
    vref.as_ptr().read()
}

/* Trusted: the volatile primitive needs an extra tracked log argument.
 * Origin Rust: <none; new executable wrapper>
 */
#[verus_verify(external_body)]
#[verus_spec(
    with Tracked(log): Tracked<&mut Option<AccessLog>>
    ensures
        *final(vref) == *old(vref),
        accesses(final(log)) == accesses(old(log)).push(VolatileAccess::Write { addr: volatile_ref_addr(old(vref)), value }),
    opens_invariants none
    no_unwind
)]
pub fn write_u32<A: Writable>(vref: &mut VolatileRef<'_, u32, A>, value: u32) {
    vref.as_mut_ptr().write(value);
}
