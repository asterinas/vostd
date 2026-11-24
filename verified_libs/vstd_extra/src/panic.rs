//! Runtime panic helper whose type (`-> !`) lets Verus discharge
//! post-conditions by branch elimination at the call site.
#[cfg(all(feature = "std", not(target_os = "none")))]
extern crate std;

use core::fmt::{Arguments, Display, Error, Formatter};
use vstd::prelude::*;
use vstd::vpanic;

verus! {

mod internal {
    // Public for unfolding the open spec function, with no public path to the marker.
    pub uninterp spec fn may_panic() -> bool;

}

/// Requires permission to panic when the condition holds.
/// A false condition discharges this precondition without panic permission.
pub open spec fn allowed_to_panic_if(condition: bool) -> bool {
    condition ==> internal::may_panic()
}

// TODO: Propose the Any proxy to upstream vstd and coordinate panic_any permissions.
#[cfg(all(feature = "std", not(target_os = "none")))]
#[verifier::external_trait_specification]
pub trait ExAny: 'static {
    type ExternalTraitSpecificationFor: core::any::Any;
}

/// Rust 1.100, library/std/src/panic.rs: begin_panic forwards this payload to the panic handler.
#[cfg(all(feature = "std", not(target_os = "none")))]
pub assume_specification<M: 'static + core::any::Any + Send>[ std::panic::panic_any::<M> ](
    msg: M,
) -> !
    requires
        allowed_to_panic_if(true),
;

// Rust 1.100 core/src/panicking.rs: the single-Display form of panic! forwards
// the argument to panic_fmt. Its Display implementation may run in the panic hook.
// TODO: Propose this specification upstream once panic permissions are supported.
pub assume_specification<T: Display>[ core::panicking::panic_display::<T> ](value: &T) -> !
    requires
        allowed_to_panic_if(true),
;

/// Unconditionally panics. The caller must permit a panic.
#[verifier::external_body]
pub fn panic_diverge() -> !
    requires
        allowed_to_panic_if(true),
{
    vpanic!("");
}

/// Forwards native formatting arguments during panic handling.
#[doc(hidden)]
pub struct PanicMessage<'a>(pub Arguments<'a>);

impl Display for PanicMessage<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        f.write_fmt(self.0)
    }
}

/// Extension trait providing a panicking `unwrap` that models Rust's
/// real `Option::unwrap` semantics.
///
/// Verus' `Option::unwrap` carries a `requires self is Some`; Rust's
/// `unwrap` instead panics on `None`. `unwrap_or_panic` *diverges* on
/// `None` (via [`panic_diverge`]) — a sound model of the real panic —
/// and discharges `is_present()` (i.e. `self is Some` for `Option`) at
/// the call site by branch elimination, so callers need not prove the
/// value is populated.
pub trait UnwrapOrPanic: Sized {
    type Inner;

    spec fn is_present(&self) -> bool;

    spec fn payload(&self) -> Self::Inner;

    fn unwrap_or_panic(self) -> (r: Self::Inner)
        requires
            allowed_to_panic_if(!self.is_present()),
        ensures
            self.is_present(),
            r == self.payload(),
    ;
}

impl<T> UnwrapOrPanic for Option<T> {
    type Inner = T;

    open spec fn is_present(&self) -> bool {
        self is Some
    }

    open spec fn payload(&self) -> T {
        self->0
    }

    fn unwrap_or_panic(self) -> (r: T) {
        match self {
            Some(v) => v,
            None => panic_diverge(),
        }
    }
}

} // verus!
