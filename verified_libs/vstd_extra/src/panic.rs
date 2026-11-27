//! Panic formatting support and external panic specifications.
#[cfg(all(feature = "std", not(target_os = "none")))]
extern crate std;

use core::fmt::{Arguments, Display, Error, Formatter};
use vstd::prelude::*;

verus! {

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
        false,
;

// Rust 1.100 core/src/panicking.rs: the single-Display form of panic! forwards
// the argument to panic_fmt. Its Display implementation may run in the panic hook.
// TODO: Propose this specification upstream once panic permissions are supported.
pub assume_specification<T: Display>[ core::panicking::panic_display::<T> ](value: &T) -> !
    requires
        false,
;

/// Forwards native formatting arguments during panic handling.
#[doc(hidden)]
pub struct PanicMessage<'a>(pub Arguments<'a>);

impl Display for PanicMessage<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        f.write_fmt(self.0)
    }
}

} // verus!
