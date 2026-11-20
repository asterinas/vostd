// SPDX-License-Identifier: MPL-2.0
#[cfg(feature = "std")]
extern crate std;

use core::fmt::{Display, Formatter};
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::fmt::DisplaySpec;

#[cfg(verus_keep_ghost)]
use crate::panic::allowed_to_panic_if;

verus! {

// TODO: Propose the Any proxy to upstream vstd and coordinate panic_any permissions.
#[cfg(feature = "std")]
#[verifier::external_trait_specification]
pub trait ExAny: 'static {
    type ExternalTraitSpecificationFor: core::any::Any;
}

/// Rust 1.100, library/std/src/panic.rs: begin_panic forwards this payload to the panic handler.
#[cfg(feature = "std")]
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
        forall|f: &Formatter<'_>| value.fmt_req(f),
;

} // verus!
