//! Specifications for functions from Rust standard library but not specified in `vstd`.
//!
//! These specifications are determined with careful inspection of the std library source code and documentation, and trusted as TCB.
//! They are subject to change if `vstd` covers more cases in the future.
pub mod acpi;
mod bitvec;
pub mod bytemuck;
pub mod cmp;
pub mod convert;
pub mod fmt;
pub mod ilog2;
pub mod int_specs;
#[cfg(target_arch = "x86_64")]
pub mod io_port;
pub mod iter;
pub mod nonnull;
pub mod ptr;
pub mod range;
pub mod slice;
pub mod smallvec;
pub mod smart_ptr;
pub mod str;
pub mod time;
pub mod vec;
#[cfg(target_arch = "x86_64")]
pub mod x86;
pub mod xmas_elf;

pub use acpi::*;
pub use bitvec::*;
pub use cmp::*;
pub use ilog2::*;
pub use int_specs::*;
#[cfg(target_arch = "x86_64")]
pub use io_port::*;
pub use iter::*;
pub use nonnull::*;
pub use ptr::*;
pub use range::*;
pub use slice::*;
pub use smallvec::*;
pub use smart_ptr::*;
pub use str::*;
pub use time::*;
pub use vec::*;
#[cfg(target_arch = "x86_64")]
pub use x86::*;

#[cfg(all(feature = "std", not(target_os = "none")))]
extern crate std;

use core::fmt::Display;
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::panic::allowed_to_panic_if;

verus! {

pub assume_specification[ core::hint::spin_loop ]()
    opens_invariants none
    no_unwind
;

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

} // verus!
