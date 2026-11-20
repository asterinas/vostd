//! Runtime panic helper whose type (`-> !`) lets Verus discharge
//! post-conditions by branch elimination at the call site.
use core::fmt::{Arguments, Display, Error, Formatter};
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::fmt::DisplaySpecImpl;
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

/// Unconditionally panics. The caller must permit a panic.
#[verifier::external_body]
pub fn panic_diverge() -> !
    requires
        allowed_to_panic_if(true),
{
    vpanic!("");
}

/// Forwards native formatting arguments during panic handling. The caller of
/// `format_args!` has already checked the individual formatting preconditions.
#[doc(hidden)]
pub struct PanicMessage<'a>(pub Arguments<'a>);

impl DisplaySpecImpl for PanicMessage<'_> {
    open spec fn fmt_req(&self, f: &Formatter<'_>) -> bool {
        true
    }
}

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
