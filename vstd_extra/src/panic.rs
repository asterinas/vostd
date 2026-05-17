//! Runtime panic helper whose type (`-> !`) lets Verus discharge
//! post-conditions by branch elimination at the call site.
use vstd::prelude::*;
use vstd::vpanic;

verus! {

/// Unconditionally diverges. Callers use `if bad { panic_diverge(); }` as a
/// runtime check that Verus accepts as establishing `!bad` afterwards.
#[verifier::external_body]
pub fn panic_diverge() -> ! {
    vpanic!("panic_diverge")
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
