//! Runtime panic helper whose type (`-> !`) lets Verus discharge
//! post-conditions by branch elimination at the call site.
use vstd::prelude::*;
use vstd::vpanic;

verus! {

mod internal {
    // Public for unfolding the open spec function, with no public path to the marker.
    pub uninterp spec fn may_panic() -> bool;

}

/// Expresses a conditional no-panic guarantee in a precondition.
/// When its argument holds, the caller can invoke the function without permitting
/// a panic. When the argument is false, the caller must permit a possible panic.
pub open spec fn no_panic_when(condition: bool) -> bool {
    !condition ==> internal::may_panic()
}

/// Unconditionally panics. The caller must permit a panic.
#[verifier::external_body]
pub fn panic_diverge() -> !
    requires
        no_panic_when(false),
{
    vpanic!("");
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
            no_panic_when(self.is_present()),
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
