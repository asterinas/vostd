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

} // verus!
