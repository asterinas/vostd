// SPDX-License-Identifier: MPL-2.0
//! Proof-carrying, type-erased, one-shot callbacks.
//!
//! # Verified Properties
//! Construction retains exactly the context's invocation predicate. Invocation
//! consumes both the callback and its tracked argument, and requires that
//! predicate. No grace-period or reclamation fact is supplied by this module.
//!
//! # Trusted boundary
//! The pinned verifier rejects function-pointer types. The three external
//! bodies below implement only allocation/type erasure and the matching call.
//! Their safety relies on private fields, a matching monomorphized runner,
//! consuming invocation, and the context's `Send + 'static` bound. No `Clone`
//! or raw-parts constructor is exposed. Dropping an uncalled callback leaks its
//! capture; it does not run or destroy a potentially not-yet-safe context.
use vstd::prelude::*;

use alloc::boxed::Box;
use core::marker::PhantomData;

verus! {

/// Sized capture whose verified runner consumes an invocation certificate.
pub trait RawCallbackContextWithProof<S>: Send + 'static {
    /// Obligation that must hold when the queued capture is finally invoked.
    spec fn call_requires(&self, proof: S) -> bool;

    /// Runs once, consuming the capture and the required certificate.
    ///
    /// # Verified Properties
    /// ## Safety
    /// - Implementations must verify their body from the supplied invocation predicate.
    /// ## Functional Correctness
    /// - Consumes the capture and certificate in one invocation.
    /// ## Preconditions
    /// - The capture's call_requires predicate holds for the certificate.
    /// ## Postconditions
    /// - No termination, no-unwind, or grace-period guarantee is imposed.
    fn run(self, proof: Tracked<S>)
        requires
            self.call_requires(proof@),
    ;
}

/* The active Verus rejects function-pointer fields, so keep the erased runner
 * address behind a small trusted interface. This is a new reusable adapter;
 * it does not change the scheduling or execution of existing callbacks.
 * Origin Rust: <none; new executable code>
 */

/// Linear, type-erased capture awaiting its invocation certificate.
#[must_use]
pub struct RawCallbackWithProof<S> {
    data: *mut (),
    run: usize,
    _proof: PhantomData<S>,
}

// SAFETY: only `new` can construct this value and accepts Send + 'static
// captures. The certificate S is tracked and carries no executable storage.
#[verifier::external]
unsafe impl<S> Send for RawCallbackWithProof<S> {

}

impl<S> RawCallbackWithProof<S> {
    /// Exact predicate retained from the original concrete capture.
    pub uninterp spec fn call_requires(&self, proof: S) -> bool;

    /* Box allocation and the monomorphized runner must be erased together;
     * Verus cannot express the function-pointer representation directly.
     * Origin Rust: <none; new executable code>
     */
    /// Allocates a capture without running it or requiring its future certificate.
    #[verifier::external_body]
    ///
    /// # Verified Properties
    /// ## Safety
    /// - Trusted Box allocation pairs a capture with its matching monomorphized runner.
    /// ## Functional Correctness
    /// - Retains the concrete capture's exact invocation predicate without invoking it.
    /// ## Preconditions
    /// - The capture implements the verified runner and is Send + 'static.
    /// ## Postconditions
    /// - Every proof argument satisfies the erased predicate exactly when it satisfies the original.
    pub fn new<C: RawCallbackContextWithProof<S>>(context: C) -> (res: Self)
        ensures
            forall|proof: S| #[trigger] res.call_requires(proof) == context.call_requires(proof),
    {
        let payload = Box::new(Payload { context, _proof: PhantomData });
        Self {
            data: Box::into_raw(payload).cast::<()>(),
            run: run_payload::<C, S> as *const () as usize,
            _proof: PhantomData,
        }
    }

    /* Restore the exact signature erased by new. Consuming self prevents a
     * second call through the safe ownership API; private fields prevent a
     * mismatched payload/runner pair.
     * Origin Rust: <none; new executable code>
     */
    /// Calls the matching runner once, transferring the supplied certificate.
    ///
    /// # Safety
    /// The callback must originate from `new` and its ownership must not have
    /// been duplicated through unsafe code. The invocation predicate is an
    /// additional proof obligation, not a runtime check.
    #[verifier::external_body]
    ///
    /// # Verified Properties
    /// ## Safety
    /// - Trusted function-pointer restoration and Box conversion rely on private paired construction.
    /// ## Functional Correctness
    /// - Consumes this callback and passes the supplied certificate to the matching runner.
    /// ## Preconditions
    /// - The callback is uniquely owned and call_requires holds; unsafe duplication is forbidden.
    /// ## Postconditions
    /// - The callback cannot be invoked again through this ownership API; panic and divergence are not excluded.
    pub unsafe fn call_once(self, proof: Tracked<S>)
        requires
            self.call_requires(proof@),
    {
        let run: unsafe fn (*mut (), Tracked<S>) = unsafe { core::mem::transmute(self.run) };
        unsafe { run(self.data, proof) };
    }
}

/* Preserve the concrete capture type until its matching runner consumes it.
 * Origin Rust: <none; new executable code>
 */

struct Payload<C: RawCallbackContextWithProof<S>, S> {
    context: C,
    _proof: PhantomData<S>,
}

/* This private shim is reachable only through the paired constructor/call
 * boundary. Its Box was allocated by new for precisely Payload<C, S>, and
 * call_once transfers a proof satisfying that capture's call_requires.
 * Origin Rust: <none; new executable code>
 */

#[verifier::external_body]
unsafe fn run_payload<C: RawCallbackContextWithProof<S>, S>(data: *mut (), proof: Tracked<S>) {
    let payload = unsafe { Box::from_raw(data.cast::<Payload<C, S>>()) };
    let Payload { context, _proof } = *payload;
    context.run(proof);
}

} // verus!
