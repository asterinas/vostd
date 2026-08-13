//! Type-erased one-shot callback wrapper for Verus code.
//!
//! Verus does not support function pointer types in public API signatures. This
//! module therefore exposes callbacks as sized capture objects implementing
//! [`RawCallbackContext`], while the executable runner erasure is kept behind
//! trusted `external_body` wrappers.
use alloc::boxed::Box;
use core::marker::PhantomData;

use vstd::prelude::*;

verus! {

/// A one-shot, type-erased callback.
///
/// `data` is a thin pointer to a heap payload, and `run` stores the address of
/// the monomorphized shim that knows how to consume that payload. The pair is a
/// TCB boundary: proofs should reason about the resource represented by the
/// callback, not about arbitrary closure bodies.
#[must_use]
pub struct RawCallback {
    data: *mut (),
    run: usize,
}

/// Captured context for a [`RawCallback`].
///
/// Implement this trait on a sized capture object instead of passing
/// `unsafe fn(C)` or `dyn FnOnce()`, both of which are outside Verus' supported
/// executable API surface.
pub trait RawCallbackContext: Send + 'static {
    fn run(self);
}

/// A one-shot callback that transports a tracked proof value to its runner.
///
/// This is the proof-carrying counterpart of [`RawCallback`]. The executable
/// representation remains a thin data pointer plus a monomorphized runner,
/// while `S` records the tracked value that must be supplied at invocation.
#[must_use]
pub struct RawCallbackWithProof<S> {
    data: *mut (),
    run: usize,
    _proof: PhantomData<S>,
}

/// Captured context for a [`RawCallbackWithProof`].
pub trait RawCallbackContextWithProof<S>: Send + 'static {
    spec fn call_requires(&self, proof: S) -> bool;

    fn run(self, proof: Tracked<S>)
        requires
            self.call_requires(proof@),
    ;
}

struct RawDropContext<T: Send + 'static> {
    value: T,
}

// SAFETY: `RawCallback::new` only accepts `C: Send + 'static` payloads, and
// `call_once` consumes the payload through the matching monomorphized runner.
#[verifier::external]
unsafe impl Send for RawCallback {

}

// SAFETY: `RawCallbackWithProof::new` only accepts `C: Send + 'static`
// payloads, and `call_once` consumes the payload through the matching
// monomorphized runner. `S` is proof-only and has no runtime representation.
#[verifier::external]
unsafe impl<S> Send for RawCallbackWithProof<S> {

}

impl<T: Send + 'static> RawCallbackContext for RawDropContext<T> {
    #[inline]
    #[verifier::external_body]
    fn run(self) {
        let RawDropContext { value } = self;
        drop(value);
    }
}

impl RawCallback {
    /// Builds a callback from an explicit captured context.
    #[inline]
    #[verifier::external_body]
    pub fn new<C: RawCallbackContext>(context: C) -> Self {
        let payload = Box::new(RawCallbackPayload { context });
        Self { data: Box::into_raw(payload).cast::<()>(), run: raw_callback_runner::<C>() }
    }

    /// Builds the common "drop this value later" callback.
    #[inline]
    #[verifier::external_body]
    pub fn defer_drop<T: Send + 'static>(value: T) -> Self {
        Self::new(RawDropContext { value })
    }

    /// Runs the callback exactly once.
    ///
    /// # Safety
    ///
    /// The caller must ensure this callback has not already been run and will
    /// not be run again.
    #[inline]
    #[verifier::external_body]
    pub unsafe fn call_once(self) {
        unsafe {
            call_raw_callback(self.data, self.run);
        }
    }
}

impl<S> RawCallbackWithProof<S> {
    /// Proof obligation retained across executable callback type erasure.
    pub uninterp spec fn call_requires(&self, proof: S) -> bool;

    /// Builds a proof-carrying callback from an explicit captured context.
    #[inline]
    #[verifier::external_body]
    pub fn new<C: RawCallbackContextWithProof<S>>(context: C) -> (res: Self)
        ensures
            forall|proof: S| #![auto] res.call_requires(proof) == context.call_requires(proof),
    {
        let payload = Box::new(RawCallbackPayloadWithProof { context, _proof: PhantomData });
        Self {
            data: Box::into_raw(payload).cast::<()>(),
            run: raw_callback_with_proof_runner::<C, S>(),
            _proof: PhantomData,
        }
    }

    /// Runs the callback exactly once and transfers `proof` to its context.
    ///
    /// # Safety
    ///
    /// The caller must ensure this callback has not already been run and will
    /// not be run again.
    #[inline]
    #[verifier::external_body]
    pub unsafe fn call_once(self, proof: Tracked<S>)
        requires
            self.call_requires(proof@),
    {
        unsafe {
            call_raw_callback_with_proof(self.data, self.run, proof);
        }
    }
}

struct RawCallbackPayload<C: RawCallbackContext> {
    context: C,
}

struct RawCallbackPayloadWithProof<C: RawCallbackContextWithProof<S>, S> {
    context: C,
    _proof: PhantomData<S>,
}

#[inline]
#[verifier::external_body]
fn raw_callback_runner<C: RawCallbackContext>() -> usize {
    run_raw_callback::<C> as *const () as usize
}

#[inline]
#[verifier::external_body]
unsafe fn call_raw_callback(data: *mut (), run: usize) {
    let run: unsafe fn (*mut ()) = unsafe { core::mem::transmute(run) };
    unsafe {
        run(data);
    }
}

#[inline]
#[verifier::external_body]
unsafe fn run_raw_callback<C: RawCallbackContext>(data: *mut ()) {
    let payload = unsafe { Box::from_raw(data.cast::<RawCallbackPayload<C>>()) };
    let RawCallbackPayload { context } = *payload;
    context.run();
}

#[inline]
#[verifier::external_body]
fn raw_callback_with_proof_runner<C: RawCallbackContextWithProof<S>, S>() -> usize {
    run_raw_callback_with_proof::<C, S> as *const () as usize
}

#[inline]
#[verifier::external_body]
unsafe fn call_raw_callback_with_proof<S>(data: *mut (), run: usize, proof: Tracked<S>) {
    let run: unsafe fn (*mut (), Tracked<S>) = unsafe { core::mem::transmute(run) };
    unsafe {
        run(data, proof);
    }
}

#[inline]
#[verifier::external_body]
unsafe fn run_raw_callback_with_proof<C: RawCallbackContextWithProof<S>, S>(
    data: *mut (),
    proof: Tracked<S>,
) {
    let payload = unsafe { Box::from_raw(data.cast::<RawCallbackPayloadWithProof<C, S>>()) };
    let RawCallbackPayloadWithProof { context, _proof } = *payload;
    context.run(proof);
}

} // verus!
