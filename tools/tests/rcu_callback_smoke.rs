// SPDX-License-Identifier: MPL-2.0
//! Verify and compile with the project Verus, then run the produced binary.
//! The checked functions test predicate preservation; ordinary Rust main tests
//! delayed invocation, Send transfer, and execution exactly once at runtime.
extern crate alloc;

#[path = "../../verified_libs/vstd_extra/src/raw_callback.rs"]
mod raw_callback;

use raw_callback::{RawCallbackContextWithProof, RawCallbackWithProof};
use std::sync::atomic::{AtomicUsize, Ordering};
use vstd::prelude::*;

verus! {

struct Context {
    counter: &'static AtomicUsize,
    expected: usize,
}

impl RawCallbackContextWithProof<nat> for Context {
    closed spec fn call_requires(&self, certificate: nat) -> bool {
        certificate == self.expected
    }

    fn run(self, certificate: Tracked<nat>) {
        assert(certificate@ == self.expected);
        self.counter.fetch_add(1, Ordering::Relaxed);
    }
}

fn make_callback(counter: &'static AtomicUsize) -> (callback: RawCallbackWithProof<nat>)
    ensures
        callback.call_requires(7nat),
        !callback.call_requires(8nat),
{
    RawCallbackWithProof::new(Context { counter, expected: 7 })
}

fn invoke(callback: RawCallbackWithProof<nat>)
    requires
        callback.call_requires(7nat),
{
    unsafe { callback.call_once(Tracked(7nat)) };
}

// This configuration must be rejected at call_once's invocation precondition.
#[cfg(rcu_reject_wrong_proof)]
fn reject_wrong_proof(counter: &'static AtomicUsize) {
    let callback = make_callback(counter);
    unsafe {
        callback.call_once(Tracked(8nat));
    }
}

// This configuration must be rejected by linear Rust ownership.
#[cfg(rcu_reject_double_call)]
fn reject_double_call(counter: &'static AtomicUsize) {
    let callback = make_callback(counter);
    unsafe {
        callback.call_once(Tracked(7nat));
    }
    unsafe {
        callback.call_once(Tracked(7nat));
    }
}

} // verus!
static CALLS: AtomicUsize = AtomicUsize::new(0);

fn main() {
    let callback = make_callback(&CALLS);
    assert_eq!(CALLS.load(Ordering::Relaxed), 0);
    std::thread::spawn(move || invoke(callback)).join().unwrap();
    assert_eq!(CALLS.load(Ordering::Relaxed), 1);
}
