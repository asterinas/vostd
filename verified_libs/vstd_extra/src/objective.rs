//! A bound for generic containers that publish their contents through ghost
//! atomics or invariants.
//!
//! Under the IRC11 weak-memory model such contents must be `Objective`: a
//! permission to a stored value hands that value to whichever thread takes it,
//! so the value must not carry thread-subjective ghost state. Without IRC11
//! the bound is vacuous.
use vstd::prelude::*;

verus! {

/// `Objective` under IRC11; satisfied by every type otherwise.
#[cfg(feature = "irc11")]
pub trait MaybeObjective: vstd::thread_view::Objective {}

#[cfg(feature = "irc11")]
impl<T: vstd::thread_view::Objective> MaybeObjective for T {}

/// `Objective` under IRC11; satisfied by every type otherwise.
#[cfg(not(feature = "irc11"))]
pub trait MaybeObjective {}

#[cfg(not(feature = "irc11"))]
impl<T> MaybeObjective for T {}

} // verus!
