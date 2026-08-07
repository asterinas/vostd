//! Compatibility exports for the native IRC11 weak-memory model.
//!
//! The original version of this module implemented a second weak-memory
//! history, thread-view, and atomic-wrapper semantics. Verus now provides
//! those primitives in `vstd::atomic_weak`, and [`crate::atomic_irc11`] adds
//! only the adapters that are still missing upstream, such as weak
//! `AtomicPtr` support.
//!
//! New code should import [`crate::atomic_irc11`] directly. This module remains
//! as a source-compatible path and deliberately contains no independent
//! weak-memory semantics.
pub use crate::atomic_irc11::*;
