// SPDX-License-Identifier: MPL-2.0
//! OSTD-specific RCU protocol proofs over generic root publication histories.
#[cfg(feature = "irc11")]
pub mod atomic;
#[cfg(feature = "irc11")]
pub mod cpu;
#[cfg(feature = "irc11")]
pub mod grace_period;
#[cfg(feature = "irc11")]
pub mod link;
#[cfg(feature = "irc11")]
pub mod permissions;
#[cfg(feature = "irc11")]
pub mod retirement;
#[cfg(feature = "irc11")]
pub mod traversal;
