// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
//! TLA-style state machines.
//!
//! Originally developed in the paper ["Anvil: Verifying Liveness of Cluster Management Controllers"](https://www.usenix.org/conference/osdi24/presentation/sun-xudong).
//! Modified from the original version which can be found on [GitHub](https://github.com/anvil-verifier/anvil).
pub mod action;
pub mod state_machine;

pub use action::*;
pub use state_machine::*;
