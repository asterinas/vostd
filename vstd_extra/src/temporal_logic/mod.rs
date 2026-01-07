//! TLA temporal logic definitions and proof rules.
//! 
//! Originally developed in the paper ["Anvil: Verifying Liveness of Cluster Management Controllers"](https://www.usenix.org/conference/osdi24/presentation/sun-xudong).
//! Modified from the original version which can be found on [GitHub](https://github.com/anvil-verifier/anvil).
// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
pub mod defs;
pub mod rules;

pub use defs::*;
pub use rules::*;
