//! External type specifications for the [`riscv` crate](https://crates.io/crates/riscv)
//! `scause` register types.
use vstd::prelude::*;

use riscv::register::scause::{Exception, Interrupt, Trap};

verus! {

/// Exposes `riscv::register::scause::Trap` variants to Verus.
#[verifier::external_type_specification]
pub struct ExTrap(Trap);

/// Exposes `riscv::register::scause::Exception` variants to Verus.
#[verifier::external_type_specification]
pub struct ExException(Exception);

/// Exposes `riscv::register::scause::Interrupt` variants to Verus.
#[verifier::external_type_specification]
pub struct ExInterrupt(Interrupt);

} // verus!
