//! This module defines an exclusive PCM.
//!
//! For Iris definition, see:
//! <https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/algebra/excl.v>
use vstd::pcm::PCM;
use vstd::prelude::*;

verus! {

/// Exclusive PCM
///
/// In modern Iris, it uses CMRA instead of PCM, which uses a core for every element instead of a unit element.
/// Here we add a unit element to stick to the PCM definition.
pub tracked enum ExclR<A> {
    Unit,
    /// Exclusive ownership of a value.
    Excl(A),
    /// Invalid state.
    ExclInvalid,
}

impl<A> PCM for ExclR<A> {
    open spec fn valid(self) -> bool {
        self !is ExclInvalid
    }

    // Compositio of two non-unit elements is always invalid.
    open spec fn op(self, other: Self) -> Self {
        match (self, other) {
            (ExclR::Unit, x) => x,
            (x, ExclR::Unit) => x,
            _ => ExclR::ExclInvalid,
        }
    }

    open spec fn unit() -> Self {
        ExclR::Unit
    }

    proof fn closed_under_incl(a: Self, b: Self) {
    }

    proof fn commutative(a: Self, b: Self) {
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }

    proof fn op_unit(a: Self) {
    }

    proof fn unit_valid() {
    }
}

} // verus!
