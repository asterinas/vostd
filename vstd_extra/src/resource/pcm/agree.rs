//! This module defines the Agreement PCM.
//!
//! For Iris definition, see:
//! <https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/algebra/agree.v>
use vstd::pcm::PCM;
use vstd::prelude::*;

verus! {

/// Agreement PCM
///
/// In modern Iris, it uses CMRA instead of PCM, which uses a core for every element instead of a unit element.
/// Here we add a unit element to stick to the PCM definition.
pub tracked enum AgreeR<A> {
    Unit,
    /// Agreement on a value.
    Agree(A),
    /// Invalid state.
    AgreeInvalid,
}

impl<A: PartialEq> PCM for AgreeR<A> {
    open spec fn valid(self) -> bool {
        self !is AgreeInvalid
    }

    /// Composition: two agreeing values must be equal.
    open spec fn op(self, other: Self) -> Self {
        match (self, other) {
            (AgreeR::Unit, x) => x,
            (x, AgreeR::Unit) => x,
            (AgreeR::Agree(a), AgreeR::Agree(b)) => {
                if a == b {
                    AgreeR::Agree(a)
                } else {
                    AgreeR::AgreeInvalid
                }
            },
            _ => AgreeR::AgreeInvalid,
        }
    }

    open spec fn unit() -> Self {
        AgreeR::Unit
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
