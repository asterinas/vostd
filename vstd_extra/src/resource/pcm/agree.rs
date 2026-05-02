//! Agreement resource algebra
//!
//! For Iris definition, see:
//! <https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/algebra/agree.v>
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;

verus! {

/// Agreement PCM
///
/// In modern Iris, it uses CMRA instead of PCM, which uses a core for every element instead of a unit element.
/// Here we add a unit element to stick to the PCM definition.
pub ghost enum AgreeR<A> {
    Unit,
    /// Agreement on a value.
    Agree(A),
    /// Invalid state.
    AgreeInvalid,
}

impl<A: PartialEq> ResourceAlgebra for AgreeR<A> {
    open spec fn valid(self) -> bool {
        self !is AgreeInvalid
    }

    /// Composition: two agreeing values must be equal.
    open spec fn op(a: Self, b: Self) -> Self {
        match (a, b) {
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

    proof fn valid_op(a: Self, b: Self) {
    }

    proof fn commutative(a: Self, b: Self) {
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }
}

impl<A: PartialEq> PCM for AgreeR<A> {
    open spec fn unit() -> Self {
        AgreeR::Unit
    }

    proof fn op_unit(self) {
    }

    proof fn unit_valid() {
    }
}

} // verus!
