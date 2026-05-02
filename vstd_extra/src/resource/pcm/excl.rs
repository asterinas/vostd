//! Exclusive resource algebra
//!
//! For Iris definition, see:
//! <https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/algebra/excl.v>
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;

verus! {

/// Exclusive PCM
///
/// In modern Iris, it uses CMRA instead of PCM, which uses a core for every element instead of a unit element.
/// Here we add a unit element to stick to the PCM definition.
pub ghost enum ExclR<A> {
    Unit,
    /// Exclusive ownership of a value.
    Excl(A),
    /// Invalid state.
    ExclInvalid,
}

impl<A> ResourceAlgebra for ExclR<A> {
    open spec fn valid(self) -> bool {
        self !is ExclInvalid
    }

    // Composition of two non-unit elements is always invalid.
    open spec fn op(a: Self, b: Self) -> Self {
        match (a, b) {
            (ExclR::Unit, x) => x,
            (x, ExclR::Unit) => x,
            _ => ExclR::ExclInvalid,
        }
    }

    proof fn valid_op(a: Self, b: Self) {
    }

    proof fn commutative(a: Self, b: Self) {
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }
}

impl<A> PCM for ExclR<A> {
    open spec fn unit() -> Self {
        ExclR::Unit
    }

    proof fn op_unit(self) {
    }

    proof fn unit_valid() {
    }
}

impl<A> ExclR<A> {
    pub open spec fn value(self) -> A {
        match self {
            ExclR::Excl(x) => x,
            _ => arbitrary(),
        }
    }
}

} // verus!
