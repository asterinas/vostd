//! Csum resource algebra.
//!
//! For Iris definition, see:
//! <https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/algebra/csum.v>
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;

verus! {

/// Csum PCM
///
/// In modern Iris, it uses CMRA instead of PCM, which uses a core for every element instead of a unit element.
/// Here we add a unit element to stick to the PCM definition.
pub ghost enum CsumR<A, B> {
    Unit,
    Cinl(A),
    Cinr(B),
    CsumInvalid,
}

impl<A: PCM, B: PCM> ResourceAlgebra for CsumR<A, B> {
    open spec fn valid(self) -> bool {
        match self {
            CsumR::Unit => true,
            CsumR::Cinl(a) => A::valid(a),
            CsumR::Cinr(b) => B::valid(b),
            CsumR::CsumInvalid => false,
        }
    }

    open spec fn op(a: Self, b: Self) -> Self {
        match (a, b) {
            (CsumR::Unit, x) => x,
            (x, CsumR::Unit) => x,
            (CsumR::Cinl(a1), CsumR::Cinl(a2)) => CsumR::Cinl(A::op(a1, a2)),
            (CsumR::Cinr(b1), CsumR::Cinr(b2)) => CsumR::Cinr(B::op(b1, b2)),
            _ => CsumR::CsumInvalid,
        }
    }

    proof fn valid_op(a: Self, b: Self) {
        if Self::op(a, b).valid() {
            match (a, b) {
                (CsumR::Cinl(a1), CsumR::Cinl(a2)) => {
                    A::valid_op(a1, a2);
                },
                (CsumR::Cinr(b1), CsumR::Cinr(b2)) => {
                    B::valid_op(b1, b2);
                },
                _ => {},
            }
        }
    }

    proof fn commutative(a: Self, b: Self) {
        match (a, b) {
            (CsumR::Cinl(a1), CsumR::Cinl(a2)) => {
                A::commutative(a1, a2);
            },
            (CsumR::Cinr(b1), CsumR::Cinr(b2)) => {
                B::commutative(b1, b2);
            },
            _ => {},
        }
    }

    proof fn associative(a: Self, b: Self, c: Self) {
        match (a, b, c) {
            (CsumR::Cinl(a1), CsumR::Cinl(a2), CsumR::Cinl(a3)) => {
                A::associative(a1, a2, a3);
            },
            (CsumR::Cinr(b1), CsumR::Cinr(b2), CsumR::Cinr(b3)) => {
                B::associative(b1, b2, b3);
            },
            _ => {},
        }
    }
}

impl<A: PCM, B: PCM> PCM for CsumR<A, B> {
    open spec fn unit() -> Self {
        CsumR::Unit
    }

    proof fn op_unit(self) {
    }

    proof fn unit_valid() {
    }
}

} // verus!
