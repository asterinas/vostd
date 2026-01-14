//! Csum PCM
//!
//! For Iris definition, see:
//! <https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/algebra/csum.v>
use vstd::pcm::PCM;
use vstd::prelude::*;

verus! {

/// Csum PCM
///
/// In modern Iris, it uses CMRA instead of PCM, which uses a core for every element instead of a unit element.
/// Here we add a unit element to stick to the PCM definition.
pub tracked enum CsumR<A, B> {
    Unit,
    Cinl(A),
    Cinr(B),
    CsumInvalid,
}

impl<A: PCM, B: PCM> PCM for CsumR<A, B> {
    open spec fn valid(self) -> bool {
        match self {
            CsumR::Unit => true,
            CsumR::Cinl(a) => A::valid(a),
            CsumR::Cinr(b) => B::valid(b),
            CsumR::CsumInvalid => false,
        }
    }

    open spec fn op(self, other: Self) -> Self {
        match (self, other) {
            (CsumR::Unit, x) => x,
            (x, CsumR::Unit) => x,
            (CsumR::Cinl(a1), CsumR::Cinl(a2)) => CsumR::Cinl(A::op(a1, a2)),
            (CsumR::Cinr(b1), CsumR::Cinr(b2)) => CsumR::Cinr(B::op(b1, b2)),
            _ => CsumR::CsumInvalid,
        }
    }

    open spec fn unit() -> Self {
        CsumR::Unit
    }

    proof fn closed_under_incl(a: Self, b: Self) {
        if Self::op(a, b).valid() {
            match (a, b) {
                (CsumR::Cinl(a1), CsumR::Cinl(a2)) => {
                    A::closed_under_incl(a1, a2);
                },
                (CsumR::Cinr(b1), CsumR::Cinr(b2)) => {
                    B::closed_under_incl(b1, b2);
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

    proof fn op_unit(a: Self) {
    }

    proof fn unit_valid() {
    }
}

} // verus!
