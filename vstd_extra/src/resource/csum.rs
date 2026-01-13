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
pub tracked enum Csum<A, B> {
    Unit,
    Cinl(A),
    Cinr(B),
    CsumInvalid,
}

impl<A: PCM, B: PCM> PCM for Csum<A, B> {
    open spec fn valid(self) -> bool {
        match self {
            Csum::Unit => true,
            Csum::Cinl(a) => A::valid(a),
            Csum::Cinr(b) => B::valid(b),
            Csum::CsumInvalid => false,
        }
    }

    open spec fn op(self, other: Self) -> Self {
        match (self, other) {
            (Csum::Unit, x) => x,
            (x, Csum::Unit) => x,
            (Csum::Cinl(a1), Csum::Cinl(a2)) => Csum::Cinl(A::op(a1, a2)),
            (Csum::Cinr(b1), Csum::Cinr(b2)) => Csum::Cinr(B::op(b1, b2)),
            _ => Csum::CsumInvalid,
        }
    }

    open spec fn unit() -> Self {
        Csum::Unit
    }

    proof fn closed_under_incl(a: Self, b: Self) {
        if Self::op(a, b).valid() {
            match (a, b) {
                (Csum::Cinl(a1), Csum::Cinl(a2)) => {
                    A::closed_under_incl(a1, a2);
                },
                (Csum::Cinr(b1), Csum::Cinr(b2)) => {
                    B::closed_under_incl(b1, b2);
                },
                _ => {},
            }
        }
    }

    proof fn commutative(a: Self, b: Self) {
        match (a, b) {
            (Csum::Cinl(a1), Csum::Cinl(a2)) => {
                A::commutative(a1, a2);
            },
            (Csum::Cinr(b1), Csum::Cinr(b2)) => {
                B::commutative(b1, b2);
            },
            _ => {},
        }
    }

    proof fn associative(a: Self, b: Self, c: Self) {
        match (a, b, c) {
            (Csum::Cinl(a1), Csum::Cinl(a2), Csum::Cinl(a3)) => {
                A::associative(a1, a2, a3);
            },
            (Csum::Cinr(b1), Csum::Cinr(b2), Csum::Cinr(b3)) => {
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
