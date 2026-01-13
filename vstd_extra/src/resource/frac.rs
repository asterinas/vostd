//! This module defines the real-based fractional permissions PCM.
//!
//! We model fractions as real numbers `q : real` in (0, 1], where 1.0 is full
//! ownership.
//!
//!
//! For Iris definition, see:
//! <https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/algebra/frac.v>

use vstd::arithmetic::*;
use vstd::pcm::PCM;
use vstd::prelude::*;

verus! {

#[verifier::ext_equal]
pub enum Frac<A> {
    Unit,
    Frac(real, A),
    Invalid,
}

impl<A: PartialEq> PCM for Frac<A> {
    open spec fn valid(self) -> bool {
        match self {
            Frac::Unit => true,
            Frac::Frac(q, _) => 0.0real < q && q <= 1.0real,
            Frac::Invalid => false,
        }
    }

    /// Two Frac combine iff they agree on the value and the sum of fractions does not exceed 1.0. This follows the original Iris design.
    open spec fn op(self, other: Self) -> Self {
        match (self, other) {
            (Frac::Unit, x) => x,
            (x, Frac::Unit) => x,
            (Frac::Frac(q1, a1), Frac::Frac(q2, a2)) => {
                if a1 == a2 && 0.0real < q1 && 0.0real < q2 && q1 + q2 <= 1.0real {
                    Frac::Frac(q1 + q2, a1)
                } else {
                    Frac::Invalid
                }
            }
            _ => Frac::Invalid,
        }
    }

    open spec fn unit() -> Self { Frac::Unit }

    proof fn closed_under_incl(a: Self, b: Self) {
    }

    proof fn commutative(a: Self, b: Self) {}

    proof fn associative(a: Self, b: Self, c: Self) {
    }
    proof fn op_unit(a: Self) {}
    proof fn unit_valid() {}
}

} // verus!
