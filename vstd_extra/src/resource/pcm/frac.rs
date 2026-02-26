//! This module defines the real-based fractional permissions PCM.
//!
//! Unlike the [`FracGhost`](https://verus-lang.github.io/verus/verusdoc/vstd/tokens/frac/struct.FracGhost.html) in vstd,
//! which requires a compile-time constant TOTAL to define integer-based fractions,
//! we model fractions as real numbers `q : real` in (0, 1] like Iris, where 1.0 is full
//! ownership, which allows arbitrary splitting of fractions at runtime.
//!
//! For Iris definition, see:
//! <https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/algebra/frac.v>
use vstd::arithmetic::*;
use vstd::pcm::PCM;
use vstd::prelude::*;

verus! {

/// Fractional PCM
#[verifier::ext_equal]
pub tracked enum FracR<T> {
    Unit,
    Frac(real, T),
    Invalid,
}

impl<T: PartialEq> PCM for FracR<T> {
    open spec fn valid(self) -> bool {
        match self {
            FracR::Unit => true,
            FracR::Frac(q, _) => 0.0real < q && q <= 1.0real,
            FracR::Invalid => false,
        }
    }

    /// Two Frac combine iff they agree on the value and the sum of fractions does not exceed 1.0. This follows the original Iris design.
    open spec fn op(self, other: Self) -> Self {
        match (self, other) {
            (FracR::Unit, x) => x,
            (x, FracR::Unit) => x,
            (FracR::Frac(q1, a1), FracR::Frac(q2, a2)) => {
                if a1 == a2 && 0.0real < q1 && 0.0real < q2 && q1 + q2 <= 1.0real {
                    FracR::Frac(q1 + q2, a1)
                } else {
                    FracR::Invalid
                }
            },
            _ => FracR::Invalid,
        }
    }

    open spec fn unit() -> Self {
        FracR::Unit
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
