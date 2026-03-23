//! Real-based fractional permissions storage protocol.
use vstd::map::*;
use vstd::pcm::Loc;
use vstd::prelude::*;
use vstd::storage_protocol::*;

verus! {

broadcast use group_map_axioms;

/// The fractional protocol monoid.
#[verifier::ext_equal]
pub ghost enum FracP<T> {
    Unit,
    Frac(real, T),
    Invalid,
}

impl<T> Protocol<(), T> for FracP<T> {
    open spec fn op(self, other: Self) -> Self {
        match (self, other) {
            (FracP::Unit, x) => x,
            (x, FracP::Unit) => x,
            (FracP::Frac(q1, v1), FracP::Frac(q2, v2)) => {
                if v1 == v2 && 0.0real < q1 && 0.0real < q2 && q1 + q2 <= 1.0real {
                    FracP::Frac(q1 + q2, v1)
                } else {
                    FracP::Invalid
                }
            },
            _ => FracP::Invalid,
        }
    }

    open spec fn rel(self, s: Map<(), T>) -> bool {
        match self {
            FracP::Frac(q, v) => {
                &&& s.contains_key(())
                &&& s[()] == v
                &&& q == 1.0real
            },
            _ => false,
        }
    }

    open spec fn unit() -> Self {
        FracP::Unit
    }

    proof fn commutative(a: Self, b: Self) {
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }

    proof fn op_unit(a: Self) {
    }
}

impl<T> FracP<T> {
    pub open spec fn frac(self) -> real {
        match self {
            FracP::Frac(q, _) => q,
            _ => 0.0real,
        }
    }

    pub open spec fn new(v: T) -> Self {
        FracP::Frac(1.0real, v)
    }

    pub open spec fn construct_frac(q: real, v: T) -> Self {
        FracP::Frac(q, v)
    }

    pub open spec fn value(self) -> T
        recommends
            self is Frac,
    {
        match self {
            FracP::Frac(_, v) => v,
            _ => arbitrary(),
        }
    }

    pub proof fn lemma_guards(self)
        requires
            self is Frac,
        ensures
            guards::<(), T, Self>(self, map![() => self.value()]),
    {
    }
}

} // verus!
