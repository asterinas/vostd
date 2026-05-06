//! Real-based fractional permissions storage protocol.
use vstd::map::*;
use vstd::prelude::*;
use vstd::resource::storage_protocol::*;
use vstd::resource::Loc;

verus! {

broadcast use group_map_axioms;

/// The fractional protocol monoid.
#[verifier::ext_equal]
pub ghost enum FractionSP<T> {
    Unit,
    Frac(real, T),
    Invalid,
}

impl<T> Protocol<(), T> for FractionSP<T> {
    open spec fn op(self, other: Self) -> Self {
        match (self, other) {
            (FractionSP::Unit, x) => x,
            (x, FractionSP::Unit) => x,
            (FractionSP::Frac(q1, v1), FractionSP::Frac(q2, v2)) => {
                if v1 == v2 && 0.0real < q1 && 0.0real < q2 && q1 + q2 <= 1.0real {
                    FractionSP::Frac(q1 + q2, v1)
                } else {
                    FractionSP::Invalid
                }
            },
            _ => FractionSP::Invalid,
        }
    }

    open spec fn rel(self, s: Map<(), T>) -> bool {
        match self {
            FractionSP::Frac(q, v) => {
                &&& s.contains_key(())
                &&& s[()] == v
                &&& q == 1.0real
            },
            _ => false,
        }
    }

    open spec fn unit() -> Self {
        FractionSP::Unit
    }

    proof fn commutative(a: Self, b: Self) {
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }

    proof fn op_unit(a: Self) {
    }
}

impl<T> FractionSP<T> {
    pub open spec fn frac(self) -> real {
        match self {
            FractionSP::Frac(q, _) => q,
            _ => 0.0real,
        }
    }

    pub open spec fn new(v: T) -> Self {
        FractionSP::Frac(1.0real, v)
    }

    pub open spec fn construct_frac(q: real, v: T) -> Self {
        FractionSP::Frac(q, v)
    }

    pub open spec fn value(self) -> T
        recommends
            self is Frac,
    {
        match self {
            FractionSP::Frac(_, v) => v,
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
