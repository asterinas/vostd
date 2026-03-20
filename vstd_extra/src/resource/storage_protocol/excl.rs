//! Exclusive storage protocol resource algebra.
use vstd::pcm::Loc;
use vstd::prelude::*;
use vstd::storage_protocol::*;

verus!{

pub ghost enum ExclP<A> {
    Unit,
    /// Exclusive ownership of a value.
    Excl(A),
    /// Invalid state.
    ExclInvalid,
}

impl<A> Protocol<(),A> for ExclP<A> {
    open spec fn op(self, other: Self) -> Self {
        match (self, other) {
            (ExclP::Unit, x) => x,
            (x, ExclP::Unit) => x,
            _ => ExclP::ExclInvalid,
        }
    }


    open spec fn rel(self, s: Map<(), A>) -> bool {
        match self {
            ExclP::Unit => s.is_empty(),
            ExclP::Excl(x) => s =~= map![() => x],
            ExclP::ExclInvalid => false,
        }
    }

    open spec fn unit() -> Self {
        ExclP::Unit
    }

    proof fn commutative(a: Self, b: Self) {
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }

    proof fn op_unit(a: Self) {
    }
}

impl<A> ExclP<A> {
    pub open spec fn value(self) -> A {
        match self {
            ExclP::Excl(x) => x,
            _ => arbitrary(),
        }
    }
}

}