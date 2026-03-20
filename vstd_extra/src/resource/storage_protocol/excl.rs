//! Exclusive storage protocol resource algebra.
use vstd::pcm::Loc;
use vstd::prelude::*;
use vstd::storage_protocol::*;

verus! {

pub ghost enum ExclP<A> {
    Unit,
    /// Exclusive ownership of a value.
    Excl(Option<A>),
    /// Invalid state.
    ExclInvalid,
}

impl<A> Protocol<(), A> for ExclP<A> {
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
            ExclP::Excl(None) => s.is_empty(),
            ExclP::Excl(Some(x)) => s =~= map![() => x],
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
            ExclP::Excl(Some(x)) => x,
            _ => arbitrary(),
        }
    }

    pub proof fn lemma_deposits(self, value: A)
        requires
            self is Excl,
            self->Excl_0 is None,
        ensures
            deposits(self, map![() => value], ExclP::Excl(Some(value))),
    {
        let m = map![() => value];
        assert forall|q: Self, s: Map<(), A>|
            #![auto]
            Self::rel(Self::op(self, q), s) implies exists|s1: Map<(), A>|
            #![auto]
            Self::rel(Self::op(ExclP::Excl(Some(value)), q), s1) && s.dom().disjoint(m.dom())
                && &&s.union_prefer_right(m) == s1 by {
            assert(s == Map::<(), A>::empty());
            assert(Self::rel(Self::op(ExclP::Excl(Some(value)), q), m));
            assert(s.dom().disjoint(m.dom()));
            assert(s.union_prefer_right(m) == m);
        }
    }
}

} // verus!
