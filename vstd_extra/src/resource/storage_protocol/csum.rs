//! Csum storage protocol.
use core::panic;

use crate::sum::*;
use vstd::pcm::Loc;
use vstd::prelude::*;
use vstd::prelude::*;
use vstd::storage_protocol::*;

verus! {

/// The Csum protocol monoid.
pub ghost enum CsumP<A, B> {
    Unit,
    Cinl(A),
    Cinr(B),
    CsumInvalid,
}

/// This protocol monoid allows exclusive ownership of either an A or a B, but not both. s
impl<A, B> Protocol<(), Sum<A, B>> for CsumP<A, B> {
    open spec fn op(self, other: Self) -> Self {
        match (self, other) {
            (CsumP::Unit, x) => x,
            (x, CsumP::Unit) => x,
            _ => CsumP::CsumInvalid,
        }
    }

    open spec fn rel(self, s: Map<(), Sum<A, B>>) -> bool {
        match self {
            CsumP::Unit => s.is_empty(),
            CsumP::Cinl(a) => s.contains_key(()) && s[()] == Sum::<A, B>::Left(a),
            CsumP::Cinr(b) => s.contains_key(()) && s[()] == Sum::<A, B>::Right(b),
            _ => false,
        }
    }

    open spec fn unit() -> Self {
        CsumP::Unit
    }

    proof fn commutative(a: Self, b: Self) {
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }

    proof fn op_unit(a: Self) {
    }
}

impl<A, B> CsumP<A, B> {
    pub open spec fn to_sum(self) -> Sum<A, B> {
        match self {
            CsumP::Cinl(a) => Sum::Left(a),
            CsumP::Cinr(b) => Sum::Right(b),
            _ => arbitrary(),
        }
    }

    pub proof fn lemma_csum_withdraws(self)
        requires
            self is Cinl || self is Cinr,
        ensures
            withdraws(self, CsumP::Unit, map![() => self.to_sum()]),
    {
        let res_map = map![() => self.to_sum()];

        assert forall|q: Self, t1: Map<(), Sum<A, B>>|
            Self::rel(Self::op(self, q), t1) implies exists|t2: Map<(), Sum<A, B>>| #[trigger]
            Self::rel(Self::op(CsumP::Unit, q), t2) && t2.dom().disjoint(res_map.dom()) && t1
                == t2.union_prefer_right(res_map) by {
            let empty_map = Map::<(), Sum<A, B>>::empty();
            assert(Self::rel(Self::op(CsumP::Unit, q), empty_map) && empty_map.dom().disjoint(
                res_map.dom(),
            ) && Self::rel(Self::op(self, q), res_map));
        }
    }
}

} // verus!
