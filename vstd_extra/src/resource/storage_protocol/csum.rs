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

impl<K,W,V,A:Protocol<K,W>,B:Protocol<K,V>> Protocol<K, Sum<W, V>> for CsumP<A, B> {
    open spec fn op(self, other: Self) -> Self {
        match (self, other) {
            (CsumP::Unit, x) => x,
            (x, CsumP::Unit) => x,
            (CsumP::Cinl(a1), CsumP::Cinl(a2)) => CsumP::Cinl(A::op(a1, a2)),
            (CsumP::Cinr(b1), CsumP::Cinr(b2)) => CsumP::Cinr(B::op(b1, b2)),
            _ => CsumP::CsumInvalid,
        }
    }

    open spec fn rel(self, s: Map<K, Sum<W, V>>) -> bool {
        match self {
            CsumP::Unit => s.is_empty(),
            CsumP::Cinl(a) => exists |m:Map<K, W>| #[trigger] A::rel(a, m) && s == m.map_values(|w| Sum::<W,V>::Left(w)),
            CsumP::Cinr(b) => exists |m:Map<K, V>| #[trigger] B::rel(b, m) && s == m.map_values(|v| Sum::<W,V>::Right(v)),
            CsumP::CsumInvalid => false,
        }
    }

    open spec fn unit() -> Self {
        CsumP::Unit
    }

    proof fn commutative(a: Self, b: Self) {
        if a is Cinl && b is Cinl {
            A::commutative(a->Cinl_0, b->Cinl_0);
        } else if a is Cinr && b is Cinr {
            B::commutative(a->Cinr_0, b->Cinr_0);
        }
    }

    proof fn associative(a: Self, b: Self, c: Self) {
        if a is Cinl && b is Cinl && c is Cinl {
            A::associative(a->Cinl_0, b->Cinl_0, c->Cinl_0);
        } else if a is Cinr && b is Cinr && c is Cinr {
            B::associative(a->Cinr_0, b->Cinr_0, c->Cinr_0);
        }
    }

    proof fn op_unit(a: Self) {}
        
}

impl<A, B> CsumP<A, B> {
    pub open spec fn to_sum(self) -> Sum<A, B> {
        match self {
            CsumP::Cinl(a) => Sum::Left(a),
            CsumP::Cinr(b) => Sum::Right(b),
            _ => arbitrary(),
        }
    }
}

/*
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
}*/

} // verus!
