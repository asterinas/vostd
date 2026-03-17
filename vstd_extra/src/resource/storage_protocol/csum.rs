//! Csum storage protocol.
use core::panic;

use crate::resource::ghost_resource::excl::UniqueTokenStorage;
use crate::sum::*;
use vstd::pcm::Loc;
use vstd::pervasive::arbitrary;
use vstd::prelude::*;
use vstd::prelude::*;
use vstd::storage_protocol::*;

verus! {

/// A Csum protocol monoid that stores either an A or a B.
/// The knowledge of the existence of a resource can be shared up to TOTAL pieces, but the resource itself cannot be shared.
pub ghost enum CsumP<A, B, const TOTAL: usize> {
    Unit,
    Cinl(Option<A>, int),
    Cinr(Option<B>, int),
    CsumInvalid,
}

impl<A, B, const TOTAL: usize> Protocol<(), Sum<A, B>> for CsumP<A, B, TOTAL> {
    open spec fn op(self, other: Self) -> Self {
        match (self, other) {
            (CsumP::Unit, x) => x,
            (x, CsumP::Unit) => x,
            (CsumP::Cinl(ov1, n1), CsumP::Cinl(ov2, n2)) => {
                if n1 <= 0 || n2 <= 0 || n1 + n2 > TOTAL || ov1 is Some && ov2 is Some {
                    CsumP::CsumInvalid
                } else {
                    CsumP::Cinl(
                        if ov1 is Some {
                            ov1
                        } else {
                            ov2
                        },
                        n1 + n2,
                    )
                }
            },
            (CsumP::Cinr(ov1, n1), CsumP::Cinr(ov2, n2)) => {
                if n1 <= 0 || n2 <= 0 || n1 + n2 > TOTAL || ov1 is Some && ov2 is Some {
                    CsumP::CsumInvalid
                } else {
                    CsumP::Cinr(
                        if ov1 is Some {
                            ov1
                        } else {
                            ov2
                        },
                        n1 + n2,
                    )
                }
            },
            _ => CsumP::CsumInvalid,
        }
    }

    open spec fn rel(self, s: Map<(), Sum<A, B>>) -> bool {
        match self {
            CsumP::Unit => s.is_empty(),
            CsumP::Cinl(None, n) => n == TOTAL && s.is_empty(),
            CsumP::Cinl(Some(a), n) => n == TOTAL && s.contains_key(()) && s[()] == Sum::<
                A,
                B,
            >::Left(a),
            CsumP::Cinr(None, n) => n == TOTAL && s.is_empty(),
            CsumP::Cinr(Some(b), n) => n == TOTAL && s.contains_key(()) && s[()] == Sum::<
                A,
                B,
            >::Right(b),
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

impl<A, B, const TOTAL: usize> CsumP<A, B, TOTAL> {
    pub open spec fn is_left(self) -> bool {
        self is Cinl
    }

    pub open spec fn is_right(self) -> bool {
        self is Cinr
    }

    pub open spec fn has_resource(self) -> bool {
        match self {
            CsumP::Cinl(ov, n) => ov is Some,
            CsumP::Cinr(ov, n) => ov is Some,
            _ => false,
        }
    }

    pub open spec fn has_resource_taken(self) -> bool {
        match self {
            CsumP::Cinl(ov, n) => ov is None,
            CsumP::Cinr(ov, n) => ov is None,
            _ => false,
        }
    }

    pub open spec fn resource(self) -> Sum<A, B> {
        match self {
            CsumP::Cinl(Some(a), n) => Sum::Left(a),
            CsumP::Cinr(Some(b), n) => Sum::Right(b),
            _ => arbitrary(),
        }
    }

    pub open spec fn frac(self) -> int {
        match self {
            CsumP::Cinl(_, n) | CsumP::Cinr(_, n) => n,
            _ => 1,
        }
    }

    pub proof fn lemma_withdraws_left(self)
        requires
            self.is_left(),
            self.has_resource(),
            1 <= self.frac() <= TOTAL,
        ensures
            withdraws(self, CsumP::Cinl(None, self.frac()), map![()=>self.resource()]),
    {
        let resource_map = map![()=>self.resource()];
        let empty_map = Map::empty();
        let new_protocol_monoid = CsumP::<A, B, TOTAL>::Cinl(None, self.frac());
        assert forall|q: Self, t1: Map<(), Sum<A, B>>|
            CsumP::rel(CsumP::op(self, q), t1) implies exists|t2: Map<(), Sum<A, B>>|
            {
                #[trigger] CsumP::rel(CsumP::op(CsumP::Cinl(None, self.frac()), q), t2)
                    && t2.dom().disjoint(resource_map.dom()) && t1 == t2.union_prefer_right(
                    resource_map,
                )
            } by {
            if self.frac() < TOTAL {
                assert(q == CsumP::<A, B, TOTAL>::Cinl(None, TOTAL - self.frac()));
                assert(CsumP::rel(CsumP::op(new_protocol_monoid, q), empty_map));
            } else {
                assert(q is Unit);
                assert(CsumP::rel(CsumP::op(new_protocol_monoid, q), empty_map));
            }
        }
    }

    pub proof fn lemma_withdraws_right(self)
        requires
            self.is_right(),
            self.has_resource(),
            1 <= self.frac() <= TOTAL,
        ensures
            withdraws(self, CsumP::Cinr(None, self.frac()), map![()=>self.resource()]),
    {
        let resource_map = map![()=>self.resource()];
        let empty_map = Map::empty();
        let new_protocol_monoid = CsumP::<A, B, TOTAL>::Cinr(None, self.frac());
        assert forall|q: Self, t1: Map<(), Sum<A, B>>|
            CsumP::rel(CsumP::op(self, q), t1) implies exists|t2: Map<(), Sum<A, B>>|
            {
                #[trigger] CsumP::rel(CsumP::op(CsumP::Cinr(None, self.frac()), q), t2)
                    && t2.dom().disjoint(resource_map.dom()) && t1 == t2.union_prefer_right(
                    resource_map,
                )
            } by {
            if self.frac() < TOTAL {
                assert(q == CsumP::<A, B, TOTAL>::Cinr(None, TOTAL - self.frac()));
                assert(CsumP::rel(CsumP::op(new_protocol_monoid, q), empty_map));
            } else {
                assert(q is Unit);
                assert(CsumP::rel(CsumP::op(new_protocol_monoid, q), empty_map));
            }
        }
    }

    pub proof fn lemma_deposit_left(self, a: A)
        requires
            self.is_left(),
            self.has_resource_taken(),
            self.frac() == TOTAL,
        ensures
            deposits(self, map![()=>Sum::Left(a)], CsumP::Cinl(Some(a), TOTAL as int)),
    {
        let resource_map = map![()=>Sum::Left(a)];
        let empty_map: Map<(), Sum<A, B>> = Map::empty();
        let new_protocol_monoid = CsumP::<A, B, TOTAL>::Cinl(Some(a), TOTAL as int);
        assert forall|q: Self, t1: Map<(), Sum<A, B>>|
            CsumP::rel(CsumP::op(self, q), t1) implies exists|t2: Map<(), Sum<A, B>>|
            {
                #[trigger] CsumP::rel(CsumP::op(new_protocol_monoid, q), t2) && t1.dom().disjoint(
                    resource_map.dom(),
                ) && t1.union_prefer_right(resource_map) == t2
            } by {
            assert(q is Unit);
            assert(t1 == empty_map);
            assert(CsumP::rel(CsumP::op(new_protocol_monoid, q), resource_map));
        }
    }

    pub proof fn lemma_deposit_right(self, b: B)
        requires
            self.is_right(),
            self.has_resource_taken(),
            self.frac() == TOTAL,
        ensures
            deposits(self, map![()=>Sum::Right(b)], CsumP::Cinr(Some(b), TOTAL as int)),
    {
        let resource_map = map![()=>Sum::Right(b)];
        let empty_map: Map<(), Sum<A, B>> = Map::empty();
        let new_protocol_monoid = CsumP::<A, B, TOTAL>::Cinr(Some(b), TOTAL as int);
        assert forall|q: Self, t1: Map<(), Sum<A, B>>|
            CsumP::rel(CsumP::op(self, q), t1) implies exists|t2: Map<(), Sum<A, B>>|
            {
                #[trigger] CsumP::rel(CsumP::op(new_protocol_monoid, q), t2) && t1.dom().disjoint(
                    resource_map.dom(),
                ) && t1.union_prefer_right(resource_map) == t2
            } by {
            assert(q is Unit);
            assert(t1 == empty_map);
            assert(CsumP::rel(CsumP::op(new_protocol_monoid, q), resource_map));
        }
    }
}

} // verus!
