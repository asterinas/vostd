//! Sum-type storage protocol.
use core::panic;

use crate::resource::ghost_resource::excl::UniqueTokenStorage;
use crate::sum::*;
use vstd::math::add;
use vstd::pcm::Loc;
use vstd::pervasive::arbitrary;
use vstd::prelude::*;
use vstd::prelude::*;
use vstd::storage_protocol::*;

verus! {

/// A sum-type protocol monoid that stores a tracked object of either type A or type B.
///
/// The knowledge of the existence of a specific type of resource can be shared up to TOTAL pieces,
/// but only one piece has the exclusive ownership of the resource,
/// allowing arbitrary withdrawing, depositing, or updating.
pub ghost enum CsumP<A, B, const TOTAL: u64> {
    /// The unit element, only for technical reasons, not intended to be used directly.
    Unit,
    /// The left side of the sum, with an optional resource, a fraction, and a boolean indicating whether it is the exclusive owner of the resource.
    Cinl(Option<A>, int, bool),
    /// The right side of the sum, with an optional resource, a fraction, and a boolean indicating whether it is the exclusive owner of the resource.
    Cinr(Option<B>, int, bool),
    /// An invalid state, used to represent an invalid combination of resources.
    CsumInvalid,
}

impl<A, B, const TOTAL: u64> Protocol<(), Sum<A, B>> for CsumP<A, B, TOTAL> {
    open spec fn op(self, other: Self) -> Self {
        match (self, other) {
            (CsumP::Unit, x) => x,
            (x, CsumP::Unit) => x,
            (CsumP::Cinl(ov1, n1, b1), CsumP::Cinl(ov2, n2, b2)) => {
                if !self.is_valid() || !other.is_valid() || n1 + n2 > TOTAL || b1 && b2
                    || ov1 is Some && ov2 is Some {
                    CsumP::CsumInvalid
                } else {
                    CsumP::Cinl(
                        if ov1 is Some {
                            ov1
                        } else {
                            ov2
                        },
                        n1 + n2,
                        b1 || b2,
                    )
                }
            },
            (CsumP::Cinr(ov1, n1, b1), CsumP::Cinr(ov2, n2, b2)) => {
                if !self.is_valid() || !other.is_valid() || n1 + n2 > TOTAL || b1 && b2
                    || ov1 is Some && ov2 is Some {
                    CsumP::CsumInvalid
                } else {
                    CsumP::Cinr(
                        if ov1 is Some {
                            ov1
                        } else {
                            ov2
                        },
                        n1 + n2,
                        b1 || b2,
                    )
                }
            },
            _ => CsumP::CsumInvalid,
        }
    }

    open spec fn rel(self, s: Map<(), Sum<A, B>>) -> bool {
        match self {
            CsumP::Unit => s.is_empty(),
            CsumP::Cinl(None, n, true) => 0 <= n <= TOTAL && s.is_empty(),
            CsumP::Cinl(Some(a), n, true) => 0 <= n <= TOTAL && s.contains_key(()) && s[()]
                == Sum::<A, B>::Left(a),
            CsumP::Cinr(None, n, true) => 0 <= n <= TOTAL && s.is_empty(),
            CsumP::Cinr(Some(b), n, true) => 0 <= n <= TOTAL && s.contains_key(()) && s[()]
                == Sum::<A, B>::Right(b),
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

impl<A, B, const TOTAL: u64> CsumP<A, B, TOTAL> {
    /// Whether the protocol monoid is currently in the left state.
    pub open spec fn is_left(self) -> bool {
        self is Cinl
    }

    /// Whether the protocol monoid is currently in the right state.
    pub open spec fn is_right(self) -> bool {
        self is Cinr
    }

    /// Whether the protocol monoid is an exclusive owner of a resource.
    pub open spec fn is_resource_owner(self) -> bool {
        match self {
            CsumP::Cinl(_, _, b) | CsumP::Cinr(_, _, b) => b,
            _ => false,
        }
    }

    /// Whether the protocol monoid currently owns a resource, only meaningful when it is the exclusive owner.
    pub open spec fn has_resource(self) -> bool {
        match self {
            CsumP::Cinl(ov, n, true) => ov is Some,
            CsumP::Cinr(ov, n, true) => ov is Some,
            _ => false,
        }
    }

    /// Whether the protocol monoid has had its resource taken, only meaningful when it is the exclusive owner.
    pub open spec fn has_resource_taken(self) -> bool {
        match self {
            CsumP::Cinl(ov, n, true) => ov is None,
            CsumP::Cinr(ov, n, true) => ov is None,
            _ => false,
        }
    }

    /// The resource stored in the protocol monoid.
    pub open spec fn resource(self) -> Sum<A, B> {
        match self {
            CsumP::Cinl(Some(a), n, true) => Sum::Left(a),
            CsumP::Cinr(Some(b), n, true) => Sum::Right(b),
            _ => arbitrary(),
        }
    }

    /// The fraction of the resource knowledge.
    pub open spec fn frac(self) -> int {
        match self {
            CsumP::Cinl(_, n, _) | CsumP::Cinr(_, n, _) => n,
            _ => 1,
        }
    }

    /// The invariant of the protocol monoid.
    pub open spec fn is_valid(self) -> bool {
        match self {
            CsumP::Unit => true,
            CsumP::Cinl(ov, n, b) => 0 < n <= TOTAL && (ov is Some ==> b),
            CsumP::Cinr(ov, n, b) => 0 < n <= TOTAL && (ov is Some ==> b),
            _ => false,
        }
    }

    pub proof fn lemma_withdraws_left(self)
        requires
            self.is_left(),
            self.is_resource_owner(),
            self.has_resource(),
            self.is_valid(),
        ensures
            withdraws(self, CsumP::Cinl(None, self.frac(), true), map![()=>self.resource()]),
    {
        match self {
            CsumP::Cinl(Some(a), n, true) => {
                let resource = Sum::<A, B>::Left(a);
                let resource_map = map![() => resource];
                let new_protocol_monoid = CsumP::<A, B, TOTAL>::Cinl(None, n, true);
                assert forall|q: Self, t1: Map<(), Sum<A, B>>|
                    #![auto]
                    CsumP::rel(CsumP::op(self, q), t1) implies exists|t2: Map<(), Sum<A, B>>|
                    #![auto]
                    CsumP::rel(CsumP::op(new_protocol_monoid, q), t2) && t2.dom().disjoint(
                        resource_map.dom(),
                    ) && t1 =~= t2.union_prefer_right(resource_map) by {
                    let t2 = Map::empty();
                    assert(CsumP::rel(CsumP::op(new_protocol_monoid, q), t2));
                    assert(t2.dom().disjoint(resource_map.dom()));
                    assert(t1 =~= t2.union_prefer_right(resource_map));
                }
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn lemma_withdraws_right(self)
        requires
            self.is_resource_owner(),
            self.is_right(),
            self.has_resource(),
            self.is_valid(),
        ensures
            withdraws(self, CsumP::Cinr(None, self.frac(), true), map![()=>self.resource()]),
    {
        match self {
            CsumP::Cinr(Some(b), n, true) => {
                let resource = Sum::<A, B>::Right(b);
                let resource_map = map![() => resource];
                let new_protocol_monoid = CsumP::<A, B, TOTAL>::Cinr(None, n, true);
                assert forall|q: Self, t1: Map<(), Sum<A, B>>|
                    #![auto]
                    CsumP::rel(CsumP::op(self, q), t1) implies exists|t2: Map<(), Sum<A, B>>|
                    #![auto]
                    CsumP::rel(CsumP::op(new_protocol_monoid, q), t2) && t2.dom().disjoint(
                        resource_map.dom(),
                    ) && t1 =~= t2.union_prefer_right(resource_map) by {
                    let t2 = Map::empty();
                    assert(CsumP::rel(CsumP::op(new_protocol_monoid, q), t2));
                    assert(t2.dom().disjoint(resource_map.dom()));
                    assert(t1 =~= t2.union_prefer_right(resource_map));
                }
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn lemma_deposit_left(self, a: A)
        requires
            self.is_resource_owner(),
            self.is_left(),
            self.has_resource_taken(),
            self.is_valid(),
        ensures
            deposits(self, map![()=>Sum::Left(a)], CsumP::Cinl(Some(a), self.frac(), true)),
    {
        let resource_map = map![()=>Sum::Left(a)];
        let empty_map: Map<(), Sum<A, B>> = Map::empty();
        let new_protocol_monoid = CsumP::<A, B, TOTAL>::Cinl(Some(a), self.frac(), true);
        assert forall|q: Self, t1: Map<(), Sum<A, B>>|
            CsumP::rel(CsumP::op(self, q), t1) implies exists|t2: Map<(), Sum<A, B>>|
            {
                #[trigger] CsumP::rel(CsumP::op(new_protocol_monoid, q), t2) && t1.dom().disjoint(
                    resource_map.dom(),
                ) && t1.union_prefer_right(resource_map) == t2
            } by {
            assert(CsumP::rel(CsumP::op(new_protocol_monoid, q), resource_map));
        }
    }

    pub proof fn lemma_deposit_right(self, b: B)
        requires
            self.is_resource_owner(),
            self.is_right(),
            self.has_resource_taken(),
            self.is_valid(),
        ensures
            deposits(self, map![()=>Sum::Right(b)], CsumP::Cinr(Some(b), self.frac(), true)),
    {
        let resource_map = map![()=>Sum::Right(b)];
        let empty_map: Map<(), Sum<A, B>> = Map::empty();
        let new_protocol_monoid = CsumP::<A, B, TOTAL>::Cinr(Some(b), self.frac(), true);
        assert forall|q: Self, t1: Map<(), Sum<A, B>>|
            CsumP::rel(CsumP::op(self, q), t1) implies exists|t2: Map<(), Sum<A, B>>|
            {
                #[trigger] CsumP::rel(CsumP::op(new_protocol_monoid, q), t2) && t1.dom().disjoint(
                    resource_map.dom(),
                ) && t1.union_prefer_right(resource_map) == t2
            } by {
            assert(CsumP::rel(CsumP::op(new_protocol_monoid, q), resource_map));
        }
    }

    pub proof fn lemma_updates_none(self)
        requires
            self.is_left() || self.is_right(),
            self.frac() == TOTAL,
            self.is_resource_owner(),
            self.has_resource_taken(),
        ensures
            updates(self, CsumP::Cinl(None, self.frac(), true)),
            updates(self, CsumP::Cinr(None, self.frac(), true)),
    {
    }
}

} // verus!
