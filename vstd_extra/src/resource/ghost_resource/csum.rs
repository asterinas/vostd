//！ Sum types for ghost resources.
use vstd::pcm::Loc;
use vstd::prelude::*;
use vstd::storage_protocol::*;

use crate::resource::storage_protocol::csum::*;
use crate::sum::*;

use super::excl::UniqueTokenStorage;

verus! {
pub tracked struct SumResource<A, B, const TOTAL:usize = 2> {
    tracked r: StorageResource<(), Sum<A, B>, CsumP<A, B, TOTAL>>,
}

pub tracked struct Left<A,B, const TOTAL:usize = 2> {
    tracked r: StorageResource<(), Sum<A, B>, CsumP<A, B, TOTAL>>,
}

pub tracked struct Right<A,B, const TOTAL:usize = 2> {
    tracked r: StorageResource<(), Sum<A, B>, CsumP<A, B, TOTAL>>,
}

impl<A, B, const TOTAL:usize> SumResource<A, B, TOTAL> {
    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    pub closed spec fn protocol_monoid(self) -> CsumP<A, B, TOTAL> {
        self.r.value()
    }

    pub open spec fn resource(self) -> Sum<A, B> {
        self.protocol_monoid().resource()
    }

    pub open spec fn is_left(self) -> bool {
        self.protocol_monoid().is_left()
    }

    pub open spec fn is_right(self) -> bool {
        self.protocol_monoid().is_right()
    }

    pub open spec fn has_resource(self) -> bool {
        self.protocol_monoid().has_resource()
    }

    pub open spec fn has_resource_taken(self) -> bool {
        self.protocol_monoid().has_resource_taken()
    }

    pub open spec fn frac(self) -> int {
        self.protocol_monoid().frac()
    }

    #[verifier::type_invariant]
    pub open spec fn type_inv(self) -> bool {
        &&& TOTAL > 0
        &&& 1 <= self.frac() <= TOTAL
        &&& self.has_resource() || self.has_resource_taken()
        &&& self.is_left() || self.is_right()
    }

    #[verifier::inline]
    pub open spec fn wf(self) -> bool {
        self.type_inv()
    }

    pub proof fn alloc_left(tracked a: A) -> (tracked res: Self)
        requires
            TOTAL > 0,
        ensures
            res.is_left(),
            res.has_resource(),
            res.resource() == Sum::<A,B>::Left(a),
    {
        let tracked mut m = Map::tracked_empty();
        m.tracked_insert((), Sum::<A,B>::Left(a));
        let tracked r = StorageResource::alloc( CsumP::Cinl(Some(a), TOTAL as int),m);
        Self { r }
    }

    pub proof fn alloc_right(tracked b: B) -> (tracked res: Self)
        requires
            TOTAL > 0,
        ensures
            res.is_right(),
            res.has_resource(),
            res.resource() == Sum::<A,B>::Right(b),
    {
        let tracked mut m = Map::tracked_empty();
        m.tracked_insert((), Sum::<A,B>::Right(b));
        let tracked r = StorageResource::alloc( CsumP::Cinr(Some(b), TOTAL as int),m);
        Self { r }
    }

        pub proof fn validate(tracked &self)
        ensures
            self.wf()
        {
            use_type_invariant(&*self);
        }

    pub proof fn validate_with_other(tracked &mut self, tracked other: &Self)
        requires
            {
                ||| old(self).is_left() && old(self).is_right()
                ||| other.is_left() && other.is_right()
                ||| old(self).is_left() && other.is_left() && old(self).has_resource() && other.has_resource()
                ||| old(self).is_right() && other.is_right() && old(self).has_resource() && other.has_resource()
            },
        ensures
            *old(self) == *self,
            self.id() != other.id(),
    {
        if self.id() == other.id() {
            self.r.validate_with_shared(&other.r);
        }
    }

    pub proof fn validate_with_left(tracked &mut self, tracked other: &Left<A,B,TOTAL>)
    requires
        old(self).id() == other.id(),
    ensures
        old(self).id() == self.id(),
        old(self).protocol_monoid() == self.protocol_monoid(),
        *old(self) == *self,
        self.is_left(),
        !(self.has_resource() && other.has_resource()),
        self.frac() + other.frac() <= TOTAL,
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.r.validate_with_shared(&other.r);
    }

    pub proof fn validate_with_right(tracked &mut self, tracked other: &Right<A,B,TOTAL>)
    requires
        old(self).id() == other.id(),
    ensures
        old(self).id() == self.id(),
        old(self).protocol_monoid() == self.protocol_monoid(),
        *old(self) == *self,
        self.is_right(),
        !(self.has_resource() && other.has_resource()),
        self.frac() + other.frac() <= TOTAL,
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.r.validate_with_shared(&other.r);
    }

    pub proof fn tracked_borrow_left(tracked &self) -> (tracked res: &A)
        requires
            self.is_left(),
            self.has_resource(),
        ensures
            *res == self.resource()->Left_0,
    {
        StorageResource::guard(&self.r,map![() => self.resource()]).tracked_borrow(()).tracked_borrow_left()
    }

    pub proof fn tracked_borrow_right(tracked &self) -> (tracked res: &B)
        requires
            self.is_right(),
            self.has_resource(),
        ensures
            *res == self.resource()->Right_0,
    {
        StorageResource::guard(&self.r,map![() => self.resource()]).tracked_borrow(()).tracked_borrow_right()
    }

    pub proof fn split_left_with_resource(tracked self, n:int) -> (tracked res: (Self, Left<A,B,TOTAL>))
        requires
            self.is_left(),
            0 < n < self.frac(),
        ensures
            res.0.id() == self.id(),
            res.0.frac() == self.frac() - n,
            res.1.id() == self.id(),
            res.1.frac() == n,
            res.0.has_resource_taken(),
            res.1.has_resource() <==> self.has_resource(),
            res.1.has_resource_taken() <==> self.has_resource_taken(),
            res.1.has_resource() ==> res.1.resource() == self.resource() -> Left_0,
    {
        use_type_invariant(&self);
        let tracked (r1, r2) = self.r.split(CsumP::Cinl(None, self.frac() - n), CsumP::Cinl(self.protocol_monoid()->Cinl_0,n));
        ( Self { r: r1 }, Left { r: r2 } )
    }

    pub proof fn split_right_with_resource(tracked self, n:int) -> (tracked res: (Self, Right<A,B,TOTAL>))
        requires
            self.is_right(),
            0 < n < self.frac(),
        ensures
            res.0.id() == self.id(),
            res.0.frac() == self.frac() - n,
            res.1.id() == self.id(),
            res.1.frac() == n,
            res.0.has_resource_taken(),
            res.1.has_resource() <==> self.has_resource(),
            res.1.has_resource_taken() <==> self.has_resource_taken(),
            res.1.has_resource() ==> res.1.resource() == self.resource() -> Right_0,
    {
        use_type_invariant(&self);
        let tracked (r1, r2) = self.r.split(CsumP::Cinr(None, self.frac() - n), CsumP::Cinr(self.protocol_monoid()->Cinr_0,n));
        ( Self { r: r1 }, Right { r: r2 } )
    }

    pub proof fn update_left(tracked self, tracked a: A) -> (tracked res: (Self, Option<Sum<A,B>>))
        requires
            self.frac() == TOTAL,
        ensures
            res.0.id() == self.id(),
            res.0.protocol_monoid() == CsumP::<A,B,TOTAL>::Cinl(Some(a), self.frac()),
            res.0.has_resource(),
            res.0.resource() == Sum::<A,B>::Left(a),
            self.has_resource() ==> res.1 == Some(self.resource()),
            self.has_resource_taken() ==> res.1 == None::<Sum<A,B>>,
    {
        use_type_invariant(&self);
        let tracked mut res = None;
        let tracked r;
        if self.has_resource() {
            if self.is_left() {
                self.protocol_monoid().lemma_withdraws_left();
                let tracked (resource, mut s) = self.r.withdraw(CsumP::Cinl(None, self.frac()), map![() => self.resource()]);
                r = resource;
                res = Some(s.tracked_remove(()));
            } else {
                self.protocol_monoid().lemma_withdraws_right();
                let tracked (resource, mut s) = self.r.withdraw(CsumP::Cinr(None, self.frac()), map![() => self.resource()]);
                r = resource;
                res = Some(s.tracked_remove(()));
            }
        } else
        {
            r = self.r;
        }
        assert(r.value().has_resource_taken());
        r.value().lemma_updates_none();
        let tracked r = r.update(CsumP::<A,B,TOTAL>::Cinl(None, self.frac()));
        r.value().lemma_deposit_left(a);
        let tracked mut m = Map::tracked_empty();
        m.tracked_insert((), Sum::<A,B>::Left(a));
        let tracked r = r.deposit(m, CsumP::<A,B,TOTAL>::Cinl(Some(a), self.frac()));
        (Self { r }, res)
    }

    pub proof fn update_right(tracked self, tracked b: B) -> (tracked res: (Self, Option<Sum<A,B>>))
        requires
            self.frac() == TOTAL,
        ensures
            res.0.id() == self.id(),
            res.0.protocol_monoid() == CsumP::<A,B,TOTAL>::Cinr(Some(b), self.frac()),
            res.0.has_resource(),
            res.0.resource() == Sum::<A,B>::Right(b),
            self.has_resource() ==> res.1 == Some(self.resource()),
            self.has_resource_taken() ==> res.1 == None::<Sum<A,B>>,
    {
        use_type_invariant(&self);
        let tracked mut res = None;
        let tracked r;
        if self.has_resource() {
            if self.is_left() {
                self.protocol_monoid().lemma_withdraws_left();
                let tracked (resource, mut s) = self.r.withdraw(CsumP::Cinl(None, self.frac()), map![() => self.resource()]);
                r = resource;
                res = Some(s.tracked_remove(()));
            } else {
                self.protocol_monoid().lemma_withdraws_right();
                let tracked (resource, mut s) = self.r.withdraw(CsumP::Cinr(None, self.frac()), map![() => self.resource()]);
                r = resource;
                res = Some(s.tracked_remove(()));
            }
        } else
        {
            r = self.r;
        }
        assert(r.value().has_resource_taken());
        r.value().lemma_updates_none();
        let tracked r = r.update(CsumP::<A,B,TOTAL>::Cinr(None, self.frac()));
        r.value().lemma_deposit_right(b);
        let tracked mut m = Map::tracked_empty();
        m.tracked_insert((), Sum::<A,B>::Right(b));
        let tracked r = r.deposit(m, CsumP::<A,B,TOTAL>::Cinr(Some(b), self.frac()));
        (Self { r }, res)
    }

    /* proof fn join_left(tracked self, tracked other: Left<A,B,TOTAL>) -> (tracked res: Self)
        requires
            self.id() == other.id(),
        ensures */
}

impl<A, B, const TOTAL:usize> Left<A, B, TOTAL> {
    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    pub closed spec fn protocol_monoid(self) -> CsumP<A, B, TOTAL> {
        self.r.value()
    }

    pub open spec fn resource(self) -> A {
        self.protocol_monoid().resource()->Left_0
    }

    #[verifier::type_invariant]
    pub open spec fn type_inv(self) -> bool {
        &&& self.protocol_monoid().is_left()
        &&& 1 <= self.frac() <= TOTAL
        &&& self.has_resource() || self.has_resource_taken()
    }

    #[verifier::inline]
    pub open spec fn wf(self) -> bool {
        self.type_inv()
    }

    pub open spec fn has_resource(self) -> bool {
        self.protocol_monoid().has_resource()
    }

    pub open spec fn has_resource_taken(self) -> bool {
        self.protocol_monoid().has_resource_taken()
    }

    pub open spec fn frac(self) -> int {
        self.protocol_monoid().frac()
    }

    pub proof fn validate(tracked &self)
    ensures
        self.wf()
    {
        use_type_invariant(&*self);
    }

    pub proof fn validate_with_left(tracked &mut self, tracked other: &Self)
        requires
            old(self).id() == other.id(),
        ensures
            *old(self) == *self,
            !(self.has_resource() && other.has_resource()),
            self.frac() + other.frac() <= TOTAL,
        {
            use_type_invariant(&*self);
            use_type_invariant(other);
            self.r.validate_with_shared(&other.r);
        }

    pub proof fn validate_with_right(tracked &self, tracked other: &Right<A,B,TOTAL>)
        ensures
            self.id() != other.id(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        if self.id() == other.id() {
            self.r.join_shared(&other.r).validate();
        }
    }

    pub proof fn tracked_borrow(tracked &self) -> (tracked res: &A)
        requires
            self.has_resource(),
        ensures
            *res == self.resource(),
    {
        use_type_invariant(&*self);
        StorageResource::guard(&self.r,map![() => Sum::<A, B>::Left(self.resource())]).tracked_borrow(()).tracked_borrow_left()
    }

    pub proof fn take_resource(tracked self) -> (tracked res:(Self, A))
        requires
            self.has_resource(),
        ensures
            res.1 == self.resource(),
            res.0.id() == self.id(),
            res.0.has_resource_taken(),
            res.0.frac() == self.frac(),
    {
        use_type_invariant(&self);
        self.protocol_monoid().lemma_withdraws_left();
        let tracked (resource, mut s) = self.r.withdraw(CsumP::Cinl(None, self.frac()), map![() => Sum::<A, B>::Left(self.resource())]);
        ( Self { r: resource }, s.tracked_remove(()).tracked_take_left() )
    }

    pub proof fn put_resource(tracked self, tracked a: A) -> (tracked res: Self)
        requires
            self.has_resource_taken(),
            self.frac() == TOTAL,
        ensures
            res.id() == self.id(),
            res.protocol_monoid() == CsumP::<A,B,TOTAL>::Cinl(Some(a), self.frac()),
            res.has_resource(),
            res.resource() == a,
    {
        use_type_invariant(&self);
        self.protocol_monoid().lemma_deposit_left(a);
        let tracked mut m = Map::tracked_empty();
        m.tracked_insert((), Sum::<A, B>::Left(a));
        let tracked r = self.r.deposit( m, CsumP::<A,B,TOTAL>::Cinl(Some(a), self.frac()));
        Self { r }
    }

    pub proof fn split(tracked self, n:int) -> (tracked res: (Self, Self))
        requires
            0 < n < self.frac(),
        ensures
            res.0.id() == self.id(),
            res.0.frac() == self.frac() - n,
            res.1.id() == self.id(),
            res.1.frac() == n,
            res.1.has_resource_taken(),
            res.0.has_resource() <==> self.has_resource(),
            res.0.has_resource_taken() <==> self.has_resource_taken(),
            res.0.has_resource() ==> res.0.resource() == self.resource(),
    {
        use_type_invariant(&self);
        let tracked (r1, r2) = self.r.split(CsumP::Cinl(self.protocol_monoid()->Cinl_0, self.frac() - n), CsumP::Cinl(None,n));
        ( Self { r: r1 }, Self { r: r2 } )
    }
}

impl<A, B, const TOTAL:usize> Right<A, B, TOTAL> {
    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    pub closed spec fn protocol_monoid(self) -> CsumP<A, B, TOTAL> {
        self.r.value()
    }

    pub open spec fn resource(self) -> B {
        self.protocol_monoid().resource()->Right_0
    }

    #[verifier::type_invariant]
    pub open spec fn type_inv(self) -> bool {
        &&& self.protocol_monoid().is_right()
        &&& 1 <= self.frac() <= TOTAL
        &&& self.has_resource() || self.has_resource_taken()
    }

    #[verifier::inline]
    pub open spec fn wf(self) -> bool {
        self.type_inv()
    }

    pub open spec fn has_resource(self) -> bool {
        self.protocol_monoid().has_resource()
    }

    pub open spec fn has_resource_taken(self) -> bool {
        self.protocol_monoid().has_resource_taken()
    }

    pub open spec fn frac(self) -> int {
        self.protocol_monoid().frac()
    }

    pub proof fn validate(tracked &self)
        ensures
            self.wf()
        {
            use_type_invariant(&*self);
        }

    pub proof fn validate_with_left(tracked &self, tracked other: &Left<A,B,TOTAL>)
        ensures
            self.id() != other.id(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        if self.id() == other.id() {
            self.r.join_shared(&other.r).validate();
        }
    }

    pub proof fn validate_with_right(tracked &mut self, tracked other: &Self)
        requires
            old(self).id() == other.id(),
        ensures
            *old(self) == *self,
            !(self.has_resource() && other.has_resource()),
            self.frac() + other.frac() <= TOTAL,
        {
            use_type_invariant(&*self);
            use_type_invariant(other);
            self.r.validate_with_shared(&other.r);
        }

    pub proof fn tracked_borrow(tracked &self) -> (tracked res: &B)
        requires
            self.has_resource(),
        ensures
            *res == self.resource(),
    {
        use_type_invariant(&*self);
        StorageResource::guard(&self.r,map![() => Sum::<A, B>::Right(self.resource())]).tracked_borrow(()).tracked_borrow_right()
    }

    pub proof fn take_resource(tracked self) -> (tracked res:(Self, B))
        requires
            self.has_resource(),
        ensures
            res.1 == self.resource(),
            res.0.id() == self.id(),
            res.0.has_resource_taken(),
            res.0.frac() == self.frac(),
    {
        use_type_invariant(&self);
        self.protocol_monoid().lemma_withdraws_right();
        let tracked (resource, mut s) = self.r.withdraw(CsumP::Cinr(None, self.frac()), map![() => Sum::<A, B>::Right(self.resource())]);
        ( Self { r: resource }, s.tracked_remove(()).tracked_take_right() )
    }

    pub proof fn put_resource(tracked self, tracked b: B) -> (tracked res: Self)
        requires
            self.has_resource_taken(),
            self.frac() == TOTAL,
        ensures
            res.id() == self.id(),
            res.protocol_monoid() == CsumP::<A,B,TOTAL>::Cinr(Some(b), self.frac()),
            res.has_resource(),
            res.resource() == b,
    {
        use_type_invariant(&self);
        self.protocol_monoid().lemma_deposit_right(b);
        let tracked mut m = Map::tracked_empty();
        m.tracked_insert((), Sum::<A, B>::Right(b));
        let tracked r = self.r.deposit( m, CsumP::<A,B,TOTAL>::Cinr(Some(b), self.frac()));
        Self { r }
    }

    pub proof fn split(tracked self, n:int) -> (tracked res: (Self, Self))
        requires
            0 < n < self.frac(),
        ensures
            res.0.id() == self.id(),
            res.0.frac() == self.frac() - n,
            res.1.id() == self.id(),
            res.1.frac() == n,
            res.1.has_resource_taken(),
            res.0.has_resource() <==> self.has_resource(),
            res.0.has_resource_taken() <==> self.has_resource_taken(),
            res.0.has_resource() ==> res.0.resource() == self.resource(),
    {
        use_type_invariant(&self);
        let tracked (r1, r2) = self.r.split(CsumP::Cinr(self.protocol_monoid()->Cinr_0, self.frac() - n), CsumP::Cinr(None,n));
        ( Self { r: r1 }, Self { r: r2 } )
    }
}

}
