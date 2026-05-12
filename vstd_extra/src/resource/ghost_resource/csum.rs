use vstd::modes::tracked_swap;
//！ Sum types for ghost resources.
use vstd::prelude::*;
use vstd::resource::{storage_protocol::*, Loc};

use crate::resource::storage_protocol::csum::*;
use crate::sum::*;

verus! {

/// `SumResource` is a token that maintains access to a resource of either type `A` or type `B`.
/// It can be split into up to `TOTAL` fractions, one of which have the exclusive right to access the resource,
/// and others shares the knowledge of the resource's existence and type, but not the ability to access it.
pub tracked struct SumResource<A, B, const TOTAL: u64 = 2> {
    tracked r: StorageResource<(), Sum<A, B>, SumSP<A, B, TOTAL>>,
}

/// `Left` ensures the resource is of type `A`.
pub tracked struct Left<A, B, const TOTAL: u64 = 2> {
    tracked r: StorageResource<(), Sum<A, B>, SumSP<A, B, TOTAL>>,
}

/// `Right` ensures the resource is of type `B`.
pub tracked struct Right<A, B, const TOTAL: u64 = 2> {
    tracked r: StorageResource<(), Sum<A, B>, SumSP<A, B, TOTAL>>,
}

/// `OneLeftOwner` is a special case of `Left` that the fraction is always one and it is the resource owner.
pub tracked struct OneLeftOwner<A, B, const TOTAL: u64 = 2> {
    tracked r: Left<A, B, TOTAL>,
}

/// `OneRightOwner` is a special case of `Right` that the fraction is always one and it is the resource owner.
pub tracked struct OneRightOwner<A, B, const TOTAL: u64 = 2> {
    tracked r: Right<A, B, TOTAL>,
}

/// `OneLeftKnowledge` is a special case of `Left` that the fraction is always one and
/// it does not own the resource.
pub tracked struct OneLeftKnowledge<A, B, const TOTAL: u64 = 2> {
    tracked r: Left<A, B, TOTAL>,
}

/// `OneRightKnowledge` is a special case of `Right` that the fraction is always one and
/// it does not own the resource.
pub tracked struct OneRightKnowledge<A, B, const TOTAL: u64 = 2> {
    tracked r: Right<A, B, TOTAL>,
}

impl<A, B, const TOTAL: u64> SumResource<A, B, TOTAL> {
    /// Returns the unique identifier.
    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    /// The underlying protocol monoid value for this resource.
    pub closed spec fn protocol_monoid(self) -> SumSP<A, B, TOTAL> {
        self.r.value()
    }

    /// Whether this token has the right to access the underlying resource.
    pub open spec fn is_resource_owner(self) -> bool {
        self.protocol_monoid().is_resource_owner()
    }

    /// The resource value, only meaningful if `is_resource_owner` is true.
    pub open spec fn resource(self) -> Sum<A, B> {
        self.protocol_monoid().resource()
    }

    /// The resource value if this token is in the left variant, only meaningful if `is_resource_owner` is true.
    pub open spec fn resource_left(self) -> A {
        self.resource()->Left_0
    }

    /// The resource value if this token is in the right variant, only meaningful if `is_resource_owner` is true.
    pub open spec fn resource_right(self) -> B {
        self.resource()->Right_0
    }

    /// Whether this token is a Left variant.
    pub open spec fn is_left(self) -> bool {
        self.protocol_monoid().is_left()
    }

    /// Whether this token is a Right variant.
    pub open spec fn is_right(self) -> bool {
        self.protocol_monoid().is_right()
    }

    /// Whether the resource is currently stored, returns `false` if this token is not the resource owner.
    pub open spec fn has_resource(self) -> bool {
        let p = self.protocol_monoid();
        p.is_resource_owner() && p.has_resource()
    }

    /// Whether the resource has been taken, returns `false` if this token is not the resource owner.
    pub open spec fn has_no_resource(self) -> bool {
        let p = self.protocol_monoid();
        p.is_resource_owner() && p.has_no_resource()
    }

    /// The fraction this token represents.
    pub open spec fn frac(self) -> int {
        self.protocol_monoid().frac()
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.wf()
    }

    /// Type invariant.
    pub open spec fn wf(self) -> bool {
        &&& 1 <= self.frac() <= TOTAL
        &&& self.protocol_monoid().is_valid()
        &&& self.is_resource_owner() ==> (self.has_resource() <==> !self.has_no_resource())
        &&& (self.is_left() <==> !self.is_right())
    }

    closed spec fn type_inv_inner(r: SumSP<A, B, TOTAL>) -> bool {
        &&& 1 <= r.frac() <= TOTAL
        &&& r.is_valid()
        &&& r.is_resource_owner() ==> (r.has_resource() <==> !r.has_no_resource())
        &&& (r.is_left() <==> !r.is_right())
    }

    proof fn alloc_unit_storage() -> (tracked res: StorageResource<
        (),
        Sum<A, B>,
        SumSP<A, B, TOTAL>,
    >) {
        StorageResource::alloc(SumSP::Unit, Map::tracked_empty())
    }

    /// Allocates a new `SumResource` with the resource of type `A`.
    pub proof fn alloc_left(tracked a: A) -> (tracked res: Self)
        requires
            TOTAL > 0,
        ensures
            res.is_left(),
            res.is_resource_owner(),
            res.has_resource(),
            res.resource() == Sum::<A, B>::Left(a),
            res.frac() == TOTAL,
            res.wf(),
    {
        let tracked mut m = Map::tracked_empty();
        m.tracked_insert((), Sum::<A, B>::Left(a));
        let tracked r = StorageResource::alloc(SumSP::Left(Some(a), TOTAL as int, true), m);
        Self { r }
    }

    /// Allocates a new `SumResource` with the resource of type `B`.
    pub proof fn alloc_right(tracked b: B) -> (tracked res: Self)
        requires
            TOTAL > 0,
        ensures
            res.is_right(),
            res.is_resource_owner(),
            res.has_resource(),
            res.resource() == Sum::<A, B>::Right(b),
            res.frac() == TOTAL,
            res.wf(),
    {
        let tracked mut m = Map::tracked_empty();
        m.tracked_insert((), Sum::<A, B>::Right(b));
        let tracked r = StorageResource::alloc(SumSP::Right(Some(b), TOTAL as int, true), m);
        Self { r }
    }

    /// `SumResource` satisfies its type invariant.
    pub proof fn validate(tracked &self)
        ensures
            self.wf(),
    {
        use_type_invariant(&*self);
    }

    /// Two `SumResource` tokens can not both be the resource owner unless they have different ids.
    pub proof fn validate_with_other(tracked &mut self, tracked other: &Self)
        requires
            old(self).is_left() && old(self).is_right() || other.is_left() && other.is_right()
                || old(self).is_left() && other.is_left() && old(self).is_resource_owner()
                && other.is_resource_owner() || old(self).is_right() && other.is_right() && old(
                self,
            ).is_resource_owner() && other.is_resource_owner(),
        ensures
            *old(self) == *final(self),
            final(self).id() != other.id(),
            final(self).wf(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        if self.id() == other.id() {
            self.r.validate_with_shared(&other.r);
        }
    }

    /// The existence of a `Left` token with the same id ensures this token is also a Left token.
    pub proof fn validate_with_left(tracked &mut self, tracked other: &Left<A, B, TOTAL>)
        requires
            old(self).id() == other.id(),
        ensures
            *old(self) == *final(self),
            final(self).is_left(),
            !(final(self).is_resource_owner() && other.is_resource_owner()),
            final(self).frac() + other.frac() <= TOTAL,
            final(self).wf(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.r.validate_with_shared(&other.r);
    }

    /// The existence of a `Right` token with the same id ensures this token is also a Right token.
    pub proof fn validate_with_right(tracked &mut self, tracked other: &Right<A, B, TOTAL>)
        requires
            old(self).id() == other.id(),
        ensures
            *old(self) == *final(self),
            final(self).is_right(),
            !(final(self).is_resource_owner() && other.is_resource_owner()),
            final(self).frac() + other.frac() <= TOTAL,
            final(self).wf(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.r.validate_with_shared(&other.r);
    }

    /// The existence of a `OneLeftOwner` token with the same id ensures this token is a Left token that is not the resource owner.
    pub proof fn validate_with_one_left_owner(
        tracked &mut self,
        tracked other: &OneLeftOwner<A, B, TOTAL>,
    )
        requires
            old(self).id() == other.id(),
        ensures
            *old(self) == *final(self),
            final(self).is_left(),
            !final(self).is_resource_owner(),
            final(self).frac() + 1 <= TOTAL,
            final(self).wf(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.r.validate_with_shared(&other.r.r);
    }

    /// The existence of a `OneRightOwner` token with the same id ensures this token is a Right token that is not the resource owner.
    pub proof fn validate_with_one_right_owner(
        tracked &mut self,
        tracked other: &OneRightOwner<A, B, TOTAL>,
    )
        requires
            old(self).id() == other.id(),
        ensures
            *old(self) == *final(self),
            final(self).is_right(),
            !final(self).is_resource_owner(),
            final(self).frac() + 1 <= TOTAL,
            final(self).wf(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.r.validate_with_shared(&other.r.r);
    }

    /// The existence of a `OneLeftKnowledge` token with the same id ensures this token is a Left token.
    pub proof fn validate_with_one_left_knowledge(
        tracked &mut self,
        tracked other: &OneLeftKnowledge<A, B, TOTAL>,
    )
        requires
            old(self).id() == other.id(),
        ensures
            *old(self) == *final(self),
            final(self).is_left(),
            final(self).frac() + 1 <= TOTAL,
            final(self).wf(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.r.validate_with_shared(&other.r.r);
    }

    /// The existence of a `OneRightKnowledge` token with the same id ensures this token is a Right token.
    pub proof fn validate_with_one_right_knowledge(
        tracked &mut self,
        tracked other: &OneRightKnowledge<A, B, TOTAL>,
    )
        requires
            old(self).id() == other.id(),
        ensures
            *old(self) == *final(self),
            final(self).is_right(),
            final(self).frac() + 1 <= TOTAL,
            final(self).wf(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.r.validate_with_shared(&other.r.r);
    }

    /// Borrows the resource of type `A`.
    pub proof fn tracked_borrow_left(tracked &self) -> (tracked res: &A)
        requires
            self.is_left(),
            self.is_resource_owner(),
            self.has_resource(),
        ensures
            *res == self.resource_left(),
    {
        StorageResource::guard(&self.r, map![() => self.resource()]).tracked_borrow(
            (),
        ).tracked_borrow_left()
    }

    /// Borrows the resource of type `B`.
    pub proof fn tracked_borrow_right(tracked &self) -> (tracked res: &B)
        requires
            self.is_right(),
            self.is_resource_owner(),
            self.has_resource(),
        ensures
            *res == self.resource()->Right_0,
    {
        StorageResource::guard(&self.r, map![() => self.resource()]).tracked_borrow(
            (),
        ).tracked_borrow_right()
    }

    /// Splits a `Left` token with the given fraction `n`, and gives the resource to that `Left` token if available.
    pub proof fn split_left_with_resource(tracked &mut self, n: int) -> (tracked res: Left<
        A,
        B,
        TOTAL,
    >)
        requires
            old(self).is_left(),
            0 < n < old(self).frac(),
        ensures
            final(self).id() == old(self).id(),
            final(self).frac() == old(self).frac() - n,
            res.id() == old(self).id(),
            res.frac() == n,
            !final(self).is_resource_owner(),
            res.is_resource_owner() <==> old(self).is_resource_owner(),
            res.is_resource_owner() ==> (res.has_resource() <==> old(self).has_resource()),
            res.has_resource() ==> res.resource() == old(self).resource_left(),
            final(self).wf(),
            res.wf(),
    {
        use_type_invariant(&*self);
        let tracked r = Self::split_left_with_resource_helper(&mut self.r, n);
        Left { r }
    }

    proof fn split_left_with_resource_helper(
        tracked r: &mut StorageResource<(), Sum<A, B>, SumSP<A, B, TOTAL>>,
        n: int,
    ) -> (tracked res: StorageResource<(), Sum<A, B>, SumSP<A, B, TOTAL>>)
        requires
            old(r).value().is_left(),
            0 < n < old(r).value().frac(),
            Self::type_inv_inner(old(r).value()),
        ensures
            Self::type_inv_inner(final(r).value()),
            Self::type_inv_inner(res.value()),
            final(r).loc() == old(r).loc(),
            final(r).loc() == res.loc(),
            final(r).value().is_left(),
            final(r).value().frac() == old(r).value().frac() - n,
            res.value().is_left(),
            res.value().frac() == n,
            !final(r).value().is_resource_owner(),
            res.value().is_resource_owner() <==> old(r).value().is_resource_owner(),
            res.value().is_resource_owner() ==> (res.value().has_resource() <==> old(
                r,
            ).value().has_resource()),
            res.value().has_resource() ==> res.value().resource()->Left_0 == old(
                r,
            ).value().resource()->Left_0,
    {
        let tracked mut tmp = Self::alloc_unit_storage();
        tracked_swap(r, &mut tmp);
        let tracked (mut r1, r2) = tmp.split(
            SumSP::Left(None, tmp.value().frac() - n, false),
            SumSP::Left(tmp.value()->Left_0, n, tmp.value().is_resource_owner()),
        );
        tracked_swap(r, &mut r1);
        r2
    }

    /// Splits a `Left` token with the given fraction `n`, without giving the resource to the `Left` token.
    pub proof fn split_left_without_resource(tracked &mut self, n: int) -> (tracked res: Left<
        A,
        B,
        TOTAL,
    >)
        requires
            old(self).is_left(),
            0 < n < old(self).frac(),
        ensures
            final(self).id() == old(self).id(),
            final(self).frac() == old(self).frac() - n,
            res.id() == old(self).id(),
            res.frac() == n,
            !res.is_resource_owner(),
            final(self).is_resource_owner() <==> old(self).is_resource_owner(),
            final(self).is_resource_owner() ==> (final(self).has_resource() <==> old(
                self,
            ).has_resource()),
            final(self).has_resource() ==> final(self).resource() == old(self).resource(),
            final(self).wf(),
            res.wf(),
    {
        use_type_invariant(&*self);
        let tracked r = Self::split_left_without_resource_helper(&mut self.r, n);
        Left { r }
    }

    proof fn split_left_without_resource_helper(
        tracked r: &mut StorageResource<(), Sum<A, B>, SumSP<A, B, TOTAL>>,
        n: int,
    ) -> (tracked res: StorageResource<(), Sum<A, B>, SumSP<A, B, TOTAL>>)
        requires
            old(r).value().is_left(),
            0 < n < old(r).value().frac(),
            Self::type_inv_inner(old(r).value()),
        ensures
            Self::type_inv_inner(final(r).value()),
            Self::type_inv_inner(res.value()),
            final(r).loc() == old(r).loc(),
            final(r).loc() == res.loc(),
            final(r).value().is_left(),
            final(r).value().frac() == old(r).value().frac() - n,
            res.value().is_left(),
            res.value().frac() == n,
            !res.value().is_resource_owner(),
            final(r).value().is_resource_owner() <==> old(r).value().is_resource_owner(),
            final(r).value().is_resource_owner() ==> (final(r).value().has_resource() <==> old(
                r,
            ).value().has_resource()),
            final(r).value().has_resource() ==> final(r).value().resource()->Left_0 == old(
                r,
            ).value().resource()->Left_0,
    {
        let tracked mut tmp = Self::alloc_unit_storage();
        tracked_swap(r, &mut tmp);
        let tracked (mut r1, r2) = tmp.split(
            SumSP::Left(
                tmp.value()->Left_0,
                tmp.value().frac() - n,
                tmp.value().is_resource_owner(),
            ),
            SumSP::Left(None, n, false),
        );
        tracked_swap(r, &mut r1);
        r2
    }

    /// Splits a `Right` token with the given fraction `n`, and gives the resource to that `Right` token if available.
    pub proof fn split_right_with_resource(tracked &mut self, n: int) -> (tracked res: Right<
        A,
        B,
        TOTAL,
    >)
        requires
            old(self).is_right(),
            0 < n < old(self).frac(),
        ensures
            final(self).id() == old(self).id(),
            final(self).frac() == old(self).frac() - n,
            res.id() == old(self).id(),
            res.frac() == n,
            !final(self).is_resource_owner(),
            res.is_resource_owner() <==> old(self).is_resource_owner(),
            res.is_resource_owner() ==> (res.has_resource() <==> old(self).has_resource()),
            res.has_resource() ==> res.resource() == old(self).resource_right(),
            final(self).wf(),
            res.wf(),
    {
        use_type_invariant(&*self);
        let tracked r = Self::split_right_with_resource_helper(&mut self.r, n);
        Right { r }
    }

    proof fn split_right_with_resource_helper(
        tracked r: &mut StorageResource<(), Sum<A, B>, SumSP<A, B, TOTAL>>,
        n: int,
    ) -> (tracked res: StorageResource<(), Sum<A, B>, SumSP<A, B, TOTAL>>)
        requires
            old(r).value().is_right(),
            0 < n < old(r).value().frac(),
            Self::type_inv_inner(old(r).value()),
        ensures
            Self::type_inv_inner(final(r).value()),
            Self::type_inv_inner(res.value()),
            final(r).loc() == old(r).loc(),
            final(r).loc() == res.loc(),
            final(r).value().is_right(),
            final(r).value().frac() == old(r).value().frac() - n,
            res.value().is_right(),
            res.value().frac() == n,
            !final(r).value().is_resource_owner(),
            res.value().is_resource_owner() <==> old(r).value().is_resource_owner(),
            res.value().is_resource_owner() ==> (res.value().has_resource() <==> old(
                r,
            ).value().has_resource()),
            res.value().has_resource() ==> res.value().resource()->Right_0 == old(
                r,
            ).value().resource()->Right_0,
    {
        let tracked mut tmp = Self::alloc_unit_storage();
        tracked_swap(r, &mut tmp);
        let tracked (mut r1, r2) = tmp.split(
            SumSP::Right(None, tmp.value().frac() - n, false),
            SumSP::Right(tmp.value()->Right_0, n, tmp.value().is_resource_owner()),
        );
        tracked_swap(r, &mut r1);
        r2
    }

    /// Splits a `Right` token with the given fraction `n`, without giving the resource to the `Right` token.
    pub proof fn split_right_without_resource(tracked &mut self, n: int) -> (tracked res: Right<
        A,
        B,
        TOTAL,
    >)
        requires
            old(self).is_right(),
            0 < n < old(self).frac(),
        ensures
            final(self).id() == old(self).id(),
            final(self).frac() == old(self).frac() - n,
            res.id() == old(self).id(),
            res.frac() == n,
            !res.is_resource_owner(),
            final(self).is_resource_owner() <==> old(self).is_resource_owner(),
            final(self).is_resource_owner() ==> (final(self).has_resource() <==> old(
                self,
            ).has_resource()),
            final(self).has_resource() ==> final(self).resource() == old(self).resource(),
            final(self).wf(),
            res.wf(),
    {
        use_type_invariant(&*self);
        let tracked r = Self::split_right_without_resource_helper(&mut self.r, n);
        Right { r }
    }

    proof fn split_right_without_resource_helper(
        tracked r: &mut StorageResource<(), Sum<A, B>, SumSP<A, B, TOTAL>>,
        n: int,
    ) -> (tracked res: StorageResource<(), Sum<A, B>, SumSP<A, B, TOTAL>>)
        requires
            old(r).value().is_right(),
            0 < n < old(r).value().frac(),
            Self::type_inv_inner(old(r).value()),
        ensures
            Self::type_inv_inner(final(r).value()),
            Self::type_inv_inner(res.value()),
            final(r).loc() == old(r).loc(),
            final(r).loc() == res.loc(),
            final(r).value().is_right(),
            final(r).value().frac() == old(r).value().frac() - n,
            res.value().is_right(),
            res.value().frac() == n,
            !res.value().is_resource_owner(),
            final(r).value().is_resource_owner() <==> old(r).value().is_resource_owner(),
            final(r).value().is_resource_owner() ==> (final(r).value().has_resource() <==> old(
                r,
            ).value().has_resource()),
            final(r).value().has_resource() ==> final(r).value().resource()->Right_0 == old(
                r,
            ).value().resource()->Right_0,
    {
        let tracked mut tmp = Self::alloc_unit_storage();
        tracked_swap(r, &mut tmp);
        let tracked (mut r1, r2) = tmp.split(
            SumSP::Right(
                tmp.value()->Right_0,
                tmp.value().frac() - n,
                tmp.value().is_resource_owner(),
            ),
            SumSP::Right(None, n, false),
        );
        tracked_swap(r, &mut r1);
        r2
    }

    /// Splits a `OneLeftOwner`, giving it the resource.
    pub proof fn split_one_left_owner(tracked &mut self) -> (tracked res: OneLeftOwner<A, B, TOTAL>)
        requires
            old(self).is_left(),
            old(self).is_resource_owner(),
            old(self).frac() > 1,
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).is_left(),
            final(self).frac() + 1 == old(self).frac(),
            !final(self).is_resource_owner(),
            res.id() == old(self).id(),
            res.wf(),
            res.has_resource() == old(self).has_resource(),
            res.has_resource() ==> res.resource() == old(self).resource_left(),
    {
        use_type_invariant(&*self);
        let tracked r = Self::split_left_with_resource_helper(&mut self.r, 1);
        OneLeftOwner { r: Left { r } }
    }

    /// Splits a `OneRightOwner`, giving it the resource.
    pub proof fn split_one_right_owner(tracked &mut self) -> (tracked res: OneRightOwner<
        A,
        B,
        TOTAL,
    >)
        requires
            old(self).is_right(),
            old(self).is_resource_owner(),
            old(self).frac() > 1,
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).is_right(),
            final(self).frac() + 1 == old(self).frac(),
            !final(self).is_resource_owner(),
            res.id() == old(self).id(),
            res.wf(),
            res.has_resource() == old(self).has_resource(),
            res.has_resource() ==> res.resource() == old(self).resource_right(),
    {
        use_type_invariant(&*self);
        let tracked r = Self::split_right_with_resource_helper(&mut self.r, 1);
        OneRightOwner { r: Right { r } }
    }

    /// Splits a `OneLeftKnowledge`, without giving it the resource.
    pub proof fn split_one_left_knowledge(tracked &mut self) -> (tracked res: OneLeftKnowledge<
        A,
        B,
        TOTAL,
    >)
        requires
            old(self).is_left(),
            old(self).frac() > 1,
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).is_left(),
            final(self).frac() + 1 == old(self).frac(),
            final(self).is_resource_owner() == old(self).is_resource_owner(),
            final(self).has_resource() == old(self).has_resource(),
            final(self).has_resource() ==> final(self).resource() == old(self).resource(),
            res.id() == old(self).id(),
            res.wf(),
    {
        use_type_invariant(&*self);
        let tracked r = Self::split_left_without_resource_helper(&mut self.r, 1);
        OneLeftKnowledge { r: Left { r } }
    }

    /// Splits a `OneRightKnowledge`, without giving it the resource.
    pub proof fn split_one_right_knowledge(tracked &mut self) -> (tracked res: OneRightKnowledge<
        A,
        B,
        TOTAL,
    >)
        requires
            old(self).is_right(),
            old(self).frac() > 1,
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).is_right(),
            final(self).frac() + 1 == old(self).frac(),
            final(self).is_resource_owner() == old(self).is_resource_owner(),
            final(self).has_resource() == old(self).has_resource(),
            final(self).has_resource() ==> final(self).resource() == old(self).resource(),
            res.id() == old(self).id(),
            res.wf(),
    {
        use_type_invariant(&*self);
        let tracked r = Self::split_right_without_resource_helper(&mut self.r, 1);
        OneRightKnowledge { r: Right { r } }
    }

    /// Takes the resource out of the token if it is in the left variant.
    pub proof fn take_resource_left(tracked &mut self) -> (tracked res: A)
        requires
            old(self).is_left(),
            old(self).is_resource_owner(),
            old(self).has_resource(),
        ensures
            final(self).is_left(),
            res == old(self).resource_left(),
            final(self).id() == old(self).id(),
            final(self).is_resource_owner(),
            final(self).has_no_resource(),
            final(self).frac() == old(self).frac(),
            final(self).wf(),
    {
        use_type_invariant(&*self);
        Self::take_resource_left_helper(&mut self.r)
    }

    proof fn take_resource_left_helper(
        tracked r: &mut StorageResource<(), Sum<A, B>, SumSP<A, B, TOTAL>>,
    ) -> (tracked res: A)
        requires
            old(r).value().is_left(),
            old(r).value().is_resource_owner(),
            old(r).value().has_resource(),
            Self::type_inv_inner(old(r).value()),
        ensures
            Self::type_inv_inner(final(r).value()),
            res == old(r).value().resource()->Left_0,
            final(r).loc() == old(r).loc(),
            final(r).value().is_left(),
            final(r).value().is_resource_owner(),
            final(r).value().has_no_resource(),
            final(r).value().frac() == old(r).value().frac(),
    {
        let tracked mut tmp = Self::alloc_unit_storage();
        tracked_swap(r, &mut tmp);
        tmp.value().lemma_withdraws_left();
        let tracked (mut r1, mut s) = tmp.withdraw(
            SumSP::Left(None, tmp.value().frac(), true),
            map![() => tmp.value().resource()],
        );
        tracked_swap(r, &mut r1);
        s.tracked_remove(()).tracked_take_left()
    }

    /// Takes the resource out of the token if it is in the right variant.
    pub proof fn take_resource_right(tracked &mut self) -> (tracked res: B)
        requires
            old(self).is_right(),
            old(self).is_resource_owner(),
            old(self).has_resource(),
        ensures
            final(self).is_right(),
            res == old(self).resource_right(),
            final(self).id() == old(self).id(),
            final(self).is_resource_owner(),
            final(self).has_no_resource(),
            final(self).frac() == old(self).frac(),
            final(self).wf(),
    {
        use_type_invariant(&*self);
        Self::take_resource_right_helper(&mut self.r)
    }

    proof fn take_resource_right_helper(
        tracked r: &mut StorageResource<(), Sum<A, B>, SumSP<A, B, TOTAL>>,
    ) -> (tracked res: B)
        requires
            old(r).value().is_right(),
            old(r).value().is_resource_owner(),
            old(r).value().has_resource(),
            Self::type_inv_inner(old(r).value()),
        ensures
            Self::type_inv_inner(final(r).value()),
            res == old(r).value().resource()->Right_0,
            final(r).loc() == old(r).loc(),
            final(r).value().is_right(),
            final(r).value().is_resource_owner(),
            final(r).value().has_no_resource(),
            final(r).value().frac() == old(r).value().frac(),
    {
        let tracked mut tmp = Self::alloc_unit_storage();
        tracked_swap(r, &mut tmp);
        tmp.value().lemma_withdraws_right();
        let tracked (mut r1, mut s) = tmp.withdraw(
            SumSP::Right(None, tmp.value().frac(), true),
            map![() => tmp.value().resource()],
        );
        tracked_swap(r, &mut r1);
        s.tracked_remove(()).tracked_take_right()
    }

    /// Puts a resource of type `A` back to the token.
    pub proof fn put_resource_left(tracked &mut self, tracked a: A)
        requires
            old(self).is_left(),
            old(self).is_resource_owner(),
            old(self).has_no_resource(),
        ensures
            final(self).is_left(),
            final(self).has_resource(),
            final(self).is_resource_owner(),
            final(self).resource_left() == a,
            final(self).id() == old(self).id(),
            final(self).frac() == old(self).frac(),
            final(self).wf(),
    {
        use_type_invariant(&*self);
        Self::put_resource_left_helper(&mut self.r, a);
    }

    proof fn put_resource_left_helper(
        tracked r: &mut StorageResource<(), Sum<A, B>, SumSP<A, B, TOTAL>>,
        tracked a: A,
    )
        requires
            old(r).value().is_left(),
            old(r).value().is_resource_owner(),
            old(r).value().has_no_resource(),
            Self::type_inv_inner(old(r).value()),
        ensures
            Self::type_inv_inner(final(r).value()),
            final(r).loc() == old(r).loc(),
            final(r).value().is_left(),
            final(r).value().is_resource_owner(),
            final(r).value().has_resource(),
            final(r).value().resource()->Left_0 == a,
            final(r).value().frac() == old(r).value().frac(),
    {
        let ghost a_ghost = a;
        let tracked mut m = Map::tracked_empty();
        m.tracked_insert((), Sum::<A, B>::Left(a));
        let tracked mut tmp = Self::alloc_unit_storage();
        tracked_swap(r, &mut tmp);
        tmp.value().lemma_deposit_left(a);
        let tracked mut r1 = tmp.deposit(m, SumSP::Left(Some(a), tmp.value().frac(), true));
        tracked_swap(r, &mut r1);
    }

    /// Puts a resource of type `B` back to the token.
    pub proof fn put_resource_right(tracked &mut self, tracked b: B)
        requires
            old(self).is_right(),
            old(self).is_resource_owner(),
            old(self).has_no_resource(),
        ensures
            final(self).is_right(),
            final(self).is_resource_owner(),
            final(self).has_resource(),
            final(self).resource_right() == b,
            final(self).id() == old(self).id(),
            final(self).frac() == old(self).frac(),
            final(self).wf(),
    {
        use_type_invariant(&*self);
        Self::put_resource_right_helper(&mut self.r, b);
    }

    proof fn put_resource_right_helper(
        tracked r: &mut StorageResource<(), Sum<A, B>, SumSP<A, B, TOTAL>>,
        tracked b: B,
    )
        requires
            old(r).value().is_right(),
            old(r).value().is_resource_owner(),
            old(r).value().has_no_resource(),
            Self::type_inv_inner(old(r).value()),
        ensures
            Self::type_inv_inner(final(r).value()),
            final(r).loc() == old(r).loc(),
            final(r).value().is_right(),
            final(r).value().is_resource_owner(),
            final(r).value().has_resource(),
            final(r).value().resource()->Right_0 == b,
            final(r).value().frac() == old(r).value().frac(),
    {
        let ghost b_ghost = b;
        let tracked mut m = Map::tracked_empty();
        m.tracked_insert((), Sum::<A, B>::Right(b));
        let tracked mut tmp = Self::alloc_unit_storage();
        tracked_swap(r, &mut tmp);
        tmp.value().lemma_deposit_right(b);
        let tracked mut r1 = tmp.deposit(m, SumSP::Right(Some(b), tmp.value().frac(), true));
        tracked_swap(r, &mut r1);
    }

    /// Updates the resource of type `A` in the token, when the token is in the left variant and is a resource owner.
    /// Returns the old resource if available.
    pub proof fn update_left(tracked &mut self, tracked a: A) -> (tracked res: Option<A>)
        requires
            old(self).is_left(),
            old(self).is_resource_owner(),
            old(self).has_resource(),
        ensures
            final(self).is_left(),
            final(self).is_resource_owner(),
            final(self).has_resource(),
            final(self).resource_left() == a,
            final(self).id() == old(self).id(),
            final(self).frac() == old(self).frac(),
            res == Some(old(self).resource_left()),
            final(self).wf(),
    {
        use_type_invariant(&*self);
        let tracked mut res = None;
        if self.has_resource() {
            let tracked r = Self::take_resource_left_helper(&mut self.r);
            res = Some(r);
        }
        Self::put_resource_left_helper(&mut self.r, a);
        res
    }

    /// Updates the resource of type `B` in the token, when the token is in the right variant and is a resource owner.
    /// Returns the old resource if available.
    pub proof fn update_right(tracked &mut self, tracked b: B) -> (tracked res: Option<B>)
        requires
            old(self).is_right(),
            old(self).is_resource_owner(),
            old(self).has_resource(),
        ensures
            final(self).is_right(),
            final(self).is_resource_owner(),
            final(self).has_resource(),
            final(self).resource_right() == b,
            final(self).id() == old(self).id(),
            final(self).frac() == old(self).frac(),
            res == Some(old(self).resource_right()),
            final(self).wf(),
    {
        use_type_invariant(&*self);
        let tracked mut res = None;
        if self.has_resource() {
            let tracked r = Self::take_resource_right_helper(&mut self.r);
            res = Some(r);
        }
        Self::put_resource_right_helper(&mut self.r, b);
        res
    }

    /// Changes the token to the left invariant with a new resource of type `A`, and returns the old resource if available.
    ///
    /// NOTE: Unlike `Self::update_left`, this operation can only be done with the full fraction, because there should be no `Right` tokens to witness
    /// the existence of the old resource after the update.
    pub proof fn change_to_left(tracked &mut self, tracked a: A) -> (tracked res: Option<Sum<A, B>>)
        requires
            old(self).is_resource_owner(),
            old(self).frac() == TOTAL,
        ensures
            final(self).id() == old(self).id(),
            final(self).protocol_monoid() == SumSP::<A, B, TOTAL>::Left(
                Some(a),
                old(self).frac(),
                true,
            ),
            final(self).frac() == old(self).frac(),
            final(self).is_left(),
            final(self).is_resource_owner(),
            final(self).has_resource(),
            final(self).resource_left() == a,
            old(self).has_resource() ==> res == Some(old(self).resource()),
            old(self).has_no_resource() ==> res == None::<Sum<A, B>>,
            final(self).wf(),
    {
        use_type_invariant(&*self);
        let tracked res = Self::change_to_left_helper(&mut self.r, a);
        res
    }

    proof fn change_to_left_helper(
        tracked r: &mut StorageResource<(), Sum<A, B>, SumSP<A, B, TOTAL>>,
        tracked a: A,
    ) -> (tracked res: Option<Sum<A, B>>)
        requires
            old(r).value().is_resource_owner(),
            old(r).value().frac() == TOTAL,
            Self::type_inv_inner(old(r).value()),
        ensures
            Self::type_inv_inner(final(r).value()),
            final(r).loc() == old(r).loc(),
            final(r).value() == SumSP::<A, B, TOTAL>::Left(Some(a), old(r).value().frac(), true),
            final(r).value().frac() == old(r).value().frac(),
            final(r).value().is_left(),
            final(r).value().is_resource_owner(),
            final(r).value().has_resource(),
            final(r).value().resource()->Left_0 == a,
            old(r).value().has_resource() ==> res == Some(old(r).value().resource()),
            old(r).value().has_no_resource() ==> res == None::<Sum<A, B>>,
    {
        let tracked mut res = None;
        let tracked mut tmp = Self::alloc_unit_storage();
        tracked_swap(r, &mut tmp);
        if tmp.value().has_resource() {
            if tmp.value().is_left() {
                let tracked ret = Self::take_resource_left_helper(&mut tmp);
                res = Some(Sum::Left(ret));
            } else {
                let tracked ret = Self::take_resource_right_helper(&mut tmp);
                res = Some(Sum::Right(ret));
            }
        }
        let tracked mut resource = tmp.update(
            SumSP::<A, B, TOTAL>::Left(None, tmp.value().frac(), true),
        );
        Self::put_resource_left_helper(&mut resource, a);
        tracked_swap(r, &mut resource);
        res
    }

    /// Changes the token to the right invariant with a new resource of type `B`, and returns the old resource if available.
    ///
    /// NOTE: Unlike `Self::update_right`, this operation can only be done with the full fraction, because there should be no `Left` tokens to witness
    /// the existence of the old resource after the update.
    pub proof fn change_to_right(tracked &mut self, tracked b: B) -> (tracked res: Option<
        Sum<A, B>,
    >)
        requires
            old(self).is_resource_owner(),
            old(self).frac() == TOTAL,
        ensures
            final(self).id() == old(self).id(),
            final(self).protocol_monoid() == SumSP::<A, B, TOTAL>::Right(
                Some(b),
                old(self).frac(),
                true,
            ),
            final(self).frac() == old(self).frac(),
            final(self).is_right(),
            final(self).is_resource_owner(),
            final(self).has_resource(),
            final(self).resource_right() == b,
            old(self).has_resource() ==> res == Some(old(self).resource()),
            old(self).has_no_resource() ==> res == None::<Sum<A, B>>,
            final(self).wf(),
    {
        use_type_invariant(&*self);
        let tracked res = Self::change_to_right_helper(&mut self.r, b);
        res
    }

    proof fn change_to_right_helper(
        tracked r: &mut StorageResource<(), Sum<A, B>, SumSP<A, B, TOTAL>>,
        tracked b: B,
    ) -> (tracked res: Option<Sum<A, B>>)
        requires
            old(r).value().is_resource_owner(),
            old(r).value().frac() == TOTAL,
            Self::type_inv_inner(old(r).value()),
        ensures
            Self::type_inv_inner(final(r).value()),
            final(r).loc() == old(r).loc(),
            final(r).value() == SumSP::<A, B, TOTAL>::Right(Some(b), old(r).value().frac(), true),
            final(r).value().frac() == old(r).value().frac(),
            final(r).value().is_right(),
            final(r).value().is_resource_owner(),
            final(r).value().has_resource(),
            final(r).value().resource()->Right_0 == b,
            old(r).value().has_resource() ==> res == Some(old(r).value().resource()),
            old(r).value().has_no_resource() ==> res == None::<Sum<A, B>>,
    {
        let tracked mut res = None;
        let tracked mut tmp = Self::alloc_unit_storage();
        tracked_swap(r, &mut tmp);
        if tmp.value().has_resource() {
            if tmp.value().is_left() {
                let tracked ret = Self::take_resource_left_helper(&mut tmp);
                res = Some(Sum::Left(ret));
            } else {
                let tracked ret = Self::take_resource_right_helper(&mut tmp);
                res = Some(Sum::Right(ret));
            }
        }
        let tracked mut resource = tmp.update(
            SumSP::<A, B, TOTAL>::Right(None, tmp.value().frac(), true),
        );
        Self::put_resource_right_helper(&mut resource, b);
        tracked_swap(r, &mut resource);
        res
    }

    /// Joins this token with another `Left` token with the same id.
    pub proof fn join_left(tracked &mut self, tracked other: Left<A, B, TOTAL>)
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self).is_left(),
            final(self).is_resource_owner() == (old(self).is_resource_owner()
                || other.is_resource_owner()),
            final(self).has_resource() == (old(self).has_resource() || other.has_resource()),
            final(self).has_resource() ==> final(self).resource() == if old(
                self,
            ).is_resource_owner() {
                old(self).resource()
            } else {
                Sum::Left(other.resource())
            },
            final(self).frac() == old(self).frac() + other.frac(),
            final(self).wf(),
    {
        use_type_invariant(&*self);
        use_type_invariant(&other);
        Self::join_left_helper(&mut self.r, other.r);
    }

    proof fn join_left_helper(
        tracked r: &mut StorageResource<(), Sum<A, B>, SumSP<A, B, TOTAL>>,
        tracked other: StorageResource<(), Sum<A, B>, SumSP<A, B, TOTAL>>,
    )
        requires
            Self::type_inv_inner(old(r).value()),
            Self::type_inv_inner(other.value()),
            old(r).loc() == other.loc(),
            other.value().is_left(),
        ensures
            Self::type_inv_inner(final(r).value()),
            final(r).loc() == old(r).loc(),
            final(r).value().is_left(),
            final(r).value().frac() == old(r).value().frac() + other.value().frac(),
            final(r).value().is_resource_owner() == (old(r).value().is_resource_owner()
                || other.value().is_resource_owner()),
            final(r).value().has_resource() == (old(r).value().has_resource()
                || other.value().has_resource()),
            final(r).value().has_resource() ==> final(r).value().resource() == if old(
                r,
            ).value().is_resource_owner() {
                old(r).value().resource()
            } else {
                other.value().resource()
            },
    {
        r.validate_with_shared(&other);
        let tracked mut tmp = Self::alloc_unit_storage();
        tracked_swap(r, &mut tmp);
        let tracked mut joined = StorageResource::join(tmp, other);
        tracked_swap(r, &mut joined);
    }

    /// Joins this token with another `Right` token with the same id.
    pub proof fn join_right(tracked &mut self, tracked other: Right<A, B, TOTAL>)
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self).is_right(),
            final(self).is_resource_owner() == (old(self).is_resource_owner()
                || other.is_resource_owner()),
            final(self).has_resource() == (old(self).has_resource() || other.has_resource()),
            final(self).has_resource() ==> final(self).resource() == if old(
                self,
            ).is_resource_owner() {
                old(self).resource()
            } else {
                Sum::Right(other.resource())
            },
            final(self).frac() == old(self).frac() + other.frac(),
            final(self).wf(),
    {
        use_type_invariant(&*self);
        use_type_invariant(&other);
        Self::join_right_helper(&mut self.r, other.r);
    }

    proof fn join_right_helper(
        tracked r: &mut StorageResource<(), Sum<A, B>, SumSP<A, B, TOTAL>>,
        tracked other: StorageResource<(), Sum<A, B>, SumSP<A, B, TOTAL>>,
    )
        requires
            Self::type_inv_inner(old(r).value()),
            Self::type_inv_inner(other.value()),
            old(r).loc() == other.loc(),
            other.value().is_right(),
        ensures
            Self::type_inv_inner(final(r).value()),
            final(r).loc() == old(r).loc(),
            final(r).value().is_right(),
            final(r).value().frac() == old(r).value().frac() + other.value().frac(),
            final(r).value().is_resource_owner() == (old(r).value().is_resource_owner()
                || other.value().is_resource_owner()),
            final(r).value().has_resource() == (old(r).value().has_resource()
                || other.value().has_resource()),
            final(r).value().has_resource() ==> final(r).value().resource() == if old(
                r,
            ).value().is_resource_owner() {
                old(r).value().resource()
            } else {
                other.value().resource()
            },
    {
        r.validate_with_shared(&other);
        let tracked mut tmp = Self::alloc_unit_storage();
        tracked_swap(r, &mut tmp);
        let tracked mut joined = StorageResource::join(tmp, other);
        tracked_swap(r, &mut joined);
    }

    /// Joins a `OneLeftOwner` token.
    pub proof fn join_one_left_owner(tracked &mut self, tracked other: OneLeftOwner<A, B, TOTAL>)
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self).is_left(),
            final(self).is_resource_owner(),
            final(self).has_resource() == other.has_resource(),
            final(self).has_resource() ==> final(self).resource_left() == other.resource(),
            final(self).frac() == old(self).frac() + 1,
            final(self).wf(),
    {
        use_type_invariant(&*self);
        use_type_invariant(&other);
        StorageResource::validate_with_shared(&mut self.r, &other.r.r);
        Self::join_left_helper(&mut self.r, other.r.r);
    }

    /// Joins a `OneRightOwner` token.
    pub proof fn join_one_right_owner(tracked &mut self, tracked other: OneRightOwner<A, B, TOTAL>)
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self).is_right(),
            final(self).is_resource_owner(),
            final(self).has_resource() == other.has_resource(),
            final(self).has_resource() ==> final(self).resource_right() == other.resource(),
            final(self).frac() == old(self).frac() + 1,
            final(self).wf(),
    {
        use_type_invariant(&*self);
        use_type_invariant(&other);
        StorageResource::validate_with_shared(&mut self.r, &other.r.r);
        Self::join_right_helper(&mut self.r, other.r.r);
    }

    /// Joins a `OneLeftKnowledge` token.
    pub proof fn join_one_left_knowledge(
        tracked &mut self,
        tracked other: OneLeftKnowledge<A, B, TOTAL>,
    )
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self).is_left(),
            final(self).is_resource_owner() == old(self).is_resource_owner(),
            final(self).has_resource() == old(self).has_resource(),
            final(self).has_resource() ==> final(self).resource() == old(self).resource(),
            final(self).frac() == old(self).frac() + 1,
            final(self).wf(),
    {
        use_type_invariant(&*self);
        use_type_invariant(&other);
        StorageResource::validate_with_shared(&mut self.r, &other.r.r);
        Self::join_left_helper(&mut self.r, other.r.r);
    }

    /// Joins a `OneRightKnowledge` token.
    pub proof fn join_one_right_knowledge(
        tracked &mut self,
        tracked other: OneRightKnowledge<A, B, TOTAL>,
    )
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self).is_right(),
            final(self).is_resource_owner() == old(self).is_resource_owner(),
            final(self).has_resource() == old(self).has_resource(),
            final(self).has_resource() ==> final(self).resource() == old(self).resource(),
            final(self).frac() == old(self).frac() + 1,
            final(self).wf(),
    {
        use_type_invariant(&*self);
        use_type_invariant(&other);
        StorageResource::validate_with_shared(&mut self.r, &other.r.r);
        Self::join_right_helper(&mut self.r, other.r.r);
    }
}

impl<A, B, const TOTAL: u64> Left<A, B, TOTAL> {
    /// Returns the unique identifier.
    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    /// The underlying protocol monoid value for this resource.
    pub closed spec fn protocol_monoid(self) -> SumSP<A, B, TOTAL> {
        self.r.value()
    }

    /// Whether this token has the right to access the underlying resource.
    pub open spec fn is_resource_owner(self) -> bool {
        self.protocol_monoid().is_resource_owner()
    }

    /// The resource value, only meaningful if `is_resource_owner` is true.
    pub open spec fn resource(self) -> A {
        self.protocol_monoid().resource()->Left_0
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.wf()
    }

    /// Type invariant.
    pub open spec fn wf(self) -> bool {
        &&& self.protocol_monoid().is_left()
        &&& self.protocol_monoid().is_valid()
        &&& 1 <= self.frac() <= TOTAL
        &&& self.is_resource_owner() ==> (self.has_resource() <==> !self.has_no_resource())
    }

    /// Whether the resource is currently stored, only meaningful if `is_resource_owner` is true.
    pub open spec fn has_resource(self) -> bool {
        self.protocol_monoid().has_resource()
    }

    /// Whether the resource has been taken, only meaningful if `is_resource_owner` is true.
    pub open spec fn has_no_resource(self) -> bool {
        self.protocol_monoid().has_no_resource()
    }

    /// The fraction this token represents.
    pub open spec fn frac(self) -> int {
        self.protocol_monoid().frac()
    }

    /// `Left` token satisfies the type invariant.
    pub proof fn validate(tracked &self)
        ensures
            self.wf(),
    {
        use_type_invariant(&*self);
    }

    /// The existence of two `Left` tokens with the same id ensures at most one of them is the resource owner.
    pub proof fn validate_with_left(tracked &mut self, tracked other: &Self)
        requires
            old(self).id() == other.id(),
        ensures
            *old(self) == *final(self),
            !(final(self).is_resource_owner() && other.is_resource_owner()),
            final(self).frac() + other.frac() <= TOTAL,
            final(self).wf(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.r.validate_with_shared(&other.r);
    }

    /// The existence of a `Right` token ensures they can not have the same id.
    pub proof fn validate_with_right(tracked &self, tracked other: &Right<A, B, TOTAL>)
        ensures
            self.id() != other.id(),
            self.wf(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        if self.id() == other.id() {
            self.r.join_shared(&other.r).validate();
        }
    }

    /// Borrows the resource of type `A`.
    pub proof fn tracked_borrow(tracked &self) -> (tracked res: &A)
        requires
            self.has_resource(),
        ensures
            *res == self.resource(),
    {
        use_type_invariant(&*self);
        StorageResource::guard(
            &self.r,
            map![() => Sum::<A, B>::Left(self.resource())],
        ).tracked_borrow(()).tracked_borrow_left()
    }

    /// Takes the resource out of the token.
    pub proof fn take_resource(tracked &mut self) -> (tracked res: A)
        requires
            old(self).is_resource_owner(),
            old(self).has_resource(),
        ensures
            final(self).id() == old(self).id(),
            res == old(self).resource(),
            final(self).is_resource_owner(),
            final(self).has_no_resource(),
            final(self).frac() == old(self).frac(),
            final(self).wf(),
    {
        use_type_invariant(&*self);
        let tracked r = SumResource::take_resource_left_helper(&mut self.r);
        r
    }

    /// Puts a resource of type `A` back to the token.
    pub proof fn put_resource(tracked &mut self, tracked a: A)
        requires
            old(self).is_resource_owner(),
            old(self).has_no_resource(),
        ensures
            final(self).id() == old(self).id(),
            final(self).protocol_monoid() == SumSP::<A, B, TOTAL>::Left(
                Some(a),
                final(self).frac(),
                true,
            ),
            final(self).is_resource_owner(),
            final(self).has_resource(),
            final(self).resource() == a,
            final(self).frac() == old(self).frac(),
            final(self).wf(),
    {
        use_type_invariant(&*self);
        SumResource::put_resource_left_helper(&mut self.r, a);
    }

    /// Splits this token into two `Left` tokens with the given fraction `n`, given the resource to the new token if available.
    pub proof fn split_with_resource(tracked &mut self, n: int) -> (tracked res: Self)
        requires
            0 < n < old(self).frac(),
        ensures
            final(self).id() == old(self).id(),
            res.id() == final(self).id(),
            final(self).frac() == old(self).frac() - n,
            res.frac() == n,
            !final(self).is_resource_owner(),
            res.is_resource_owner() <==> old(self).is_resource_owner(),
            res.is_resource_owner() ==> (res.has_resource() <==> old(self).has_resource()),
            res.has_resource() ==> res.resource() == old(self).resource(),
            final(self).wf(),
            res.wf(),
    {
        use_type_invariant(&*self);
        let tracked r = SumResource::split_left_with_resource_helper(&mut self.r, n);
        Self { r }
    }

    /// Splits this token into two `Left` tokens with the given fraction `n`, without giving the resource to the new token.
    pub proof fn split_without_resource(tracked &mut self, n: int) -> (tracked res: Self)
        requires
            0 < n < old(self).frac(),
        ensures
            final(self).id() == old(self).id(),
            res.id() == final(self).id(),
            final(self).frac() == old(self).frac() - n,
            res.frac() == n,
            !res.is_resource_owner(),
            final(self).is_resource_owner() <==> old(self).is_resource_owner(),
            final(self).is_resource_owner() ==> (final(self).has_resource() <==> old(
                self,
            ).has_resource()),
            final(self).has_resource() ==> final(self).resource() == old(self).resource(),
            final(self).wf(),
            res.wf(),
    {
        use_type_invariant(&*self);
        let tracked r = SumResource::split_left_without_resource_helper(&mut self.r, n);
        Self { r }
    }

    /// Updates the token with a new resource of type `A`, and returns the old resource if available.
    pub proof fn update(tracked &mut self, tracked a: A) -> (tracked res: Option<A>)
        requires
            old(self).is_resource_owner(),
        ensures
            final(self).id() == old(self).id(),
            final(self).is_resource_owner(),
            final(self).has_resource(),
            final(self).resource() == a,
            final(self).frac() == old(self).frac(),
            res == if old(self).has_resource() {
                Some(old(self).resource())
            } else {
                None
            },
            final(self).wf(),
    {
        use_type_invariant(&*self);
        let tracked mut res = None;
        if self.has_resource() {
            res = Some(self.take_resource());
        }
        self.put_resource(a);
        res
    }
}

impl<A, B, const TOTAL: u64> Right<A, B, TOTAL> {
    /// Returns the unique identifier.
    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    /// The underlying protocol monoid value for this resource.
    pub closed spec fn protocol_monoid(self) -> SumSP<A, B, TOTAL> {
        self.r.value()
    }

    /// Whether this token has the right to access the underlying resource.
    pub open spec fn is_resource_owner(self) -> bool {
        self.protocol_monoid().is_resource_owner()
    }

    /// The resource value, only meaningful if `is_resource_owner` is true.
    pub open spec fn resource(self) -> B {
        self.protocol_monoid().resource()->Right_0
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.wf()
    }

    /// Type invariant.
    pub open spec fn wf(self) -> bool {
        &&& self.protocol_monoid().is_right()
        &&& self.protocol_monoid().is_valid()
        &&& 1 <= self.frac() <= TOTAL
        &&& self.is_resource_owner() ==> (self.has_resource() <==> !self.has_no_resource())
    }

    /// Whether the resource is currently stored, only meaningful if `is_resource_owner` is true.
    pub open spec fn has_resource(self) -> bool {
        self.protocol_monoid().has_resource()
    }

    /// Whether the resource has been taken, only meaningful if `is_resource_owner` is true.
    pub open spec fn has_no_resource(self) -> bool {
        self.protocol_monoid().has_no_resource()
    }

    /// The fraction this token represents.
    pub open spec fn frac(self) -> int {
        self.protocol_monoid().frac()
    }

    /// `Right` token satisfies the type invariant.
    pub proof fn validate(tracked &self)
        ensures
            self.wf(),
    {
        use_type_invariant(&*self);
    }

    /// The existence of a `Left` token ensures they can not have the same id.
    pub proof fn validate_with_left(tracked &self, tracked other: &Left<A, B, TOTAL>)
        ensures
            self.id() != other.id(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        if self.id() == other.id() {
            self.r.join_shared(&other.r).validate();
        }
    }

    /// The existence of two `Right` tokens with the same id ensures at most one of them is the resource owner.
    pub proof fn validate_with_right(tracked &mut self, tracked other: &Self)
        requires
            old(self).id() == other.id(),
        ensures
            *old(self) == *final(self),
            !(final(self).is_resource_owner() && other.is_resource_owner()),
            final(self).frac() + other.frac() <= TOTAL,
            final(self).wf(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.r.validate_with_shared(&other.r);
    }

    /// Borrows the resource of type `B`.
    pub proof fn tracked_borrow(tracked &self) -> (tracked res: &B)
        requires
            self.has_resource(),
        ensures
            *res == self.resource(),
    {
        use_type_invariant(&*self);
        StorageResource::guard(
            &self.r,
            map![() => Sum::<A, B>::Right(self.resource())],
        ).tracked_borrow(()).tracked_borrow_right()
    }

    /// Takes the resource out of the token.
    pub proof fn take_resource(tracked &mut self) -> (tracked res: B)
        requires
            old(self).is_resource_owner(),
            old(self).has_resource(),
        ensures
            final(self).id() == old(self).id(),
            res == old(self).resource(),
            final(self).is_resource_owner(),
            final(self).has_no_resource(),
            final(self).frac() == old(self).frac(),
            final(self).wf(),
    {
        use_type_invariant(&*self);
        let tracked r = SumResource::take_resource_right_helper(&mut self.r);
        r
    }

    /// Puts a resource of type `B` back to the token.
    pub proof fn put_resource(tracked &mut self, tracked b: B)
        requires
            old(self).is_resource_owner(),
            old(self).has_no_resource(),
        ensures
            final(self).id() == old(self).id(),
            final(self).protocol_monoid() == SumSP::<A, B, TOTAL>::Right(
                Some(b),
                final(self).frac(),
                true,
            ),
            final(self).is_resource_owner(),
            final(self).has_resource(),
            final(self).resource() == b,
            final(self).frac() == old(self).frac(),
            final(self).wf(),
    {
        use_type_invariant(&*self);
        SumResource::put_resource_right_helper(&mut self.r, b);
    }

    /// Splits this token into two `Right` tokens with the given fraction `n`, given the resource to the new token if available.
    pub proof fn split_with_resource(tracked &mut self, n: int) -> (tracked res: Self)
        requires
            0 < n < old(self).frac(),
        ensures
            final(self).id() == old(self).id(),
            res.id() == final(self).id(),
            final(self).frac() == old(self).frac() - n,
            res.frac() == n,
            !final(self).is_resource_owner(),
            res.is_resource_owner() <==> old(self).is_resource_owner(),
            res.is_resource_owner() ==> (res.has_resource() <==> old(self).has_resource()),
            res.has_resource() ==> res.resource() == old(self).resource(),
            final(self).wf(),
            res.wf(),
    {
        use_type_invariant(&*self);
        let tracked r = SumResource::split_right_with_resource_helper(&mut self.r, n);
        Self { r }
    }

    /// Splits this token into two `Right` tokens with the given fraction `n`, without giving the resource to the new token.
    pub proof fn split_without_resource(tracked &mut self, n: int) -> (tracked res: Self)
        requires
            0 < n < old(self).frac(),
        ensures
            final(self).id() == old(self).id(),
            res.id() == final(self).id(),
            final(self).frac() == old(self).frac() - n,
            res.frac() == n,
            !res.is_resource_owner(),
            final(self).is_resource_owner() <==> old(self).is_resource_owner(),
            final(self).is_resource_owner() ==> (final(self).has_resource() <==> old(
                self,
            ).has_resource()),
            final(self).has_resource() ==> final(self).resource() == old(self).resource(),
            final(self).wf(),
            res.wf(),
    {
        use_type_invariant(&*self);
        let tracked r = SumResource::split_right_without_resource_helper(&mut self.r, n);
        Self { r }
    }

    /// Updates the token with a new resource of type `B`, and returns the old resource if available.
    pub proof fn update(tracked &mut self, tracked b: B) -> (tracked res: Option<B>)
        requires
            old(self).is_resource_owner(),
        ensures
            final(self).id() == old(self).id(),
            final(self).is_resource_owner(),
            final(self).has_resource(),
            final(self).resource() == b,
            final(self).frac() == old(self).frac(),
            res == if old(self).has_resource() {
                Some(old(self).resource())
            } else {
                None
            },
            final(self).wf(),
    {
        use_type_invariant(&*self);
        let tracked mut res = None;
        if self.has_resource() {
            res = Some(self.take_resource());
        }
        self.put_resource(b);
        res
    }
}

impl<A, B, const TOTAL: u64> OneLeftOwner<A, B, TOTAL> {
    /// Returns the unique identifier.
    pub closed spec fn id(self) -> Loc {
        self.r.id()
    }

    /// The underlying protocol monoid value for this resource.
    pub closed spec fn protocol_monoid(self) -> SumSP<A, B, TOTAL> {
        self.r.protocol_monoid()
    }

    /// Returns the resource owned by this token.
    pub closed spec fn resource(self) -> A {
        self.r.resource()
    }

    /// Returns the fraction of this token, which should always be 1.
    pub closed spec fn frac(self) -> int {
        self.r.frac()
    }

    /// Whether this token currently has the resource stored.
    pub closed spec fn has_resource(self) -> bool {
        self.r.has_resource()
    }

    /// Whether the resource has been taken from this token.
    pub closed spec fn has_no_resource(self) -> bool {
        self.r.has_no_resource()
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.wf()
    }

    /// Type invariant.
    pub open spec fn wf(self) -> bool {
        &&& self.protocol_monoid().is_left()
        &&& self.protocol_monoid().is_valid()
        &&& self.protocol_monoid().is_resource_owner()
        &&& self.frac() == 1
        &&& TOTAL >= 1
        &&& self.has_resource() <==> !self.has_no_resource()
    }

    /// `OneLeftOwner` token satisfies the type invariant.
    pub proof fn validate(tracked &self)
        ensures
            self.wf(),
    {
        use_type_invariant(&*self);
    }

    /// The existence of two `OneLeftOwner` tokens ensures they can not have the same id.
    pub proof fn validate_with_one_left_owner(tracked &mut self, tracked other: &Self)
        ensures
            *old(self) == *final(self),
            final(self).id() != other.id(),
            final(self).wf(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        if self.id() == other.id() {
            self.r.validate_with_left(&other.r);
        }
    }

    /// Borrows the resource of type `A`.
    pub proof fn tracked_borrow(tracked &self) -> (tracked res: &A)
        requires
            self.has_resource(),
        ensures
            *res == self.resource(),
    {
        use_type_invariant(&*self);
        self.r.tracked_borrow()
    }

    /// Takes the resource out of the token.
    pub proof fn take_resource(tracked &mut self) -> (tracked res: A)
        requires
            old(self).has_resource(),
        ensures
            res == old(self).resource(),
            final(self).has_no_resource(),
            final(self).wf(),
    {
        use_type_invariant(&*self);
        self.r.take_resource()
    }

    /// Puts a resource of type `A` back to the token.
    pub proof fn put_resource(tracked &mut self, tracked a: A)
        requires
            old(self).has_no_resource(),
        ensures
            final(self).resource() == a,
            final(self).has_resource(),
            final(self).wf(),
    {
        use_type_invariant(&*self);
        self.r.put_resource(a);
    }

    /// Updates the resource of type `A` in the token, and returns the old resource if available.
    pub proof fn update(tracked &mut self, tracked a: A) -> (tracked res: Option<A>)
        ensures
            final(self).resource() == a,
            final(self).has_resource(),
            final(self).wf(),
            res == if old(self).has_resource() {
                Some(old(self).resource())
            } else {
                None
            },
    {
        use_type_invariant(&*self);
        self.r.update(a)
    }
}

impl<A, B, const TOTAL: u64> OneRightOwner<A, B, TOTAL> {
    /// Returns the unique identifier.
    pub closed spec fn id(self) -> Loc {
        self.r.id()
    }

    /// The underlying protocol monoid value for this resource.
    pub closed spec fn protocol_monoid(self) -> SumSP<A, B, TOTAL> {
        self.r.protocol_monoid()
    }

    /// Returns the resource owned by this token.
    pub closed spec fn resource(self) -> B {
        self.r.resource()
    }

    /// Returns the fraction of this token, which should always be 1.
    pub closed spec fn frac(self) -> int {
        self.r.frac()
    }

    /// Whether this token currently has the resource stored.
    pub closed spec fn has_resource(self) -> bool {
        self.r.has_resource()
    }

    /// Whether the resource has been taken from this token.
    pub closed spec fn has_no_resource(self) -> bool {
        self.r.has_no_resource()
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.wf()
    }

    /// Type invariant.
    pub open spec fn wf(self) -> bool {
        &&& self.protocol_monoid().is_right()
        &&& self.protocol_monoid().is_valid()
        &&& self.protocol_monoid().is_resource_owner()
        &&& self.frac() == 1
        &&& TOTAL >= 1
        &&& self.has_resource() <==> !self.has_no_resource()
    }

    /// `OneRightOwner` token satisfies the type invariant.
    pub proof fn validate(tracked &self)
        ensures
            self.wf(),
    {
        use_type_invariant(&*self);
    }

    /// The existence of two `OneRightOwner` tokens ensures they can not have the same id.
    pub proof fn validate_with_one_right_owner(tracked &mut self, tracked other: &Self)
        ensures
            *old(self) == *final(self),
            final(self).id() != other.id(),
            final(self).wf(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        if self.id() == other.id() {
            self.r.validate_with_right(&other.r);
        }
    }

    /// Borrows the resource of type `B`.
    pub proof fn tracked_borrow(tracked &self) -> (tracked res: &B)
        requires
            self.has_resource(),
        ensures
            *res == self.resource(),
    {
        use_type_invariant(&*self);
        self.r.tracked_borrow()
    }

    /// Takes the resource out of the token.
    pub proof fn take_resource(tracked &mut self) -> (tracked res: B)
        requires
            old(self).has_resource(),
        ensures
            res == old(self).resource(),
            final(self).has_no_resource(),
            final(self).wf(),
    {
        use_type_invariant(&*self);
        self.r.take_resource()
    }

    /// Puts a resource of type `B` back to the token.
    pub proof fn put_resource(tracked &mut self, tracked b: B)
        requires
            old(self).has_no_resource(),
        ensures
            final(self).resource() == b,
            final(self).has_resource(),
            final(self).wf(),
    {
        use_type_invariant(&*self);
        self.r.put_resource(b);
    }

    /// Updates the resource of type `B` in the token, and returns the old resource if available.
    pub proof fn update(tracked &mut self, tracked b: B) -> (tracked res: Option<B>)
        ensures
            final(self).resource() == b,
            final(self).has_resource(),
            final(self).wf(),
            res == if old(self).has_resource() {
                Some(old(self).resource())
            } else {
                None
            },
    {
        use_type_invariant(&*self);
        self.r.update(b)
    }
}

impl<A, B, const TOTAL: u64> OneLeftKnowledge<A, B, TOTAL> {
    /// Returns the unique identifier.
    pub closed spec fn id(self) -> Loc {
        self.r.id()
    }

    /// The underlying protocol monoid value for this resource.
    pub closed spec fn protocol_monoid(self) -> SumSP<A, B, TOTAL> {
        self.r.protocol_monoid()
    }

    /// Returns the fraction of this token, which should always be 1.
    pub closed spec fn frac(self) -> int {
        self.r.frac()
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.wf()
    }

    /// Type invariant.
    pub open spec fn wf(self) -> bool {
        &&& self.protocol_monoid().is_left()
        &&& self.protocol_monoid().is_valid()
        &&& !self.protocol_monoid().is_resource_owner()
        &&& self.frac() == 1
        &&& TOTAL >= 1
    }

    /// `OneLeftKnowledge` token satisfies the type invariant.
    pub proof fn validate(tracked &self)
        ensures
            self.wf(),
    {
        use_type_invariant(&*self);
    }

    /// The existence of `OneRightKnowledge` token ensures they can not have the same id.
    pub proof fn validate_with_one_right_knowledge(
        tracked &self,
        tracked other: &OneRightKnowledge<A, B, TOTAL>,
    )
        ensures
            self.id() != other.id(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        if self.id() == other.id() {
            self.r.validate_with_right(&other.r);
        }
    }

    /// The existence of `OneRightOwner` token ensures they can not have the same id.
    pub proof fn validate_with_one_right_owner(
        tracked &self,
        tracked other: &OneRightOwner<A, B, TOTAL>,
    )
        ensures
            self.id() != other.id(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        if self.id() == other.id() {
            self.r.validate_with_right(&other.r);
        }
    }
}

impl<A, B, const TOTAL: u64> OneRightKnowledge<A, B, TOTAL> {
    /// Returns the unique identifier.
    pub closed spec fn id(self) -> Loc {
        self.r.id()
    }

    /// The underlying protocol monoid value for this resource.
    pub closed spec fn protocol_monoid(self) -> SumSP<A, B, TOTAL> {
        self.r.protocol_monoid()
    }

    /// Returns the fraction of this token, which should always be 1.
    pub closed spec fn frac(self) -> int {
        self.r.frac()
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.wf()
    }

    /// Type invariant.
    pub open spec fn wf(self) -> bool {
        &&& self.protocol_monoid().is_right()
        &&& self.protocol_monoid().is_valid()
        &&& !self.protocol_monoid().is_resource_owner()
        &&& self.frac() == 1
        &&& TOTAL >= 1
    }

    /// `OneRightKnowledge` token satisfies the type invariant.
    pub proof fn validate(tracked &self)
        ensures
            self.wf(),
    {
        use_type_invariant(&*self);
    }

    /// The existence of `OneLeftKnowledge` token ensures they can not have the same id.
    pub proof fn validate_with_one_left_knowledge(
        tracked &self,
        tracked other: &OneLeftKnowledge<A, B, TOTAL>,
    )
        ensures
            self.id() != other.id(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        if self.id() == other.id() {
            self.r.validate_with_left(&other.r);
        }
    }

    /// The existence of `OneLeftOwner` token ensures they can not have the same id.
    pub proof fn validate_with_one_left_owner(
        tracked &self,
        tracked other: &OneLeftOwner<A, B, TOTAL>,
    )
        ensures
            self.id() != other.id(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        if self.id() == other.id() {
            self.r.validate_with_left(&other.r);
        }
    }
}

} // verus!
