use std::f32::consts::E;

use vstd::modes::tracked_swap;
//！ Sum types for ghost resources.
use vstd::pcm::Loc;
use vstd::prelude::*;
use vstd::storage_protocol::*;

use crate::resource::storage_protocol::csum::*;
use crate::sum::*;

verus! {

/// `SumResource` is a token that maintains access to a resource of either type `A` or type `B`.
/// It can be split into up to `TOTAL` fractions, one of which have the exclusive right to access the resource,
/// and others shares the knowledge of the resource's existence and type, but not the ability to access it.
pub tracked struct SumResource<A, B, const TOTAL: u64 = 2> {
    tracked r: StorageResource<(), Sum<A, B>, CsumP<A, B, TOTAL>>,
}

/// `Left` ensures the resource is of type `A`.
pub tracked struct Left<A, B, const TOTAL: u64 = 2> {
    tracked r: StorageResource<(), Sum<A, B>, CsumP<A, B, TOTAL>>,
}

/// `Right` ensures the resource is of type `B`.
pub tracked struct Right<A, B, const TOTAL: u64 = 2> {
    tracked r: StorageResource<(), Sum<A, B>, CsumP<A, B, TOTAL>>,
}

impl<A, B, const TOTAL: u64> SumResource<A, B, TOTAL> {
    /// Returns the unique identifier.
    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    /// The underlying protocol monoid value for this resource.
    pub closed spec fn protocol_monoid(self) -> CsumP<A, B, TOTAL> {
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

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.wf()
    }

    /// Type invariant.
    pub open spec fn wf(self) -> bool {
        &&& 1 <= self.frac() <= TOTAL
        &&& self.protocol_monoid().is_valid()
        &&& self.is_resource_owner() ==> (self.has_resource() || self.has_no_resource())
        &&& self.is_left() || self.is_right()
    }

    closed spec fn type_inv_inner(r: CsumP<A, B, TOTAL>) -> bool {
        &&& 1 <= r.frac() <= TOTAL
        &&& r.is_valid()
        &&& r.is_resource_owner() ==> (r.has_resource() || r.has_no_resource())
        &&& r.is_left() || r.is_right()
    }

    proof fn alloc_unit_storage() -> (tracked res: StorageResource<
        (),
        Sum<A, B>,
        CsumP<A, B, TOTAL>,
    >) {
        StorageResource::alloc(CsumP::Unit, Map::tracked_empty())
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
        let tracked r = StorageResource::alloc(CsumP::Cinl(Some(a), TOTAL as int, true), m);
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
        let tracked r = StorageResource::alloc(CsumP::Cinr(Some(b), TOTAL as int, true), m);
        Self { r }
    }

    /// Every `SumResource` satisfies the well-formedness invariant.
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
            *old(self) == *self,
            self.id() != other.id(),
            self.wf(),
            other.wf(),
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
            *old(self) == *self,
            self.is_left(),
            !(self.is_resource_owner() && other.is_resource_owner()),
            self.frac() + other.frac() <= TOTAL,
            self.wf(),
            other.wf(),
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
            *old(self) == *self,
            self.is_right(),
            !(self.is_resource_owner() && other.is_resource_owner()),
            self.frac() + other.frac() <= TOTAL,
            self.wf(),
            other.wf(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.r.validate_with_shared(&other.r);
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
            self.id() == old(self).id(),
            self.frac() == old(self).frac() - n,
            res.id() == old(self).id(),
            res.frac() == n,
            !self.is_resource_owner(),
            res.is_resource_owner() <==> old(self).is_resource_owner(),
            res.is_resource_owner() ==> (res.has_resource() <==> old(self).has_resource()),
            res.has_resource() ==> res.resource() == old(self).resource_left(),
            self.wf(),
            res.wf(),
    {
        use_type_invariant(&*self);
        let tracked r = Self::split_left_with_resource_helper(&mut self.r, n);
        Left { r }
    }

    proof fn split_left_with_resource_helper(
        tracked r: &mut StorageResource<(), Sum<A, B>, CsumP<A, B, TOTAL>>,
        n: int,
    ) -> (tracked res: StorageResource<(), Sum<A, B>, CsumP<A, B, TOTAL>>)
        requires
            old(r).value().is_left(),
            0 < n < old(r).value().frac(),
            Self::type_inv_inner(old(r).value()),
        ensures
            Self::type_inv_inner(r.value()),
            Self::type_inv_inner(res.value()),
            r.loc() == old(r).loc(),
            r.loc() == res.loc(),
            r.value().is_left(),
            r.value().frac() == old(r).value().frac() - n,
            res.value().is_left(),
            res.value().frac() == n,
            !r.value().is_resource_owner(),
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
            CsumP::Cinl(None, tmp.value().frac() - n, false),
            CsumP::Cinl(tmp.value()->Cinl_0, n, tmp.value().is_resource_owner()),
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
            self.id() == old(self).id(),
            self.frac() == old(self).frac() - n,
            res.id() == old(self).id(),
            res.frac() == n,
            !res.is_resource_owner(),
            self.is_resource_owner() <==> old(self).is_resource_owner(),
            self.is_resource_owner() ==> (self.has_resource() <==> old(self).has_resource()),
            self.has_resource() ==> self.resource() == old(self).resource(),
            self.wf(),
            res.wf(),
    {
        use_type_invariant(&*self);
        let tracked r = Self::split_left_without_resource_helper(&mut self.r, n);
        Left { r }
    }

    proof fn split_left_without_resource_helper(
        tracked r: &mut StorageResource<(), Sum<A, B>, CsumP<A, B, TOTAL>>,
        n: int,
    ) -> (tracked res: StorageResource<(), Sum<A, B>, CsumP<A, B, TOTAL>>)
        requires
            old(r).value().is_left(),
            0 < n < old(r).value().frac(),
            Self::type_inv_inner(old(r).value()),
        ensures
            Self::type_inv_inner(r.value()),
            Self::type_inv_inner(res.value()),
            r.loc() == old(r).loc(),
            r.loc() == res.loc(),
            r.value().is_left(),
            r.value().frac() == old(r).value().frac() - n,
            res.value().is_left(),
            res.value().frac() == n,
            !res.value().is_resource_owner(),
            r.value().is_resource_owner() <==> old(r).value().is_resource_owner(),
            r.value().is_resource_owner() ==> (r.value().has_resource() <==> old(
                r,
            ).value().has_resource()),
            r.value().has_resource() ==> r.value().resource()->Left_0 == old(
                r,
            ).value().resource()->Left_0,
    {
        let tracked mut tmp = Self::alloc_unit_storage();
        tracked_swap(r, &mut tmp);
        let tracked (mut r1, r2) = tmp.split(
            CsumP::Cinl(
                tmp.value()->Cinl_0,
                tmp.value().frac() - n,
                tmp.value().is_resource_owner(),
            ),
            CsumP::Cinl(None, n, false),
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
            self.id() == old(self).id(),
            self.frac() == old(self).frac() - n,
            res.id() == old(self).id(),
            res.frac() == n,
            !self.is_resource_owner(),
            res.is_resource_owner() <==> old(self).is_resource_owner(),
            res.is_resource_owner() ==> (res.has_resource() <==> old(self).has_resource()),
            res.has_resource() ==> res.resource() == old(self).resource_right(),
            self.wf(),
            res.wf(),
    {
        use_type_invariant(&*self);
        let tracked r = Self::split_right_with_resource_helper(&mut self.r, n);
        Right { r }
    }

    proof fn split_right_with_resource_helper(
        tracked r: &mut StorageResource<(), Sum<A, B>, CsumP<A, B, TOTAL>>,
        n: int,
    ) -> (tracked res: StorageResource<(), Sum<A, B>, CsumP<A, B, TOTAL>>)
        requires
            old(r).value().is_right(),
            0 < n < old(r).value().frac(),
            Self::type_inv_inner(old(r).value()),
        ensures
            Self::type_inv_inner(r.value()),
            Self::type_inv_inner(res.value()),
            r.loc() == old(r).loc(),
            r.loc() == res.loc(),
            r.value().is_right(),
            r.value().frac() == old(r).value().frac() - n,
            res.value().is_right(),
            res.value().frac() == n,
            !r.value().is_resource_owner(),
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
            CsumP::Cinr(None, tmp.value().frac() - n, false),
            CsumP::Cinr(tmp.value()->Cinr_0, n, tmp.value().is_resource_owner()),
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
            self.id() == old(self).id(),
            self.frac() == old(self).frac() - n,
            res.id() == old(self).id(),
            res.frac() == n,
            !res.is_resource_owner(),
            self.is_resource_owner() <==> old(self).is_resource_owner(),
            self.is_resource_owner() ==> (self.has_resource() <==> old(self).has_resource()),
            self.has_resource() ==> self.resource() == old(self).resource(),
            self.wf(),
            res.wf(),
    {
        use_type_invariant(&*self);
        let tracked r = Self::split_right_without_resource_helper(&mut self.r, n);
        Right { r }
    }

    proof fn split_right_without_resource_helper(
        tracked r: &mut StorageResource<(), Sum<A, B>, CsumP<A, B, TOTAL>>,
        n: int,
    ) -> (tracked res: StorageResource<(), Sum<A, B>, CsumP<A, B, TOTAL>>)
        requires
            old(r).value().is_right(),
            0 < n < old(r).value().frac(),
            Self::type_inv_inner(old(r).value()),
        ensures
            Self::type_inv_inner(r.value()),
            Self::type_inv_inner(res.value()),
            r.loc() == old(r).loc(),
            r.loc() == res.loc(),
            r.value().is_right(),
            r.value().frac() == old(r).value().frac() - n,
            res.value().is_right(),
            res.value().frac() == n,
            !res.value().is_resource_owner(),
            r.value().is_resource_owner() <==> old(r).value().is_resource_owner(),
            r.value().is_resource_owner() ==> (r.value().has_resource() <==> old(
                r,
            ).value().has_resource()),
            r.value().has_resource() ==> r.value().resource()->Right_0 == old(
                r,
            ).value().resource()->Right_0,
    {
        let tracked mut tmp = Self::alloc_unit_storage();
        tracked_swap(r, &mut tmp);
        let tracked (mut r1, r2) = tmp.split(
            CsumP::Cinr(
                tmp.value()->Cinr_0,
                tmp.value().frac() - n,
                tmp.value().is_resource_owner(),
            ),
            CsumP::Cinr(None, n, false),
        );
        tracked_swap(r, &mut r1);
        r2
    }

    /// Takes the resource out of the token if it is in the left variant.
    pub proof fn take_resource_left(tracked &mut self) -> (tracked res: A)
        requires
            old(self).is_left(),
            old(self).is_resource_owner(),
            old(self).has_resource(),
        ensures
            self.is_left(),
            res == old(self).resource_left(),
            self.id() == old(self).id(),
            self.is_resource_owner(),
            self.has_no_resource(),
            self.frac() == old(self).frac(),
            self.wf(),
    {
        use_type_invariant(&*self);
        Self::take_resource_left_helper(&mut self.r)
    }

    proof fn take_resource_left_helper(
        tracked r: &mut StorageResource<(), Sum<A, B>, CsumP<A, B, TOTAL>>,
    ) -> (tracked res: A)
        requires
            old(r).value().is_left(),
            old(r).value().is_resource_owner(),
            old(r).value().has_resource(),
            Self::type_inv_inner(old(r).value()),
        ensures
            Self::type_inv_inner(r.value()),
            res == old(r).value().resource()->Left_0,
            r.loc() == old(r).loc(),
            r.value().is_left(),
            r.value().is_resource_owner(),
            r.value().has_no_resource(),
            r.value().frac() == old(r).value().frac(),
    {
        let tracked mut tmp = Self::alloc_unit_storage();
        tracked_swap(r, &mut tmp);
        tmp.value().lemma_withdraws_left();
        let tracked (mut r1, mut s) = tmp.withdraw(
            CsumP::Cinl(None, tmp.value().frac(), true),
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
            self.is_right(),
            res == old(self).resource_right(),
            self.id() == old(self).id(),
            self.is_resource_owner(),
            self.has_no_resource(),
            self.frac() == old(self).frac(),
            self.wf(),
    {
        use_type_invariant(&*self);
        Self::take_resource_right_helper(&mut self.r)
    }

    proof fn take_resource_right_helper(
        tracked r: &mut StorageResource<(), Sum<A, B>, CsumP<A, B, TOTAL>>,
    ) -> (tracked res: B)
        requires
            old(r).value().is_right(),
            old(r).value().is_resource_owner(),
            old(r).value().has_resource(),
            Self::type_inv_inner(old(r).value()),
        ensures
            Self::type_inv_inner(r.value()),
            res == old(r).value().resource()->Right_0,
            r.loc() == old(r).loc(),
            r.value().is_right(),
            r.value().is_resource_owner(),
            r.value().has_no_resource(),
            r.value().frac() == old(r).value().frac(),
    {
        let tracked mut tmp = Self::alloc_unit_storage();
        tracked_swap(r, &mut tmp);
        tmp.value().lemma_withdraws_right();
        let tracked (mut r1, mut s) = tmp.withdraw(
            CsumP::Cinr(None, tmp.value().frac(), true),
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
            self.is_left(),
            self.has_resource(),
            self.is_resource_owner(),
            self.resource_left() == a,
            self.id() == old(self).id(),
            self.frac() == old(self).frac(),
            self.wf(),
    {
        use_type_invariant(&*self);
        Self::put_resource_left_helper(&mut self.r, a);
    }

    proof fn put_resource_left_helper(
        tracked r: &mut StorageResource<(), Sum<A, B>, CsumP<A, B, TOTAL>>,
        tracked a: A,
    )
        requires
            old(r).value().is_left(),
            old(r).value().is_resource_owner(),
            old(r).value().has_no_resource(),
            Self::type_inv_inner(old(r).value()),
        ensures
            Self::type_inv_inner(r.value()),
            r.loc() == old(r).loc(),
            r.value().is_left(),
            r.value().is_resource_owner(),
            r.value().has_resource(),
            r.value().resource()->Left_0 == a,
            r.value().frac() == old(r).value().frac(),
    {
        let ghost a_ghost = a;
        let tracked mut m = Map::tracked_empty();
        m.tracked_insert((), Sum::<A, B>::Left(a));
        let tracked mut tmp = Self::alloc_unit_storage();
        tracked_swap(r, &mut tmp);
        tmp.value().lemma_deposit_left(a);
        let tracked mut r1 = tmp.deposit(m, CsumP::Cinl(Some(a), tmp.value().frac(), true));
        tracked_swap(r, &mut r1);
    }

    /// Puts a resource of type `B` back to the token.
    pub proof fn put_resource_right(tracked &mut self, tracked b: B)
        requires
            old(self).is_right(),
            old(self).is_resource_owner(),
            old(self).has_no_resource(),
        ensures
            self.is_right(),
            self.is_resource_owner(),
            self.has_resource(),
            self.resource_right() == b,
            self.id() == old(self).id(),
            self.frac() == old(self).frac(),
            self.wf(),
    {
        use_type_invariant(&*self);
        Self::put_resource_right_helper(&mut self.r, b);
    }

    proof fn put_resource_right_helper(
        tracked r: &mut StorageResource<(), Sum<A, B>, CsumP<A, B, TOTAL>>,
        tracked b: B,
    )
        requires
            old(r).value().is_right(),
            old(r).value().is_resource_owner(),
            old(r).value().has_no_resource(),
            Self::type_inv_inner(old(r).value()),
        ensures
            Self::type_inv_inner(r.value()),
            r.loc() == old(r).loc(),
            r.value().is_right(),
            r.value().is_resource_owner(),
            r.value().has_resource(),
            r.value().resource()->Right_0 == b,
            r.value().frac() == old(r).value().frac(),
    {
        let ghost b_ghost = b;
        let tracked mut m = Map::tracked_empty();
        m.tracked_insert((), Sum::<A, B>::Right(b));
        let tracked mut tmp = Self::alloc_unit_storage();
        tracked_swap(r, &mut tmp);
        tmp.value().lemma_deposit_right(b);
        let tracked mut r1 = tmp.deposit(m, CsumP::Cinr(Some(b), tmp.value().frac(), true));
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
            self.is_left(),
            self.is_resource_owner(),
            self.has_resource(),
            self.resource_left() == a,
            self.id() == old(self).id(),
            self.frac() == old(self).frac(),
            res == Some(old(self).resource_left()),
            self.wf(),
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
            self.is_right(),
            self.is_resource_owner(),
            self.has_resource(),
            self.resource_right() == b,
            self.id() == old(self).id(),
            self.frac() == old(self).frac(),
            res == Some(old(self).resource_right()),
            self.wf(),
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
            self.id() == old(self).id(),
            self.protocol_monoid() == CsumP::<A, B, TOTAL>::Cinl(Some(a), old(self).frac(), true),
            self.frac() == old(self).frac(),
            self.is_left(),
            self.is_resource_owner(),
            self.has_resource(),
            self.resource_left() == a,
            old(self).has_resource() ==> res == Some(old(self).resource()),
            old(self).has_no_resource() ==> res == None::<Sum<A, B>>,
            self.wf(),
    {
        use_type_invariant(&*self);
        let tracked res = Self::change_to_left_helper(&mut self.r, a);
        res
    }

    proof fn change_to_left_helper(
        tracked r: &mut StorageResource<(), Sum<A, B>, CsumP<A, B, TOTAL>>,
        tracked a: A,
    ) -> (tracked res: Option<Sum<A, B>>)
        requires
            old(r).value().is_resource_owner(),
            old(r).value().frac() == TOTAL,
            Self::type_inv_inner(old(r).value()),
        ensures
            Self::type_inv_inner(r.value()),
            r.loc() == old(r).loc(),
            r.value() == CsumP::<A, B, TOTAL>::Cinl(Some(a), old(r).value().frac(), true),
            r.value().frac() == old(r).value().frac(),
            r.value().is_left(),
            r.value().is_resource_owner(),
            r.value().has_resource(),
            r.value().resource()->Left_0 == a,
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
            CsumP::<A, B, TOTAL>::Cinl(None, tmp.value().frac(), true),
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
            self.id() == old(self).id(),
            self.protocol_monoid() == CsumP::<A, B, TOTAL>::Cinr(Some(b), old(self).frac(), true),
            self.frac() == old(self).frac(),
            self.is_right(),
            self.is_resource_owner(),
            self.has_resource(),
            self.resource_right() == b,
            old(self).has_resource() ==> res == Some(old(self).resource()),
            old(self).has_no_resource() ==> res == None::<Sum<A, B>>,
            self.wf(),
    {
        use_type_invariant(&*self);
        let tracked res = Self::change_to_right_helper(&mut self.r, b);
        res
    }

    proof fn change_to_right_helper(
        tracked r: &mut StorageResource<(), Sum<A, B>, CsumP<A, B, TOTAL>>,
        tracked b: B,
    ) -> (tracked res: Option<Sum<A, B>>)
        requires
            old(r).value().is_resource_owner(),
            old(r).value().frac() == TOTAL,
            Self::type_inv_inner(old(r).value()),
        ensures
            Self::type_inv_inner(r.value()),
            r.loc() == old(r).loc(),
            r.value() == CsumP::<A, B, TOTAL>::Cinr(Some(b), old(r).value().frac(), true),
            r.value().frac() == old(r).value().frac(),
            r.value().is_right(),
            r.value().is_resource_owner(),
            r.value().has_resource(),
            r.value().resource()->Right_0 == b,
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
            CsumP::<A, B, TOTAL>::Cinr(None, tmp.value().frac(), true),
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
            self.id() == old(self).id(),
            self.is_left(),
            self.is_resource_owner() == old(self).is_resource_owner() || other.is_resource_owner(),
            self.has_resource() == old(self).has_resource() || other.has_resource(),
            self.has_resource() ==> self.resource() == if old(self).has_resource() {
                old(self).resource()
            } else {
                Sum::Left(other.resource())
            },
            self.frac() == old(self).frac() + other.frac(),
            self.wf(),
    {
        use_type_invariant(&*self);
        use_type_invariant(&other);
        Self::join_left_helper(&mut self.r, other.r);
    }

    proof fn join_left_helper(
        tracked r: &mut StorageResource<(), Sum<A, B>, CsumP<A, B, TOTAL>>,
        tracked other: StorageResource<(), Sum<A, B>, CsumP<A, B, TOTAL>>,
    )
        requires
            Self::type_inv_inner(old(r).value()),
            Self::type_inv_inner(other.value()),
            old(r).loc() == other.loc(),
            other.value().is_left(),
        ensures
            Self::type_inv_inner(r.value()),
            r.loc() == old(r).loc(),
            r.value().is_left(),
            r.value().frac() == old(r).value().frac() + other.value().frac(),
            r.value().is_resource_owner() == old(r).value().is_resource_owner()
                || other.value().is_resource_owner(),
            r.value().has_resource() == old(r).value().has_resource()
                || other.value().has_resource(),
            r.value().has_resource() ==> r.value().resource() == if old(r).value().has_resource() {
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
            self.id() == old(self).id(),
            self.is_right(),
            self.is_resource_owner() == old(self).is_resource_owner() || other.is_resource_owner(),
            self.has_resource() == old(self).has_resource() || other.has_resource(),
            self.has_resource() ==> self.resource() == if old(self).has_resource() {
                old(self).resource()
            } else {
                Sum::Right(other.resource())
            },
            self.frac() == old(self).frac() + other.frac(),
            self.wf(),
    {
        use_type_invariant(&*self);
        use_type_invariant(&other);
        Self::join_right_helper(&mut self.r, other.r);
    }

    proof fn join_right_helper(
        tracked r: &mut StorageResource<(), Sum<A, B>, CsumP<A, B, TOTAL>>,
        tracked other: StorageResource<(), Sum<A, B>, CsumP<A, B, TOTAL>>,
    )
        requires
            Self::type_inv_inner(old(r).value()),
            Self::type_inv_inner(other.value()),
            old(r).loc() == other.loc(),
            other.value().is_right(),
        ensures
            Self::type_inv_inner(r.value()),
            r.loc() == old(r).loc(),
            r.value().is_right(),
            r.value().frac() == old(r).value().frac() + other.value().frac(),
            r.value().is_resource_owner() == old(r).value().is_resource_owner()
                || other.value().is_resource_owner(),
            r.value().has_resource() == old(r).value().has_resource()
                || other.value().has_resource(),
            r.value().has_resource() ==> r.value().resource() == if old(r).value().has_resource() {
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
}

impl<A, B, const TOTAL: u64> Left<A, B, TOTAL> {
    /// Returns the unique identifier.
    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    /// The underlying protocol monoid value for this resource.
    pub closed spec fn protocol_monoid(self) -> CsumP<A, B, TOTAL> {
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
        &&& self.is_resource_owner() ==> (self.has_resource() || self.has_no_resource())
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

    /// Every `Left` token should satisfy the type invariant.
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
            *old(self) == *self,
            !(self.is_resource_owner() && other.is_resource_owner()),
            self.frac() + other.frac() <= TOTAL,
            self.wf(),
            other.wf(),
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
            self.id() == old(self).id(),
            res == old(self).resource(),
            self.is_resource_owner(),
            self.has_no_resource(),
            self.frac() == old(self).frac(),
            self.wf(),
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
            self.id() == old(self).id(),
            self.protocol_monoid() == CsumP::<A, B, TOTAL>::Cinl(Some(a), self.frac(), true),
            self.is_resource_owner(),
            self.has_resource(),
            self.resource() == a,
            self.wf(),
    {
        use_type_invariant(&*self);
        SumResource::put_resource_left_helper(&mut self.r, a);
    }

    /// Splits this token into two `Left` tokens with the given fraction `n`, given the resource to the new token if available.
    pub proof fn split_with_resource(tracked &mut self, n: int) -> (tracked res: Self)
        requires
            0 < n < old(self).frac(),
        ensures
            self.id() == old(self).id(),
            res.id() == self.id(),
            self.frac() == old(self).frac() - n,
            res.frac() == n,
            !self.is_resource_owner(),
            res.is_resource_owner() <==> old(self).is_resource_owner(),
            res.is_resource_owner() ==> (res.has_resource() <==> old(self).has_resource()),
            res.has_resource() ==> res.resource() == old(self).resource(),
            self.wf(),
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
            self.id() == old(self).id(),
            res.id() == self.id(),
            self.frac() == old(self).frac() - n,
            res.frac() == n,
            !res.is_resource_owner(),
            self.is_resource_owner() <==> old(self).is_resource_owner(),
            self.is_resource_owner() ==> (self.has_resource() <==> old(self).has_resource()),
            self.has_resource() ==> self.resource() == old(self).resource(),
            self.wf(),
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
            self.id() == old(self).id(),
            self.is_resource_owner(),
            self.has_resource(),
            self.resource() == a,
            res == if old(self).has_resource() {
                Some(old(self).resource())
            } else {
                None
            },
            self.wf(),
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
    pub closed spec fn protocol_monoid(self) -> CsumP<A, B, TOTAL> {
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
        &&& self.is_resource_owner() ==> (self.has_resource() || self.has_no_resource())
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

    /// Validates the internal consistency of this resource token.
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
            *old(self) == *self,
            !(self.is_resource_owner() && other.is_resource_owner()),
            self.frac() + other.frac() <= TOTAL,
            self.wf(),
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
            self.id() == old(self).id(),
            res == old(self).resource(),
            self.is_resource_owner(),
            self.has_no_resource(),
            self.frac() == old(self).frac(),
            self.wf(),
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
            self.id() == old(self).id(),
            self.protocol_monoid() == CsumP::<A, B, TOTAL>::Cinr(Some(b), self.frac(), true),
            self.is_resource_owner(),
            self.has_resource(),
            self.resource() == b,
            self.wf(),
    {
        use_type_invariant(&*self);
        SumResource::put_resource_right_helper(&mut self.r, b);
    }

    /// Splits this token into two `Right` tokens with the given fraction `n`, given the resource to the new token if available.
    pub proof fn split_with_resource(tracked &mut self, n: int) -> (tracked res: Self)
        requires
            0 < n < old(self).frac(),
        ensures
            self.id() == old(self).id(),
            res.id() == self.id(),
            self.frac() == old(self).frac() - n,
            res.frac() == n,
            !self.is_resource_owner(),
            res.is_resource_owner() <==> old(self).is_resource_owner(),
            res.is_resource_owner() ==> (res.has_resource() <==> old(self).has_resource()),
            res.has_resource() ==> res.resource() == old(self).resource(),
            self.wf(),
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
            self.id() == old(self).id(),
            res.id() == self.id(),
            self.frac() == old(self).frac() - n,
            res.frac() == n,
            !res.is_resource_owner(),
            self.is_resource_owner() <==> old(self).is_resource_owner(),
            self.is_resource_owner() ==> (self.has_resource() <==> old(self).has_resource()),
            self.has_resource() ==> self.resource() == old(self).resource(),
            self.wf(),
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
            self.id() == old(self).id(),
            self.is_resource_owner(),
            self.has_resource(),
            self.resource() == b,
            res == if old(self).has_resource() {
                Some(old(self).resource())
            } else {
                None
            },
            self.wf(),
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

} // verus!
