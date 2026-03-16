//！ Sum types for ghost resources.
use vstd::prelude::*;
use vstd::pcm::Loc;
use vstd::storage_protocol::*;


use crate::resource::storage_protocol::csum::*;
use crate::sum::*;


verus! {

/// `SumResourceStorage` is a storage resource that stores either an A or a B, but not both.
pub tracked struct SumResourceStorage<A, B> {
    tracked r: StorageResource<(), Sum<A, B>, CsumP<A, B>>,
}

impl<A,B> SumResourceStorage<A, B>
{
    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    pub closed spec fn protocol_monoid(self) -> CsumP<A, B> {
        self.r.value()
    }

    pub open spec fn is_empty(self) -> bool {
        self.protocol_monoid() is Unit
    }

    pub open spec fn is_left(self) -> bool {
        self.protocol_monoid() is Cinl
    }

    pub open spec fn is_right(self) -> bool {
        self.protocol_monoid() is Cinr
    }
    
    pub open spec fn resource(self) -> Sum<A, B> {
        self.protocol_monoid().to_sum()
    }

    pub proof fn alloc_empty() -> (tracked res:Self)
    ensures
        res.is_empty(),
    {
        let tracked r = StorageResource::alloc(CsumP::Unit, Map::tracked_empty());
        SumResourceStorage { r }
    }

    pub proof fn alloc_left(tracked a: A) -> (tracked res: Self)
    ensures
        res.is_left(),
        res.resource() is Left,
        res.resource()->Left_0 == a,
    {
        let tracked mut m = Map::tracked_empty();
        m.tracked_insert((), Sum::Left(a));
        let tracked r = StorageResource::alloc(CsumP::Cinl(a), m);
        SumResourceStorage { r }
    }

    pub proof fn alloc_right(tracked b: B) -> (tracked res: Self)
    ensures
        res.is_right(),
        res.resource() is Right,
        res.resource()->Right_0 == b,
    {
        let tracked mut m = Map::tracked_empty();
        m.tracked_insert((), Sum::Right(b));
        let tracked r = StorageResource::alloc(CsumP::Cinr(b), m);
        SumResourceStorage { r }
    }

    pub proof fn tracked_take(tracked self) -> (tracked res: Sum<A, B>)
        requires
            self.is_left() || self.is_right(),
        ensures
            res == self.resource(),
    {
        self.protocol_monoid().lemma_csum_withdraws();
        let tracked r = self.r;
        let tracked (_,mut m) = r.withdraw(CsumP::Unit, map![() => self.protocol_monoid().to_sum()]);
        m.tracked_remove(())
    }

    pub proof fn tracked_take_left(tracked self) -> (tracked res: A)
        requires
            self.is_left(),
        ensures
            res == self.resource()->Left_0,
    {
        let tracked sum = self.tracked_take();
        sum.tracked_take_left()
    }

    pub proof fn tracked_take_right(tracked self) -> (tracked res: B)
        requires
            self.is_right(),
        ensures
            res == self.resource()->Right_0,
    {
        let tracked sum = self.tracked_take();
        sum.tracked_take_right()
    }

    pub proof fn tracked_borrow(tracked &self) -> (tracked res: &Sum<A, B>)
        requires
            self.is_left() || self.is_right(),
        ensures
            *res == self.resource(),
    {
        StorageResource::guard(&self.r, map![() => self.resource()]).tracked_borrow(())
    }

    pub proof fn tracked_borrow_left(tracked &self) -> (tracked res: &A)
        requires
            self.is_left(),
        ensures
            *res == self.resource()->Left_0,
    {
        self.tracked_borrow().tracked_borrow_left()
    }

    pub proof fn tracked_borrow_right(tracked &self) -> (tracked res: &B)
        requires
            self.is_right(),
        ensures
            *res == self.resource()->Right_0,
    {
        self.tracked_borrow().tracked_borrow_right()  
    }

}

} // verus!
