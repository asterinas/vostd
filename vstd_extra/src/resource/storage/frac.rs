//! This module defines the real-based fractional permissions storage protocol.
//!
//! - `FracS` defines the basic fractional protocol monoid.
//! - `FracStorage` define the actual storage resource that can be split
//! into arbitrary finite pieces for shared read access, it can be seen
//! as a real-based re-implemetation of `FracGhost`(https://verus-lang.github.io/verus/verusdoc/vstd/tokens/frac/struct.FracGhost.html).
use crate::ownership::Inv;
use vstd::map::*;
use vstd::pcm::Loc;
use vstd::prelude::*;
use vstd::storage_protocol::*;

verus! {

broadcast use group_map_axioms;

/// The fractional protocol monoid
#[verifier::ext_equal]
pub tracked enum FracS<T> {
    Unit,
    Frac(real, T),
    Invalid,
}

impl <T> Protocol<(),T> for FracS<T> {
    open spec fn op(self,other: Self) -> Self {
        match (self,other) {
            (FracS::Unit, x) => x,
            (x, FracS::Unit) => x,
            (FracS::Frac(q1, v1), FracS::Frac(q2, v2)) => {
                if v1 == v2 && 0.0real < q1 && 0.0real < q2 && q1 + q2 <= 1.0real {
                    FracS::Frac(q1 + q2, v1)
                } else {
                    FracS::Invalid
                }
            }
            _ => FracS::Invalid,
        }
    }

    open spec fn rel(self, s:Map<(),T>) -> bool {
        match self {
            FracS::Frac(q, v) => {
                &&& s.contains_key(())
                &&& s[()] == v
                &&& q == 1.0real
            }
            _ => false,
        }
    }

    open spec fn unit() -> Self {
        FracS::Unit
    }

    proof fn commutative(a: Self, b: Self){
    }

    proof fn associative(a: Self, b: Self, c: Self){
    }

    proof fn op_unit(a: Self){
    }
}

impl<T> FracS<T> {
    pub open spec fn frac(self) -> real {
        match self {
            FracS::Frac(q, _) => q,
            _ => 0.0real,
        }
    }

    pub open spec fn new(v:T) -> Self
    {
        FracS::Frac(1.0real, v)
    }

    pub open spec fn construct_frac(q:real, v:T) -> Self
    {
        FracS::Frac(q, v)
    }

    pub open spec fn value(self) -> T
    recommends
        self is Frac,
    {
        match self {
            FracS::Frac(_, v) => v,
            _ => arbitrary()
        }
    }

    pub proof fn lemma_guards(self)
    requires
        self is Frac,
    ensures
        guards::<(),T,Self>(self,map![() => self.value()]),
    {
    }
}

/// The authoritative fractional storage resource.
pub tracked struct FracStorage<T> {
    resource: Option<StorageResource<(), T, FracS<T>>>,
}

impl<T> Inv for FracStorage<T> {
    closed spec fn inv(self) -> bool {
        &&& self.resource is Some
        &&& self.protocol_monoid() is Frac
        &&& 0.0real < self.frac() && self.frac() <= 1.0real}
    }

impl<T> FracStorage<T> {
    pub closed spec fn resource(self) -> StorageResource<(), T, FracS<T>> {
        self.resource -> Some_0
    }

    pub closed spec fn id(self) -> Loc{
        self.resource().loc()
    }

    pub closed spec fn protocol_monoid(self) -> FracS<T> {
        self.resource().value()
    }

    pub open spec fn value(self) -> T {
        self.protocol_monoid().value()
    }

    pub closed spec fn frac(self) -> real {
        self.protocol_monoid().frac()
    }

    pub open spec fn has_full_frac(self) -> bool {
        self.frac() == 1.0real
    }

    pub open spec fn match_ref(self, r: FracStorage<T>) -> bool {
        &&& self.id() == r.id()
        &&& self.value() == r.value()
    }

    /// Allocate a new fractional storage resource with full permission.
    pub proof fn alloc(tracked v:T) -> (tracked res: Self)
    ensures
        res.inv(),
        res.has_full_frac(),
    {
        let tracked mut m = Map::<(),T>::tracked_empty();
        m.tracked_insert((), v);
        let tracked resource = StorageResource::alloc(FracS::new(v), m);
        FracStorage { resource: Some(resource) }
    }

    /// Split the fractional storage resource into two fractions.
    pub proof fn split(tracked &mut self) -> (tracked r: FracStorage<T>)
    requires
        old(self).inv(),
    ensures
        self.inv(),
        true,
    {
        let frac = self.frac();
        let half_frac = frac / 2.0real;
        let m = FracS::construct_frac(half_frac, self.value());
        let tracked resource = self.resource.tracked_take();
        let tracked (resource_1, resource_2) = resource.split(m,m);
        self.resource = Some(resource_1);
        FracStorage { resource: Some(resource_2) }
    }

    pub proof fn lemma_guards(self)
    requires
        self.inv(),
    ensures
        guards::<(),T,FracS<T>>(self.protocol_monoid(),map![() => self.value()]),
    {
        self.protocol_monoid().lemma_guards();
    }

    /// Borrowing the ghost resource from the fractional reference.
    pub proof fn tracked_borrow(tracked &self) -> (tracked s: &T)
    requires
        self.inv(),
    ensures
        *s == self.value(),
    {
        let m = Map::<(),T>::empty().insert((), self.value());
        self.lemma_guards();
        let tracked resource = StorageResource::guard(self.resource.tracked_borrow(), m);
        resource.tracked_borrow(())
    }
}

}
