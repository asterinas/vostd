//! This module defines the real-based fractional permissions storage protocol.
//! 
//! - `FracS` defines the basic fractional protocol monoid.
//! - `FracStorage` and `FracStorageRef` define the actual storage resource that 
//! can be split into fractional references for shared read access.
use vstd::prelude::*;
use vstd::pcm::Loc;
use vstd::storage_protocol::*;

verus!{

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
    pub open spec fn frac_val(self) -> real {
        match self {
            FracS::Frac(q, _) => q,
            _ => 0.0real,
        }
    }

    pub open spec fn new(v:T) -> Self
    {
        FracS::Frac(1.0real, v)
    }
}

/// The authoritative fractional storage resource, who counts how many references exist.
pub tracked struct FracStorage<T> {
    ref_nums: nat,
    r: StorageResource<(), T, FracS<T>>,
}

/// A fractional storage resource reference.
pub tracked struct FracStorageRef<T> {
    r: StorageResource<(), T, FracS<T>>,
}

impl<T> FracStorage<T> {
    #[verifier::type_invariant]
    spec fn type_inv(self) -> bool {
        &&& self.protocol_monoid() is Frac
        &&& if self.ref_nums == 0 {self.has_full_frac()} else {0.0real < self.frac_val() && self.frac_val() < 1.0real}
    }
    pub closed spec fn id(self) -> Loc{
        self.r.loc()
    }

    pub closed spec fn protocol_monoid(self) -> FracS<T> {
        self.r.value()
    }

    pub closed spec fn frac_val(self) -> real {
        self.protocol_monoid().frac_val()
    }
    
    pub open spec fn has_full_frac(self) -> bool {
        self.frac_val() == 1.0real
    }

    pub closed spec fn ref_nums(self) -> nat {
        self.ref_nums
    }

    pub open spec fn match_ref(self, r: FracStorageRef<T>) -> bool {
        self.id() == r.id()
    }
    
    /// Allocate a new fractional storage resource with full permission.
    pub proof fn alloc(tracked v:T) -> (tracked res: Self)
    ensures
        res.has_full_frac(),
    {
        let tracked mut m = Map::<(),T>::tracked_empty();
        m.tracked_insert((), v);
        let tracked r = StorageResource::alloc(FracS::new(v), m);
        FracStorage { ref_nums:0, r }
    }

    /// Create a fractional reference from the authoritative storage.
    #[verifier::external_body]
    pub proof fn create_ref(tracked &mut self) -> (tracked r: FracStorageRef<T>){
        unimplemented!()
    }
}

impl<T> FracStorageRef<T> {
    #[verifier::type_invariant]
    spec fn type_inv(self) -> bool {
        &&& self.protocol_monoid() is Frac
        &&& 0.0real < self.frac_val() && self.frac_val() < 1.0real
    }

    pub closed spec fn id(self) -> Loc{
        self.r.loc()
    }

    pub closed spec fn protocol_monoid(self) -> FracS<T> {
        self.r.value()
    }

    pub closed spec fn frac_val(self) -> real {
        self.protocol_monoid().frac_val()
    }
    
    pub open spec fn has_full_frac(self) -> bool {
        self.frac_val() == 1.0real
    }

    #[verifier::external_body]
    pub proof fn borrow(tracked &self) -> (tracked s: &T)
    {
        unimplemented!()
    }
}

}