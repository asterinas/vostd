use vstd::prelude::*;
use vstd::pcm::PCM;

verus! {


#[derive(PartialEq, Eq)]
pub tracked enum Excl_<A> {
    /// Exclusive ownership of a value
    Excl(A),
    /// Invalid state
    ExclInvalid,
}

// None represents the unit element
pub tracked struct Excl<A>(pub Option<Excl_<A>>);

impl<A> PCM for Excl<A> {
    open spec fn valid(self) -> bool {
        match self.0 {
            None => true,
            Some(Excl_::Excl(_)) => true,
            Some(Excl_::ExclInvalid) => false,
        }
    }
    
    open spec fn op(self, other: Self) -> Self {
        match (self.0, other.0) {
            (None, x) => Excl(x),
            (x, None) => Excl(x),
            (Some(_), Some(_)) => Excl(Some(Excl_::ExclInvalid)),
        }
    }
    
    open spec fn unit() -> Self {
        Excl(None)
    }
    
    proof fn closed_under_incl(a: Self, b: Self){}
    proof fn commutative(a: Self, b: Self) {}
    proof fn associative(a: Self, b: Self, c: Self) {}
    proof fn op_unit(a: Self) {}
    proof fn unit_valid() {}
}

} // verus!