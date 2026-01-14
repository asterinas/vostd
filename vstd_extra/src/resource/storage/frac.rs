//! This module defines the real-based fractional permissions storage protocol.

use vstd::prelude::*;
use vstd::storage_protocol::*;

verus!{

#[verifier::ext_equal]
pub tracked enum FracS<T> {
    Unit,
    Frac(real, T),
    Invalid,
}

impl <T> Protocol<(),Option<T>> for FracS<T> {
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

    open spec fn rel(self, s:Map<(),Option<T>>) -> bool {
        match self {
            FracS::Frac(q, v) => {
                s.contains_key(()) && s[()] == Some(v)
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

}