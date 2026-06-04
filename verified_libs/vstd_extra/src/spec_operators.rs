use vstd::prelude::*;

verus! {

pub trait SpecAddTrait<Rhs = Self> {
    type Output;

    spec fn spec_add(self, rhs: Rhs) -> Self::Output;
}

pub trait SpecSubTrait<Rhs = Self> {
    type Output;

    spec fn spec_sub(self, rhs: Rhs) -> Self::Output;
}

pub trait SpecMulTrait<Rhs = Self> {
    type Output;

    spec fn spec_mul(self, rhs: Rhs) -> Self::Output;
}

pub trait SpecShlTrait<Rhs = Self> {
    type Output;

    spec fn spec_shl(self, rhs: Rhs) -> Self::Output;
}

pub trait SpecShrTrait<Rhs = Self> {
    type Output;

    spec fn spec_shr(self, rhs: Rhs) -> Self::Output;
}

pub trait SpecBitAndTrait<Rhs = Self> {
    type Output;

    spec fn spec_bitand(self, rhs: Rhs) -> Self::Output;
}

pub trait SpecBitOrTrait<Rhs = Self> {
    type Output;

    spec fn spec_bitor(self, rhs: Rhs) -> Self::Output;
}

pub trait SpecBitXorTrait<Rhs = Self> {
    type Output;

    spec fn spec_bitxor(self, rhs: Rhs) -> Self::Output;
}

pub trait SpecNegTrait {
    type Output;

    spec fn spec_neg(self) -> Self::Output;
}

} // verus!
