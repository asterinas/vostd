use vstd::atomic::PermissionU64;
use vstd::cell::pcell::{PCell, PointsTo};
use vstd::prelude::*;

verus! {

/// Extensional equality for `PermissionU64`: two permissions with the same
/// `id()` and `value()` are equal. This is sound because `PermissionU64`'s
/// view is determined entirely by `(patomic, value)`, and the tracked struct
/// is a newtype wrapper around its view.
pub axiom fn axiom_permission_u64_ext_eq(p1: PermissionU64, p2: PermissionU64)
    requires
        p1.id() == p2.id(),
        p1.value() == p2.value(),
    ensures
        p1 == p2,
;

/// Auxliary traits to define spec-mode operators, as traits like `SpecAdd` are
/// not available outside `vstd`.
trait SimpleSpecAdd {
    spec fn spec_add(self, other: Self) -> Self;
}

trait SimpleSpecSub {
    spec fn spec_sub(self, other: Self) -> Self;
}

trait SimpleSpecMul {
    spec fn spec_mul(self, other: Self) -> Self;
}

trait SimpleSpecShl {
    spec fn spec_shl(self, other: Self) -> Self;
}

trait SimpleSpecShr {
    spec fn spec_shr(self, other: Self) -> Self;
}

trait SimpleSpecBitAnd {
    spec fn spec_bitand(self, other: Self) -> Self;
}

trait SimpleSpecBitOr {
    spec fn spec_bitor(self, other: Self) -> Self;
}

trait SimpleSpecBitXor {
    spec fn spec_bitxor(self, other: Self) -> Self;
}

trait SimpleSpecNeg {
    spec fn spec_neg(self) -> Self;
}

trait SimpleSpecOrd {
    fn spec_lt(self, other: Self) -> bool;

    fn spec_le(self, other: Self) -> bool;

    fn spec_gt(self, other: Self) -> bool;

    fn spec_ge(self, other: Self) -> bool;
}

} // verus!
