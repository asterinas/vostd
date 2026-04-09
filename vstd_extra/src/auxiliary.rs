use vstd::prelude::*;
use vstd::atomic::PermissionU64;

verus! {

// Produces an arbitrary PointsTo permission for type T, this is sound because one can not use
// such a permission to access memory.
#[verifier(external_body)]
pub proof fn arbitrary_cell_pointsto<T>() -> (tracked res: vstd::cell::pcell::PointsTo<T>) {
    unimplemented!();
}

/// Extensional equality for `PermissionU64`: two permissions with the same
/// `id()` and `value()` are equal. This is sound because `PermissionU64`'s
/// view is determined entirely by `(patomic, value)`, and the tracked struct
/// is a newtype wrapper around its view.
pub axiom fn axiom_permission_u64_ext_eq(p1: PermissionU64, p2: PermissionU64)
    requires
        p1.id() == p2.id(),
        p1.value() == p2.value(),
    ensures
        p1 == p2;

} // verus!
