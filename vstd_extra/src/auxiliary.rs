use vstd::atomic::PermissionU64;
use vstd::cell::pcell::{PCell, PointsTo};
use vstd::prelude::*;

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
        p1 == p2,
;

/// A Verus version of `unsafe { &mut *cell.get() }` for `UnsafeCell<T>`.
/// FIXME: Waiting for official support from Verus.
#[verifier::external_body]
pub exec fn pcell_borrow_mut<'a, T>(cell: &'a PCell<T>, perm: &'a mut Tracked<PointsTo<T>>) -> (res:
    &'a mut T)
    requires
        cell.id() == perm.id(),
    ensures
        *final(res) == *final(perm).value(),
        final(perm).id() == old(perm).id(),
    no_unwind
{
    // SAFETY: the caller must ensure that `perm` is a valid permission for `cell`.
    unimplemented!();
}

} // verus!
