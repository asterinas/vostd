use vstd::atomic::PermissionU64;
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

pub trait OptionExtraFns<T> {
    spec fn tracked_borrow_mut_requires(self) -> bool;

    spec fn tracked_borrow_mut_ensures(self, value: T) -> bool;

    proof fn tracked_borrow_mut(tracked &mut self) -> (tracked value: &mut T)
        requires
            self.tracked_borrow_mut_requires(),
        ensures
            old(self).tracked_borrow_mut_ensures(*value),
            final(self).tracked_borrow_mut_ensures(*final(value)),
    ;
}

impl<T> OptionExtraFns<T> for Option<T> {
    open spec fn tracked_borrow_mut_requires(self) -> bool {
        self is Some
    }

    open spec fn tracked_borrow_mut_ensures(self, value: T) -> bool {
        self is Some && self->0 == value
    }

    proof fn tracked_borrow_mut(tracked &mut self) -> tracked &mut T {
        match self {
            Some(ref mut value) => value,
            None => proof_from_false(),
        }
    }
}

} // verus!
