// SPDX-License-Identifier: MPL-2.0
//! Client resources paired with an RCU allocation registration.
//!
//! # Verified Properties
//!
//! Persistent block information and the unique base retire permission identify
//! the same allocation and exact typed pointer. Packing and unpacking preserve
//! the client's tracked resource without duplicating it.
//!
//! The client determines what its resource means. This wrapper alone does not
//! establish memory accessibility, detachment, or permission to reclaim memory.
use vstd::prelude::*;
use vstd_extra::ownership::Inv;

use super::{RcuBaseRetirePerm, RcuBlockInfo, RcuRegistration};

verus! {

/// One allocation's registration paired with a linear client resource.
#[verifier::reject_recursive_types(T)]
pub tracked struct RcuOwnedObject<T, O> {
    registration: RcuRegistration<T>,
    ownership: O,
}

impl<T, O> Inv for RcuOwnedObject<T, O> {
    open spec fn inv(self) -> bool {
        &&& self.block_info().inv()
        &&& self.retire_perm().inv()
        &&& self.block_info().domain() == self.retire_perm().domain()
        &&& self.block_info().obj() == self.retire_perm().obj()
        &&& equal(self.block_info().ptr(), self.retire_perm().ptr())
    }
}

impl<T, O> RcuOwnedObject<T, O> {
    /// Persistent identity and unique base retire permission.
    pub closed spec fn registration(self) -> RcuRegistration<T> {
        self.registration
    }

    /// Persistent identity of the registered allocation.
    pub open spec fn block_info(self) -> RcuBlockInfo<T> {
        self.registration().0
    }

    /// Unique base retire permission for the registered allocation.
    pub open spec fn retire_perm(self) -> RcuBaseRetirePerm<T> {
        self.registration().1
    }

    /// Client resource associated with this registration.
    pub closed spec fn ownership(self) -> O {
        self.ownership
    }

    /// Pairs a consistent registration with a client resource without copying either.
    pub proof fn tracked_new(
        tracked registration: RcuRegistration<T>,
        tracked ownership: O,
    ) -> (tracked res: Self)
        requires
            registration.0.inv(),
            registration.1.inv(),
            registration.0.domain() == registration.1.domain(),
            registration.0.obj() == registration.1.obj(),
            equal(registration.0.ptr(), registration.1.ptr()),
        ensures
            res.inv(),
            res.registration() == registration,
            res.ownership() == ownership,
    {
        Self { registration, ownership }
    }

    /// Consumes the wrapper and returns its unchanged registration and client resource.
    pub proof fn tracked_into_parts(tracked self) -> (tracked res: (RcuRegistration<T>, O))
        returns
            (self.registration(), self.ownership()),
    {
        (self.registration, self.ownership)
    }
}

} // verus!
