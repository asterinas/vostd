// SPDX-License-Identifier: MPL-2.0
//! Logical protocol for nested local IRQ guards.
//!
//! Models `DisabledLocalIrqGuard`: disabling saves the previous state, and
//! restoring consumes a permission in reverse acquisition order. Nothing here
//! touches hardware, and the guard constructor and Drop are not yet connected.
//! IF does not exclude NMIs or exceptions.
use vstd::{prelude::*, resource::Loc};
use vstd_extra::ownership::Inv;

use crate::specs::task::{
    cpu_core::CpuCoreLocalState,
    cpu_local::{CpuLocalAuth, CpuLocalPointsTo},
};

use crate::cpu::CpuId;

verus! {

/// Observable logical state of one CPU's nested IRQ guards.
pub ghost struct LocalIrqView {
    pub cpu: CpuId,
    pub enabled: bool,
    pub depth: nat,
}

/// Exclusive IRQ state, suitable for inclusion in a `CpuCoreOwner`.
pub tracked struct LocalIrqState {
    points_to: CpuLocalPointsTo<bool>,
    ghost depth: nat,
}

/// Linear permission to restore the state saved by one logical guard.
///
/// Private fields prevent forging it. Identity and depth prevent restoring
/// another resource or releasing an outer guard while an inner one is live.
pub tracked struct IrqRestorePermission {
    ghost id: Loc,
    ghost previous: LocalIrqView,
}

impl View for LocalIrqState {
    type V = LocalIrqView;

    closed spec fn view(&self) -> LocalIrqView {
        LocalIrqView {
            cpu: self.points_to.cpu(),
            enabled: self.points_to.value(),
            depth: self.depth,
        }
    }
}

impl CpuCoreLocalState for LocalIrqState {
    open spec fn belongs_to_cpu(self, cpu: CpuId) -> bool {
        self@.cpu == cpu
    }

    open spec fn local_key(self) -> Seq<Loc> {
        seq![self.id()]
    }
}

impl Inv for LocalIrqState {
    /// Any outstanding logical guard keeps this CPU's IRQ state disabled.
    open spec fn inv(self) -> bool {
        self@.depth > 0 ==> !self@.enabled
    }
}

impl Inv for IrqRestorePermission {
    open spec fn inv(self) -> bool {
        self.previous().depth > 0 ==> !self.previous().enabled
    }
}

impl IrqRestorePermission {
    /// Identity of the authority whose state this permission restores.
    pub closed spec fn id(&self) -> Loc {
        self.id
    }

    /// State saved when this permission was issued.
    pub closed spec fn previous(&self) -> LocalIrqView {
        self.previous
    }
}

impl LocalIrqState {
    /// Identity inherited from the CPU-local authority.
    pub closed spec fn id(&self) -> Loc {
        self.points_to.id()
    }

    /// Disables logical IRQs and issues a permission to restore the prior state.
    pub proof fn tracked_disable(
        tracked &mut self,
        tracked auth: &mut CpuLocalAuth<bool>,
    ) -> (tracked permission: IrqRestorePermission)
        requires
            old(self).inv(),
            old(self).id() == old(auth).id(),
        ensures
            final(self).inv(),
            permission.inv(),
            final(self).id() == old(self).id(),
            final(self)@ == (LocalIrqView {
                cpu: old(self)@.cpu,
                enabled: false,
                depth: old(self)@.depth + 1,
            }),
            permission.id() == old(self).id(),
            permission.previous() == old(self)@,
            final(auth).id() == old(auth).id(),
            final(auth)@ == old(auth)@.insert(old(self)@.cpu, false),
            final(auth).cpus() == old(auth).cpus(),
    {
        let ghost previous = self@;
        let ghost id = self.id();
        self.points_to.tracked_update(auth, false);
        self.depth = self.depth + 1;
        IrqRestorePermission { id, previous }
    }

    /// Consumes the innermost permission and restores its saved logical state.
    pub proof fn tracked_restore(
        tracked &mut self,
        tracked auth: &mut CpuLocalAuth<bool>,
        tracked permission: IrqRestorePermission,
    )
        requires
            permission.inv(),
            old(self).id() == old(auth).id(),
            permission.id() == old(self).id(),
            permission.previous().cpu == old(self)@.cpu,
            permission.previous().depth + 1 == old(self)@.depth,
        ensures
            final(self).inv(),
            final(self).id() == old(self).id(),
            final(self)@ == permission.previous(),
            final(auth).id() == old(auth).id(),
            final(auth)@ == old(auth)@.insert(old(self)@.cpu, permission.previous().enabled),
            final(auth).cpus() == old(auth).cpus(),
    {
        self.points_to.tracked_update(auth, permission.previous.enabled);
        self.depth = permission.previous.depth;
    }
}

} // verus!
