// SPDX-License-Identifier: MPL-2.0
//! Logical protocol for nested local IRQ guards.
//!
//! # Verified Properties
//!
//! `DisabledLocalIrqGuard::new` connects this protocol to executable construction
//! through trusted IRQ contracts on x86, RISC-V, and LoongArch.
//! Restoration here is logical only. Local IRQ masking excludes neither NMIs
//! nor exceptions.
//! TODO: provide CPU-bound owners and connect logical restoration to `Drop`.
use vstd::{prelude::*, resource::Loc};
use vstd_extra::ownership::Inv;

use crate::specs::task::{
    cpu_core::CpuCoreLocalState,
    cpu_local::{CpuLocalAuth, CpuLocalPointsTo},
};

use crate::cpu::CpuId;

verus! {

/// Observable logical state of one CPU's nested IRQ guards.
pub ghost struct LocalIrqGuardView {
    pub cpu: CpuId,
    pub enabled: bool,
    pub depth: nat,
}

/// Exclusive IRQ guard state for the executing, pinned CPU.
///
/// Provisioning must establish privilege, exclusive hardware access, and
/// agreement with `hardware_enabled`; CPU-local allocation alone cannot do so.
/// No constructor is provided yet. While the owner is live, unmodeled changes
/// are forbidden and returning handlers must restore the IRQ enable state.
/// `coherent()` relates hardware observations to the logical guard state.
pub tracked struct LocalIrqGuardOwner {
    points_to: CpuLocalPointsTo<bool>,
    ghost depth: nat,
    ghost hardware_enabled: bool,
}

impl !Send for LocalIrqGuardOwner {

}

impl !Sync for LocalIrqGuardOwner {

}

/// Linear permission to restore the state saved by one logical guard.
///
/// Private identity and depth enforce resource matching and nesting order.
pub tracked struct IrqRestorePermission {
    ghost id: Loc,
    ghost previous: LocalIrqGuardView,
}

impl View for LocalIrqGuardOwner {
    type V = LocalIrqGuardView;

    closed spec fn view(&self) -> LocalIrqGuardView {
        LocalIrqGuardView {
            cpu: self.points_to.cpu(),
            enabled: self.points_to.value(),
            depth: self.depth,
        }
    }
}

impl CpuCoreLocalState for LocalIrqGuardOwner {
    open spec fn belongs_to_cpu(self, cpu: CpuId) -> bool {
        self@.cpu == cpu
    }

    open spec fn local_key(self) -> Seq<Loc> {
        seq![self.id()]
    }
}

impl Inv for LocalIrqGuardOwner {
    /// Any outstanding logical guard keeps this CPU's logical IRQ state disabled.
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
    pub closed spec fn previous(&self) -> LocalIrqGuardView {
        self.previous
    }
}

impl LocalIrqGuardOwner {
    /// Local IRQ enable state observed by the trusted architecture operations.
    pub closed spec fn hardware_enabled(&self) -> bool {
        self.hardware_enabled
    }

    /// Agreement between the logical guard state and the hardware observation.
    pub open spec fn coherent(&self) -> bool {
        self.hardware_enabled() == self@.enabled
    }

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
            final(self)@ == (LocalIrqGuardView {
                cpu: old(self)@.cpu,
                enabled: false,
                depth: old(self)@.depth + 1,
            }),
            permission.id() == old(self).id(),
            permission.previous() == old(self)@,
            final(auth).id() == old(auth).id(),
            final(auth)@ == old(auth)@.insert(old(self)@.cpu, false),
            final(auth).cpus() == old(auth).cpus(),
            final(self).hardware_enabled() == old(self).hardware_enabled(),
    {
        let ghost previous = self@;
        let ghost id = self.id();
        self.points_to.tracked_update(auth, false);
        self.depth = self.depth + 1;
        IrqRestorePermission { id, previous }
    }

    /// Consumes the innermost permission and restores only its saved logical state.
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
            final(self).hardware_enabled() == old(self).hardware_enabled(),
    {
        self.points_to.tracked_update(auth, permission.previous.enabled);
        self.depth = permission.previous.depth;
    }
}

} // verus!
