// SPDX-License-Identifier: MPL-2.0
//! Scheduling related information in a task.
use vstd::{
    atomic::{PAtomicU32, PermissionU32},
    prelude::*,
};

use crate::cpu::{axiom_cpu_count_bounds, cpu_count, lemma_cpu_id_model, lemma_type_inv_range};

// use core::sync::atomic::{AtomicU32, Ordering};

use crate::{cpu::CpuId /*, task::Task */};

/// Fields of a task that OSTD will never touch.
///
/// The type ought to be defined by the OSTD user and injected into the task.
/// They are not part of the dynamic task data because it's slower there for
/// the user-defined scheduler to access. The better ways to let the user
/// define them, such as
/// [existential types](https://github.com/rust-lang/rfcs/pull/2492) do not
/// exist yet. So we decide to define them in OSTD.
/* Origin Rust: #[derive(Debug)] (dropped: PAtomicU32 has no Debug impl) */
#[verus_verify]
pub struct TaskScheduleInfo {
    /// The CPU that the task would like to be running on.
    pub cpu: AtomicCpuId,
}

/// An atomic CPUID container.
/* Origin Rust: #[derive(Debug)] pub struct AtomicCpuId(AtomicU32); */
#[verus_verify]
pub struct AtomicCpuId(PAtomicU32);

verus! {

impl AtomicCpuId {
    /// The null value of CPUID.
    ///
    /// An `AtomicCpuId` with `AtomicCpuId::NONE` as its inner value is empty.
    /* `pub` is required by Verus since public contracts refer to it. */
    pub const NONE: u32 = u32::MAX;

    /// Sets the inner value of an `AtomicCpuId` if it's empty.
    ///
    /// The return value is a result indicating whether the new value was written
    /// and containing the previous value. If the previous value is empty, it returns
    /// `Ok(())`. Otherwise, it returns `Err(previous_value)` which the previous
    /// value is a valid CPU ID.
    #[verus_spec(
        ret =>
        with
            Tracked(perm): Tracked<&mut PermissionU32>,
        requires
            old(perm).view().patomic == self.patomic_id(),
            Self::inv_value(old(perm).view().value),
        ensures
            self.patomic_id() == final(perm).view().patomic,
            ret is Ok ==> final(perm).view().value == cpu_id.as_usize() as u32,
            ret matches Err(prev) ==> prev@ == old(perm).view().value
                && final(perm).view().value == old(perm).view().value,
            Self::inv_value(final(perm).view().value),
    )]
    pub fn set_if_is_none(&self, cpu_id: CpuId) -> core::result::Result<(), CpuId> {
        proof! {
            broadcast use {
                axiom_cpu_count_bounds,
                lemma_cpu_id_model,
                lemma_type_inv_range,
            };
            use_type_invariant(&cpu_id);
            assert(Self::inv_value(cpu_id.as_usize() as u32));
        }
        /* PAtomicU32::compare_exchange takes the tracked permission and hardcodes
         * `SeqCst`, so the call drops the two `Ordering::Relaxed` arguments; the
         * `map_err` closure needs its own spec to carry the `unwrap` precondition.
         * Origin Rust: self.0.compare_exchange(Self::NONE, cpu_id.as_usize() as u32, Ordering::Relaxed, Ordering::Relaxed).map(|_| ()).map_err(|prev| (prev as usize).try_into().unwrap())
         */
        self.0.compare_exchange(Tracked(perm), Self::NONE, cpu_id.as_usize() as u32).map(
            |_| (),
        ).map_err(
            |prev: u32| -> (payload: CpuId)
                requires
                    cpu_count() > prev,
                ensures
                    payload@ == prev,
                { (prev as usize).try_into().unwrap() },
        )
    }

    /// Sets the inner value of an `AtomicCpuId` anyway.
    #[verus_spec(
        with
            Tracked(perm): Tracked<&mut PermissionU32>,
        requires
            old(perm).view().patomic == self.patomic_id(),
        ensures
            self.patomic_id() == final(perm).view().patomic,
            final(perm).view().value == cpu_id.as_usize() as u32,
            Self::inv_value(final(perm).view().value),
    )]
    pub fn set_anyway(&self, cpu_id: CpuId) {
        proof! {
            broadcast use {
                axiom_cpu_count_bounds,
                lemma_cpu_id_model,
                lemma_type_inv_range,
            };
            use_type_invariant(&cpu_id);
            assert(Self::inv_value(cpu_id.as_usize() as u32));
        }
        /* Origin Rust: self.0.store(cpu_id.as_usize() as u32, Ordering::Relaxed); */
        self.0.store(Tracked(perm), cpu_id.as_usize() as u32);
    }

    /// Sets the inner value of an `AtomicCpuId` to `AtomicCpuId::NONE`, i.e. makes
    /// an `AtomicCpuId` empty.
    #[verus_spec(
        with
            Tracked(perm): Tracked<&mut PermissionU32>,
        requires
            old(perm).view().patomic == self.patomic_id(),
        ensures
            self.patomic_id() == final(perm).view().patomic,
            final(perm).view().value == Self::NONE,
            Self::inv_value(final(perm).view().value),
    )]
    pub fn set_to_none(&self) {
        /* Origin Rust: self.0.store(Self::NONE, Ordering::Relaxed); */
        self.0.store(Tracked(perm), Self::NONE);
    }

    /// Gets the inner value of an `AtomicCpuId`.
    #[verus_spec(
        ret =>
        with
            Tracked(perm): Tracked<&PermissionU32>,
        requires
            perm.view().patomic == self.patomic_id(),
            Self::inv_value(perm.view().value),
        ensures
            ret is None == (perm.view().value == Self::NONE),
            ret matches Some(id) ==> id@ == perm.view().value,
    )]
    pub fn get(&self) -> Option<CpuId> {
        /* Origin Rust: let val = self.0.load(Ordering::Relaxed); */
        let val = self.0.load(Tracked(perm));
        if val == Self::NONE {
            None
        } else {
            Some((val as usize).try_into().ok()?)
        }
    }

    /// The identity of the inner atomic cell, for tying permissions to `self`.
    /// A closed helper, since a `pub` contract cannot use the private field.
    pub closed spec fn patomic_id(&self) -> int {
        self.0.id()
    }

    /// The trace invariant of the CPUID cell: the stored word is the null
    /// constant `NONE` or encodes a valid CPU ID (below the CPU count).
    pub open spec fn inv_value(v: u32) -> bool {
        v == Self::NONE || 0 <= v < cpu_count()
    }
}

} // verus!
impl Default for AtomicCpuId {
    fn default() -> Self {
        Self(PAtomicU32::new(Self::NONE).0)
    }
}

/* impl CommonSchedInfo for Task {
    fn cpu(&self) -> &AtomicCpuId {
        &self.schedule_info().cpu
    }
} */

/// Trait for fetching common scheduling information.
pub trait CommonSchedInfo {
    /// Gets the CPU that the task is running on or lately ran on.
    fn cpu(&self) -> &AtomicCpuId;
}
