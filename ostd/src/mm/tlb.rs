// SPDX-License-Identifier: MPL-2.0
//! TLB flush operations.
use vstd::prelude::*;
use vstd_extra::ownership::*;

use crate::specs::mm::tlb::{FlushSet, TlbModel};

use super::{
    PAGE_SIZE, Vaddr,
    frame::{Frame, meta::AnyFrameMeta},
};
use alloc::vec::Vec;
use core::{
    ops::Range,
    sync::atomic::{AtomicBool, Ordering},
};

use crate::{
    //arch::irq,
    cpu::{AtomicCpuSet, CpuSet /*, PinCurrentCpu*/},
    //cpu_local,
    //sync::{LocalIrqDisabled, SpinLock},
};

/// A TLB flusher that is aware of which CPUs are needed to be flushed.
///
/// The flusher needs to stick to the current CPU.
#[verus_verify]
pub struct TlbFlusher<'a /*, G: PinCurrentCpu*/> {
    target_cpus: &'a AtomicCpuSet,
    have_unsynced_flush: CpuSet,
    ops_stack: OpsStack,
    //_pin_current: G,
}

verus! {

impl<'a> TlbFlusher<'a> {
    /// The flushes issued but not yet dispatched.
    pub closed spec fn pending(&self) -> FlushSet {
        self.ops_stack@
    }

    /// How many more requests can be issued before the pending requests
    /// escalate to flushing all non-global entries.
    pub closed spec fn remaining_slots(&self) -> nat {
        self.ops_stack.remaining_slots()
    }
}

} // verus!
#[verus_verify]
impl<'a /*, G: PinCurrentCpu*/> TlbFlusher<'a /*, G*/> {
    /// Creates a new TLB flusher with the specified CPUs to be flushed.
    ///
    /// The target CPUs should be a reference to an [`AtomicCpuSet`] that will
    /// be loaded upon [`Self::dispatch_tlb_flush`].
    ///
    /// The flusher needs to stick to the current CPU. So please provide a
    /// guard that implements [`PinCurrentCpu`].
    #[verus_spec(r =>
        ensures
            r.pending() == FlushSet::empty(),
            r.remaining_slots() == FLUSH_ALL_OPS_THRESHOLD,
    )]
    pub fn new(target_cpus: &'a AtomicCpuSet /*, pin_current_guard: G*/) -> Self {
        Self {
            target_cpus,
            have_unsynced_flush: CpuSet::new_empty(),
            ops_stack: OpsStack::new(),
            //_pin_current: pin_current_guard,
        }
    }

    /// Issues a pending TLB flush request.
    ///
    /// This function does not guarantee to flush the TLB entries on either
    /// this CPU or remote CPUs. The flush requests are only performed when
    /// [`Self::dispatch_tlb_flush`] is called.
    #[verus_spec(
        ensures
            if old(self).remaining_slots() == 0 || op.escalates_to_all() {
                &&& final(self).pending() == FlushSet::all_user()
                &&& final(self).remaining_slots() == 0
            } else {
                &&& final(self).pending() == old(self).pending().join(op@)
                &&& final(self).remaining_slots() == old(self).remaining_slots() - 1
            },
    )]
    pub fn issue_tlb_flush(&mut self, op: TlbFlushOp) {
        self.ops_stack.push(op, None);
    }

    /// Issues a TLB flush request that must happen before dropping the page.
    ///
    /// If we need to remove a mapped page from the page table, we can only
    /// recycle the page after all the relevant TLB entries in all CPUs are
    /// flushed. Otherwise if the page is recycled for other purposes, the user
    /// space program can still access the page through the TLB entries. This
    /// method is designed to be used in such cases.
    #[verus_spec(
        ensures
            if old(self).remaining_slots() == 0 || op.escalates_to_all() {
                &&& final(self).pending() == FlushSet::all_user()
                &&& final(self).remaining_slots() == 0
            } else {
                &&& final(self).pending() == old(self).pending().join(op@)
                &&& final(self).remaining_slots() == old(self).remaining_slots() - 1
            },
    )]
    // Verification note: `page_keeper` is commented out, so `drop_after_flush`
    // is dropped once the request is recorded, not after the flush.
    pub fn issue_tlb_flush_with(
        &mut self,
        op: TlbFlushOp,
        drop_after_flush: Frame<dyn AnyFrameMeta>,
    ) {
        self.ops_stack.push(op, Some(drop_after_flush));
    }

    /// Dispatches all the pending TLB flush requests.
    ///
    /// All previous pending requests issued by [`Self::issue_tlb_flush`] or
    /// [`Self::issue_tlb_flush_with`] starts to be processed after this
    /// function. But it may not be synchronous. Upon the return of this
    /// function, the TLB entries may not be coherent.
    #[verifier::external_body]
    #[verus_spec(
        with Tracked(model): Tracked<&mut TlbModel>
        requires
            old(model).inv(),
        ensures
            // The model only over-approximates the TLBs, so keeping it is sound.
            // Remote flushes complete only in `sync_tlb_flush`, and the local
            // flush cannot be attributed to a CPU yet.
            *final(model) == *old(model),
            final(self).pending() == FlushSet::empty(),
            final(self).remaining_slots() == FLUSH_ALL_OPS_THRESHOLD,
    )]
    pub fn dispatch_tlb_flush(&mut self) {
        unimplemented!() /*let irq_guard = crate::trap::irq::disable_local();
        

        if self.ops_stack.is_empty() {
        return;
        }

        // `Release` to make sure our modification on the PT is visible to CPUs
        // that are going to activate the PT.
        let mut target_cpus = self.target_cpus.load(Ordering::Release);

        let cur_cpu = irq_guard.current_cpu();
        let mut need_flush_on_self = false;

        if target_cpus.contains(cur_cpu) {
        target_cpus.remove(cur_cpu);
        need_flush_on_self = true;
        }

        for cpu in target_cpus.iter() {
        {
        let mut flush_ops = FLUSH_OPS.get_on_cpu(cpu).lock();
        flush_ops.push_from(&self.ops_stack);

        // Clear ACK before dropping the lock to avoid false ACKs.
        ACK_REMOTE_FLUSH
        .get_on_cpu(cpu)
        .store(false, Ordering::Relaxed);
        }
        self.have_unsynced_flush.add(cpu);
        }

        crate::smp::inter_processor_call(&target_cpus, do_remote_flush);

        // Flush ourselves after sending all IPIs to save some time.
        if need_flush_on_self {
        self.ops_stack.flush_all();
        } else {
        self.ops_stack.clear_without_flush();
        }*/
    }

    /// Waits for all the previous TLB flush requests to be completed.
    ///
    /// After this function, all TLB entries corresponding to previous
    /// dispatched TLB flush requests are guaranteed to be coherent.
    ///
    /// The TLB flush requests are issued with [`Self::issue_tlb_flush`] and
    /// dispatched with [`Self::dispatch_tlb_flush`]. This method will not
    /// dispatch any issued requests so it will not guarantee TLB coherence
    /// of requests that are not dispatched.
    ///
    /// # Panics
    ///
    /// This method panics if the IRQs are disabled. Since the remote flush are
    /// processed in IRQs, two CPUs may deadlock if they are waiting for each
    /// other's TLB coherence.
    #[verifier::external_body]
    pub fn sync_tlb_flush(&mut self) {
        unimplemented!() /*
        assert!(
        irq::is_local_enabled(),
        "Waiting for remote flush with IRQs disabled"
        );

        for cpu in self.have_unsynced_flush.iter() {
        while !ACK_REMOTE_FLUSH.get_on_cpu(cpu).load(Ordering::Relaxed) {
        core::hint::spin_loop();
        }
        }

        self.have_unsynced_flush = CpuSet::new_empty();
         */
    }
}

verus! {

/// The operation to flush TLB entries.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TlbFlushOp {
    /// Flush all TLB entries except for the global entries.
    All,
    /// Flush the TLB entry for the specified virtual address.
    Address(Vaddr),
    /// Flush the TLB entries for the specified virtual address range.
    Range(Range<Vaddr>),
}

// SAFETY: The derived `PartialEq` is structural equality. The impl is manual
// because Verus has no `Structural` impl for `Range`.
unsafe impl Structural for TlbFlushOp {

}

impl View for TlbFlushOp {
    type V = FlushSet;

    open spec fn view(&self) -> FlushSet {
        match *self {
            TlbFlushOp::All => FlushSet::all_user(),
            TlbFlushOp::Address(va) => FlushSet { all_user: false, vas: Set::empty().insert(va) },
            // `tlb_flush_addr_range` invalidates one address per base page,
            // starting from `range.start`.
            TlbFlushOp::Range(range) => FlushSet {
                all_user: false,
                vas: Set::from_finite_type(
                    |va: Vaddr|
                        range.start <= va < range.end && (va - range.start) % PAGE_SIZE as int == 0,
                ),
            },
        }
    }
}

impl TlbFlushOp {
    /// Whether a request for this operation is recorded as `TlbFlushOp::All`:
    /// it is `All`, or a range longer than [`FLUSH_ALL_RANGE_THRESHOLD`].
    pub open spec fn escalates_to_all(self) -> bool {
        match self {
            TlbFlushOp::All => true,
            TlbFlushOp::Address(_) => false,
            TlbFlushOp::Range(range) => range.end - range.start > FLUSH_ALL_RANGE_THRESHOLD,
        }
    }
}

impl TlbFlushOp {
    /// Performs the TLB flush operation on the current CPU.
    #[verifier::external_body]
    pub fn perform_on_current(&self) {
        unimplemented!()/*use crate::arch::mm::{
            tlb_flush_addr, tlb_flush_addr_range, tlb_flush_all_excluding_global,
        };
        match self {
            TlbFlushOp::All => tlb_flush_all_excluding_global(),
            TlbFlushOp::Address(addr) => tlb_flush_addr(*addr),
            TlbFlushOp::Range(range) => tlb_flush_addr_range(range),
        }*/

    }
}

} // verus!
#[verus_verify]
impl TlbFlushOp {
    #[verus_spec(
        returns
            match self {
                TlbFlushOp::Range(range) => {
                    if range.end - range.start > FLUSH_ALL_RANGE_THRESHOLD {
                        TlbFlushOp::All
                    } else {
                        self
                    }
                },
                _ => self,
            },
    )]
    fn optimize_for_large_range(self) -> Self {
        match self {
            TlbFlushOp::Range(range) => {
                if range.len() > FLUSH_ALL_RANGE_THRESHOLD {
                    TlbFlushOp::All
                } else {
                    TlbFlushOp::Range(range)
                }
            }
            _ => self,
        }
    }
}

verus! {

// The queues of pending requests on each CPU.
/*cpu_local! {
    static FLUSH_OPS: SpinLock<OpsStack, LocalIrqDisabled> = SpinLock::new(OpsStack::new());
    /// Whether this CPU finishes the last remote flush request.
    static ACK_REMOTE_FLUSH: AtomicBool = AtomicBool::new(true);
}*/
#[verifier::external_body]
fn do_remote_flush() {
    unimplemented!()/*
    // No races because we are in IRQs or have disabled preemption.
    let current_cpu = crate::cpu::CpuId::current_racy();

    let mut new_op_queue = OpsStack::new();
    {
        let mut op_queue = FLUSH_OPS.get_on_cpu(current_cpu).lock();

        core::mem::swap(&mut *op_queue, &mut new_op_queue);

        // ACK before dropping the lock so that we won't miss flush requests.
        ACK_REMOTE_FLUSH
            .get_on_cpu(current_cpu)
            .store(true, Ordering::Relaxed);
    }
    // Unlock the locks quickly to avoid contention. ACK before flushing is
    // fine since we cannot switch back to userspace now.
    new_op_queue.flush_all();
    */

}

// Origin Rust: both thresholds are private `const`s. They are `pub` so that
// `TlbFlushOp::escalates_to_all` and the `TlbFlusher` contracts can name them.
/// If a TLB flushing request exceeds this threshold, we flush all.
pub const FLUSH_ALL_RANGE_THRESHOLD: usize = 32 * PAGE_SIZE;

/// If the number of pending requests exceeds this threshold, we flush all the
/// TLB entries instead of flushing them one by one.
pub const FLUSH_ALL_OPS_THRESHOLD: usize = 32;

struct OpsStack {
    ops: [Option<TlbFlushOp>; FLUSH_ALL_OPS_THRESHOLD],
    need_flush_all: bool,
    size: usize,
    //    page_keeper: Vec<Frame<dyn AnyFrameMeta>>,
}

/// The meaning of the collected operations, in collection order.
spec fn ops_flush_set(ops: Seq<Option<TlbFlushOp>>) -> FlushSet {
    ops.fold_left(
        FlushSet::empty(),
        |acc: FlushSet, op: Option<TlbFlushOp>|
            match op {
                Some(op) => acc.join(op@),
                None => acc,
            },
    )
}

impl View for OpsStack {
    type V = FlushSet;

    closed spec fn view(&self) -> FlushSet {
        if self.need_flush_all {
            FlushSet::all_user()
        } else {
            ops_flush_set(self.ops@[..self.size])
        }
    }
}

impl OpsStack {
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.size <= FLUSH_ALL_OPS_THRESHOLD
    }

    /// How many more operations can be collected before escalating.
    closed spec fn remaining_slots(self) -> nat {
        if self.need_flush_all {
            0
        } else {
            (FLUSH_ALL_OPS_THRESHOLD - self.size) as nat
        }
    }
}

} // verus!
#[verus_verify]
impl OpsStack {
    // Verus does not support the array-fill expression of a non-`Copy` type.
    #[verifier::external_body]
    #[verus_spec(r =>
        ensures
            r@ == FlushSet::empty(),
            r.remaining_slots() == FLUSH_ALL_OPS_THRESHOLD,
    )]
    const fn new() -> Self {
        Self {
            ops: [const { None }; FLUSH_ALL_OPS_THRESHOLD],
            need_flush_all: false,
            size: 0,
            //            page_keeper: Vec::new(),
        }
    }

    #[verus_spec(r =>
        ensures
            r ==> self@ == FlushSet::empty(),
        returns
            self.remaining_slots() == FLUSH_ALL_OPS_THRESHOLD
    )]
    fn is_empty(&self) -> bool {
        proof! {
            use_type_invariant(self);
        }
        !self.need_flush_all && self.size == 0
    }

    /// Escalating to a full flush covers every non-global entry, but may lose
    /// the address-specific coverage of global entries.
    #[verus_spec(
        ensures
            if old(self).remaining_slots() == 0 || op.escalates_to_all() {
                &&& final(self)@ == FlushSet::all_user()
                &&& final(self).remaining_slots() == 0
            } else {
                &&& final(self)@ == old(self)@.join(op@)
                &&& final(self).remaining_slots() == old(self).remaining_slots() - 1
            },
    )]
    fn push(&mut self, op: TlbFlushOp, drop_after_flush: Option<Frame<dyn AnyFrameMeta>>) {
        proof! {
            use_type_invariant(&*self);
        }
        if let Some(frame) = drop_after_flush {
            //            self.page_keeper.push(frame);
        }
        if self.need_flush_all {
            return;
        }
        let op = op.optimize_for_large_range();
        if op == TlbFlushOp::All || self.size >= FLUSH_ALL_OPS_THRESHOLD {
            self.need_flush_all = true;
            self.size = 0;
            return;
        }
        proof_decl! { let ghost collected = self.ops@[..self.size]; }
        self.ops[self.size] = Some(op);
        self.size += 1;
        proof! {
            assert(self.ops@[..self.size] =~= collected.push(Some(op)));
            assert(collected.push(Some(op)).drop_last() =~= collected);
        }
    }

    #[verus_spec(
        ensures
            if old(self).remaining_slots() + other.remaining_slots() <= FLUSH_ALL_OPS_THRESHOLD {
                &&& final(self)@ == FlushSet::all_user()
                &&& final(self).remaining_slots() == 0
            } else {
                &&& final(self)@ == old(self)@.join(other@)
                &&& final(self).remaining_slots() == old(self).remaining_slots()
                    + other.remaining_slots() - FLUSH_ALL_OPS_THRESHOLD
            },
    )]
    fn push_from(&mut self, other: &OpsStack) {
        proof! {
            use_type_invariant(&*self);
            use_type_invariant(other);
        }
        //        self.page_keeper.extend(other.page_keeper.iter().cloned());
        if self.need_flush_all {
            return;
        }
        if other.need_flush_all || self.size + other.size >= FLUSH_ALL_OPS_THRESHOLD {
            self.need_flush_all = true;
            self.size = 0;
            return;
        }
        proof_decl! {
            let ghost start = self@;
            let ghost start_size = self.size;
        }
        proof! {
            assert(other.ops@[..0] =~= Seq::<Option<TlbFlushOp>>::empty());
            assert(start.join(FlushSet::empty()).vas =~= start.vas);
        }
        #[verus_spec(
            invariant
                !self.need_flush_all,
                !other.need_flush_all,
                other.size <= FLUSH_ALL_OPS_THRESHOLD,
                start_size + other.size < FLUSH_ALL_OPS_THRESHOLD,
                self.size == start_size + i,
                self@ == start.join(ops_flush_set(other.ops@[..i])),
        )]
        for i in 0..other.size {
            proof! {
                use_type_invariant(&*self);
                use_type_invariant(other);
            }
            proof_decl! {
                let ghost collected = self.ops@[..self.size];
                let ghost copied = other.ops@[..i];
            }
            self.ops[self.size] = other.ops[i].clone();
            self.size += 1;
            proof! {
                let x = other.ops@[i as int];
                assert(self.ops@[self.size - 1] == x);
                assert(self.ops@[..self.size] =~= collected.push(x));
                assert(other.ops@[..i + 1] =~= copied.push(x));
                assert(collected.push(x).drop_last() =~= collected);
                assert(copied.push(x).drop_last() =~= copied);
                let prefix = ops_flush_set(copied);
                if let Some(op) = x {
                    assert((start.vas + prefix.vas) + op@.vas =~= start.vas + (prefix.vas
                        + op@.vas));
                }
            }
        }
    }

    #[verifier::external_body]
    fn flush_all(&mut self) {
        if self.need_flush_all {
            unimplemented!() /*crate::arch::mm::tlb_flush_all_excluding_global();*/
        } else {
            for i in 0..self.size {
                if let Some(op) = &self.ops[i] {
                    op.perform_on_current();
                }
            }
        }

        self.clear_without_flush();
    }

    #[verus_spec(
        ensures
            final(self)@ == FlushSet::empty(),
            final(self).remaining_slots() == FLUSH_ALL_OPS_THRESHOLD,
    )]
    fn clear_without_flush(&mut self) {
        proof! {
            use_type_invariant(&*self);
        }
        self.need_flush_all = false;
        self.size = 0;
        //        self.page_keeper.clear();
    }
}
