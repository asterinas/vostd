//! The abstract TLB model.
//!
//! [`TlbModel`] is a tracked resource that owns one [`CpuTlb`] per CPU. Each
//! [`CpuTlb`] bounds what that CPU's TLB may cache: an entry is either backed by
//! the current page table of a resident address space, or it is in `stale`.
//! Hardware fills and evictions keep this bound, so they are not steps.
//!
//! Both resources keep their state private, so a proof cannot forge them or
//! drop stale entries. Removing stale entries is reserved for the contracts of
//! the hardware flush primitives.
//!
//! The model describes the least that each flush invalidates. The trusted arch
//! flushes may invalidate more (on RISC-V, `sfence.vma` also drops global
//! entries and entries of other address spaces), which keeps the model a sound
//! upper bound on what a TLB may cache.
//!
//! The request bookkeeping of `OpsStack` and `TlbFlusher::issue_tlb_flush[_with]`
//! is verified against [`FlushSet`]. `OpsStack::new`, the hardware flushes, and
//! dispatching and synchronizing flush requests remain trusted. Which CPU runs
//! the code is not modelled yet.
//!
//! Frames are not kept alive until their TLB entries are flushed: the
//! `page_keeper` of `OpsStack` is commented out, so the frame passed to
//! `TlbFlusher::issue_tlb_flush_with` is dropped once the request is recorded.
use vstd::prelude::*;
use vstd_extra::ownership::*;

use crate::specs::mm::page_table::*;

use crate::mm::{Paddr, Vaddr};

verus! {

/// The TLB entries that a group of flush operations invalidates, by their ISA
/// meaning.
pub ghost struct FlushSet {
    /// At least every non-global entry is invalidated, as by `TlbFlushOp::All`.
    pub all_user: bool,
    /// At least the entries translating any of these addresses are
    /// invalidated, including global ones, as by `invlpg` or `sfence.vma`.
    pub vas: Set<Vaddr>,
}

impl FlushSet {
    pub open spec fn empty() -> Self {
        FlushSet { all_user: false, vas: Set::empty() }
    }

    /// The meaning of flushing all non-global entries, which drops any
    /// address-specific operations collected before.
    pub open spec fn all_user() -> Self {
        FlushSet { all_user: true, vas: Set::empty() }
    }

    pub open spec fn join(self, other: Self) -> Self {
        FlushSet { all_user: self.all_user || other.all_user, vas: self.vas + other.vas }
    }
}

/// The address space that a TLB entry is tagged with.
pub ghost enum AsId {
    /// Global entries. The model does not invalidate them on address-space
    /// switches or `TlbFlushOp::All`, although some architectures do.
    Kernel,
    /// Non-global entries of the user page table with this root.
    User(Paddr),
}

pub ghost struct TlbEntry {
    pub asid: AsId,
    pub map: Mapping,
}

/// An abstract CPU index. It is connected to `CpuId` by the code that owns
/// the per-CPU resources, not by this model.
pub type CpuIdx = nat;

/// The state of one CPU's TLB, as an upper bound on what it may cache.
pub ghost struct CpuTlbState {
    /// The user address space installed in CR3 or `satp`, if any.
    pub active: Option<AsId>,
    /// The address spaces that may have entries cached on this CPU.
    pub resident: Set<AsId>,
    /// The entries that may be cached although their page tables no longer
    /// contain them.
    pub stale: Set<TlbEntry>,
}

impl Inv for CpuTlbState {
    open spec fn inv(self) -> bool {
        &&& self.resident.contains(AsId::Kernel)
        &&& self.active matches Some(asid) ==> self.resident.contains(asid)
        &&& forall|e: TlbEntry| #[trigger]
            self.stale.contains(e) ==> e.map.inv() && self.resident.contains(e.asid)
    }
}

/// The tracked TLB of one CPU.
pub tracked struct CpuTlb {
    ghost cpu: CpuIdx,
    ghost state: CpuTlbState,
}

impl View for CpuTlb {
    type V = CpuTlbState;

    closed spec fn view(&self) -> CpuTlbState {
        self.state
    }
}

impl CpuTlb {
    /// The CPU whose TLB this is.
    pub closed spec fn cpu(self) -> CpuIdx {
        self.cpu
    }
}

/// The tracked TLBs of all CPUs, `0..num_cpus()`.
pub tracked struct TlbModel {
    ghost num_cpus: nat,
    tracked cpus: Map<CpuIdx, CpuTlb>,
}

impl Inv for TlbModel {
    closed spec fn inv(self) -> bool {
        &&& forall|c: CpuIdx| #[trigger] self.cpus.contains_key(c) <==> c < self.num_cpus
        &&& forall|c: CpuIdx|
            #![trigger self.cpus[c]]
            c < self.num_cpus ==> self.cpus[c].cpu() == c && self.cpus[c]@.inv()
    }
}

impl TlbModel {
    pub closed spec fn num_cpus(self) -> nat {
        self.num_cpus
    }

    /// The TLB state of CPU `c`.
    pub closed spec fn cpu_state(self, c: CpuIdx) -> CpuTlbState {
        self.cpus[c]@
    }

    /// No CPU caches an entry that its page table no longer backs.
    pub open spec fn coherent(self) -> bool {
        forall|c: CpuIdx, e: TlbEntry|
            c < self.num_cpus() ==> !#[trigger] self.cpu_state(c).stale.contains(e)
    }
}

} // verus!
