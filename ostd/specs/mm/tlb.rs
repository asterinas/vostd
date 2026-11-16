use vstd::prelude::*;
use vstd_extra::ownership::*;

use crate::specs::mm::page_table::*;

use crate::mm::{Paddr, Vaddr, tlb::TlbFlushOp};

verus! {

/// The TLB entries that a group of flush operations invalidates, by their ISA
/// meaning.
pub ghost struct FlushSet {
    /// Every non-global entry is invalidated, as by `TlbFlushOp::All`.
    pub all_user: bool,
    /// Entries translating any of these addresses are invalidated, as by
    /// `invlpg` or `sfence.vma`. This includes global entries.
    pub vas: ISet<Vaddr>,
}

impl FlushSet {
    pub open spec fn empty() -> Self {
        FlushSet { all_user: false, vas: ISet::empty() }
    }

    /// The meaning of flushing all non-global entries, which drops any
    /// address-specific operations collected before.
    pub open spec fn all_user() -> Self {
        FlushSet { all_user: true, vas: ISet::empty() }
    }

    pub open spec fn join(self, other: Self) -> Self {
        FlushSet { all_user: self.all_user || other.all_user, vas: self.vas + other.vas }
    }

    /// Whether flushing `self` invalidates `e`, ignoring which address space
    /// the CPU has active.
    pub open spec fn covers(self, e: TlbEntry) -> bool {
        ||| self.all_user && e.asid != AsId::Kernel
        ||| exists|va: Vaddr| #[trigger]
            self.vas.contains(va) && e.map.va_range.start <= va < e.map.va_range.end
    }
}

/// The address space that a TLB entry is tagged with.
pub ghost enum AsId {
    /// Global entries, which survive address-space switches and
    /// `TlbFlushOp::All`.
    Kernel,
    /// Non-global entries of the user page table with this root.
    User(Paddr),
}

pub ghost struct TlbEntry {
    pub asid: AsId,
    pub map: Mapping,
}

/// An upper bound on what one CPU's TLB may cache.
///
/// Hardware fills and evictions are not steps: a fill copies a mapping of a
/// resident address space from its page table, and an eviction only shrinks
/// the cache. So any entry cached by the CPU is either backed by the current
/// page table of a resident address space, or is in `stale`.
pub tracked struct CpuTlb {
    /// The user address space installed in CR3 or `satp`, if any.
    pub ghost active: Option<AsId>,
    /// The address spaces that may have entries cached on this CPU.
    pub ghost resident: ISet<AsId>,
    /// The entries that may be cached although their page tables no longer
    /// contain them.
    pub ghost stale: ISet<TlbEntry>,
}

impl Inv for CpuTlb {
    open spec fn inv(self) -> bool {
        &&& self.resident.contains(AsId::Kernel)
        &&& self.active matches Some(asid) ==> self.resident.contains(asid)
        &&& forall|e: TlbEntry| #[trigger]
            self.stale.contains(e) ==> e.map.inv() && self.resident.contains(e.asid)
    }
}

impl CpuTlb {
    /// The mappings in `removed` left the page table of `asid`. If this CPU may
    /// cache entries of `asid`, they become stale.
    pub open spec fn pt_removed(self, asid: AsId, removed: Set<Mapping>) -> Self {
        if self.resident.contains(asid) {
            CpuTlb {
                stale: self.stale + ISet::new(
                    |e: TlbEntry| e.asid == asid && removed.contains(e.map),
                ),
                ..self
            }
        } else {
            self
        }
    }

    /// Flushes `fs` on this CPU. Only entries of the active address space and
    /// global entries are invalidated.
    pub open spec fn flush(self, fs: FlushSet) -> Self {
        CpuTlb {
            stale: self.stale.filter(
                |e: TlbEntry|
                    !(fs.covers(e) && (e.asid == AsId::Kernel || self.active == Some(e.asid))),
            ),
            ..self
        }
    }

    /// Installs the user page table of `asid`. This does not invalidate the
    /// entries of the previous address space.
    pub open spec fn switch(self, asid: AsId) -> Self {
        CpuTlb { active: Some(asid), resident: self.resident.insert(asid), ..self }
    }
}

pub ghost struct TlbModel {
    pub pending: Seq<TlbFlushOp>,
    pub mappings: Set<Mapping>,
}

impl Inv for TlbModel {
    open spec fn inv(self) -> bool {
        &&& mappings_well_formed(self.mappings)
        &&& mappings_disjoint_vaddrs(self.mappings)
        &&& mappings_disjoint_paddrs(self.mappings)
    }
}

impl TlbModel {
    pub open spec fn update(self, pt: PageTableView, va: Vaddr) -> Self {
        let m = pt.mappings.filter(|m: Mapping| m.va_range.start <= va < m.va_range.end).choose();
        TlbModel { pending: self.pending, mappings: self.mappings.insert(m) }
    }

    pub axiom fn tracked_update(&mut self, pt: PageTableView, va: Vaddr)
        requires
            old(self).inv(),
            forall|m: Mapping|
                old(self).mappings has m ==> !(m.va_range.start <= va < m.va_range.end),
            exists|m: Mapping| pt.mappings has m ==> m.va_range.start <= va < m.va_range.end,
        ensures
            *final(self) == old(self).update(pt, va),
    ;

    pub open spec fn flush(self, va: Vaddr) -> Self {
        let m = self.mappings.filter(|m: Mapping| m.va_range.start <= va < m.va_range.end);
        TlbModel { pending: self.pending, mappings: self.mappings - m }
    }

    pub axiom fn tracked_flush(&mut self, va: Vaddr)
        requires
            old(self).inv(),
        ensures
            *final(self) == old(self).flush(va),
    ;

    pub open spec fn consistent_with_pt(self, pt: PageTableView) -> bool {
        self.mappings <= pt.mappings
    }

    pub proof fn lemma_flush_preserves_inv(self, va: Vaddr)
        requires
            self.inv(),
        ensures
            self.flush(va).inv(),
    {
    }

    pub open spec fn issue_tlb_flush(self, op: TlbFlushOp) -> Self {
        TlbModel { pending: self.pending.push(op), mappings: self.mappings }
    }

    pub proof fn tracked_issue_tlb_flush(tracked &mut self, tracked op: TlbFlushOp)
        requires
            old(self).inv(),
        ensures
            *final(self) == old(self).issue_tlb_flush(op),
            final(self).inv(),
    {
        self.pending.tracked_push(op);
    }

    pub open spec fn dispatch_tlb_flush_spec(self) -> Self {
        let op = self.pending.last();
        let popped = TlbModel {
            pending: self.pending[..self.pending.len() - 1],
            mappings: self.mappings,
        };
        match op {
            TlbFlushOp::All => popped,
            TlbFlushOp::Address(va) => popped.flush(va),
            TlbFlushOp::Range(range) => popped.flush(range.start),
        }
    }
}

} // verus!
