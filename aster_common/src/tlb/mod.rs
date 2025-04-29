pub mod align;
pub mod flush;
pub mod model;

use vstd::prelude::*;
use vstd_extra::prelude::*;
use core::ops::Range;
use crate::x86_64::mm::CONST_PAGE_SIZE;
use crate::mm::Vaddr;

pub use flush::*;
pub use model::*;

extern_const!(
/// If a TLB flushing request exceeds this threshold, we flush all.
pub FLUSH_ALL_RANGE_THRESHOLD [FLUSH_ALL_RANGE_THRESHOLD_SPEC, CONST_FLUSH_ALL_RANGE_THRESHOLD]: usize = 32 * CONST_PAGE_SIZE);

extern_const!(
/// If the number of pending requests exceeds this threshold, we flush all the
/// TLB entries instead of flushing them one by one.
pub FLUSH_ALL_OPS_THRESHOLD [FLUSH_ALL_OPS_THRESHOLD_SPEC, CONST_FLUSH_ALL_OPS_THRESHOLD]: usize = 32);

verus! {

/// The operation to flush TLB entries.
#[derive(Debug)]
pub enum TlbFlushOp {
    /// Flush all TLB entries except for the global entries.
    All,
    /// Flush the TLB entry for the specified virtual address.
    Address(Vaddr),
    /// Flush the TLB entries for the specified virtual address range.
    Range(Range<Vaddr>),
}

impl TlbFlushOp {
    pub open spec fn invariants(&self) -> bool {
        &&& if let Self::Address(va) = *self {
            align::va_is_aligned(va as int)
        } else if let Self::Range(r) = *self {
            &&& r.start <= r.end
            &&& align::va_is_aligned(r.start as int)
        } else {
            true
        }
    }

    pub open spec fn is_flush_all(&self) -> bool {
        if let Self::All = self {
            true
        } else {
            false
        }
    }

    pub open spec fn va_to_set(vaddr: Vaddr) -> Set<int> {
        Set::empty().insert(vaddr as int)
    }

    pub proof fn lemma_va_to_set(va: Vaddr)
        ensures
            Self::va_to_set(va).len() == 1,
    {
    }

    pub open spec fn range_to_set(r: &Range<Vaddr>) -> Set<int>
        recommends
            r.start <= r.end,
    {
        Set::new(|va: int| { r.start <= va < r.end })
    }

    #[verifier::external_body]
    pub proof fn axiom_range_to_set(r: &Range<Vaddr>)
        requires
            r.start <= r.end,
        ensures
            Self::range_to_set(r).to_seq().min() == r.start,
            Self::range_to_set(r).len() == r.end - r.start,
    {
        // I think this can prove the second postcondition, but Verus doesn't think so...
        assert(forall|va: int| Self::range_to_set(r).contains(va) <==> r.start <= va < r.end);
    }

    pub open spec fn vaddr_set_spec(self) -> Set<int>
        recommends
            !self.is_flush_all(),
    {
        if let Self::Address(vaddr) = self {
            Self::va_to_set(vaddr)
        } else if let Self::Range(r) = self {
            Self::range_to_set(&r)
        } else {
            Set::empty()
        }
    }

    pub proof fn lemma_vaddr_set_element(self)
        requires
            !self.is_flush_all(),
        ensures
            if let Self::Address(vaddr) = self {
                self.vaddr_set_spec().contains(vaddr as int)
            } else if let Self::Range(r) = self {
                forall|va: int|
                    #![auto]
                    r.start <= va < r.end ==> self.vaddr_set_spec().contains(va)
            } else {
                true
            },
    {
    }

    /// Performs the TLB flush operation on the current CPU.
    pub fn perform_on_current(&self, Tracked(tlb): Tracked<TlbModel>) -> (res: Tracked<TlbModel>)
        requires
            self.invariants(),
        ensures
            res@.op_issued(*self),
    {
        match self {
            TlbFlushOp::All => tlb_flush_all_excluding_global(Tracked(tlb)),
            TlbFlushOp::Address(addr) => tlb_flush_addr(*addr, Tracked(tlb)),
            TlbFlushOp::Range(range) => {
                assert(align::va_set_is_aligned(Self::range_to_set(range))) by {
                    Self::axiom_range_to_set(range);
                }
                tlb_flush_addr_range(range, Tracked(tlb))
            },
        }
    }

    pub(super) fn optimize_for_large_range(self) -> (res: Self)
        requires
            self.invariants(),
        ensures
            res.invariants(),
    {
        match self {
            TlbFlushOp::Range(range) => {
                if range.end - range.start > FLUSH_ALL_RANGE_THRESHOLD() {
                    TlbFlushOp::All
                } else {
                    TlbFlushOp::Range(range)
                }
            },
            _ => self,
        }
    }
}

} // verus!
