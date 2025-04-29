use vstd::prelude::*;
use crate::x86_64::PageTableEntry;
use crate::prelude::Vaddr;
use crate::page_table::PageTableModel;
use super::{TlbFlushOp, align::*};

verus! {

pub tracked struct TlbModel {
    pub ghost pt_paddr: int,
    pub ghost cached: Map<int, Option<PageTableEntry>>,
}

impl TlbModel {
    pub open spec fn clear(self) -> Self {
        TlbModel { pt_paddr: self.pt_paddr, cached: Map::empty() }
    }

    pub open spec fn relate_page_table(&self, pt: PageTableModel) -> bool {
        self.pt_paddr == pt.tree.root_paddr() && forall|va| #[trigger]
            self.cached.contains_key(va) ==> pt.flat.contains_key(va as Vaddr)
    }

    pub open spec fn has_tlb_entry(&self, va: int) -> bool {
        self.cached.contains_key(va)
    }

    #[verifier::external_body]
    pub proof fn axiom_tlb_flush_amplify(&self, va: int)
        ensures
            !self.has_tlb_entry(va) ==> {
                forall|_va: int|
                    #![auto]
                    va_expansion(va).contains(_va) ==> { !self.has_tlb_entry(_va) }
            },
    {
    }

    pub open spec fn flush_va(self, va: int) -> Self {
        Self { pt_paddr: self.pt_paddr, cached: self.cached.remove_keys(va_expansion(va)) }
    }

    pub proof fn lemma_flush_va(self, flushed: Self, va: int)
        requires
            flushed =~= self.flush_va(va),
        ensures
            forall|_va: int|
                #![auto]
                va_expansion(va).contains(_va) ==> { !flushed.has_tlb_entry(_va) },
    {
    }

    pub open spec fn flush_va_set(self, va_set: Set<int>) -> Self
        recommends
            va_set.finite(),
    {
        Self { pt_paddr: self.pt_paddr, cached: self.cached.remove_keys(va_set_expansion(va_set)) }
    }

    pub proof fn lemma_flush_va_set(&self, flushed: Self, va_set: Set<int>)
        requires
            va_set.finite(),
            flushed =~= self.flush_va_set(va_set),
        ensures
            forall|va: int| #![auto] va_set.contains(va_base(va)) ==> !flushed.has_tlb_entry(va),
    {
    }

    pub open spec fn op_issued(&self, op: TlbFlushOp) -> bool {
        match op {
            TlbFlushOp::Address(vaddr) => { !self.has_tlb_entry(vaddr as int) },
            TlbFlushOp::Range(r) => {
                forall|vaddr: int| r.start <= vaddr < r.end ==> !self.has_tlb_entry(vaddr as int)
            },
            TlbFlushOp::All => true,
        }
    }

    pub proof fn lemma_op_issued(&self, op: TlbFlushOp)
        requires
            op.is_flush_all() || {
                !op.is_flush_all() && {
                    forall|va: int|
                        #![auto]
                        op.vaddr_set_spec().contains(va) ==> !self.has_tlb_entry(va)
                }
            },
        ensures
            self.op_issued(op),
    {
        match op {
            TlbFlushOp::Address(vaddr) => {
                assert(op.vaddr_set_spec().contains(vaddr as int)) by { op.lemma_vaddr_set_element()
                };
            },
            TlbFlushOp::Range(r) => {
                assert(forall|va: int|
                    r.start <= va < r.end ==> { op.vaddr_set_spec().contains(va) }) by {
                    op.lemma_vaddr_set_element()
                };
            },
            TlbFlushOp::All => (),
        }
    }
}

} // verus!
