#[allow(unused_imports)]
use vstd::prelude::*;
use aster_common::x86_64::PageTableEntry;
use aster_common::page_table::PageTableModel;
use super::local_queue::TlbFlushOp;

verus! {

pub tracked struct TlbModel {
    pub ghost pt_paddr: int,
    pub ghost mapped: Map<int, Option<PageTableEntry>>,
}

impl TlbModel {
    pub open spec fn clear(self) -> Self {
        TlbModel { pt_paddr: self.pt_paddr, mapped: Map::empty() }
    }

    pub open spec fn relate_page_table(&self, pt: PageTableModel) -> bool {
        self.pt_paddr == pt.base && forall|va| #[trigger]
            self.mapped.contains_key(va) ==> pt.mapped.contains_key(va)
    }

    pub open spec fn has_tlb_entry(&self, va: int) -> bool {
        self.mapped.contains_key(va)
    }

    pub open spec fn flush_va(self, va: int) -> Self {
        Self { pt_paddr: self.pt_paddr, mapped: self.mapped.remove(va) }
    }

    pub open spec fn flush_va_set(self, va_set: Seq<int>) -> Self {
        Self { pt_paddr: self.pt_paddr, mapped: self.mapped.remove_keys(va_set.to_set()) }
    }

    pub proof fn lemma_flush_va_set(&self, flushed: Self, va_set: Seq<int>)
        requires
            flushed =~= self.flush_va_set(va_set),
        ensures
            forall|va: int| #![auto] va_set.contains(va) ==> !flushed.has_tlb_entry(va),
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
                assert(op.vaddr_set_spec().contains(vaddr as int)) by { op.axiom_vaddr_set_spec() };
            },
            TlbFlushOp::Range(r) => {
                assert(forall|va: int|
                    r.start <= va < r.end ==> { op.vaddr_set_spec().contains(va) }) by {
                    op.axiom_vaddr_set_spec()
                };
            },
            TlbFlushOp::All => (),
        }
    }
}

} // verus!
