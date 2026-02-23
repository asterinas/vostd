use vstd::prelude::*;

use crate::specs::mm::cpu::*;
use crate::specs::mm::page_table::*;
use crate::mm::{Vaddr, Paddr};
use crate::mm::tlb::TlbFlushOp;

use vstd::set;
use vstd_extra::ownership::*;

verus! {

pub struct TlbModel {
    pub pending: Seq<TlbFlushOp>,
    pub mappings: Set<Mapping>
}

impl Inv for TlbModel {
    open spec fn inv(self) -> bool {
        &&& forall|m: Mapping| #![auto] self.mappings has m ==> m.inv()
        &&& forall|m: Mapping, n:Mapping| #![auto]
            self.mappings has m ==>
            self.mappings has n ==>
            m != n ==>
            Mapping::disjoint_vaddrs(m, n)
        &&& forall|m: Mapping, n:Mapping| #![auto]
            self.mappings has m ==>
            self.mappings has n ==>
            m != n ==>
            Mapping::disjoint_paddrs(m, n)
    }
}

impl TlbModel {
    pub open spec fn update_spec(self, pt: PageTableView, va: Vaddr) -> Self
    {
        let m = pt.mappings.filter(|m: Mapping| m.va_range.start <= va < m.va_range.end).choose();
        TlbModel {
            pending: self.pending,
            mappings: self.mappings.insert(m),
        }
    }

    pub axiom fn update(&mut self, pt: PageTableView, va: Vaddr)
        requires
            old(self).inv(),
            forall|m: Mapping| old(self).mappings has m ==> !(m.va_range.start <= va < m.va_range.end),
            exists|m: Mapping| pt.mappings has m ==> m.va_range.start <= va < m.va_range.end,
        ensures
            *self == old(self).update_spec(pt, va);

    pub open spec fn flush_spec(self, va: Vaddr) -> Self
    {
        let m = self.mappings.filter(|m: Mapping| m.va_range.start <= va < m.va_range.end);
        TlbModel {
            pending: self.pending,
            mappings: self.mappings - m,
        }
    }

    pub axiom fn flush(&mut self, va: Vaddr)
        requires
            old(self).inv(),
        ensures
            *self == old(self).flush_spec(va);

    pub open spec fn consistent_with_pt(self, pt: PageTableView) -> bool {
        self.mappings <= pt.mappings
    }

    pub proof fn lemma_flush_preserves_inv(self, va: Vaddr)
        requires
            self.inv(),
        ensures
            self.flush_spec(va).inv()
    { }

    pub proof fn lemma_update_preserves_consistent(self, pt: PageTableView, va: Vaddr)
        requires
            pt.inv(),
            self.inv(),
            self.consistent_with_pt(pt),
            exists|m: Mapping| pt.mappings has m && m.va_range.start <= va < m.va_range.end,
        ensures
            self.update_spec(pt, va).consistent_with_pt(pt),
    {
        let filtered = pt.mappings.filter(|m: Mapping| m.va_range.start <= va < m.va_range.end);
        let m = filtered.choose();

        let witness: Mapping = choose|a: Mapping| pt.mappings has a && a.va_range.start <= va < a.va_range.end;
        assert(filtered.contains(witness));

        if self.mappings.contains(m) {
            assert(self.mappings.insert(m) =~= self.mappings);
        } else {
            assert(filtered.contains(m));
            assert(pt.mappings.contains(m));
        }
    }

    pub proof fn lemma_consistent_with_pt_implies_inv(self, pt: PageTableView)
        requires
            self.inv(),
            self.consistent_with_pt(pt),
            pt.inv(),
        ensures
            self.inv()
    { }

    pub open spec fn issue_tlb_flush_spec(self, op: TlbFlushOp) -> Self
    {
        TlbModel {
            pending: self.pending.push(op),
            mappings: self.mappings,
        }
    }

    pub proof fn issue_tlb_flush(tracked &mut self, tracked op: TlbFlushOp)
        requires
            old(self).inv(),
        ensures
            *self == old(self).issue_tlb_flush_spec(op),
            self.inv()
        {
            self.pending.tracked_push(op);
        }

    pub open spec fn dispatch_tlb_flush_spec(self) -> Self
    {
        let op = self.pending.last();
        let popped = TlbModel {
            pending: self.pending.take(self.pending.len() - 1),
            mappings: self.mappings,
        };
        match op {
            TlbFlushOp::All => popped,
            TlbFlushOp::Address(va) => popped.flush_spec(va),
            TlbFlushOp::Range(range) => popped.flush_spec(range.start),
        }
    }

}

}
