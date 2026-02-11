use vstd::prelude::*;

use crate::specs::mm::cpu::*;

verus! {

pub struct TlbModel {
    pub mappings: Set<Mapping>
}

impl Inv for TlbModel {
    open spec fn inv(self) -> bool {
        &&& forall|m: Mapping| m in self.mappings ==> m.inv()
        &&& forall|m: Mapping| m in self.mappings ==> m.va % m.page_size == 0
        &&& forall|m: Mapping| m in self.mappings ==> m.pa % m.page_size == 0
        &&& forall|m: Mapping| m in self.mappings ==> set![4096, 2097152, 1073741824].contains(m.page_size)
        &&& forall|m: Mapping| forall|n: Mapping|
            m in self.mappings ==>
            n in self.mappings ==> {
                &&& m.va + m.page_size <= n.va || n.va + n.page_size <= m.va
                &&& m.pa + m.page_size <= n.pa || n.pa + n.page_size <= m.pa
            }
    }
}

impl TlbModel {
    pub open spec fn update_spec(self, pt: PageTableView, va: Vaddr) -> Self
    {
        let m = pt.mappings.filter(|m: Mapping| m.va_range.start <= va < m.va_range.end).choose();
        TlbModel {
            mappings: self.mappings.insert(m),
        }
    }

    pub axiom fn update(&mut self, pt: PageTableView, va: Vaddr)
        requires
            old(self).inv(),
            forall|m: Mapping| self.mappings.contains(m) ==> !(m.va_range.start <= va < m.va_range.end),
            exists|m: Mapping| pt.mappings.contains(m) ==> m.va_range.start <= va < m.va_range.end,
        ensures
            *self == old(self).update_spec(pt, va);

    pub open spec fn flush_spec(self, va: Vaddr) -> Self
    {
        let m = self.mappings.filter(|m: Mapping| m.va_range.start <= va < m.va_range.end);
        TlbModel {
            mappings: self.mappings - m,
        }
    }

    pub axiom fn flush(&mut self, va: Vaddr)
        requires
            old(self).inv(),
        ensures
            *self == old(self).flush_spec(va);

    pub proof fn lemma_flush_preserves_inv(self, va: Vaddr)
        requires
            self.inv(),
        ensures
            self.flush_spec(va).inv()
    {
        admit()
    }

    pub proof fn lemma_update_preserves_inv(self, pt: PageTableView, va: Vaddr)
        requires
            pt.inv(),
            self.inv(),
        ensures
            self.update_spec(pt, va).inv()
    {
        admit()
    }
}

}