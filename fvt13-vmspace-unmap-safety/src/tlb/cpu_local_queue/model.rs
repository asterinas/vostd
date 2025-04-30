use vstd::prelude::*;
use vstd::cell::PointsTo;
use core::ops::Range;
use aster_common::x86_64::mm::{PAGE_SIZE, MAX_NR_PAGES};
use aster_common::cpu::{CpuId, cpu_num};
use aster_common::mm::{Paddr, Vaddr};
use aster_common::tlb::TlbModel;
use aster_common::page::dyn_page::DynPage;
use aster_common::page::model::PageModel;
use aster_common::page::meta::{meta_slot_model::MetaSlotModel, page_usage::PageState};
use aster_common::tlb::{
    FLUSH_ALL_OPS_THRESHOLD, CONST_FLUSH_ALL_OPS_THRESHOLD, FLUSH_ALL_OPS_THRESHOLD_SPEC,
    TlbFlushOp,
};
use crate::spin::{SpinLockGuard, SpinLock};
use super::OpsStack;

verus! {

pub tracked struct OpsStackModel {
    pub ghost ops: Seq<TlbFlushOp>,
    pub need_flush_all: bool,
    pub ghost size: int,
}

impl OpsStackModel {
    pub open spec fn need_flush_all_spec(&self) -> bool {
        self.need_flush_all
    }

    pub proof fn lemma_need_flush_all_spec(&self)
        ensures
            self.need_flush_all == self.need_flush_all_spec(),
    {
    }

    pub open spec fn size_spec(&self) -> int {
        self.size as int
    }

    pub proof fn lemma_size_spec(&self)
        ensures
            self.size == self.size_spec(),
    {
    }

    pub open spec fn invariants(&self) -> bool {
        &&& self.need_flush_all == self.need_flush_all_spec()
        &&& self.size == self.size_spec()
        &&& self.ops.len() == self.size_spec()
        &&& 0 <= self.size_spec() < FLUSH_ALL_OPS_THRESHOLD_SPEC()
        &&& self.need_flush_all_spec() ==> self.size_spec() == 0
        &&& !self.ops.contains(TlbFlushOp::All)
    }

    // pub open spec fn relate(&self, op_stack: &OpsStack) -> bool {
    //     &&& op_stack.need_flush_all == self.need_flush_all
    //     &&& op_stack.size == self.size
    //     &&& op_stack.need_flush_all ==> { (self.ops =~= Seq::empty()) && (self.size == 0) }
    //     &&& !op_stack.need_flush_all ==> {
    //         forall |i: int| #![auto] 0 <= i < op_stack.size ==>
    //             op_stack.ops[i].unwrap() =~= self.ops[i]
    //     }
    // }
    // TODO:
    pub open spec fn vaddr_set_spec(&self) -> Set<int> {
        self.ops.map_values(|op: TlbFlushOp| { op.vaddr_set_spec().to_seq() }).flatten().to_set()
    }

    #[verifier::external_body]
    // TODO:
    pub proof fn axiom_vaddr_set_subset(self, vaddr_set: Set<int>)
        requires
            vaddr_set =~= self.vaddr_set_spec(),
        ensures
            forall|i: int|
                #![auto]
                0 <= i < self.ops.len() ==> self.ops[i].vaddr_set_spec().subset_of(vaddr_set),
    {
    }

    pub open spec fn new() -> Self {
        Self { ops: Seq::empty(), need_flush_all: false, size: 0 }
    }

    pub proof fn hold_invariants_after_new(&self)
        requires
            *self =~= Self::new(),
        ensures
            self.invariants(),
    {
    }

    pub open spec fn push(self, op: TlbFlushOp) -> Self {
        if op.is_flush_all() {
            Self { ops: Seq::empty(), need_flush_all: true, size: 0 }
        } else if self.need_flush_all_spec() {
            self
        } else {
            let new_size = self.size_spec() + 1;
            let need_flush_all = new_size == FLUSH_ALL_OPS_THRESHOLD_SPEC();
            let size = (if need_flush_all {
                0
            } else {
                new_size
            });
            let ops = if need_flush_all {
                Seq::empty()
            } else {
                self.ops.push(op)
            };
            Self { ops, need_flush_all, size }
        }
    }

    pub proof fn hold_invarians_after_push(self, op: TlbFlushOp) -> (res: Self)
        requires
            self.invariants(),
        ensures
            res =~= self.push(op),
            res.invariants(),
    {
        self.push(op)
    }

    pub open spec fn flush_all(self, tlb: TlbModel) -> (Self, TlbModel) {
        let new_tlb = if self.need_flush_all_spec() {
            tlb.clear()
        } else {
            tlb.flush_va_set(self.vaddr_set_spec())
        };

        (Self { ops: Seq::empty(), need_flush_all: false, size: 0 }, new_tlb)
    }

    pub proof fn hold_invariants_after_flush_all(self, flushed: Self, tlb: TlbModel)
        requires
            self.invariants(),
            flushed =~= self.flush_all(tlb).0,
        ensures
            flushed.invariants(),
    {
    }
    // pub proof fn lemma_tlb_flush(self, tlb: TlbModel) -> (res: (Self, TlbModel))
    //     requires
    //         self.invariants(),
    //     ensures
    //         res =~= self.flush_all(tlb),
    //         res.0.invariants(),
    //         forall |i: int| #![auto] 0 <= i < self.size_spec() ==> {
    //             res.1.op_issued(self.ops[i])
    //         },
    // {
    //     let new_tlb =
    //         if self.need_flush_all_spec() { tlb.clear() }
    //         else {
    //             let va_set = self.vaddr_set_spec();
    //             let new_tlb = tlb.flush_va_set(va_set);
    //             assert(forall |i: int| #![auto] 0 <= i < self.size_spec() ==>
    //                 self.ops[i].vaddr_set_spec().subset_of(va_set)
    //             ) by { self.axiom_vaddr_set_subset(va_set); };
    //             assert forall |i: int | #![auto] 0 <= i < self.size_spec() implies {
    //                 new_tlb.op_issued(self.ops[i])
    //             } by {
    //                 new_tlb.lemma_op_issued(self.ops[i]);
    //             };
    //             new_tlb
    //         };
    //     (Self {
    //         ops: Seq::empty(),
    //         need_flush_all: false,
    //         size: 0,
    //     }, new_tlb)
    // }

}

} // verus!
verus! {

pub tracked struct KeptPageModel {
    pub ghost page_paddr: int,
    pub ghost owner_cpus: Set<int>,
    pub op: TlbFlushOp,
}

impl KeptPageModel {
    pub open spec fn paddr_spec(&self) -> int {
        self.page_paddr
    }

    pub open spec fn cpu_is_owner(&self, cpu_id: int) -> bool {
        self.owner_cpus.contains(cpu_id)
    }

    pub open spec fn inv_owner(&self, page: &PageModel) -> bool {
        &&& page.relate_paddr(self.paddr_spec() as usize)
        &&& match page.state {
            PageState::Typed | PageState::Untyped => true,
            PageState::Unused => false,
        }
        &&& self.owner_cpus.finite()
        &&& self.owner_cpus.len() + page.owners.len() <= page.ref_count
        &&& page.ref_count > self.owner_cpus.len()
    }
    // pub open spec fn drop_spec(
    //     self,
    //     page: PageModel,
    //     cpu_id: int
    // ) -> (Self, PageModel) {
    //     (Self {
    //         page_perm: self.page_perm,
    //         owner_cpus: self.owner_cpus.remove(cpu_id),
    //         op: self.op,
    //     },
    //     PageModel {
    //         ref_count: page.ref_count - 1,
    //         ..page
    //     })
    // }
    // pub proof fn lemma_drop_spec(
    //     self,
    //     page: PageModel,
    //     cpu_id: int
    // ) -> (res: (Self, PageModel))
    //     requires
    //         self.inv_owner(&page),
    //         self.cpu_is_owner(cpu_id),
    //         page.invariants(),
    //     ensures
    //         res =~= self.drop_spec(page, cpu_id),
    //         res.0.inv_owner(&res.1),
    //         !res.0.cpu_is_owner(cpu_id),
    //         res.1.invariants(),
    // {
    //     (Self {
    //         page_perm: self.page_perm,
    //         owner_cpus: self.owner_cpus.remove(cpu_id),
    //         op: self.op,
    //     },
    //     PageModel {
    //         ref_count: page.ref_count - 1,
    //         ..page
    //     })
    // }

}

pub tracked struct KeptPageVecModel {
    pub ghost vec: Seq<KeptPageModel>,
}

impl KeptPageVecModel {
    pub open spec fn empty() -> Self {
        Self { vec: Seq::empty() }
    }

    pub open spec fn paddr_set_spec(&self) -> Seq<int> {
        self.vec.map_values(|kept_page: KeptPageModel| { kept_page.paddr_spec() as int })
    }

    #[verifier::external_body]
    // Here needs a lemma of 'vstd::map'.
    // We describe what the set should be.
    pub proof fn axiom_paddr_set_spec(&self, paddr_set: Seq<int>)
        requires
            paddr_set =~= self.paddr_set_spec(),
        ensures
            forall|i: int|
                #![auto]
                0 <= i < self.vec.len() ==> { paddr_set.contains(self.vec[i].paddr_spec() as int) },
    {
    }

    pub open spec fn paddr_to_idx(&self, paddr: int) -> int
        recommends
            self.invariants(),
    {
        self.paddr_set_spec().index_of(paddr)
    }

    pub open spec fn idx_to_paddr(&self, idx: int) -> int
        recommends
            0 <= idx < self.vec.len(),
    {
        self.vec[idx].paddr_spec() as int
    }

    pub proof fn lemma_all_paddrs_in_paddr_set(&self)
        requires
            self.invariants(),
        ensures
            forall|i: int|
                #![auto]
                0 <= i < self.vec.len() ==> { self.paddr_set_spec().contains(self.idx_to_paddr(i))
                },
    {
        let paddr_set = self.paddr_set_spec();
        assert(forall|i: int|
            #![auto]
            0 <= i < self.vec.len() ==> {
                self.paddr_set_spec().contains(self.vec[i].paddr_spec() as int)
            }) by {
            self.axiom_paddr_set_spec(paddr_set);
        }
    }

    pub open spec fn invariants(&self) -> bool {
        self.paddr_set_spec().no_duplicates()
    }

    pub open spec fn inv_owner(&self, pages: &Map<int, PageModel>) -> bool {
        forall|i: int|
            #![auto]
            0 <= i < self.vec.len() ==> {
                &&& 0 <= self.idx_to_paddr(i) < MAX_NR_PAGES()
                &&& self.vec[i].inv_owner(&pages[self.idx_to_paddr(i)])
            }
    }

    pub open spec fn cpu_is_owner(&self, cpu_id: int) -> bool {
        forall|i: int|
            #![trigger self.vec[i]]
            0 <= i < self.vec.len() ==> { self.vec[i].cpu_is_owner(cpu_id) }
    }
    // pub open spec fn clear(
    //     self,
    //     pages: Map<int, PageModel>,
    //     cpu_id: int,
    // ) -> (Self, Map<int, PageModel>) {
    //     let new_pages = pages.map_entries(|paddr: int, page: PageModel| {
    //         if self.paddr_set_spec().contains(paddr) {
    //             let kept_page = self.vec[self.paddr_to_idx(paddr)];
    //             kept_page.drop_spec(page, cpu_id).1
    //         } else { page }
    //     });
    //     (Self::empty(), new_pages)
    // }
    // pub proof fn lemma_clear(
    //     self,
    //     pages: Map<int, PageModel>,
    //     cpu_id: int,
    // ) -> (res: (Self, Map<int, PageModel>))
    //     requires
    //         self.invariants(),
    //         self.cpu_is_owner(cpu_id),
    //         self.inv_owner(&pages),
    //         forall |i: int| #![auto]
    //             0 <= i < MAX_NR_PAGES() <==> pages.dom().contains(i),
    //         forall |i: int| {
    //             0 <= i < MAX_NR_PAGES() ==> {
    //                 #[trigger] pages.dom().contains(i) &&
    //                 pages[i].index == i &&
    //                 pages[i].invariants()
    //             }
    //         },
    //     ensures
    //         res =~= self.clear(pages, cpu_id),
    //         res.0.invariants(),
    //         forall |i: int| #![auto]
    //             0 <= i < MAX_NR_PAGES() <==> res.1.dom().contains(i),
    //         forall |i: int| {
    //             0 <= i < MAX_NR_PAGES() ==> {
    //                 #[trigger] res.1.dom().contains(i) &&
    //                 res.1[i].index == i &&
    //                 res.1[i].invariants()
    //             }
    //         },
    // {
    //     let new_pages = pages.map_entries(|paddr: int, page: PageModel| {
    //         if self.paddr_set_spec().contains(paddr) {
    //             let kept_page = self.vec[self.paddr_to_idx(paddr)];
    //             kept_page.drop_spec(page, cpu_id).1
    //         } else { page }
    //     });
    //     // assert(forall |pa: int| pages.contains_key(pa) <==> new_pages.contains_key(pa));
    //     // assert(forall |pa: int| pages.contains_key(pa) ==> {
    //     //     if self.paddr_set_spec().contains(pa) {
    //     //         new_pages[pa] =~= self.vec[self.paddr_to_idx(pa)].drop_spec(pages[pa], cpu_id).1
    //     //     } else { new_pages[pa] =~= pages[pa] }
    //     // });
    //     // assert(forall |pa: int| !self.paddr_set_spec().contains(pa) ==> {
    //     //     (pages.contains_key(pa) && new_pages.contains_key(pa)) ==> {
    //     //         &&& 0 <= pa < MAX_NR_PAGES()
    //     //         &&& new_pages[pa] =~= pages[pa]
    //     //         &&& pages[pa].invariants()
    //     //         &&& new_pages[pa].invariants()
    //     //     }
    //     // });
    //     assert(forall |pa: int| #![auto] self.paddr_set_spec().contains(pa) ==> {
    //         &&& new_pages[pa].state =~= pages[pa].state
    //         &&& match pages[pa].state {
    //             PageState::Typed | PageState::Untyped => true,
    //             PageState::Unused => false,
    //         }
    //     });
    //     assert(forall |pa: int| #![auto] self.paddr_set_spec().contains(pa) ==> {
    //         &&& pages[pa].invariants()
    //         &&& self.vec[self.paddr_to_idx(pa)].inv_owner(&pages[pa])
    //         &&& new_pages[pa].ref_count == pages[pa].ref_count - 1
    //     });
    //     assert forall |pa: int| #![auto] self.paddr_set_spec().contains(pa) implies {
    //         new_pages[pa].invariants()
    //     } by {
    //         let res = self.vec[self.paddr_to_idx(pa)].lemma_drop_spec(pages[pa], cpu_id);
    //         assert(new_pages[pa] =~= res.1);
    //     };
    //     (Self::empty(), new_pages)
    // }

}

} // verus!
