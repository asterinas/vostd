// mod model;
use vstd::prelude::*;
use vstd::cell::PointsTo;
use vstd::rwlock::RwLock;
use vstd_extra::prelude::*;
use core::ops::Range;
use aster_common::x86_64::mm::{PAGE_SIZE, MAX_NR_PAGES};
use aster_common::cpu::{CpuId, valid_cpu, set::CpuSet, set::atomic::*, set::model::CpuSetModel};
use aster_common::mm::{Paddr, Vaddr};
use aster_common::page::dyn_page::DynPage;
use aster_common::page::model::PageModel;
use aster_common::page::meta::{meta_slot_model::MetaSlotModel, page_usage::PageState};
use aster_common::tlb::{TlbFlushOp, TlbModel};

extern_const!(
pub MAX_QUEUE_LEN [MAX_QUEUE_LEN_SPEC, CONST_MAX_QUEUE_LEN]: usize = 65536);

verus! {

struct DeferPage(TlbFlushOp, DynPage, AtomicCpuSet);

impl DeferPage {
    pub closed spec fn invariants(&self) -> bool {
        &&& self.0.invariants()
        &&& self.1.inv_ptr()
        &&& self.2.wf()
    }
    // pub closed spec fn is_same(&self, op_pair: (TlbFlushOp, DynPage), cpu: CpuSetModel) -> bool {
    //     &&& self.0 =~= op_pair.0
    //     &&& self.1 =~= op_pair.1
    //     &&& self.2.is_same(cpu)
    // }

}

pub open spec fn defer_page_vec_invariants(v: Seq<DeferPage>) -> bool {
    forall|i: int| #![auto] 0 <= i < v.len() ==> v[i].invariants()
}

struct DeferPagesArray {
    pages: RwLock<Vec<DeferPage>, spec_fn(Vec<DeferPage>) -> bool>,
}

impl DeferPagesArray {
    pub closed spec fn invariants(&self) -> bool {
        &&& forall|v: Vec<DeferPage>|
            #![auto]
            self.pages.pred()(v) <==> defer_page_vec_invariants(v@)
    }

    pub fn new() -> (res: Self)
        ensures
            res.invariants(),
    {
        Self {
            pages: RwLock::<Vec<DeferPage>, spec_fn(Vec<DeferPage>) -> bool>::new(
                Vec::new(),
                Ghost(|v: Vec<DeferPage>| defer_page_vec_invariants(v@)),
            ),
        }
    }

    // Recycle the pages that can be recycled.
    //
    // This should be called by the current CPU.
    pub fn recycle(&self)
        requires
            self.invariants(),
        ensures
    {
        let (mut pages, write_handle) = self.pages.acquire_write();
        let ghost pages_ghost = pages@;
        let mut all_cpu_sets = Vec::<CpuSet>::new();
        let mut new_pages = Vec::<DeferPage>::new();
        let mut cpu_sets = Vec::<CpuSet>::new();
        while pages.len() > 0
            invariant
                self.invariants(),
                self.pages.inv(pages),
                pages@.is_prefix_of(pages_ghost),
                new_pages@.len() == cpu_sets@.len(),
                all_cpu_sets@.len() + pages@.len() == pages_ghost.len(),
                forall|i: int|
                    #![auto]
                    0 <= i < cpu_sets@.len() ==> { !cpu_sets@[i].is_empty_spec() },
                defer_page_vec_invariants(new_pages@),
                forall|i: int|
                    #![auto]
                    pages@.len() <= i < pages_ghost.len() ==> {
                        !all_cpu_sets[pages_ghost.len() - i - 1].is_empty_spec()
                            ==> new_pages@.contains(pages_ghost[i])
                    },
            decreases pages.len(),
        {
            assert(pages@.len() > 0);
            let _len = pages.len();
            let defer_page = pages.pop().unwrap();
            assert(pages@.len() == _len - 1);
            assert(defer_page =~= pages_ghost[pages@.len() as int]);
            assert(defer_page.invariants());
            assert(forall|i: int|
                #![auto]
                pages@.len() < i < pages_ghost.len() ==> {
                    !all_cpu_sets[pages_ghost.len() - i - 1].is_empty_spec()
                        ==> new_pages@.contains(pages_ghost[i])
                });
            let cpu_set = defer_page.2.load();
            all_cpu_sets.push(cpu_set.clone());
            if !cpu_set.is_empty() {
                assert(!cpu_set.is_empty_spec());
                new_pages.push(defer_page);
                cpu_sets.push(cpu_set);
                // Actually the assumption is proved here.
                // It can be proved by Verus automatically before the vector 'push'.
                assume(forall|i: int|
                    #![auto]
                    pages@.len() < i < pages_ghost.len() ==> {
                        !all_cpu_sets[pages_ghost.len() - i - 1].is_empty_spec()
                            ==> new_pages@.contains(pages_ghost[i])
                    });
                assert(new_pages@.last() =~= defer_page);
                assert(new_pages@.contains(defer_page));
                assert(new_pages@.contains(pages_ghost[pages@.len() as int]));
            }
        }
        // We ensure that after 'recycle', all kept pages with empty 'target_cpus' are recycled.
        assert(forall|i: int|
            #![auto]
            0 <= i < cpu_sets@.len() ==> { !cpu_sets@[i].is_empty_spec() });
        write_handle.release_write(new_pages);
    }

    /// Adds the pages to the array.
    ///
    /// This should be called by the current CPU.
    pub fn add(&mut self, mut defers: Vec<(TlbFlushOp, DynPage)>, target_cpus: CpuSet)
        requires
            old(self).invariants(),
            defers@.len() <= MAX_QUEUE_LEN_SPEC(),
            forall|i: int|
                #![auto]
                0 <= i < defers@.len() ==> {
                    &&& defers@[i].0.invariants()
                    &&& defers@[i].1.inv_ptr()
                },
            target_cpus.invariants(),
        ensures
            self.invariants(),
    {
        if defers.len() == 0 {
            return ;
        }
        let (mut pages, write_handle) = self.pages.acquire_write();
        assert(self.pages.inv(pages));
        assert(self.pages.pred()(pages) <==> self.pages.inv(pages));
        assert(self.pages.pred()(pages) <==> defer_page_vec_invariants(pages@));
        assert(forall|i: int| #![auto] 0 <= i < pages@.len() ==> { pages@[i].invariants() });
        let defers_len = defers.len();
        let ghost defers_ghost = defers@;
        let pages_len = pages.len();
        let mut inserted = 0;
        while !(defers.len() == 0)
            invariant
                defers_len <= MAX_QUEUE_LEN_SPEC(),
                forall|i: int|
                    #![auto]
                    0 <= i < defers_ghost.len() ==> {
                        &&& defers_ghost[i].0.invariants()
                        &&& defers_ghost[i].1.inv_ptr()
                    },
                target_cpus.invariants(),
                forall|i: int| #![auto] 0 <= i < pages@.len() ==> { pages@[i].invariants() },
                0 <= inserted <= defers_len,
                pages@.len() == pages_len + inserted,
                defers@.len() == defers_len - inserted,
                defers@.is_prefix_of(
                    defers_ghost,
                ),
        // forall |i: int| #![trigger pages_len + i] 0 <= i < inserted ==> {
        //     &&& pages@[pages_len + i].0 =~= defers_ghost[defers_len - i - 1].0
        //     &&& pages@[pages_len + i].1 =~= defers_ghost[defers_len - i - 1].1
        // },

            ensures
                inserted == defers_len,
                defers@.len() == 0,
                defers@ =~= Seq::empty(),
            decreases defers.len(),
        {
            assert(defers@.len() > 0);
            let _len = defers.len();
            assert(defers@.last() =~= defers_ghost[defers_len - inserted - 1]);
            let (op, page) = defers.pop().unwrap();
            assert(defers@.len() == _len - 1);
            assert(op =~= defers_ghost[defers_len - inserted - 1].0);
            assert(page =~= defers_ghost[defers_len - inserted - 1].1);
            let defer_page = DeferPage(op, page, AtomicCpuSet::new(target_cpus.clone()));
            assert(defer_page.invariants());
            // assert(defer_page.is_same(defers_ghost[defers_len - inserted - 1], target_cpus@));
            pages.push(defer_page);
            // assert(pages@[pages_len + inserted].is_same(defers_ghost[defers_len - inserted - 1], target_cpus@));
            inserted += 1;
        }
        write_handle.release_write(pages);
        // I don't know that for a mut type, how to refer to the mutted value in post-condition.
        assert(defers@.len() == 0);
        assert(defers@ =~= Seq::empty());
    }

    /// Check the remote CPU's requests and process them.
    ///
    /// This should be called by the other CPUs.
    pub fn process_remote_requests(&self, current: CpuId, Tracked(tlb): Tracked<TlbModel>) -> (res:
        Tracked<TlbModel>)
        requires
            self.invariants(),
            valid_cpu(current@),
        ensures
            self.invariants(),
    {
        let read_handle = self.pages.acquire_read();
        let pages = read_handle.borrow();
        let ghost pages_ghost = pages@;
        let mut tokens: Vec::<Ghost<AtomicCpuSetSpec::cpu_set_inv>> = Vec::new();
        for i in 0..pages.len()
            invariant
                0 <= i <= pages@.len(),
                pages@ =~= pages_ghost,
                self.invariants(),
                valid_cpu(current@),
                self.pages.inv(*pages),
                tokens@.len() == i,
                forall|j: int|
                    #![auto]
                    0 <= j < i ==> { pages_ghost[j].2.token_val(tokens@[j]@, current@) },
        {
            let op = &pages[i].0;
            let _page = &pages[i].1;
            let target_cpus = &pages[i].2;
            let ghost mut token;
            let (b, Ghost(_token)) = target_cpus.contains(current);
            if b {
                let tracked _tlb = TlbModel { ..tlb };
                let __tlb = op.perform_on_current(Tracked(_tlb));
                // Pre-condition.
                // Only when the Tlb request is issued can the cpu be removed
                // from the 'target_cpus' set.
                assert(__tlb@.op_issued(*op));
                // Here the token is persistent, which represents that
                // the current cpu is removed from the 'target_cpus' forever.
                let Ghost(token_removed) = target_cpus.remove(current);
                assert(target_cpus.token_val(token_removed, current@));
                proof {
                    token = token_removed;
                }
            } else {
                proof {
                    token = _token;
                }
            }
            assert(target_cpus.token_val(token, current@));
            tokens.push(Ghost(token));
        }
        // We ensure that the current CPU has issued all Tlb flush requests it found.
        assert(forall|i: int|
            #![auto]
            0 <= i < pages@.len() ==> { pages_ghost[i].2.token_val(tokens@[i]@, current@) });
        read_handle.release_read();
        Tracked(tlb)
    }
}

} // verus!
