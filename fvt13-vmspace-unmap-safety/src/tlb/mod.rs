mod cpu_local_queue;
// pub mod local_queue;
// pub mod model;

use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use aster_common::x86_64::mm::{PAGE_SIZE, MAX_NR_PAGES};
use aster_common::cpu::PinCurrentCpu;
use aster_common::task::{disable_preempt, DisabledPreemptGuard};
use aster_common::mm::{Paddr, Vaddr};
use aster_common::page::meta::page_usage::PageState;
use crate::spin::{SpinLockGuard, SpinLock};

verus! {

// fn do_remote_flush(Tracked(s): Tracked<AbstractModel>) -> (res: Tracked<AbstractModel>)
//     requires
//         s.invariants(),
//     ensures
//         res@.invariants(),
// {
//     let preempt_guard = disable_preempt();
//     let current_cpu = preempt_guard.current_cpu();
//     // Here we proof that:
//     // The kept page handles can be dropped safely
//     // since all the cached ptes on the current cpu have been evicted.
//     let tracked mut res: AbstractModel;
//     proof {
//         let pages = s.pages;
//         let tlb_queue = s.tlb_queues[current_cpu.cpu_id_spec() as int];
//         let tlb = s.tlbs[current_cpu.cpu_id_spec() as int];
//         let op_queue = tlb_queue.flush_ops;
//         let page_keeper = tlb_queue.page_keeper;
//         // Propert0 (pre-condition):
//         //  1. All kept pages are 'used' page.
//         //  2. Cpu owners of kept pages also contribute to the reference count.
//         assert(forall |i: int| 0 <= i < page_keeper.vec.len() ==> {
//             let pa = #[trigger] page_keeper.idx_to_paddr(i);
//             &&& pages.contains_key(pa)
//             &&& match pages[pa].state {
//                 PageState::Typed | PageState::Untyped => true,
//                 PageState::Unused => false,
//             }
//             &&& pages[pa].ref_count > page_keeper.vec[i].owner_cpus.len()
//             &&& pages[pa].ref_count >= page_keeper.vec[i].owner_cpus.len() + pages[pa].owners.len()
//         });
//         // Propert1:
//         // The current cpu is one of the owners of all kept pages in `page_keeper` queue.
//         // 'Owner' is a logical concept here. It presents that
//         // the cpu's tlb may have a cached-pte which points to the kept page.
//         assert(forall |i: int| #![auto] 0 <= i < page_keeper.vec.len() ==> {
//             page_keeper.vec[i].cpu_is_owner(current_cpu.cpu_id_spec() as int)
//         });
//         let _res = op_queue.flush_all(tlb);
//         let (new_op_queue, new_tlb) = _res;
//         // Propert2:
//         // We proof that after issueing all tlb flush requests,
//         // the cpu's tlb is impossible to have a cached-pte pointing to the kept page.
//         // So the current cpu is no longer the owner of kept pages.
//         // Therefore we can drop all kept page handlers safely.
//         assert(forall |i: int| #![auto] 0 <= i < op_queue.size_spec() ==> {
//             new_tlb.op_issued(op_queue.ops[i])
//         }) by {
//             let res = op_queue.lemma_tlb_flush(tlb);
//             assert(new_tlb =~= res.1);
//         };
//         let _res = page_keeper.clear(pages, current_cpu.cpu_id_spec() as int);
//         let (new_page_keeper, new_pages) = _res;
//         // Property3:
//         //  1. `new_pages` model also holds the 'PageModel::invariants'.
//         //  2. Reference counts of kept pages are decreasing by 1.
//         assert(new_page_keeper =~= KeptPageVecModel::empty());
//         assert(forall |i: int| #![auto] {
//             &&& forall |i: int| #![auto]
//                 0 <= i < MAX_NR_PAGES() <==> new_pages.dom().contains(i)
//             &&& 0 <= i < MAX_NR_PAGES() ==> {
//                 new_pages.dom().contains(i) &&
//                 new_pages[i].index == i &&
//                 new_pages[i].invariants()
//             }
//         }) by {
//             let res = page_keeper.lemma_clear(pages, current_cpu.cpu_id_spec() as int);
//             assert(new_pages =~= res.1);
//         };
//         assert forall |i: int| 0 <= i < page_keeper.vec.len() implies {
//             let pa = #[trigger] page_keeper.idx_to_paddr(i);
//             new_pages[pa].ref_count == pages[pa].ref_count - 1
//         } by {
//             let pa = page_keeper.idx_to_paddr(i);
//             assert(page_keeper.paddr_set_spec().contains(pa)) by {
//                 page_keeper.lemma_all_paddrs_in_paddr_set();
//             };
//             let res = page_keeper.vec[i].lemma_drop_spec(pages[pa], current_cpu.cpu_id_spec() as int);
//             assert(new_pages[pa] =~= res.1);
//         };
//         res = AbstractModel {
//             tlb_queues: s.tlb_queues.update(
//                 current_cpu.cpu_id_spec() as int,
//                 TlbQueueModel {
//                     flush_ops: new_op_queue,
//                     page_keeper: new_page_keeper,
//                 }
//             ),
//             tlbs: s.tlbs.update(
//                 current_cpu.cpu_id_spec() as int,
//                 new_tlb,
//             ),
//             pages: new_pages,
//         }
//     }
//     assert(res.tlb_queues[current_cpu.cpu_id_spec() as int].page_keeper.inv_owner(&res.pages));
//     // TODO:
//     // 'KeptPageModel::owner_cpus' is a shared data among all cpus.
//     // Here we ignore the fact inorder to bypass the verification of concurrent codes.
//     assume(forall |i: int| #![auto] 0 <= i < MAX_NR_PAGES() ==> {
//         res.tlb_queues[i].page_keeper.inv_owner(&res.pages)
//     });
//     Tracked(res)
// }

} // verus!
verus! {

// /// A TLB flusher that is aware of which CPUs are needed to be flushed.
// ///
// /// The flusher needs to stick to the current CPU.
// pub struct TlbFlusher<'a, G: PinCurrentCpu> {
//     // cpus: Option<&'a AtomicCpuSet>,
//     target_cpus: CpuSet,
//     // Better to store them here since loading and counting them from the CPUs
//     // list brings non-trivial overhead.
//     need_remote_flush: bool,
//     need_self_flush: bool,
//     current_cpu: CpuId,
//     _pin_current: G,
// }
// impl<'a, G: PinCurrentCpu> TlbFlusher<'a, G> {
//     /// Creates a new TLB flusher with the specified CPUs to be flushed.
//     ///
//     /// The flusher needs to stick to the current CPU. So please provide a
//     /// guard that implements [`PinCurrentCpu`].
//     // pub fn new(cpus: Option<&'a AtomicCpuSet>, pin_current_guard: G) -> Self {
//     //     let target_cpus =
//     //         if cpus.is_some() { cpus.unwrap().load() }
//     //         else { CpuSet::new_full() };
//     //     let current_cpu = pin_current_guard.current_cpu();
//     //     let mut need_self_flush = false;
//     //     let mut need_remote_flush = false;
//     //     for cpu in target_cpus.iter() {
//     //         if cpu == current_cpu {
//     //             need_self_flush = true;
//     //         } else {
//     //             need_remote_flush = true;
//     //         }
//     //     }
//     //     Self {
//     //         cpus,
//     //         target_cpus,
//     //         need_remote_flush,
//     //         need_self_flush,
//     //         current_cpu,
//     //         _pin_current: pin_current_guard,
//     //     }
//     // }
//     // pub fn update_cpu(&mut self) {
//     //     if self.cpus.is_none() { return };
//     //     let target_cpus = self.cpus.unwrap().load();
//     //     let current_cpu = self.current_cpu;
//     //     let mut need_self_flush = false;
//     //     let mut need_remote_flush = false;
//     //     for cpu in target_cpus.iter() {
//     //         if cpu == current_cpu {
//     //             need_self_flush = true;
//     //         } else {
//     //             need_remote_flush = true;
//     //         }
//     //     }
//     //     self.target_cpus = target_cpus;
//     //     self.need_self_flush = need_self_flush;
//     //     self.need_remote_flush = need_remote_flush;
//     // }
//     /// Issues a pending TLB flush request.
//     ///
//     /// On SMP systems, the notification is sent to all the relevant CPUs only
//     /// when [`Self::dispatch_tlb_flush`] is called.
//     pub fn issue_tlb_flush(&self, op: TlbFlushOp) {
//         self.issue_tlb_flush_(op, None);
//     }
//     /// Dispatches all the pending TLB flush requests.
//     ///
//     /// The pending requests are issued by [`Self::issue_tlb_flush`].
//     pub fn dispatch_tlb_flush(&self) {
//         if !self.need_remote_flush {
//             return;
//         }
//         crate::smp::inter_processor_call(&self.target_cpus, do_remote_flush);
//     }
//     /// Issues a TLB flush request that must happen before dropping the page.
//     ///
//     /// If we need to remove a mapped page from the page table, we can only
//     /// recycle the page after all the relevant TLB entries in all CPUs are
//     /// flushed. Otherwise if the page is recycled for other purposes, the user
//     /// space program can still access the page through the TLB entries. This
//     /// method is designed to be used in such cases.
//     pub fn issue_tlb_flush_with(&self, op: TlbFlushOp, drop_after_flush: DynPage) {
//         self.issue_tlb_flush_(op, Some(drop_after_flush));
//     }
//     /// Whether the TLB flusher needs to flush the TLB entries on other CPUs.
//     pub fn need_remote_flush(&self) -> bool {
//         self.need_remote_flush
//     }
//     /// Whether the TLB flusher needs to flush the TLB entries on the current CPU.
//     pub fn need_self_flush(&self) -> bool {
//         self.need_self_flush
//     }
//     fn issue_tlb_flush_(&self, op: TlbFlushOp, drop_after_flush: Option<DynPage>) {
//         let op = op.optimize_for_large_range();
//         // Fast path for single CPU cases.
//         if !self.need_remote_flush {
//             if self.need_self_flush {
//                 op.perform_on_current();
//             }
//             return;
//         }
//         // Slow path for multi-CPU cases.
//         for cpu in self.target_cpus.iter() {
//             let mut op_queue = FLUSH_OPS.get_on_cpu(cpu).lock();
//             if let Some(drop_after_flush) = drop_after_flush.clone() {
//                 PAGE_KEEPER.get_on_cpu(cpu).lock().push(drop_after_flush);
//             }
//             op_queue.push(op.clone());
//         }
//     }
// }

} // verus!
