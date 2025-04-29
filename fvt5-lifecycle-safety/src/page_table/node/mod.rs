pub mod model;
pub mod specs;

extern crate vstd_extra;

use vstd::prelude::*;
use vstd::cell;
use core::marker::PhantomData;
use crate::common::*;
use crate::page::{*, model::*};
use super::*;
use crate::rust_core_mem::*;
use aster_common::prelude::*;

verus! {

impl RawPageTableNode {
    #[rustc_allow_incoherent_impl]
    pub open spec fn relate(self, model: PageTableNodeValue) -> bool {
        self.paddr() == model.paddr()
    }

    #[rustc_allow_incoherent_impl]
    pub fn inc_ref_count(&self, Tracked(s): Tracked<AbstractState>) -> (res: Tracked<AbstractState>)
        requires
            self.has_valid_paddr(),
            self.relate_model(s.get_page(self.paddr())),
            s.invariants(),
            s.get_page(self.paddr()).ref_count < u32::MAX,
        ensures
            Self::inc_ref_count_spec(*self, s, res@),
            res@.invariants(),
    {
        //inc_page_ref_count(self.paddr());
        inc_page_ref_count(self.paddr(), Tracked(s))
    }

    #[rustc_allow_incoherent_impl]
    pub fn clone_shallow(&self, Tracked(s): Tracked<AbstractState>) -> (res: (
        Self,
        Tracked<AbstractState>,
    ))
        requires
            self.has_valid_paddr(),
            self.relate_model(s.get_page(self.paddr())),
            s.invariants(),
            s.get_page(self.paddr()).ref_count < u32::MAX,
        ensures
            Self::clone_shallow_spec(*self, s, res.1@),
            res.0.relate_model(res.1@.get_page(self.paddr())),
            res.1@.invariants(),
    {
        //self.inc_ref_count();
        let Tracked(increased_state) = self.inc_ref_count(Tracked(s));

        //Ghost operations
        let tracked end_state = increased_state.restore_owner_at(
            self.paddr(),
            RAW_PAGE_TABLE_NODE_OWNER,
        );
        proof {
            let ghost page_model = increased_state.get_page(self.paddr());
            let ghost end_page_model = end_state.get_page(self.paddr());
            s.lemma_update_page_model_spec_same_paddr_twice(
                self.paddr(),
                page_model,
                end_page_model,
            );
        }

        (Self { raw: self.raw, level: self.level, _phantom: PhantomData }, Tracked(end_state))
    }

    #[rustc_allow_incoherent_impl]
    pub fn into(self, Tracked(s): Tracked<AbstractState>) -> (res: (
        Page<PageTablePageMeta>,
        Tracked<AbstractState>,
    ))
        requires
            self.has_valid_paddr(),
            self.relate_model(s.get_page(self.paddr())),
            s.invariants(),
        ensures
            res.0.inv_ptr(),
            res.0.relate_model(res.1@.get_page(self.paddr())),
            res.1@.invariants(),
            res.1@ == s,
    {
        Page::<PageTablePageMeta>::from(self, Tracked(s))
    }

    #[rustc_allow_incoherent_impl]
    pub fn from_raw_parts(
        paddr: Paddr,
        level: PagingLevel,
        Tracked(s): Tracked<AbstractState>,
    ) -> (res: (Self, Tracked<AbstractState>))
        requires
            paddr % PAGE_SIZE_SPEC() == 0,
            paddr < MAX_PADDR_SPEC(),
            s.invariants(),
            s.get_page(paddr).usage == PageUsage::PageTable,
            s.get_page(paddr).isleaked(),
        ensures
            RawPageTableNode::from_raw_parts_spec(paddr, s, res.1@),
            res.0.relate_model(res.1@.get_page(paddr)),
            res.1@.invariants(),
    {
        //Ghost operations
        proof {
            s.lemma_get_page_index_eq_page_to_index_spec(paddr);
        }
        let tracked end_state = s.restore_owner_at(paddr, RAW_PAGE_TABLE_NODE_OWNER);

        (Self { raw: paddr, level, _phantom: PhantomData }, Tracked(end_state))
    }

    #[rustc_allow_incoherent_impl]
    pub fn from_raw_parts_unleaked(
        paddr: Paddr,
        level: PagingLevel,
        Tracked(s): Tracked<AbstractState>,
    ) -> (res: (Self, Tracked<AbstractState>))
        requires
            paddr % PAGE_SIZE_SPEC() == 0,
            paddr < MAX_PADDR_SPEC(),
            s.invariants(),
            s.get_page(paddr).usage == PageUsage::PageTable,
        ensures
    //        RawPageTableNode::from_raw_parts_spec(paddr, s, res.1@),

            res.0.paddr() == paddr,
            res.0.relate_model(res.1@.get_page(paddr)),
            res.1@.invariants(),
            res.1@.get_page(paddr).ref_count == s.get_page(paddr).ref_count + 1,
    {
        //Ghost operations
        proof {
            s.lemma_get_page_index_eq_page_to_index_spec(paddr);
        }

        let raw = Self { raw: paddr, level, _phantom: PhantomData };

        assert(raw.raw == paddr);
        assert(raw.relate_model(s.get_page(paddr))) by { admit() };
        assert(s.get_page(paddr).ref_count < u32::MAX) by { admit() };

        let (raw2, s2) = raw.clone_shallow(Tracked(s));

        assert(raw2.raw == paddr) by { admit() };

        //    let tracked increased_state = raw.inc_ref_count(Tracked(s));
        //    let tracked end_state = increased_state@.restore_owner_at(paddr,RAW_PAGE_TABLE_NODE_OWNER);

        //    assert(raw.paddr() == paddr);
        //    assert(raw.relate_model(s.get_page(paddr)));

        (raw2, s2)
    }

    #[rustc_allow_incoherent_impl]
    pub fn first_activate(&self, Tracked(s): Tracked<AbstractState>) -> (res: Tracked<
        AbstractState,
    >)
        requires
            self.has_valid_paddr(),
            self.relate_model(s.get_page(self.paddr())),
            s.invariants(),
            s.get_page(self.paddr()).ref_count < u32::MAX,
        ensures
            RawPageTableNode::first_activate_spec(*self, s, res@),
            res@.invariants(),
    {
        //self.inc_ref_count();
        //activate_page_table(self.raw, CachePolicy::Writeback);
        let Tracked(increased_state) = self.inc_ref_count(Tracked(s));
        unsafe {
            activate_page_table(self.raw, CachePolicy::Writeback);
        }

        //Ghost operations
        proof {
            s.lemma_inc_then_restore_owner_implies_share_with(
                self.paddr(),
                PAGE_TABLE_CPU_OWNER,
                increased_state,
            );
        }
        Tracked(increased_state.restore_owner_at(self.paddr(), PAGE_TABLE_CPU_OWNER))
    }

    #[verifier::loop_isolation(false)]
    #[verifier::exec_allows_no_decreases_clause]
    #[rustc_allow_incoherent_impl]
    pub fn lock(self, Tracked(s): Tracked<AbstractState>) -> (res: (
        PageTableNode,
        Tracked<AbstractState>,
    ))
        requires
            self.has_valid_paddr(),
            self.relate_model(s.get_page(self.paddr())),
            s.invariants(),
        ensures
            Self::lock_spec(self, res.0, s, res.1@),
            res.0.relate_model(res.1@.get_page(self.paddr())),
            res.1@.invariants(),
    {
        //let level = self.level;
        //let page: Page<PageTablePageMeta<E, C>> = self.into();
        let level = self.level;
        let (page, Tracked(s)) = self.into(Tracked(s));
        let ghost snapshot = s;
        // Acquire the lock.
        /* while page
    .meta()
    .lock
    .compare_exchange(0, 1, Ordering::Acquire, Ordering::Relaxed)
    .is_err()
    {
        core::hint::spin_loop();
    }*/
        let tracked perm = s.take_pageperm(page.paddr());
        let tracked mut pagetable_model = perm.specific_perm.tracked_unwrap_pagetable_model();

        while page.meta_pt(
            Tracked(&perm.ptr_perm),
            Tracked(perm.inner_perm.tracked_borrow()),
        ).lock.compare_exchange(Tracked(&mut pagetable_model.lock), 0, 1).is_err()
            invariant
                SpecificPagePerm::PT(pagetable_model).match_meta_slot_inner(
                    perm.get_inner_perm().value(),
                ),
        {
            spin_loop();
        }

        proof {
            perm.specific_perm = SpecificPagePerm::PT(pagetable_model);
            s.insert_pageperm(page.paddr(), perm);
            assert(s.get_page(page.paddr()).relate_perm(s.get_perm(page.paddr())));
        }

        //Ghost operations
        let tracked end_state = s.transfer_at(
            page.paddr(),
            RAW_PAGE_TABLE_NODE_OWNER,
            PAGE_TABLE_NODE_OWNER,
        );
        (PageTableNode { page }, Tracked(end_state))
    }
}

} // verus!
verus! {

impl Page<PageTablePageMeta> {
    #[rustc_allow_incoherent_impl]
    pub fn from(raw: RawPageTableNode, Tracked(s): Tracked<AbstractState>) -> (res: (
        Self,
        Tracked<AbstractState>,
    ))
        requires
            raw.has_valid_paddr(),
            raw.relate_model(s.get_page(raw.paddr())),
            s.invariants(),
        ensures
            res.0.inv_ptr(),
            res.0.relate_model(res.1@.get_page(raw.paddr())),
            res.1@.invariants(),
            res.1@ == s,
    {
        //let raw = ManuallyDrop::new(raw);
        let paddr = raw.paddr();
        let raw = manually_drop(raw);

        //Ghost operations
        let ghost page_model = s.get_page_ghost(paddr);
        let tracked forget_state = s.leak_owner_at(paddr, RAW_PAGE_TABLE_NODE_OWNER);
        let ghost page_model_forget = forget_state.get_page_ghost(paddr);
        proof {
            s.lemma_leak_owner_then_restore_owner_implies_unchanged(
                paddr,
                RAW_PAGE_TABLE_NODE_OWNER,
                forget_state,
            );
        }

        //unsafe { Page::<PageTablePageMeta<E, C>>::from_raw(raw.paddr()) }
        Page::<PageTablePageMeta>::from_raw(
            paddr,
            Ghost(RAW_PAGE_TABLE_NODE_OWNER),
            Tracked(forget_state),
        )
    }
}

} // verus!
verus! {

impl PageTableNode {
    #[rustc_allow_incoherent_impl]
    pub open spec fn relate(self, model: PageTableNodeValue) -> bool {
        self.paddr() == model.paddr()
    }

    #[rustc_allow_incoherent_impl]
    pub fn clone_raw(&self, Tracked(s): Tracked<AbstractState>) -> (res: (
        RawPageTableNode,
        Tracked<AbstractState>,
    ))
        requires
            self.inv(),
            s.invariants(),
            s.get_page(self.paddr()).ref_count < u32::MAX,
            self.relate_model(s.get_page(self.page.paddr())),
        ensures
            PageTableNode::clone_raw_spec(self, s, res.1@),
            res.0.relate_model(res.1@.get_page(self.page.paddr())),
            res.1@.invariants(),
    {
        //let page = ManuallyDrop::new(self.page.clone());
        let (cloned_page, Tracked(cloned_state)) = self.page.clone(
            Ghost(RAW_PAGE_TABLE_NODE_OWNER),
            Tracked(s),
        );
        forget_wrapper(cloned_page);

        //Ghost operations
        let paddr = self.page.paddr();
        let tracked forget_state = cloned_state.leak_owner_at(paddr, RAW_PAGE_TABLE_NODE_OWNER);
        proof {
            forget_state.lemma_get_page_implies_relate_perm(paddr);
            cloned_state.lemma_leak_owner_then_restore_owner_implies_unchanged(
                paddr,
                RAW_PAGE_TABLE_NODE_OWNER,
                forget_state,
            );

        }
        let tracked perm: &PagePerm = forget_state.borrow_pageperm(paddr);
        let tracked inner_perm = perm.tracked_borrow_inner_perm();
        let tracked pagetable_perm = perm.tracked_borrow_pagetable_inner_perm();
        //unsafe { RawPageTableNode::from_raw_parts(page.paddr(), page.meta().level) }
        let level = self.level(
            Tracked(&perm.ptr_perm),
            Tracked(inner_perm),
            Tracked(pagetable_perm),
        );
        RawPageTableNode::from_raw_parts(paddr, level, Tracked(forget_state))
    }

    #[rustc_allow_incoherent_impl]
    pub fn into_raw(self, Tracked(s): Tracked<AbstractState>) -> (res: (
        RawPageTableNode,
        Tracked<AbstractState>,
    ))
        requires
            self.inv(),
            s.invariants(),
            self.relate_model(s.get_page(self.page.paddr())),
        ensures
            PageTableNode::into_raw_spec(self, s, res.1@),
            res.0.relate_model(res.1@.get_page(self.page.paddr())),
            res.1@.invariants(),
    {
        //let this = ManuallyDrop::new(self);
        //this.page.meta().lock.store(0, Ordering::Release);
        let paddr = self.page.paddr();
        let tracked mut s = s;
        let tracked perm = s.take_pageperm(self.page.paddr());

        let tracked pagetable_model = perm.specific_perm.tracked_unwrap_pagetable_model();
        self.page.meta_pt(
            Tracked(&mut perm.ptr_perm),
            Tracked(perm.inner_perm.tracked_borrow()),
        ).lock.store(Tracked(&mut pagetable_model.lock), 0);

        let level = self.level(
            Tracked(&perm.ptr_perm),
            Tracked(perm.inner_perm.tracked_borrow()),
            Tracked(&pagetable_model.inner),
        );
        proof {
            perm.specific_perm = SpecificPagePerm::PT(pagetable_model);
            s.insert_pageperm(self.page.paddr(), perm);
        }
        forget_wrapper(self);

        //Ghost operations
        let tracked forget_state = s.leak_owner_at(paddr, PAGE_TABLE_NODE_OWNER);
        proof {
            s.lemma_leak_owner_then_restore_owner_implies_transfer(
                paddr,
                PAGE_TABLE_NODE_OWNER,
                RAW_PAGE_TABLE_NODE_OWNER,
                forget_state,
            );
        }

        //unsafe { RawPageTableNode::from_raw_parts(this.page.paddr(), this.page.meta().level)
        RawPageTableNode::from_raw_parts(paddr, level, Tracked(forget_state))
    }
}

} // verus!
