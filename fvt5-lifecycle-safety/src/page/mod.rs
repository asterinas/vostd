//pub mod meta;
pub mod model;
pub mod proofs;
pub mod specs;

use std::marker::PhantomData;
use std::borrow::BorrowMut;

extern crate vstd_extra;
use vstd::prelude::*;
use vstd::simple_pptr;
use vstd::simple_pptr::*;
use vstd::multiset::*;
use vstd::atomic::{PAtomicU32, PermissionU32};
use vstd::atomic_ghost::*;
use vstd::cell;

use aster_common::prelude::*;
use crate::rust_core_mem::*;
use crate::abstract_state::*;
use crate::frame::{*, model::*};
use specs::*;
use model::*;

verus! {

impl<M: PageMeta> Page<M> {
    #[rustc_allow_incoherent_impl]
    pub fn from_unused(
        paddr: Paddr,
        metadata: MetaSlotInner,
        Ghost(owner): Ghost<PageOwner>,
        Tracked(specific_perm): Tracked<SpecificPagePerm>,
        Tracked(s): Tracked<AbstractState>,
    ) -> (res: (Option<Self>, Tracked<AbstractState>))
        requires
            s.invariants(),
            0 <= paddr && paddr < MAX_PADDR_SPEC(),
            paddr % PAGE_SIZE_SPEC() == 0,
            specific_perm.match_meta_slot_inner(metadata),
            specific_perm.match_usage(M::USAGE_spec()),
            s.get_page(paddr).state == PageState::Unused,
            owner.as_usage() == M::USAGE_spec(),
        ensures
    // This specification does not need any modification despite the new model

            PageModel::from_unused_spec(paddr, res.0, owner, s, res.1@),
            res.1@.invariants(),
    {
        //let vaddr = mapping::page_to_meta::<PagingConsts>(paddr);
        //let ptr = vaddr as *const MetaSlot;
        let vaddr = page_to_meta(paddr);
        let ptr: PPtr<MetaSlot> = PPtr::from_usize(vaddr as usize);

        //Ghost operations
        let tracked mut s = s;
        let ghost page_model = s.get_page_ghost(paddr);
        proof {
            assert(s.pages.dom().contains(page_to_index_spec(paddr as int)));
        }
        let tracked mut perm = s.take_pageperm(paddr);

        //let usage = unsafe { &(*ptr).usage };
        //let ref_count = unsafe { &(*ptr).ref_count };
        //usage
        //    .compare_exchange(0, M::USAGE as u8, Ordering::SeqCst, Ordering::Relaxed)
        //    .expect("page already in use when trying to get a new handle");
        let usage = M::USAGE();
        let u = usage.as_u8();
        let slot = ptr.borrow(Tracked(&perm.ptr_perm));
        let cas =
            atomic_with_ghost!(
            slot.usage =>
            compare_exchange(0, u);
            update prev -> next;
            ghost g => {
                match g {
                    ActualUsage::Unused(p) => {
                        g = ActualUsage::Used(usage);
                        perm.inner_perm = Some(p);
                    },
                    _ => {
                        g = g;
                    },
                }
            }
        );
        if !cas.is_ok() {
            let Tracked(s_panic) = panic(Tracked(s), "failed to claim slot");
            assert(s_panic.invariants()) by { admit() };
            proof {
                s_panic.insert_pageperm(paddr, perm);
            }
            return (None, Tracked(s_panic));
        }
        //let old_ref_count = ref_count.fetch_add(1, Ordering::Relaxed);

        let old_ref_count = slot.ref_count.fetch_add(Tracked(&mut perm.ref_count_perm), 1);

        //unsafe { (ptr as *mut M).write(metadata) };
        let tracked mut inner_perm = perm.inner_perm.tracked_unwrap();
        slot._inner.put(Tracked(&mut inner_perm), metadata);
        proof {
            perm.inner_perm = Some(inner_perm);
            perm.specific_perm = specific_perm;
            s.insert_pageperm(paddr, perm);
        }
        let ghost initialized_page_model = PageModel {
            state: usage.as_state(),
            usage,
            ref_count: 1,
            owners: Multiset::empty().insert(owner),
            ..page_model
        };
        let tracked s_end = s.update_page_model_tracked(paddr, initialized_page_model);

        assert(s_end.invariants()) by { admit() };

        (Some(Self { ptr, _marker: PhantomData }), Tracked(s_end))
    }

    #[rustc_allow_incoherent_impl]
    pub fn into_raw(
        self,
        Ghost(owner): Ghost<PageOwner>,
        Tracked(s): Tracked<AbstractState>,
    ) -> (res: (Paddr, Tracked<AbstractState>))
        requires
            self.has_valid_paddr(),
            self.relate_model(s.get_page(self.paddr())),
            s.invariants(),
            s.get_page(self.paddr()).state != PageState::Unused,
            s.get_page(self.paddr()).owners.contains(owner),
        ensures
            PageModel::into_raw_spec(self, owner, s, res.1@),
            res.0 == self.paddr(),
            res.1@.invariants(),
    {
        //let paddr = self.paddr();
        //core::mem::forget(self);
        let paddr = self.paddr();
        forget_wrapper(self);

        //Ghost Operation
        let tracked end_state = s.leak_owner_at(paddr, owner);

        (paddr, Tracked(end_state))
    }

    #[verifier::external_body]
    #[rustc_allow_incoherent_impl]
    pub fn from_raw(
        paddr: Paddr,
        Ghost(owner): Ghost<PageOwner>,
        Tracked(s): Tracked<AbstractState>,
    ) -> (res: (Self, Tracked<AbstractState>))
        requires
            paddr % PAGE_SIZE_SPEC() == 0,
            paddr < MAX_PADDR_SPEC(),
            owner.as_usage() == s.get_page(paddr).usage,
            s.invariants(),
            s.get_page(paddr).state != PageState::Unused,
            s.get_page(paddr).isleaked(),
        ensures
            PageModel::from_raw_spec(res.0, owner, s, res.1@),
            res.0.paddr() == paddr,
            res.1@.invariants(),
    {
        //Ghost operations
        proof {
            s.lemma_get_page_index_eq_page_to_index_spec(paddr);
        }
        let tracked end_state = s.restore_owner_at(paddr, owner);

        //Physical operations
        //let vaddr = mapping::page_to_meta::<PagingConsts>(paddr);
        //let ptr = vaddr as *const MetaSlot;
        let vaddr = page_to_meta(paddr);
        let ptr = PPtr::from_usize(vaddr as usize);

        (Self { ptr, _marker: PhantomData }, Tracked(end_state))
    }

    //Clone allows introducing an arbitaty owner if its usage matches the page's usage
    //This design is to make verificaton of PageTableNode::clone_raw easier
    #[rustc_allow_incoherent_impl]
    pub fn clone(&self, Ghost(owner): Ghost<PageOwner>, Tracked(s): Tracked<AbstractState>) -> (res:
        (Self, Tracked<AbstractState>))
        requires
            self.has_valid_paddr(),
            self.relate_model(s.get_page(self.paddr())),
            !s.get_page(self.paddr()).owners.is_empty(),
            s.get_page(self.paddr()).ref_count < u32::MAX,
            s.get_page(self.paddr()).usage == owner.as_usage(),
            s.get_page(self.paddr()).state != PageState::Unused,
            s.invariants(),
        ensures
            PageModel::clone_spec(*self, owner, s, res.1@),
            res.0 == *self,
            res.1@.invariants(),
    {
        let paddr = self.paddr();
        //Get abstract models
        let ghost page_model = s.get_page_ghost(paddr);
        let ghost init_state_snapshot = s;
        let tracked mut s = s;
        let tracked perm = s.take_pageperm(paddr);
        //self.ref_count().fetch_add(1, Ordering::Relaxed);
        self.ref_count(Tracked(&mut perm.ptr_perm)).fetch_add(Tracked(&mut perm.ref_count_perm), 1);

        //Ghost operations
        let tracked end_state = s.share_with_at(paddr, owner, perm, init_state_snapshot);

        (Page { ptr: self.ptr, _marker: PhantomData }, Tracked(end_state))
    }

    #[rustc_allow_incoherent_impl]
    pub fn reference_count<'a>(
        &'a self,
        p_slot: Tracked<&'a simple_pptr::PointsTo<MetaSlot>>,
        p_ref_count: Tracked<&PermissionU32>,
    ) -> (res: u32)
        requires
            self.inv_ptr(),
            p_slot@.pptr() == self.ptr,
            p_slot@.is_init(),
            p_ref_count@.is_for(p_slot@.value().ref_count),
        ensures
            res == p_ref_count@@.value,
    {
        self.ref_count(p_slot).load(p_ref_count)
    }

    #[rustc_allow_incoherent_impl]
    pub fn ref_count<'a>(&'a self, p_slot: Tracked<&'a simple_pptr::PointsTo<MetaSlot>>) -> (res:
        &'a PAtomicU32)
        requires
            self.inv_ptr(),
            p_slot@.pptr() == self.ptr,
            p_slot@.is_init(),
        ensures
            *res == p_slot@.value().ref_count,
    {
        //unsafe { &(*self.ptr).ref_count }
        &self.ptr.borrow(p_slot).ref_count
    }

    #[rustc_allow_incoherent_impl]
    fn try_from(dyn_page: DynPage, Tracked(s): Tracked<AbstractState>) -> (res: (
        Result<Self, DynPage>,
        Tracked<AbstractState>,
    ))
        requires
            dyn_page.inv_ptr(),
            dyn_page.relate_model(s.get_page(dyn_page.paddr())),
            s.invariants(),
            s.get_page(dyn_page.paddr()).state != PageState::Unused,
        ensures
            res.0.is_ok() <==> s.get_page(dyn_page.paddr()).usage == M::USAGE(),
            res.0.is_ok() ==> res.0.get_Ok_0().relate_model(s.get_page(dyn_page.paddr())),
            res.0.is_err() ==> res.0.get_Err_0() == dyn_page,
            res.1@.invariants(),
            res.1@ == s,
    {
        if dyn_page.usage(Tracked(&s)) == M::USAGE().as_u8() {
            let result = Page { ptr: dyn_page.ptr, _marker: PhantomData };
            forget_wrapper(dyn_page);
            (Ok(result), Tracked(s))
        } else {
            (Err(dyn_page), Tracked(s))
        }
    }

    #[rustc_allow_incoherent_impl]
    pub fn into(self, Tracked(s): Tracked<AbstractState>) -> (res: (
        DynPage,
        Tracked<AbstractState>,
    ))
        requires
            self.has_valid_paddr(),
            self.relate_model(s.get_page(self.paddr())),
            s.get_page(self.paddr()).state != PageState::Unused,
            s.invariants(),
        ensures
            res.0.relate_model(res.1@.get_page(self.paddr())),
            res.1@.invariants(),
            res.1@ == s,
    {
        //let result = Self { ptr: page.ptr };
        //let _ = ManuallyDrop::new(page);
        let result = DynPage { ptr: self.ptr };
        forget_wrapper(self);
        (result, Tracked(s))
    }
}

pub fn inc_page_ref_count(paddr: Paddr, Tracked(s): Tracked<AbstractState>) -> (res: Tracked<
    AbstractState,
>)
    requires
        paddr < MAX_PADDR_SPEC(),
        paddr % PAGE_SIZE_SPEC() == 0,
        s.invariants(),
        s.get_page(paddr).state != PageState::Unused,
        s.get_page(paddr).ref_count < u32::MAX,
    ensures
        PageModel::inc_page_ref_count_spec(paddr, s, res@),
        res@.invariants(),
{
    //Get abstract models
    let ghost page_model = s.get_page_ghost(paddr);
    let ghost init_state_snapshot = s;
    let tracked mut s = s;
    let tracked mut perm = s.take_pageperm(paddr);

    //let vaddr: Vaddr = mapping::page_to_meta::<PagingConsts>(paddr);
    //let slot = unsafe { &*(vaddr as *const MetaSlot) };
    //let old = slot.ref_count.fetch_add(1, Ordering::Relaxed);
    let vaddr = page_to_meta(paddr);
    let slot: &MetaSlot = PPtr::from_usize(vaddr as usize).borrow(Tracked(&perm.ptr_perm));
    let old = slot.ref_count.fetch_add(Tracked(&mut perm.ref_count_perm), 1);

    //Ghost operations
    Tracked(s.inc_at(paddr, perm, init_state_snapshot))
}

} // verus!
verus! {

impl Page<FrameMeta> {
    #[rustc_allow_incoherent_impl]
    pub fn into_frame(self, Tracked(s): Tracked<AbstractState>) -> (res: (
        Frame,
        Tracked<AbstractState>,
    ))
        requires
            self.has_valid_paddr(),
            self.relate_model(s.get_page(self.paddr())),
            s.get_page(self.paddr()).state == PageState::Untyped,
            s.get_page(self.paddr()).usage == PageUsage::Frame,
            exists|thread_id: int|
                s.get_page(self.paddr()).owners.contains(PageOwner::User { thread_id }),
            s.invariants(),
        ensures
            res.0.inv(),
            res.0.relate_model(res.1@.get_page(self.paddr())),
            res.1@.invariants(),
            res.1@ == s,
    {
        // Self { page }
        (Frame { page: self }, Tracked(s))
    }
}

} // verus!
verus! {

impl DynPage {
    #[rustc_allow_incoherent_impl]
    pub fn into_raw(
        self,
        Ghost(owner): Ghost<PageOwner>,
        Tracked(s): Tracked<AbstractState>,
    ) -> (res: (Paddr, Tracked<AbstractState>))
        requires
            self.has_valid_paddr(),
            self.relate_model(s.get_page(self.paddr())),
            s.invariants(),
            s.get_page(self.paddr()).state != PageState::Unused,
            s.get_page(self.paddr()).owners.contains(owner),
        ensures
            PageModel::dynpage_into_raw_spec(self, owner, s, res.1@),
            res.0 == self.paddr(),
            res.1@.invariants(),
    {
        //let paddr = self.paddr();
        //core::mem::forget(self);
        let paddr = self.paddr();
        forget_wrapper(self);

        //Ghost Operation
        let tracked end_state = s.leak_owner_at(paddr, owner);

        (paddr, Tracked(end_state))
    }

    #[rustc_allow_incoherent_impl]
    pub fn from_raw(
        paddr: Paddr,
        Ghost(owner): Ghost<PageOwner>,
        Tracked(s): Tracked<AbstractState>,
    ) -> (res: (Self, Tracked<AbstractState>))
        requires
            paddr % PAGE_SIZE_SPEC() == 0,
            paddr < MAX_PADDR_SPEC(),
            owner.as_usage() == s.get_page(paddr).usage,
            s.invariants(),
            s.get_page(paddr).state != PageState::Unused,
            s.get_page(paddr).isleaked(),
        ensures
            PageModel::dynpage_from_raw_spec(res.0, owner, s, res.1@),
            res.0.paddr() == paddr,
            res.1@.invariants(),
    {
        broadcast use vstd_extra::manually_drop::ex_manually_drop_value_axiom;
        //Ghost operations

        proof {
            s.lemma_get_page_index_eq_page_to_index_spec(paddr);
        }
        let tracked end_state = s.restore_owner_at(paddr, owner);

        //Physical operations
        //let vaddr = mapping::page_to_meta::<PagingConsts>(paddr);
        //let ptr = vaddr as *const MetaSlot;
        let vaddr = page_to_meta(paddr);
        let ptr = PPtr::from_usize(vaddr as usize);

        (Self { ptr }, Tracked(end_state))
    }

    #[rustc_allow_incoherent_impl]
    pub fn ref_count<'a>(&'a self, p_slot: Tracked<&'a simple_pptr::PointsTo<MetaSlot>>) -> (res:
        &'a PAtomicU32)
        requires
            self.inv_ptr(),
            p_slot@.pptr() == self.ptr,
            p_slot@.is_init(),
        ensures
            *res == p_slot@.value().ref_count,
    {
        //unsafe { &(*self.ptr).ref_count }
        &self.ptr.borrow(p_slot).ref_count
    }

    #[rustc_allow_incoherent_impl]
    pub fn clone(&self, Ghost(owner): Ghost<PageOwner>, Tracked(s): Tracked<AbstractState>) -> (res:
        (Self, Tracked<AbstractState>))
        requires
            self.has_valid_paddr(),
            self.relate_model(s.get_page(self.paddr())),
            !s.get_page(self.paddr()).owners.is_empty(),
            s.get_page(self.paddr()).ref_count < u32::MAX,
            s.get_page(self.paddr()).usage == owner.as_usage(),
            s.get_page(self.paddr()).state != PageState::Unused,
            s.invariants(),
        ensures
            PageModel::dynpage_clone_spec(*self, owner, s, res.1@),
            res.0 == *self,
            res.1@.invariants(),
    {
        let paddr = self.paddr();
        //Get abstract models
        let ghost page_model = s.get_page_ghost(paddr);
        let ghost init_state_snapshot = s;
        let tracked mut s = s;
        let tracked perm = s.take_pageperm(paddr);
        //self.ref_count().fetch_add(1, Ordering::Relaxed);
        self.ref_count(Tracked(&mut perm.ptr_perm)).fetch_add(Tracked(&mut perm.ref_count_perm), 1);

        //Ghost operations
        let tracked end_state = s.share_with_at(paddr, owner, perm, init_state_snapshot);

        (Self { ptr: self.ptr }, Tracked(end_state))
    }

    #[verifier::external_body]
    #[rustc_allow_incoherent_impl]
    pub fn usage(&self, Tracked(s): Tracked<&AbstractState>) -> (res: u8)
        requires
            self.inv_ptr(),
            s.invariants(),
        ensures
            res == s.get_page(self.paddr()).usage.as_u8(),
    {
        //let usage_raw = unsafe { (*self.ptr).usage.load(Ordering::Relaxed) };
        let tracked perm = s.borrow_pageperm(self.paddr());
        self.ptr.borrow(Tracked(&perm.ptr_perm)).usage.load()
    }

    #[rustc_allow_incoherent_impl]
    pub fn try_into<M: PageMeta>(self, Tracked(s): Tracked<AbstractState>) -> (res: (
        Result<Page<M>, DynPage>,
        Tracked<AbstractState>,
    ))
        requires
            self.inv_ptr(),
            self.relate_model(s.get_page(self.paddr())),
            s.invariants(),
            s.get_page(self.paddr()).state != PageState::Unused,
        ensures
            res.0.is_ok() <==> s.get_page(self.paddr()).usage == M::USAGE(),
            res.0.is_ok() ==> res.0.get_Ok_0().relate_model(s.get_page(self.paddr())),
            res.0.is_err() ==> res.0.get_Err_0() == self,
            res.1@.invariants(),
            res.1@ == s,
    {
        Page::<M>::try_from(self, Tracked(s))
    }
}

} // verus!
