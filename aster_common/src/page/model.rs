use vstd::prelude::*;
use vstd::simple_pptr::*;
use vstd::atomic::*;
use vstd::multiset::*;
use super::*;
use crate::prelude::*;

verus! {

pub enum PageTablePageOwner {
    PageTableNode,
    RawPageTableNode,
    CPU,
}

pub enum PageOwner {
    Kernel { context_id: int },
    User { thread_id: int },
    Dma,
    Cpu,
    PageTable(PageTablePageOwner),
}

pub const PAGE_TABLE_NODE_OWNER: PageOwner = PageOwner::PageTable(
    PageTablePageOwner::PageTableNode,
);

pub const RAW_PAGE_TABLE_NODE_OWNER: PageOwner = PageOwner::PageTable(
    PageTablePageOwner::RawPageTableNode,
);

pub const PAGE_TABLE_CPU_OWNER: PageOwner = PageOwner::PageTable(PageTablePageOwner::CPU);

pub enum PageUsePermission {
    NoPerm,
    RawPointer,
    PageTableEntry,
    ReadWrite,
}

} // verus!
verus! {

pub tracked enum SpecificPagePerm {
    PT(PageTablePageMetaModel),
    NoPerm,
}

//PagePerm is a collection of permissions for MetaSlot components
pub tracked struct PagePerm {
    pub tracked ptr_perm: simple_pptr::PointsTo<MetaSlot>,
    pub tracked ref_count_perm: PermissionU32,
    pub tracked inner_perm: Option<cell::PointsTo<MetaSlotInner>>,
    pub tracked specific_perm: SpecificPagePerm,
}

#[rustc_has_incoherent_inherent_impls]
pub tracked struct PageModel {
    pub index: u64,
    pub ghost state: PageState,
    pub ghost usage: PageUsage,
    pub ghost ref_count: int,
    pub ghost owners: Multiset<
        PageOwner,
    >,
    //pub tracked ptr_perm: Tracked<simple_pptr::PointsTo<MetaSlot>>,
}

} // verus!
verus! {

impl PageOwner {
    pub open spec fn as_usage_spec(&self) -> PageUsage {
        match self {
            PageOwner::Kernel { .. } => PageUsage::Kernel,
            PageOwner::User { .. } => PageUsage::Frame,
            PageOwner::PageTable(_) => PageUsage::PageTable,
            PageOwner::Dma => PageUsage::Reserved,
            PageOwner::Cpu => PageUsage::Reserved,
        }
    }

    #[verifier::when_used_as_spec(as_usage_spec)]
    pub fn as_usage(&self) -> PageUsage {
        match self {
            PageOwner::Kernel { .. } => PageUsage::Kernel,
            PageOwner::User { .. } => PageUsage::Frame,
            PageOwner::PageTable(_) => PageUsage::PageTable,
            PageOwner::Dma => PageUsage::Reserved,
            PageOwner::Cpu => PageUsage::Reserved,
        }
    }
}

} // verus!
verus! {

impl PagePerm {
    pub open spec fn invariants(self) -> bool {
        &&& self.ptr_perm.is_init() ==> {
            &&& self.ptr_perm.value().wf()
            &&& self.ref_count_perm.is_for(self.ptr_perm.value().ref_count)
        }
        &&& self.ptr_perm.is_init() && self.inner_perm.is_some() && self.get_inner_perm().is_init()
            ==> {
            &&& self.ptr_perm.value()._inner.id() == self.get_inner_perm().id()
            &&& match self.specific_perm {
                SpecificPagePerm::PT(perm) => {
                    &&& is_variant(self.get_inner_perm().value(), "_pt")
                    &&& perm.relate(self.ptr_perm.value().borrow_pt_spec(&self.get_inner_perm()))
                },
                SpecificPagePerm::NoPerm => { is_variant(self.get_inner_perm().value(), "_frame") },
            }
        }
    }

    #[verifier::inline]
    pub open spec fn get_inner_perm(self) -> cell::PointsTo<MetaSlotInner>
        recommends
            self.inner_perm.is_some(),
    {
        self.inner_perm.unwrap()
    }

    #[verifier::inline]
    pub open spec fn get_pagetable_inner_perm(self) -> cell::PointsTo<PageTablePageMetaInner>
        recommends
            self.specific_perm is PT,
    {
        self.specific_perm.get_pagetable_inner_perm()
    }

    #[verifier::inline]
    pub open spec fn get_lock_perm(self) -> PermissionU8
        recommends
            self.specific_perm is PT,
    {
        self.specific_perm.get_lock_perm()
    }

    #[verifier::inline]
    pub open spec fn get_pagetable_model(self) -> PageTablePageMetaModel
        recommends
            self.specific_perm is PT,
    {
        self.specific_perm.get_pagetable_model()
    }

    pub proof fn tracked_borrow_inner_perm(tracked &self) -> (tracked res: &cell::PointsTo<
        MetaSlotInner,
    >)
        requires
            self.inner_perm.is_some(),
        ensures
            *res == self.get_inner_perm(),
    {
        &self.inner_perm.tracked_borrow()
    }

    pub proof fn tracked_borrow_pagetable_inner_perm(tracked &self) -> (tracked res:
        &cell::PointsTo<PageTablePageMetaInner>)
        requires
            self.specific_perm is PT,
        ensures
            *res == self.get_pagetable_inner_perm(),
    {
        self.specific_perm.tracked_borrow_pagetable_inner_perm()
    }

    pub proof fn tracked_borrow_lock_perm(tracked &self) -> (tracked res: &PermissionU8)
        requires
            self.specific_perm is PT,
        ensures
            *res == self.get_lock_perm(),
    {
        self.specific_perm.tracked_borrow_lock_perm()
    }
}

impl SpecificPagePerm {
    pub open spec fn match_meta_slot_inner(self, inner: MetaSlotInner) -> bool {
        match self {
            SpecificPagePerm::PT(perm) => {
                &&& is_variant(inner, "_pt")
                &&& perm.relate(inner.borrow_pt_spec())
                &&& perm.inner.is_init()
            },
            SpecificPagePerm::NoPerm => is_variant(inner, "_frame"),
        }
    }

    pub open spec fn match_usage(self, usage: PageUsage) -> bool {
        match self {
            SpecificPagePerm::PT(perm) => usage is PageTable && perm.inner.is_init(),
            SpecificPagePerm::NoPerm => !(usage is PageTable),
        }
    }

    #[verifier::inline]
    pub open spec fn get_pagetable_model(self) -> PageTablePageMetaModel
        recommends
            self is PT,
    {
        self->PT_0
    }

    #[verifier::inline]
    pub open spec fn get_pagetable_inner_perm(self) -> cell::PointsTo<PageTablePageMetaInner>
        recommends
            self is PT,
    {
        self->PT_0.inner
    }

    #[verifier::inline]
    pub open spec fn get_lock_perm(self) -> PermissionU8
        recommends
            self is PT,
    {
        self->PT_0.lock
    }

    pub proof fn tracked_borrow_pagetable_model(tracked &self) -> (tracked res:
        &PageTablePageMetaModel)
        requires
            self is PT,
        ensures
            *res == self.get_pagetable_model(),
    {
        let tracked perm: Option<&PageTablePageMetaModel> = match self {
            SpecificPagePerm::PT(perm) => Some(perm),
            _ => None,
        };
        perm.tracked_borrow()
    }

    pub proof fn tracked_borrow_pagetable_inner_perm(tracked &self) -> (tracked res:
        &cell::PointsTo<PageTablePageMetaInner>)
        requires
            self is PT,
        ensures
            *res == self.get_pagetable_inner_perm(),
    {
        &self.tracked_borrow_pagetable_model().inner
    }

    pub proof fn tracked_borrow_lock_perm(tracked &self) -> (tracked res: &PermissionU8)
        requires
            self is PT,
        ensures
            *res == self.get_lock_perm(),
    {
        &self.tracked_borrow_pagetable_model().lock
    }

    pub proof fn tracked_unwrap_pagetable_model(tracked self) -> (tracked res:
        PageTablePageMetaModel)
        requires
            self is PT,
        ensures
            res == self->PT_0,
    {
        let tracked perm = match self {
            SpecificPagePerm::PT(perm) => Some(perm),
            _ => None,
        };
        perm.tracked_unwrap()
    }
}

} // verus!
verus! {

impl PageModel {
    pub open spec fn field_invariants(&self) -> bool {
        &&& 0 <= self.index && self.index < MAX_PADDR() / PAGE_SIZE()
        &&& self.state == self.usage.as_state()
        //&&& self.owners.finite()
        //&&& FRAME_METADATA_RANGE().start + self.index * META_SLOT_SIZE() == self.ptr_perm@.addr()

    }

    pub open spec fn state_invariants(&self) -> bool {
        match self.state {
            PageState::Unused => {
                &&& self.usage == PageUsage::Unused
                &&& self.ref_count == 0
                &&& self.owners.is_empty()
            },
            PageState::Typed => {
                &&& !(self.usage == PageUsage::Unused || self.usage == PageUsage::Frame)
                &&& self.ref_count > 0
                //&&& !self.owners.is_empty()
                &&& self.ref_count >= self.owners.len() as int
            },
            PageState::Untyped => {
                &&& self.usage == PageUsage::Frame
                &&& self.ref_count > 0
                //&&& !self.owners.is_empty()
                &&& self.ref_count >= self.owners.len() as int
            },
        }
    }

    pub open spec fn owners_invariants(self) -> bool {
        &&& forall|owner: PageOwner| #[trigger]
            self.owners.contains(owner) ==> owner.as_usage() == self.usage
    }

    pub open spec fn invariants(&self) -> bool {
        &&& self.field_invariants()
        &&& self.state_invariants()
        &&& self.owners_invariants()
    }

    pub open spec fn step_invariants(&self, next: &Self) -> bool {
        &&& next.index == self.index
    }

    pub open spec fn relate_paddr(&self, paddr: Paddr) -> bool {
        &&& paddr == self.index * PAGE_SIZE()
    }

    pub open spec fn isleaked(self) -> bool {
        self.ref_count > self.owners.len() as int
    }

    #[verifier::inline]
    pub open spec fn has_valid_index(self) -> bool {
        0 <= self.index < MAX_NR_PAGES()
    }

    pub open spec fn relate_perm(self, perm: PagePerm) -> bool {
        &&& FRAME_METADATA_RANGE().start + self.index * META_SLOT_SIZE() == perm.ptr_perm.addr()
        &&& self.ref_count == perm.ref_count_perm.value()
        &&& perm.ptr_perm.is_init()
        &&& match self.state {
            PageState::Unused => {
                &&& perm.inner_perm.is_none()
                &&& perm.specific_perm is NoPerm
            },
            PageState::Typed => {
                &&& perm.inner_perm.is_some()
                &&& perm.get_inner_perm().is_init()
                &&& perm.specific_perm.match_usage(self.usage)
            },
            PageState::Untyped => {
                &&& perm.inner_perm.is_some()
                &&& perm.get_inner_perm().is_init()
                &&& perm.specific_perm.match_usage(self.usage)
            },
        }
    }

    #[verifier::external_body]
    pub proof fn axiom_page_model_singleton(a: &PageModel, b: &PageModel, paddr: Paddr)
        requires
            a.relate_paddr(paddr),
            b.relate_paddr(paddr),
        ensures
            a == b,
    {
        assert(a.index == b.index);
    }

    pub open spec fn relate_page<M: PageMeta>(&self, page: &Page<M>) -> bool {
        &&& FRAME_METADATA_RANGE().start + self.index * META_SLOT_SIZE() == page.ptr.addr()
    }

    pub open spec fn relate_meta_slot(&self, slot: &MetaSlot) -> bool {
        &&& FRAME_METADATA_RANGE().start + self.index * META_SLOT_SIZE() == slot.id()
    }

    pub open spec fn relate_meta_slot_model(&self, slot: &MetaSlotModel) -> bool {
        &&& self.index * PAGE_SIZE() == slot.address@
    }

    pub open spec fn relate_meta_slot_model_properties(&self, slot: &MetaSlotModel) -> bool {
        &&& match (self.state, slot.state, slot.usage) {
            (PageState::Unused, MetaSlotState::Unused, PageUsage::Unused) => true,
            (PageState::Untyped, MetaSlotState::Used, PageUsage::Frame) => true,
            (PageState::Typed, MetaSlotState::Used, _) => true,
            _ => false,
        }
        &&& self.usage == slot.usage
        &&& self.ref_count
            == slot.ref_count
        //&&& self.ptr_perm@.addr() == page_to_meta(slot.address as usize)

    }

    pub open spec fn relate_meta_slot_full(&self, slot: &MetaSlotModel) -> bool {
        &&& self.relate_meta_slot_model(slot)
        &&& self.relate_meta_slot_model_properties(slot)
    }

    #[verifier::external_body]
    pub proof fn axiom_relate_meta_slot_model_properties(&self, slot: &MetaSlotModel)
        requires
            slot.invariants(),
            self.relate_meta_slot_model(slot),
        ensures
            self.relate_meta_slot_model_properties(slot),
    {
    }
}

} // verus!
verus! {

impl<M: PageMeta> Page<M> {
    #[rustc_allow_incoherent_impl]
    pub open spec fn has_valid_paddr(self) -> bool {
        &&& self.paddr() < MAX_PADDR_SPEC()
        &&& self.paddr() % PAGE_SIZE_SPEC() == 0
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn relate_model(&self, model: PageModel) -> bool {
        &&& self.ptr.addr() == FRAME_METADATA_RANGE().start + model.index * META_SLOT_SIZE()
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn relate_meta_slot(&self, slot: &MetaSlot) -> bool {
        self.ptr.addr() == slot.id()
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn lemma_relate_same_meta_slot_relate_model(&self, model: PageModel, slot: &MetaSlot)
        requires
            self.relate_meta_slot(slot),
            model.relate_meta_slot(slot),
        ensures
            self.relate_model(model),
    {
    }
}

} // verus!
verus! {

impl<M: PageMeta> Page<M> {
    #[rustc_allow_incoherent_impl]
    pub proof fn lemma_inv_ptr_implies_has_valid_paddr(&self)
        ensures
            self.inv_ptr() ==> self.has_valid_paddr(),
    {
        if self.inv_ptr() {
            lemma_meta_to_page_soundness(self.ptr.addr() as Vaddr);
        }
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn lemma_relate_model_has_valid_index_implies_inv_ptr(&self, model: PageModel)
        requires
            self.relate_model(model),
            model.has_valid_index(),
        ensures
            self.inv_ptr(),
    {
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn lemma_has_valid_paddr_implies_get_page_satisfies_invariants(
        &self,
        s: AbstractState,
    )
        requires
            s.invariants(),
            self.has_valid_paddr(),
        ensures
            s.get_page(self.paddr()).invariants(),
    {
        s.lemma_get_page_satisfies_invariants(self.paddr());
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn lemma_has_valid_paddr_implies_get_page_has_valid_index(&self, s: AbstractState)
        requires
            s.invariants(),
            self.has_valid_paddr(),
        ensures
            s.get_page(self.paddr()).has_valid_index(),
    {
        s.lemma_get_page_has_valid_index(self.paddr());
    }
}

} // verus!
verus! {

impl<M: PageMeta> Page<M> {
    #[rustc_allow_incoherent_impl]
    pub open spec fn from_slot_spec(slot: &MetaSlot) -> Page<M>;

    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    #[verifier::when_used_as_spec(from_slot_spec)]
    pub fn from_slot(slot: &MetaSlot) -> (res: Page<M>)
        ensures
            res == Self::from_slot_spec(slot),
            slot.id() == res.ptr.addr(),
    {
        let addr: usize = slot as *const MetaSlot as usize;
        let ptr = PPtr::from_usize(addr);
        Page { ptr, _marker: PhantomData }
    }

    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub proof fn from_slot_spec_ensures(slot: &MetaSlot)
        ensures
            Self::from_slot(slot).relate_meta_slot(slot),
    {
    }

    #[rustc_allow_incoherent_impl]
    pub uninterp spec fn model_from_slot_spec(slot: &MetaSlot) -> Tracked<PageModel>;

    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    #[verifier::when_used_as_spec(model_from_slot_spec)]
    pub fn model_from_slot(slot: &MetaSlot) -> (res: Tracked<PageModel>)
        ensures
            res == Self::model_from_slot_spec(slot),
            slot.id() == res@.index * META_SLOT_SIZE(),
    {
        unimplemented!()
    }

    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub proof fn model_from_slot_spec_ensures(slot: &MetaSlot)
        ensures
            Self::model_from_slot(slot)@.relate_meta_slot(slot),
    {
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn model_from_slot_relate_abstract_data(
        paddr: Paddr,
        slot: &MetaSlot,
        model: &PageModel,
        s: &AbstractState,
    )
        requires
            s.invariants(),
            paddr < MAX_PADDR(),
            paddr % PAGE_SIZE() == 0,
            slot == MetaSlot::concrete_from_paddr(paddr),
            model == Page::<M>::model_from_slot(slot)@,
        ensures
            s.get_page(paddr) == model,
    {
        let x = s.get_page(paddr);
        assert(x.relate_paddr(paddr)) by {
            s.get_page_relate_to_paddr(paddr);
        };
        assert(paddr == meta_to_page(slot.id() as usize) as u64) by {
            MetaSlot::axiom_concrete_from_paddr_id(paddr);
        };
        assert(model.relate_meta_slot(slot)) by {
            Page::<M>::model_from_slot_spec_ensures(slot);
        };
        assert(FRAME_METADATA_RANGE().start + model.index * META_SLOT_SIZE() == slot.id());
        assert(model.relate_paddr(paddr));
        assert(x == model) by {
            PageModel::axiom_page_model_singleton(&x, model, paddr);
        };
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn new_spec(slot: &MetaSlot) -> (res: (Page<M>, Tracked<PageModel>)) {
        let page = Page::from_slot(slot);
        let model = Page::<M>::model_from_slot(slot);
        (page, model)
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn new_spec_ensures(slot: &MetaSlot)
        ensures
            Self::new(slot).0.relate_meta_slot(slot),
            Self::new(slot).1@.relate_meta_slot(slot),
    {
        let (page, model) = Self::new(slot);
        Self::from_slot_spec_ensures(slot);
        Self::model_from_slot_spec_ensures(slot);
    }

    #[rustc_allow_incoherent_impl]
    #[verifier::when_used_as_spec(new_spec)]
    pub fn new(slot: &MetaSlot) -> (res: (Page<M>, Tracked<PageModel>))
        ensures
            res == Self::new_spec(slot),
            res.0 == Self::from_slot(slot),
            res.1 == Self::model_from_slot(slot),
            res.0.relate_meta_slot(slot),
            res.1@.relate_meta_slot(slot),
            res.0.relate_model(res.1@),
    {
        let page = Page::from_slot(slot);
        let Tracked(model) = Page::<M>::model_from_slot(slot);
        proof {
            Self::new_spec_ensures(slot);
        }
        (page, Tracked(model))
    }
}

// impl<M: PageMeta> Page<M>
} // verus!
