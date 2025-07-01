//! The model of a metadata slot. It includes:
//! - The model of the metadata slot: `MetaSlotModel`.
//! - The invariants for both MetaSlot and MetaSlotModel.
//! - The primitives for MetaSlot.
use vstd::prelude::*;
use vstd::cell::*;
use vstd::atomic::*;

use crate::prelude::*;

verus! {

/// Internal state of the MetaSlot.
#[derive(PartialEq)]
pub ghost enum MetaSlotState {
    Unused,
    Claimed,
    Used,
    Finalizing,
}

} // verus!
verus! {

#[rustc_has_incoherent_inherent_impls]
/// The logical model of a metadata slot.
pub tracked struct MetaSlotModel {
    pub tracked ref_count_perm: Tracked<PermissionU32>,
    pub tracked inner_perm: Option<Tracked<PointsTo<MetaSlotInner>>>,
    pub ghost address: u64,
    pub ghost ref_count: u32,
    pub ghost state: MetaSlotState,
    pub ghost usage: PageUsage,
}

impl MetaSlotModel {
    pub open spec fn invariants(&self) -> bool {
        &&& self.ref_count_perm@.value() == self.ref_count@
        &&& self.address < MAX_PADDR()
        &&& self.address % PAGE_SIZE() as u64 == 0
        &&& self.state == MetaSlotState::Unused ==> {
            &&& self.inner_perm.is_none()
            &&& self.ref_count == 0
            &&& self.usage == PageUsage::Unused
        }
        &&& self.state == MetaSlotState::Claimed ==> {
            &&& self.inner_perm.is_some()
            &&& self.usage != PageUsage::Unused
        }
        &&& self.state == MetaSlotState::Used ==> {
            &&& self.inner_perm.is_some()
            &&& self.inner_perm.unwrap()@.is_init()
            &&& self.usage != PageUsage::Unused
        }
        &&& self.state == MetaSlotState::Finalizing ==> {
            &&& self.inner_perm.is_some()
            &&& self.inner_perm.unwrap()@.is_uninit()
            &&& self.usage != PageUsage::Unused
        }
    }
}

} // verus!
verus! {

impl MetaSlot {
    #[rustc_allow_incoherent_impl]
    pub uninterp spec fn id(&self) -> u64;

    #[rustc_allow_incoherent_impl]
    pub open spec fn invariant_id(&self) -> bool {
        &&& self.id() % META_SLOT_SIZE() as u64 == 0
        &&& FRAME_METADATA_RANGE().start <= self.id()
        &&& self.id() < FRAME_METADATA_RANGE().start + MAX_NR_PAGES() * META_SLOT_SIZE() as u64
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn invariants(&self) -> bool {
        &&& self.wf()
        &&& self.invariant_id()
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn relate_model(&self, model: &MetaSlotModel) -> bool {
        self.invariants() ==> {
            &&& model.invariants()
            &&& model.address == meta_to_page(self.id() as usize)
            &&& self.ref_count.id() == model.ref_count_perm@.id()
            &&& model.state != MetaSlotState::Unused ==> {
                model.inner_perm.unwrap()@.id() == self._inner.id()
            }
        }
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn inv_relate(&self, model: &MetaSlotModel) -> bool {
        &&& self.invariants()
        &&& self.relate_model(model)
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn invariants_implies_model(&self, model: &MetaSlotModel)
        requires
            self.invariants(),
            self.relate_model(model),
        ensures
            model.invariants(),
    {
    }
}

} // verus!
verus! {

//
// # Primitives for MetaSlot
//
impl MetaSlot {
    #[rustc_allow_incoherent_impl]
    pub uninterp spec fn model_from_paddr_spec(paddr: Paddr) -> Tracked<MetaSlotModel>;

    #[rustc_allow_incoherent_impl]
    pub uninterp spec fn concrete_from_paddr_spec(paddr: Paddr) -> &'static Self;

    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    #[verifier::when_used_as_spec(concrete_from_paddr_spec)]
    pub fn concrete_from_paddr(paddr: Paddr) -> (res: &'static Self)
        requires
            paddr % PAGE_SIZE() == 0,
            paddr < MAX_PADDR(),
        ensures
            res == Self::concrete_from_paddr_spec(paddr),
            paddr == meta_to_page(res.id() as usize),
    {
        let vaddr = page_to_meta(paddr);
        let ptr = vaddr as *const MetaSlot;
        unsafe { &*ptr }
    }

    ///
    /// MetaSlot is statically bind to a physical address. In this case, we need to
    /// provide the hypothesis that a concrete MetaSlot derived from `paddr` is
    /// indeed attached to that physical address.
    ///
    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub proof fn axiom_concrete_from_paddr_id(paddr: Paddr)
        requires
            paddr % PAGE_SIZE() == 0,
            paddr < MAX_PADDR(),
        ensures
            paddr == meta_to_page(Self::concrete_from_paddr(paddr).id() as usize),
    {
    }

    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    #[verifier::when_used_as_spec(model_from_paddr_spec)]
    pub fn model_from_paddr(paddr: Paddr) -> (res: Tracked<MetaSlotModel>)
        requires
            paddr % PAGE_SIZE() == 0,
            paddr < MAX_PADDR(),
        ensures
            res == Self::model_from_paddr_spec(paddr),
            Self::concrete_from_paddr(paddr).invariants() ==> {
                &&& res@.invariants()
                &&& Self::concrete_from_paddr(paddr).relate_model(&res@)
            },
    {
        unimplemented!()
    }

    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub proof fn axiom_model_from_paddr_address(paddr: Paddr)
        requires
            paddr % PAGE_SIZE() == 0,
            paddr < MAX_PADDR(),
        ensures
            Self::model_from_paddr(paddr)@.address@ == paddr,
    {
    }

    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub proof fn axiom_relate_model_same_paddr(
        paddr: Paddr,
        slot: &'static MetaSlot,
        model: &MetaSlotModel,
    )
        requires
            paddr % PAGE_SIZE() == 0,
            paddr < MAX_PADDR(),
            slot == MetaSlot::concrete_from_paddr(paddr),
            model == &MetaSlot::model_from_paddr(paddr)@,
            slot.invariants(),
        ensures
            slot.relate_model(model),
    {
    }

    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub proof fn axiom_meta_slot_model_singleton(a: &MetaSlotModel, b: &MetaSlotModel)
        requires
            a.address == b.address,
        ensures
            a == b,
    {
    }

    #[rustc_allow_incoherent_impl]
    pub fn from_paddr(paddr: Paddr) -> (res: (&'static Self, Tracked<MetaSlotModel>))
        requires
            paddr % PAGE_SIZE() == 0,
            paddr < MAX_PADDR(),
        ensures
            res.0 == MetaSlot::concrete_from_paddr(paddr),
            res.1 == MetaSlot::model_from_paddr(paddr),
            res.0.invariants() ==> {
                &&& res.1@.invariants()
                &&& res.0.inv_relate(&res.1@)
            },
    {
        let slot: &'static MetaSlot = MetaSlot::concrete_from_paddr(paddr);
        let Tracked(model) = MetaSlot::model_from_paddr(paddr);
        (slot, Tracked(model))
    }

    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub fn as_meta_slot_ptr(&self) -> (res: Vaddr)
        ensures
            res as int == self.id(),
    {
        self as *const MetaSlot as Vaddr
    }
}

} // verus!
