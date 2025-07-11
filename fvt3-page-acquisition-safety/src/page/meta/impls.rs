use std::fs::read;

use vstd::prelude::*;
use crate::rust_core_mem::manually_drop;
use crate::common::*;

use super::*;
use super::model::*;

verus! {

/// # Define of the `PageUsage` to `u8` conversion.
///
/// Note: Verus currently does not support `num_derive::FromPrimitive`, so we define the conversion manually.
impl PageUsage {
    pub open spec fn as_u8_spec(&self) -> (res: u8) {
        match self {
            Self::Unused => 0,
            Self::Reserved => 1,
            Self::Frame => 32,
            Self::PageTable => 64,
            Self::Meta => 65,
            Self::Kernel => 66,
        }
    }

    #[verifier::when_used_as_spec(as_u8_spec)]
    pub fn as_u8(&self) -> (res: u8)
        ensures
            res == self.as_u8_spec(),
    {
        match self {
            Self::Unused => 0,
            Self::Reserved => 1,
            Self::Frame => 32,
            Self::PageTable => 64,
            Self::Meta => 65,
            Self::Kernel => 66,
        }
    }
}

} // verus!
verus! {

/// # Write of the `MetaSlotInner` to the `MetaSlot`.
///
/// Verus (and also safe Rust) does not support writing value to
/// the union type. So we use a more verbose way to define the
/// new object of the `MetaSlotInner`.
impl MetaSlotInner {
    pub fn new<M: PageMeta>() -> (res: Self) {
        match M::get_usage() {
            PageUsage::Frame => Self { _frame: manually_drop(super::FrameMeta::default()) },
            PageUsage::PageTable => Self {
                _pt: manually_drop(super::PageTablePageMeta::default()),
            },
            _ => Self { _others: [0u8;0] },
        }
    }
}

} // verus!
verus! {

impl MetaSlot {
    /// Simulate the initial state of the `MetaSlot`.
    ///
    /// This function is purely logical and not used for the implementation.
    /// It is defined for verify the invariants of the `MetaSlot`.
    ///
    pub fn init() -> (res: (Self, Tracked<MetaSlotModel>))
        ensures
            res.0.inv_relate(&res.1@),
            res.1@.ref_count == 0u32,
            res.1@.state == MetaSlotState::Unused,
    {
        let (cell, Tracked(cell_perm)) = PCell::empty();
        let usage = AtomicU8::new(Ghost(cell), 0, Tracked(ActualUsage::Unused(cell_perm)));
        let (ref_count, Tracked(ref_count_perm)) = PAtomicU32::new(0);
        assert(ref_count.id() == ref_count_perm.id());
        assert(ref_count_perm@.value == 0);

        let slot = MetaSlot { _inner: cell, usage, ref_count };
        assume(slot.invariants());

        let tracked model = MetaSlotModel {
            ref_count: 0,
            inner_perm: None,
            address: meta_to_page(slot.id() as Vaddr),
            ref_count_perm: Tracked(ref_count_perm),
            state: MetaSlotState::Unused,
            usage: PageUsage::Unused,
        };
        assert(model.address == meta_to_page(slot.id() as Vaddr));

        (slot, Tracked(model))
    }

    /// implements `self.usage.compare_exchange(0, u)`
    pub fn claim(&self, usage: PageUsage, Tracked(model): Tracked<MetaSlotModel>) -> (res: (
        bool,
        Tracked<MetaSlotModel>,
    ))
        requires
            self.inv_relate(&model),
            usage != PageUsage::Unused,
            model.state == MetaSlotState::Unused,
        ensures
            self.inv_relate(&res.1@),
            model.claim_spec(self, usage, res.0, &res.1@),
    {
        let u = usage.as_u8();
        assert(u != 0);
        let tracked mut inner_perm = None;
        let cas =
            atomic_with_ghost!(
        &self.usage =>
        compare_exchange(0, u);
        update prev -> next;
        ghost g => {
            match g {
                ActualUsage::Unused(perm) => {
                    g = ActualUsage::Used(usage);
                    inner_perm = Some(perm);
                },
                _ => {
                    g = g;
                },
            }
        }
    );

        if cas.is_ok() {
            assert(inner_perm.is_some());
            let tracked model = MetaSlotModel {
                state: MetaSlotState::Claimed,
                inner_perm: Some(Tracked(inner_perm.tracked_unwrap())),
                usage: usage,
                ..model
            };
            return (true, Tracked(model));
        }
        (false, Tracked(model))
    }

    /// implements `self.ref_count.fetch_add(1)` during `from_unused()`
    pub fn inc0(&self, mut model: Tracked<MetaSlotModel>) -> (res: (u32, Tracked<MetaSlotModel>))
        requires
            self.inv_relate(&model@),
            model@.state == MetaSlotState::Claimed,
            model@.ref_count == 0,
        ensures
            self.inv_relate(&res.1@),
            model@.inc0_spec(res.0, &res.1@),
    {
        let tracked mut unwrap_model: MetaSlotModel = model.get();
        let n = self.ref_count.fetch_add(Tracked(unwrap_model.ref_count_perm.borrow_mut()), 1);
        let tracked model = MetaSlotModel { ref_count: 1u32, ..unwrap_model };
        (n, Tracked(model))
    }

    /// implements `self.ref_count.fetch_add(1)` for `inc_ref_count()`
    pub fn inc(&self, mut model: Tracked<MetaSlotModel>) -> (res: (u32, Tracked<MetaSlotModel>))
        requires
            self.inv_relate(&model@),
            model@.state == MetaSlotState::Used,
            model@.ref_count < u32::MAX,
        ensures
            self.inv_relate(&res.1@),
            model@.inc_spec(res.0, &res.1@),
    {
        let tracked mut unwrap_model: MetaSlotModel = model.get();
        let n = self.ref_count.fetch_add(Tracked(unwrap_model.ref_count_perm.borrow_mut()), 1);
        let tracked model = MetaSlotModel {
            ref_count: (unwrap_model.ref_count + 1) as u32,
            ..unwrap_model
        };
        (n, Tracked(model))
    }

    /// implements `self.ref_count.fetch_add(1)` for `drop()`
    pub fn dec(&self, mut model: Tracked<MetaSlotModel>) -> (res: (u32, Tracked<MetaSlotModel>))
        requires
            self.inv_relate(&model@),
            model@.state == MetaSlotState::Used,
            model@.ref_count > 0,
        ensures
            self.inv_relate(&res.1@),
            model@.dec_spec(res.0, &res.1@),
    {
        let tracked mut unwrap_model: MetaSlotModel = model.get();
        let n = self.ref_count.fetch_sub(Tracked(unwrap_model.ref_count_perm.borrow_mut()), 1);
        let tracked model = MetaSlotModel {
            ref_count: (unwrap_model.ref_count@ - 1) as u32,
            ..unwrap_model
        };
        (n, Tracked(model))
    }

    /// implements `(ptr as *mut M).write(M::default())` for `from_unused()`
    pub fn put_inner(&self, inner: MetaSlotInner, mut model: Tracked<MetaSlotModel>) -> (res:
        Tracked<MetaSlotModel>)
        requires
            self.inv_relate(&model@),
            model@.state == MetaSlotState::Claimed,
            model@.inner_perm.is_some(),
            model@.inner_perm.unwrap()@.is_uninit(),
            model@.inner_perm.unwrap()@.id() == self._inner.id(),
        ensures
            self.inv_relate(&res@),
            model@.put_inner_spec(inner, &res@),
    {
        let tracked mut unwrap_model: MetaSlotModel = model.get();
        let tracked mut perm: PointsTo<MetaSlotInner> =
            unwrap_model.inner_perm.tracked_unwrap().get();
        self._inner.put(Tracked(&mut perm), inner);
        let tracked model = MetaSlotModel { inner_perm: Some(Tracked(perm)), ..unwrap_model };
        Tracked(model)
    }

    /// seal the `inner` for `from_unused()`
    ///
    /// This function is purely logical and not used for the implementation.
    pub fn seal(&self, mut model: Tracked<MetaSlotModel>) -> (res: Tracked<MetaSlotModel>)
        requires
            self.inv_relate(&model@),
            model@.inner_perm.unwrap()@.is_init(),
            model@.state == MetaSlotState::Claimed,
        ensures
            self.inv_relate(&res@),
            res@ == model@.seal_spec(),
    {
        let tracked mut unwrap_model: MetaSlotModel = model.get();
        let tracked model = MetaSlotModel { state: MetaSlotState::Used, ..unwrap_model };
        Tracked(model)
    }

    /// complete M::on_drop() for `drop_as_last()`
    ///
    /// This function is purely logical and not used for the implementation.
    pub fn clear_inner(&self, mut model: Tracked<MetaSlotModel>) -> (res: Tracked<MetaSlotModel>)
        requires
            self.inv_relate(&model@),
            model@.state == MetaSlotState::Used,
            model@.ref_count@ == 0,
        ensures
            self.inv_relate(&res@),
            model@.clear_inner_spec(&res@),
    {
        let tracked mut unwrap_model: MetaSlotModel = model.get();
        let tracked mut perm: PointsTo<MetaSlotInner> =
            unwrap_model.inner_perm.tracked_unwrap().get();
        self._inner.take(Tracked(&mut perm));
        let tracked model = MetaSlotModel {
            state: MetaSlotState::Finalizing,
            inner_perm: Some(Tracked(perm)),
            ..unwrap_model
        };
        Tracked(model)
    }

    /// implements `self.usage.store(0)` for `drop_as_last()`
    pub fn clear(&self, mut model: Tracked<MetaSlotModel>) -> (res: Tracked<MetaSlotModel>)
        requires
            self.inv_relate(&model@),
            model@.state == MetaSlotState::Finalizing,
            model@.ref_count == 0,
        ensures
            self.inv_relate(&res@),
            model@.clear_spec(&res@),
    {
        let tracked mut unwrap_model: MetaSlotModel = model.get();
        let tracked mut perm: PointsTo<MetaSlotInner> =
            unwrap_model.inner_perm.tracked_unwrap().get();
        atomic_with_ghost!(
        &self.usage =>
        store(0);
        update prev -> next;
        ghost g => {
            g = ActualUsage::Unused(perm)
        }
    );
        let tracked model = MetaSlotModel {
            state: MetaSlotState::Unused,
            inner_perm: None,
            usage: PageUsage::Unused,
            ..unwrap_model
        };

        Tracked(model)
    }
}

} // verus!
