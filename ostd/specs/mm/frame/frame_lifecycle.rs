use vstd::prelude::*;

use crate::mm::frame::meta::AnyFrameMeta;
use crate::mm::frame::meta::mapping::frame_to_index;
use crate::mm::frame::Frame;
use crate::mm::Paddr;
use crate::specs::mm::frame::frame_specs::*;
use crate::specs::mm::frame::meta_owners::MetaSlotOwner;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;

use vstd_extra::drop_tracking::*;
use vstd_extra::ownership::*;

verus! {

#[verus_verify]
impl<'a, M: AnyFrameMeta> Frame<M> {

    /// Original lemma: when `raw_count == 1` before `from_raw`, the
    /// `from_raw` + `ManuallyDrop::new` pair is a no-op on `regions`.
    pub proof fn lemma_from_raw_manuallydrop_inverse(
        raw: Paddr,
        frame: Self,
        regions0: MetaRegionOwners,
        regions1: MetaRegionOwners
    )
        requires
            Self::from_raw_requires(regions0, raw),
            Self::from_raw_ensures(regions0, regions1, raw, frame),
            <Self as TrackDrop>::constructor_requires(frame, regions1),

        ensures
            forall |regions2: MetaRegionOwners|
                <Self as TrackDrop>::constructor_ensures(frame, regions1, regions2) ==>
                regions2 == regions0
    {
        admit()
    }

    /// Generalized lemma: for any starting `raw_count <= 1`, the
    /// `from_raw` + `ManuallyDrop::new` pair leaves `raw_count == 1`
    /// and preserves all other slot fields.  Consumes the `BorrowDebt`
    /// issued by `from_raw`.
    pub proof fn lemma_from_raw_manuallydrop_general(
        raw: Paddr,
        frame: Self,
        regions0: MetaRegionOwners,
        regions1: MetaRegionOwners,
        tracked debt: BorrowDebt,
    )
        requires
            Self::from_raw_requires_safety(regions0, raw),
            regions0.slot_owners[frame_to_index(raw)].raw_count <= 1,
            Self::from_raw_ensures(regions0, regions1, raw, frame),
            <Self as TrackDrop>::constructor_requires(frame, regions1),
            debt.frame_index == frame_to_index(raw),
            debt.raw_count_at_issue == regions0.slot_owners[frame_to_index(raw)].raw_count,

        ensures
            forall |regions2: MetaRegionOwners|
                #![trigger regions2.slot_owners[frame_to_index(raw)]]
                <Self as TrackDrop>::constructor_ensures(frame, regions1, regions2) ==> {
                    // raw_count is always 1 after from_raw (→0) + ManuallyDrop::new (→1)
                    &&& regions2.slot_owners[frame_to_index(raw)].raw_count == 1
                    // All other fields of this slot are preserved from regions0
                    &&& regions2.slot_owners[frame_to_index(raw)].inner_perms
                        == regions0.slot_owners[frame_to_index(raw)].inner_perms
                    &&& regions2.slot_owners[frame_to_index(raw)].self_addr
                        == regions0.slot_owners[frame_to_index(raw)].self_addr
                    &&& regions2.slot_owners[frame_to_index(raw)].usage
                        == regions0.slot_owners[frame_to_index(raw)].usage
                    &&& regions2.slot_owners[frame_to_index(raw)].path_if_in_pt
                        == regions0.slot_owners[frame_to_index(raw)].path_if_in_pt
                    // Other slots are unchanged
                    &&& forall |i: usize|
                        #![trigger regions2.slot_owners[i]]
                        i != frame_to_index(raw) ==> regions2.slot_owners[i]
                            == regions0.slot_owners[i]
                    &&& regions2.slot_owners.dom() =~= regions0.slot_owners.dom()
                    &&& regions2.slots =~= regions1.slots
                    &&& regions2.inv()
                }
    {
        admit()
    }

}

}
