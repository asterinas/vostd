use vstd::prelude::*;

use crate::mm::frame::meta::AnyFrameMeta;
use crate::mm::frame::meta::mapping::frame_to_index;
use crate::mm::frame::Frame;
use crate::mm::Paddr;
use crate::specs::mm::frame::frame_specs::*;
use crate::specs::mm::frame::mapping::group_page_meta;
use crate::specs::mm::frame::meta_owners::{MetaSlotOwner, REF_COUNT_UNUSED};
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;

use vstd_extra::drop_tracking::*;
use vstd_extra::ownership::*;

verus! {

#[verus_verify]
impl<'a, M: AnyFrameMeta> Frame<M> {

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
            regions0.slot_owners[frame_to_index(raw)].inner_perms.ref_count.value()
                != REF_COUNT_UNUSED,
            Self::from_raw_ensures(regions0, regions1, raw, frame),
            <Self as TrackDrop>::constructor_requires(frame, regions1),
            debt.frame_index == frame_to_index(raw),
            debt.raw_count_at_issue == regions0.slot_owners[frame_to_index(raw)].raw_count,

        ensures
            forall |regions2: MetaRegionOwners|
                #![trigger regions2.slot_owners[frame_to_index(raw)]]
                <Self as TrackDrop>::constructor_ensures(frame, regions1, regions2) ==> {
                    &&& regions2.slot_owners[frame_to_index(raw)].raw_count == 1
                    &&& regions2.slot_owners[frame_to_index(raw)].inner_perms
                        == regions0.slot_owners[frame_to_index(raw)].inner_perms
                    &&& regions2.slot_owners[frame_to_index(raw)].self_addr
                        == regions0.slot_owners[frame_to_index(raw)].self_addr
                    &&& regions2.slot_owners[frame_to_index(raw)].usage
                        == regions0.slot_owners[frame_to_index(raw)].usage
                    &&& regions2.slot_owners[frame_to_index(raw)].paths_in_pt
                        == regions0.slot_owners[frame_to_index(raw)].paths_in_pt
                    &&& forall |i: usize|
                        #![trigger regions2.slot_owners[i]]
                        i != frame_to_index(raw) ==> regions2.slot_owners[i]
                            == regions0.slot_owners[i]
                    &&& regions2.slot_owners.dom() =~= regions0.slot_owners.dom()
                    &&& regions2.slots =~= regions1.slots
                    &&& regions2.inv()
                }
    {
        broadcast use group_page_meta;
        debt.discharge_in_lemma(&regions1);
        let idx = frame_to_index(raw);
        assert(frame.paddr() == raw);
        assert(regions0.slot_owners.dom() =~= regions1.slot_owners.dom());

        assert forall |regions2: MetaRegionOwners|
            <Self as TrackDrop>::constructor_ensures(frame, regions1, regions2)
        implies
            regions2.slot_owners[idx].raw_count == 1
            && regions2.slot_owners[idx].inner_perms
                == regions0.slot_owners[idx].inner_perms
            && regions2.slot_owners[idx].self_addr
                == regions0.slot_owners[idx].self_addr
            && regions2.slot_owners[idx].usage == regions0.slot_owners[idx].usage
            && regions2.slot_owners[idx].paths_in_pt
                == regions0.slot_owners[idx].paths_in_pt
            && (forall |i: usize|
                #![trigger regions2.slot_owners[i]]
                i != idx ==> regions2.slot_owners[i] == regions0.slot_owners[i])
            && regions2.slot_owners.dom() =~= regions0.slot_owners.dom()
            && regions2.slots =~= regions1.slots
            && #[trigger] regions2.inv()
        by {
            assert forall |i: usize| i != idx implies
                #[trigger] regions2.slot_owners[i] == regions0.slot_owners[i]
            by {
                assert(regions2.slot_owners[i] == regions1.slot_owners[i]);
                assert(regions1.slot_owners[i] == regions0.slot_owners[i]);
            }

            assert forall |i: usize| #[trigger] regions2.slot_owners.contains_key(i)
                implies regions2.slot_owners[i].inv()
            by {
                if i == idx {
                    assert(regions1.slot_owners[idx].inv());
                    assert(regions0.slot_owners[idx].inner_perms.ref_count.value()
                        != REF_COUNT_UNUSED);
                } else {
                    assert(regions1.slot_owners[i].inv());
                }
            }

            assert forall |i: usize| #[trigger] regions2.slots.contains_key(i)
                implies {
                    &&& regions2.slot_owners.contains_key(i)
                    &&& regions2.slot_owners[i].inv()
                    &&& regions2.slots[i].is_init()
                    &&& regions2.slots[i].value().wf(regions2.slot_owners[i])
                    &&& regions2.slot_owners[i].self_addr == regions2.slots[i].addr()
                }
            by {
                assert(regions1.slots.contains_key(i));
                if i != idx {
                    assert(regions2.slot_owners[i] == regions1.slot_owners[i]);
                }
            }
            assert(regions2.inv());
        }
    }

}

}
