use vstd::prelude::*;

use crate::mm::frame::meta::AnyFrameMeta;
use crate::mm::frame::Frame;
use crate::mm::Paddr;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;

use vstd_extra::drop_tracking::*;

verus! {

#[verus_verify]
impl<'a, M: AnyFrameMeta> Frame<M> {

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

}

}
