use vstd::prelude::*;

use crate::mm::frame::Frame;
use crate::mm::frame::meta::AnyFrameMeta;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::mm::Paddr;

use vstd_extra::undroppable::*;

verus! {

#[verus_verify]
impl<'a, M: AnyFrameMeta> Frame<M> {
    
    pub proof fn lemma_from_raw_neverdrop_inverse(
        raw: Paddr,
        frame: Self,
        regions0: MetaRegionOwners,
        regions1: MetaRegionOwners
    )
        requires
            Self::from_raw_requires(regions0, raw),
            Self::from_raw_ensures(regions0, regions1, raw, frame),
            <Self as Undroppable>::constructor_requires(frame, regions1),
            
        ensures
            forall |regions2: MetaRegionOwners|
                <Self as Undroppable>::constructor_ensures(frame, regions1, regions2) ==>
                regions2 == regions0
    {
        admit()
    }

}

}