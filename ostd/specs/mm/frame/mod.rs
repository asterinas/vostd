use vstd::simple_pptr;
use vstd_extra::resource::ghost_resource::{count::Count, tokens::CountResource};

use crate::mm::frame::meta::{MetaSlot, REF_COUNT_MAX};

pub mod frame_specs;
pub mod linked_list;
pub mod mapping;
pub mod memory_region_specs;
pub mod meta_owners;
pub mod meta_region_owners;
pub mod meta_specs;
pub mod segment;
pub mod unique;

pub type FramePermission = Count<simple_pptr::PointsTo<MetaSlot>, REF_COUNT_MAX>;
pub type FramePermissionResource =
    CountResource<simple_pptr::PointsTo<MetaSlot>, REF_COUNT_MAX>;
