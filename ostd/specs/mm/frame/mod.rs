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

pub const FRAME_PERMISSION_TOTAL: u64 = REF_COUNT_MAX + 1;

pub type FramePermission = Count<simple_pptr::PointsTo<MetaSlot>, FRAME_PERMISSION_TOTAL>;
pub type FramePermissionResource =
    CountResource<simple_pptr::PointsTo<MetaSlot>, FRAME_PERMISSION_TOTAL>;
