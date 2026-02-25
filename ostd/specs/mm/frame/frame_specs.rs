use vstd::prelude::*;

use vstd_extra::cast_ptr::*;
use vstd_extra::ownership::*;

use crate::mm::frame::meta::{mapping::frame_to_index, get_slot_spec, REF_COUNT_UNUSED};
use crate::mm::frame::*;
use crate::mm::{Paddr, PagingLevel, Vaddr};
use crate::specs::arch::mm::{MAX_NR_PAGES, MAX_PADDR, PAGE_SIZE};
use crate::specs::mm::frame::meta_owners::MetaSlotStorage;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;

use core::marker::PhantomData;

verus! {

impl<'a, M: AnyFrameMeta + Repr<MetaSlotStorage> + OwnerOf> Frame<M> {

}

} // verus!
