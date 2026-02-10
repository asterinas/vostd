pub mod cpu;
pub mod frame;
pub mod page_table;
pub mod virt_mem;
pub mod virt_mem_newer;

use vstd::prelude::*;

use crate::mm::vm_space::UserPtConfig;
use crate::mm::{Paddr, Vaddr};
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::page_table::{Guards, PageTableOwner};
use crate::specs::mm::virt_mem_newer::FrameContents;

verus! {

pub tracked struct GlobalMemOwner<'rcu> {
    pub regions: MetaRegionOwners,
    pub guards: Guards<'rcu, UserPtConfig>,
    pub pt: PageTableOwner<UserPtConfig>,
    pub memory: Map<Paddr, FrameContents>,
}

} // verus!
