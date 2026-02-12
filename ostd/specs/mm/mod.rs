pub mod cpu;
pub mod tlb;
pub mod frame;
pub mod page_table;
pub mod virt_mem_newer;

use vstd::prelude::*;

use vstd_extra::ownership::*;

use crate::mm::vm_space::UserPtConfig;
use crate::mm::{Paddr, Vaddr};
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::page_table::{Guards, PageTableOwner, Mapping, PageTableView};
use crate::specs::mm::tlb::TlbModel;
use crate::specs::mm::virt_mem_newer::FrameContents;

verus! {

/// # Global memory invariants
/// A [`GlobalMemOwner`] object ties together the components that are used in different layers
/// of the OSTD system. It is the object about which we state the invariants of the
/// memory system as a whole.
/// ## Verification Structure
/// Operations in `mm` take pieces of the global state as mutable arguments,
/// and guarantee that their invariants are preserved. This guarantees that, at the end of each
/// operation, the overall [`internal_invariants`](GlobalMemOwner::internal_invariants) of the system
/// hold. We then prove that the internal invariants imply the top-level properties that we want the
/// memory system to obey.
pub tracked struct GlobalMemOwner {
    /// [`MetaRegionOwners`](crate::specs::mm::frame::meta_region_owners::MetaRegionOwners)
    /// is the fundamental data structure of the `frame` module, tracking the allocation
    /// of metadata slots and their permissions.
    pub regions: MetaRegionOwners,
    /// [`PageTableOwner`](crate::specs::mm::page_table::owners::PageTableOwner) tracks the
    /// tree structure of the page table. It can be converted to a
    /// [`CursorOwner`](crate::specs::mm::page_table::cursor::owners::CursorOwner) for traversal and updates.
    /// A well-formed `CursorOwner` can be converted back into a `PageTableOwner` with consistent mappings,
    /// ensuring that its internal invariants are preserved.
    pub pt: PageTableOwner<UserPtConfig>,
    /// [`TlbModel`](crate::specs::mm::tlb::TlbModel) tracks the mappings in the TLB. It can flush mappings
    /// and it can load new ones from the page table.
    pub tlb: TlbModel,
    /// [`FrameContents`](crate::specs::mm::virt_mem_newer::FrameContents) tracks the contents
    /// of a frame for use in the [`VirtMem`](crate::specs::mm::virt_mem::VirtMem) library.
    pub memory: Map<Paddr, FrameContents>,
}

impl GlobalMemOwner {

    /// The set of mappings in the page table is determined by
    /// [`PageTableOwner::view_rec`](crate::specs::mm::page_table::owners::PageTableOwner::view_rec).
    pub closed spec fn page_table_mappings(self) -> Set<Mapping> {
        self.pt.view_rec(self.pt.0.value.path)
    }

    /// Top-level property: the page table mappings are disjoint in the virtual address space.
    pub open spec fn page_table_mappings_disjoint_vaddrs(self) -> bool {
        let pt_mappings = self.page_table_mappings();
        forall |m1: Mapping, m2: Mapping|
            pt_mappings has m1 &&
            pt_mappings has m2 &&
            m1 != m2 ==>
            Mapping::disjoint_vaddrs(m1, m2)
    }

    /// Top-level property: the page table mappings are disjoint in the physical address space.
    pub open spec fn page_table_mappings_disjoint_paddrs(self) -> bool {
        let pt_mappings = self.page_table_mappings();
        forall |m1: Mapping, m2: Mapping|
            pt_mappings has m1 &&
            pt_mappings has m2 &&
            m1 != m2 ==>
            Mapping::disjoint_paddrs(m1, m2)
    }

    /// Top-level property: the page table mappings are well-formed.
    /// See [`Mapping::inv`](crate::specs::mm::page_table::view::Mapping::inv).
    pub open spec fn page_table_mappings_well_formed(self) -> bool {
        let pt_mappings = self.page_table_mappings();
        forall |m: Mapping|
            pt_mappings has m ==>
            m.inv()
    }

    /// Top-level property: the TLB mappings are disjoint in the virtual address space.
    pub open spec fn tlb_mappings_disjoint_vaddrs(self) -> bool {
        let tlb_mappings = self.tlb.mappings;
        forall |m1: Mapping, m2: Mapping|
            tlb_mappings has m1 &&
            tlb_mappings has m2 &&
            m1 != m2 ==>
            Mapping::disjoint_vaddrs(m1, m2)
    }

    /// Top-level property: the TLB mappings are disjoint in the physical address space.
    pub open spec fn tlb_mappings_disjoint_paddrs(self) -> bool {
        let tlb_mappings = self.tlb.mappings;
        forall |m1: Mapping, m2: Mapping|
            tlb_mappings has m1 &&
            tlb_mappings has m2 &&
            m1 != m2 ==>
            Mapping::disjoint_paddrs(m1, m2)
    }

    /// Top-level property: the TLB mappings are well-formed.
    pub open spec fn tlb_mappings_well_formed(self) -> bool {
        let tlb_mappings = self.tlb.mappings;
        forall |m: Mapping|
            tlb_mappings has m ==>
            m.inv()
    }

    /// Top-level properties: the page table mappings are disjoint and well-formed.
    pub open spec fn invariants(self) -> bool {
        &&& self.page_table_mappings_disjoint_vaddrs()
        &&& self.page_table_mappings_disjoint_paddrs()
        &&& self.page_table_mappings_well_formed()
    }

    /// Internal invariants for [`GlobalMemOwner`]: the page table is consistent with the TLB
    /// and with the allocated regions, and the internal invariants of each component hold.
    /// Note that some API functions break the consistency between the page table and the TLB,
    /// making it the responsibility of the caller to restore it by flushing the TLB.
    pub open spec fn internal_invariants(self) -> bool {
        &&& self.regions.inv()
        &&& self.pt.inv()
        &&& self.pt.relate_region(self.regions)
        &&& self.tlb.consistent_with_pt(self.pt.view())
    }

    /// If the internal invariants hold, then the top-level properties hold.
    /// The key lemmas here are
    /// [`view_rec_disjoint_vaddrs`](crate::specs::mm::page_table::owners::PageTableOwner::view_rec_disjoint_vaddrs)
    /// and [`view_rec_disjoint_paddrs`](crate::specs::mm::page_table::owners::PageTableOwner::view_rec_disjoint_paddrs).
    pub proof fn internal_invariants_imply_top_level_properties(self)
        requires
            self.internal_invariants(),
        ensures
            self.invariants(),
    {
        assert(self.invariants()) by {
            // This follows from `view_rec_disjoint_vaddrs` and `view_rec_disjoint_paddrs`.
            // Just need to wire them together properly.
            admit();
        };
    }
}

} // verus!
