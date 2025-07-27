pub mod mapping;

use vstd::prelude::*;
use vstd::{
    raw_ptr::{PointsTo},
    cell::{self, PCell},
};

use crate::spec::{common::*, utils::*};
use crate::exec::PageTableConfig;
use super::super::{common::*, types::*};
use super::super::node::rwlock::PageTablePageRwLock;

pub use mapping::*;

verus! {

struct_with_invariants! {
    pub struct PageTablePageMeta {
        /// The number of valid PTEs. It is mutable if the lock is held.
        pub nr_children:PCell<u16>,
        /// The level of the page table page. A page table page cannot be
        /// referenced by page tables of different levels.
        pub level: PagingLevel,
        /// The lock for the page table page.
        pub lock: PageTablePageRwLock,
        pub nid: Ghost<NodeId>,
        pub inst: Tracked<SpecInstance>,
    }

    pub open spec fn wf(&self) -> bool {
        predicate {
            &&& self.lock.wf()
            &&& self.level == self.lock.level_spec()
            &&& 1 <= self.level <= 4
            &&& NodeHelper::valid_nid(self.nid@)
            &&& self.nid@ == self.lock.nid@
            &&& self.inst@.cpu_num() == GLOBAL_CPU_NUM
            &&& self.inst@.id() == self.lock.pt_inst_id()
            &&& self.level as nat == NodeHelper::nid_to_level(self.nid@)
        }
    }
}

/// The maximum number of bytes of the metadata of a frame.
pub const FRAME_METADATA_MAX_SIZE: usize = META_SLOT_SIZE - 24;

/// The maximum alignment in bytes of the metadata of a frame.
pub const FRAME_METADATA_MAX_ALIGN: usize = META_SLOT_SIZE;

pub const META_SLOT_SIZE: usize = 96;

pub enum MetaSlotType {
    PageTablePageMeta,
    Others,
}

pub struct MetaSlot {
    /// The metadata of a frame.
    ///
    /// It is placed at the beginning of a slot because:
    ///  - the implementation can simply cast a `*const MetaSlot`
    ///    to a `*const AnyFrameMeta` for manipulation;
    ///  - if the metadata need special alignment, we can provide
    ///    at most `PAGE_METADATA_ALIGN` bytes of alignment;
    ///  - the subsequent fields can utilize the padding of the
    ///    reference count to save space.
    ///
    /// Don't interpret this field as an array of bytes. It is a
    /// placeholder for the metadata of a frame.
    pub storage: PCell<[u8; FRAME_METADATA_MAX_SIZE]>,
}

impl MetaSlot {
    #[verus_verify(external_body)]
    #[verus_spec( res =>
        with
            Tracked(perm): Tracked<&MetaSlotPerm>
        requires
            perm.is_pt(),
            perm.wf(),
            perm.metadata_perm()@.pcell == self.storage.id(),
        ensures
            *res =~= perm.get_pt(),
            res.wf(),
    )]
    pub fn get_inner_pt(&self) -> &PageTablePageMeta {
        unimplemented!()
    }
}

pub tracked struct MetaSlotPerm {
    pub ghost usage: MetaSlotType,
    pub ptr_perm: PointsTo<MetaSlot>,
    pub metadata_perm: cell::PointsTo<[u8; FRAME_METADATA_MAX_SIZE]>,
    pub ghost frame_paddr: Paddr,
}

impl MetaSlotPerm {
    #[verifier::inline]
    pub open spec fn ptr(&self) -> *const MetaSlot {
        self.ptr_perm.ptr()
    }

    #[verifier::inline]
    pub open spec fn ptr_perm(&self) -> PointsTo<MetaSlot> {
        self.ptr_perm
    }

    #[verifier::inline]
    pub open spec fn metadata_perm(&self) -> cell::PointsTo<[u8; FRAME_METADATA_MAX_SIZE]> {
        self.metadata_perm
    }

    #[verifier::inline]
    pub open spec fn usage(&self) -> MetaSlotType {
        self.usage
    }

    #[verifier::inline]
    pub open spec fn is_pt(&self) -> bool {
        self.usage() is PageTablePageMeta
    }

    #[verifier::inline]
    pub open spec fn relate(&self, ptr: *const MetaSlot) -> bool {
        &&& self.ptr() == ptr
    }

    pub uninterp spec fn interp_storage_as_pt(
        metadata: [u8; FRAME_METADATA_MAX_SIZE],
    ) -> PageTablePageMeta;

    pub open spec fn get_pt(&self) -> PageTablePageMeta
        recommends
            self.is_pt(),
    {
        Self::interp_storage_as_pt(self.metadata_perm().value())
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.ptr_perm().is_init()
        &&& self.metadata_perm().is_init()
        &&& self.metadata_perm()@.pcell == self.value().storage.id()
        &&& valid_paddr(self.frame_paddr)
        &&& self.frame_paddr() == meta_to_frame(self.meta_vaddr())
        &&& frame_to_meta(self.frame_paddr()) == self.meta_vaddr()
        &&& self.is_pt() ==> {
            &&& self.frame_paddr == self.get_pt().lock.paddr_spec()
            &&& self.get_pt().wf()
        }
    }

    pub open spec fn frame_paddr(&self) -> Paddr {
        self.frame_paddr
    }

    #[verifier::inline]
    pub open spec fn meta_vaddr(&self) -> Vaddr {
        self.ptr() as usize
    }

    #[verifier::inline]
    pub open spec fn value(&self) -> MetaSlot {
        self.ptr_perm().value()
    }
}

} // verus!
