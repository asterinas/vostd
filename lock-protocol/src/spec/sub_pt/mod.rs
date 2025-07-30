pub mod state_machine;

use std::ops::Sub;

use state_machine::{frames_valid, FrameView, SubPageTableStateMachine};

use vstd::{prelude::*};
use vstd::simple_pptr::{PPtr, PointsTo};

use crate::mm::allocator::{AllocatorModel, pa_is_valid_kernel_address};
use crate::mm::{Paddr, PageTableConfig, PageTablePageMeta};
use crate::mm::NR_ENTRIES;
use crate::mm::page_table::cursor::MAX_NR_LEVELS;
use crate::exec::SIZEOF_PAGETABLEENTRY;
use crate::exec::SIZEOF_FRAME;
use crate::spec::sub_pt::state_machine::ptes_frames_matches;
use crate::mm::page_table::PagingConstsTrait;
verus! {

pub open spec fn level_is_in_range<C: PageTableConfig>(level: int) -> bool {
    1 <= level <= C::C::NR_LEVELS_SPEC() as int
}

pub open spec fn index_is_in_range(index: int) -> bool {
    0 <= index < NR_ENTRIES
}

pub open spec fn pa_is_valid_pt_address(pa: int) -> bool {
    &&& pa_is_valid_kernel_address(pa as int)
    &&& pa % SIZEOF_FRAME as int == 0
}

pub open spec fn index_pte_paddr(frame_pa: int, index: int) -> int {
    frame_pa + index * SIZEOF_PAGETABLEENTRY as int
}

/// The sub-page-table ghost state.
pub tracked struct SubPageTable<C: PageTableConfig> {
    // The allocator model will be provided by the lock protocol. And it will
    // be finally submitted to the lock protocol, so that we can reason about
    // allocations in the entire page table.
    pub alloc_model: AllocatorModel<PageTablePageMeta<C>>,
    /// Permissions of frames in the sub-page-table are stored in this map.
    pub perms: Map<Paddr, PointsTo<crate::exec::MockPageTablePage>>,
    // State machine.
    pub root: Ghost<FrameView<C>>,
    pub instance: SubPageTableStateMachine::Instance<C>,
    pub frames: SubPageTableStateMachine::frames<C>,
    pub i_ptes: SubPageTableStateMachine::i_ptes<C>,
    pub ptes: SubPageTableStateMachine::ptes<C>,
}

impl<C: PageTableConfig> SubPageTable<C> {
    pub open spec fn wf(&self) -> bool {
        &&& self.alloc_model.invariants()
        // The instance matches the fields.
        &&& self.frames.instance_id() == self.instance.id()
        &&& self.ptes.instance_id() == self.instance.id()
        &&& self.i_ptes.instance_id() == self.instance.id()
        &&& forall|pa: Paddr| #[trigger]
            self.frames.value().contains_key(pa as int) <==> #[trigger] self.perms.contains_key(pa)
        &&& forall|pa: Paddr| #[trigger]
            self.frames.value().contains_key(pa as int)
                ==> #[trigger] self.alloc_model.meta_map.contains_key(pa as int)
        &&& forall|pa: Paddr|
            #![trigger self.frames.value().contains_key(pa as int)]
            #![trigger self.perms.get(pa)]
            self.frames.value().contains_key(pa as int) ==> {
                let frame = self.frames.value().get(pa as int).unwrap();
                let perm = self.perms.get(pa).unwrap();
                &&& frame.pa == pa as int
                &&& frame.pa == perm.pptr().addr() as int
                &&& perm.mem_contents().is_init()
            }
        &&& self.root == self.instance.root()
        &&& frames_valid(self.root@, &self.frames.value(), &self.i_ptes.value())
        &&& ptes_frames_matches(&self.frames.value(), &self.i_ptes.value(), &self.ptes.value())
    }
}

} // verus!
