use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::spec::{common::*, utils::*, tree::*};
use super::super::{common::*, types::*};
use super::*;

verus! {

struct_with_invariants!{

pub struct FrameAllocator {
}

pub open spec fn wf(&self) -> bool {
    predicate {
        &&& self.frames@.len() == MAX_FRAME_NUM
        &&& self.usages@.len() == MAX_FRAME_NUM

        &&& forall |fid: FrameId| valid_fid(fid) ==>
            match self.usages@[fid as int] {
                FrameUsage::Void => {
                    &&& is_variant(self.frames@[fid as int], "void_frame")
                },
                FrameUsage::PageTable => {
                    &&& is_variant(self.frames@[fid as int], "page_table_frame")
                    &&& manually_drop_unwrap(
                        get_union_field::<Frame, ManuallyDrop<PageTableFrame>>(
                            self.frames@[fid as int],
                            "page_table_frame",
                        )
                    ).wf()
                    &&& manually_drop_unwrap(
                        get_union_field::<Frame, ManuallyDrop<PageTableFrame>>(
                            self.frames@[fid as int],
                            "page_table_frame",
                        )
                    ).pa == fid_to_pa(fid)
                },
            }
    }
}

}

impl FrameAllocator {
    pub open spec fn inv_pt_frame(frame: Frame) -> bool {
        &&& is_variant(frame, "page_table_frame")
        &&& manually_drop_unwrap(
            get_union_field::<Frame, ManuallyDrop<PageTableFrame>>(frame, "page_table_frame"),
        ).wf()
    }

    pub open spec fn get_pt_frame_from_pa_spec(&self, pa: Paddr) -> PageTableFrame {
        manually_drop_unwrap(
            get_union_field::<Frame, ManuallyDrop<PageTableFrame>>(
                self.frames@[pa_to_fid(pa) as int],
                "page_table_frame",
            ),
        )
    }

    pub fn get_pt_frame_from_pa(&self, pa: Paddr) -> (res: &Frame)
        requires
            self.wf(),
            valid_paddr(pa),
            paddr_is_aligned(pa),
            self.usages@[pa_to_fid_spec(pa) as int] is PageTable,
        ensures
            *res =~= self.frames@[pa_to_fid(pa) as int],
            Self::inv_pt_frame(*res),
    {
        let fid: FrameId = pa_to_fid(pa);
        &self.frames[fid as usize]
    }

    #[verifier::external_body]
    pub fn find_void_frame(&self) -> (res: FrameId)
        requires
            self.wf(),
        ensures
            valid_fid(res),
            self.usages@[res as int] is Void,
    {
        0
    }

    pub fn find_void_frame_pa(&self) -> (res: Paddr)
        requires
            self.wf(),
        ensures
            valid_paddr(res),
            paddr_is_aligned(res),
            self.usages@[pa_to_fid(res) as int] is Void,
    {
        let fid = self.find_void_frame();
        assert(pa_to_fid(fid_to_pa(fid)) == fid) by { lemma_fid_to_pa_pa_to_fid(fid) };
        fid_to_pa(fid)
    }

    #[verifier::external_body]
    pub fn allocate_pt_frame(
        // &mut self,
        &self,
        pa: Paddr,
        nid: Ghost<NodeId>,
        inst: Tracked<SpecInstance>,
        node_token: Tracked<NodeToken>,
        rc_token: Tracked<RcToken>,
    )
        requires
            self.wf(),
            valid_paddr(pa),
            paddr_is_aligned(pa),
            self.usages@[pa_to_fid(pa) as int] is Void,  // Fix this
            NodeHelper::valid_nid(nid@),
            inst@.cpu_num() == GLOBAL_CPU_NUM,
            node_token@.instance_id() == inst@.id(),
            node_token@.key() == nid@,
            node_token@.value() is WriteUnLocked,
            rc_token@.instance_id() == inst@.id(),
            rc_token@.key() == nid@,
            rc_token@.value() == 0,
        ensures
            self.wf(),
            self.usages@[pa_to_fid(pa) as int] is PageTable,
    {
    }
}

} // verus!
