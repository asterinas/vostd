use vstd::prelude::*;
use vstd::simple_pptr::*;

use crate::mm::NR_ENTRIES;
use crate::spec::simple_page_table;
use crate::exec;

verus! {

// NOTE: these do not work for creating new frame, see @create_new_frame
// pub broadcast proof fn axiom_pptr_write_frame(pt: PointsTo<exec::SimpleFrame>, f: exec::SimpleFrame)
// requires
//     #[trigger] pt.mem_contents() == MemContents::<exec::SimpleFrame>::Init(f),
//     #[trigger] f.ptes == #[trigger] pt.value().ptes,
// ensures
//     forall |i: int| 0 <= i < NR_ENTRIES ==>
//         #[trigger] pt.value().ptes[i] == #[trigger] f.ptes[i],
//     forall |i: int| 0 <= i < NR_ENTRIES ==>
//         #[trigger] pt.value().ptes[i].frame_pa == #[trigger] f.ptes[i].frame_pa
// ;
// use vstd::array::*;
// pub broadcast proof fn axiom_frame_ptes(f: exec::SimpleFrame)
// ensures
//     #[trigger] f.ptes == f.ptes,
//     forall |i: int| 0 <= i < NR_ENTRIES ==>
//         #[trigger] array_view(f.ptes)[i].frame_pa == f.ptes[i].frame_pa
// ;
// pub fn set_frame_ptes(f: &mut exec::SimpleFrame, i: usize, v: exec::SimplePageTableEntry)
// requires
//     old(f).ptes.len() > i,
// ensures
//     f.ptes[i as int] == v,
//     f.ptes[i as int].frame_pa == v.frame_pa,
//     f.ptes[i as int].level == v.level,
//     f.ptes[i as int].pte_addr == v.pte_addr
// {
//     f.ptes.set(i, v);
// }

} // verus!
