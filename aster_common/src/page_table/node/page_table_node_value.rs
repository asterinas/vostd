use vstd::prelude::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::seq::*;

use vstd_extra::prelude::*;
use vstd_extra::array_ptr;
use vstd_extra::ghost_tree::*;

use crate::x86_64;
use crate::prelude::*;
use crate::x86_64::mm;

verus! {

#[rustc_has_incoherent_inherent_impls]
pub tracked struct PageTableNodeValue {
    pub ghost paddr: usize,
    pub ghost is_pt: bool,  // if the node is a page table or a raw page
    pub ghost is_tracked: bool,  // if the node is tracked
    pub ghost nr_raws: nat,  // number of RawPageTableNodes
    pub ghost is_locked: bool,  // whether the node is locked
    pub ghost in_cpu: nat,  // number of CPUs that are currently using the node
    pub ghost nr_parents: nat,  // number of parents
    pub tracked perms: Option<array_ptr::PointsTo<PageTableEntry, CONST_NR_ENTRIES>>,
}

impl Inv for PageTableNodeValue {
    open spec fn inv(&self) -> bool {
        if self.paddr == 0 {
            &&& self.nr_raws == 0
            &&& self.is_locked == false
            &&& self.in_cpu == 0
            &&& self.nr_parents == 0
            &&& self.perms.is_none()
        } else {
            &&& self.perms.is_some()
            &&& self.perms.unwrap().addr() == paddr_to_vaddr(self.paddr)
            &&& self.perms.unwrap().wf()
            &&& self.paddr % PAGE_SIZE_SPEC() == 0
            &&& self.paddr < MAX_PADDR_SPEC()
        }
    }
}

impl TreeNodeValue for PageTableNodeValue {
    open spec fn default() -> Self {
        Self {
            paddr: 0,
            is_pt: true,
            is_tracked: true,
            nr_raws: 0,
            is_locked: false,
            in_cpu: 0,
            nr_parents: 0,
            perms: None,
        }
    }

    proof fn default_preserves_inv()
        ensures
            #[trigger] Self::default().inv(),
    {
    }
}

} // verus!
