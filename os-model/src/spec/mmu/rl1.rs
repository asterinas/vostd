use vstd::prelude::*;
use crate::spec::mmu::*;
use crate::spec::mmu::pt_mem::*;
#[cfg(verus_keep_ghost)]
use crate::spec::mmu::defs::{aligned, LoadResult, update_range, MAX_BASE};
use crate::spec::mmu::defs::{PTE, Core};
use crate::spec::mmu::rl3::{Writes};
use crate::spec::mmu::translation::{MASK_NEG_DIRTY_ACCESS};

verus! {

// This file contains refinement layer 1 of the MMU. Compared to layer 2, it removes store buffers
// and defines an atomic semantics to page table walks. This is the most abstract version of the
// MMU model.
pub struct State {
    pub happy: bool,
    /// Byte-indexed physical (non-page-table) memory
    pub phys_mem: Seq<u8>,
    /// Page table memory
    pub pt_mem: PTMem,
    /// Per-node state (TLBs)
    pub tlbs: Map<Core, Map<usize, PTE>>,
    pub writes: Writes,
    /// Tracks the virtual addresses and entries for which we may see non-atomic results.
    /// If polarity is positive, translations may non-atomically fail.
    /// If polarity is negative, translations may non-atomically succeed.
    pub pending_maps: Map<usize, PTE>,
    pub pending_unmaps: Map<usize, PTE>,
    pub polarity: Polarity,
}

pub enum Step {
    // Mixed
    Invlpg,
    // Faulting memory op due to failed translation
    // (atomic walk)
    MemOpNoTr,
    // Faulting memory op due to failed translation
    // (non-atomic walk result)
    MemOpNoTrNA { vbase: usize },
    // Memory op using a translation from the TLB
    MemOpTLB { tlb_va: usize },
    TLBFill { core: Core, vaddr: usize },
    TLBEvict { core: Core, tlb_va: usize },
    // Non-atomic TLB fill after an unmap
    TLBFillNA { core: Core, vaddr: usize },
    // TSO
    WriteNonneg,
    WriteNonpos,
    Read,
    Barrier,
    SadWrite,
    Sadness,
    Stutter,
}

impl State {
    pub open spec fn is_this_write_happy(
        self,
        core: Core,
        addr: usize,
        value: usize,
        pol: Polarity,
    ) -> bool {
        &&& !self.writes.tso.is_empty() ==> core == self.writes.core
        &&& if pol is Mapping {
            self.pt_mem.is_nonneg_write(addr, value)
        } else {
            self.pt_mem.is_nonpos_write(addr, value)
        }
    }

    pub open spec fn is_tso_read_deterministic(self, core: Core, addr: usize) -> bool {
        self.writes.tso.contains(addr) ==> self.writes.core == core
    }

    pub open spec fn can_flip_polarity(self, c: Constants) -> bool {
        &&& self.writes.tso === set![]
        &&& self.writes.nonpos === set![]
    }
    //pub open spec fn wf(self, c: Constants) -> bool {
    //    true
    //}
    //
    //pub open spec fn inv(self, c: Constants) -> bool {
    //    self.happy ==> {
    //    &&& self.wf(c)
    //    }
    //}

}

// ---- Mixed (relevant to multiple of TSO/Cache/Non-Atomic) ----
pub open spec fn step_Invlpg(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Invlpg(core, va)
    &&& pre.happy
    &&& c.valid_core(core)
    &&& !pre.tlbs[core].contains_key(va)
    &&& post == State {
        writes: Writes {
            core: pre.writes.core,
            tso: if core == pre.writes.core {
                set![]
            } else {
                pre.writes.tso
            },
            nonpos: if post.writes.tso === set![] {
                pre.writes.nonpos.remove(core)
            } else {
                pre.writes.nonpos
            },
        },
        pending_maps: if core == pre.writes.core {
            map![]
        } else {
            pre.pending_maps
        },
        pending_unmaps: if post.writes.nonpos === set![] {
            map![]
        } else {
            pre.pending_unmaps
        },
        ..pre
    }
}

pub open spec fn step_MemOpNoTr(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::MemOp(core, memop_vaddr, memop)
    &&& pre.happy
    &&& c.valid_core(core)
    &&& aligned(memop_vaddr as nat, memop.op_size())
    &&& memop.valid_op_size()
    &&& pre.pt_mem.pt_walk(memop_vaddr).result() is Invalid
    &&& memop.is_pagefault()
    &&& post == pre
}

pub open spec fn step_MemOpNoTrNA(
    pre: State,
    post: State,
    c: Constants,
    vbase: usize,
    lbl: Lbl,
) -> bool {
    &&& lbl matches Lbl::MemOp(core, memop_vaddr, memop)
    &&& pre.happy
    &&& pre.polarity is Mapping
    &&& c.valid_core(core)
    &&& aligned(memop_vaddr as nat, memop.op_size())
    &&& memop.valid_op_size()
    &&& pre.pending_maps.contains_key(vbase)
    &&& vbase <= memop_vaddr < vbase + pre.pending_maps[vbase].frame.size
    &&& memop.is_pagefault()
    &&& post == pre
}

pub open spec fn step_MemOpTLB(
    pre: State,
    post: State,
    c: Constants,
    tlb_va: usize,
    lbl: Lbl,
) -> bool {
    &&& lbl matches Lbl::MemOp(core, memop_vaddr, memop)
    &&& pre.happy
    &&& c.valid_core(core)
    &&& aligned(memop_vaddr as nat, memop.op_size())
    &&& memop.valid_op_size()
    &&& pre.tlbs[core].contains_key(tlb_va)
    &&& {
        let pte = pre.tlbs[core][tlb_va];
        let paddr = pte.frame.base + (memop_vaddr - tlb_va);
        &&& tlb_va <= memop_vaddr < tlb_va + pte.frame.size
        &&& match memop {
            MemOp::Store { new_value, result } => {
                if paddr < c.phys_mem_size && !pte.flags.is_supervisor && pte.flags.is_writable {
                    &&& result is Ok
                    &&& post.phys_mem === update_range(pre.phys_mem, paddr, new_value)
                } else {
                    &&& result is Pagefault
                    &&& post.phys_mem === pre.phys_mem
                }
            },
            MemOp::Load { is_exec, result, .. } => {
                if paddr < c.phys_mem_size && !pte.flags.is_supervisor && (is_exec
                    ==> !pte.flags.disable_execute) {
                    &&& result == LoadResult::Value(
                        pre.phys_mem.subrange(paddr, paddr + memop.op_size()),
                    )
                    &&& post.phys_mem === pre.phys_mem
                } else {
                    &&& result is Pagefault
                    &&& post.phys_mem === pre.phys_mem
                }
            },
        }
    }
    &&& post.happy == pre.happy
    &&& post.pt_mem == pre.pt_mem
    &&& post.tlbs == pre.tlbs
    &&& post.writes == pre.writes
    &&& post.pending_maps == pre.pending_maps
    &&& post.pending_unmaps == pre.pending_unmaps
}

// ---- Non-atomic page table walks ----
/// A TLB fill resulting from an atomic page table walk
pub open spec fn step_TLBFill(
    pre: State,
    post: State,
    c: Constants,
    core: Core,
    vaddr: usize,
    lbl: Lbl,
) -> bool {
    &&& lbl is Tau
    &&& pre.happy
    &&& c.valid_core(core)
    &&& vaddr < MAX_BASE
    &&& pre.pt_mem.pt_walk(vaddr).result() matches WalkResult::Valid { vbase, pte }
    &&& post == State { tlbs: pre.tlbs.insert(core, pre.tlbs[core].insert(vbase, pte)), ..pre }
}

pub open spec fn step_TLBEvict(
    pre: State,
    post: State,
    c: Constants,
    core: Core,
    tlb_va: usize,
    lbl: Lbl,
) -> bool {
    &&& lbl is Tau
    &&& pre.happy
    &&& c.valid_core(core)
    &&& pre.tlbs[core].contains_key(tlb_va)
    &&& post == State { tlbs: pre.tlbs.insert(core, pre.tlbs[core].remove(tlb_va)), ..pre }
}

/// A TLB fill resulting from a non-atomic page table walk
pub open spec fn step_TLBFillNA(
    pre: State,
    post: State,
    c: Constants,
    core: Core,
    vaddr: usize,
    lbl: Lbl,
) -> bool {
    let pte = pre.pending_unmaps[vaddr];
    &&& lbl is Tau
    &&& pre.happy
    &&& pre.polarity is Unmapping
    &&& c.valid_core(core)
    &&& pre.writes.nonpos.contains(core)
    &&& pre.pending_unmaps.contains_key(vaddr)
    &&& post == State { tlbs: pre.tlbs.insert(core, pre.tlbs[core].insert(vaddr, pte)), ..pre }
}

// ---- TSO ----
pub open spec fn step_WriteNonneg(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Write(core, addr, value)
    &&& pre.happy
    &&& c.valid_core(core)
    &&& c.in_ptmem_range(addr as nat, 8)
    &&& aligned(addr as nat, 8)
    &&& pre.is_this_write_happy(core, addr, value, Polarity::Mapping)
    &&& pre.polarity is Mapping || pre.can_flip_polarity(c)
    &&& post.happy == pre.happy
    &&& post.phys_mem == pre.phys_mem
    &&& post.pt_mem == pre.pt_mem.write(addr, value)
    &&& post.tlbs == pre.tlbs
    &&& post.writes.tso == pre.writes.tso.insert(addr)
    &&& post.writes.core == core
    &&& post.polarity == Polarity::Mapping
    &&& post.writes.nonpos == pre.writes.nonpos
    &&& post.pending_maps == pre.pending_maps.union_prefer_right(
        Map::new(
            |vbase| post.pt_mem@.contains_key(vbase) && !pre.pt_mem@.contains_key(vbase),
            |vbase| post.pt_mem@[vbase],
        ),
    )
    &&& post.pending_unmaps == pre.pending_unmaps
}

pub open spec fn step_WriteNonpos(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Write(core, addr, value)
    &&& pre.happy
    &&& c.valid_core(core)
    &&& c.in_ptmem_range(addr as nat, 8)
    &&& aligned(addr as nat, 8)
    &&& pre.is_this_write_happy(core, addr, value, Polarity::Unmapping)
    &&& pre.polarity is Unmapping || pre.can_flip_polarity(c)
    &&& post.happy == pre.happy
    &&& post.phys_mem == pre.phys_mem
    &&& post.pt_mem == pre.pt_mem.write(addr, value)
    &&& post.tlbs == pre.tlbs
    &&& post.writes.tso == pre.writes.tso.insert(addr)
    &&& post.writes.core == core
    &&& post.polarity == Polarity::Unmapping
    &&& post.writes.nonpos == Set::new(|core| c.valid_core(core))
    &&& post.pending_maps == pre.pending_maps
    &&& post.pending_unmaps == pre.pending_unmaps.union_prefer_right(
        Map::new(
            |vbase| pre.pt_mem@.contains_key(vbase) && !post.pt_mem@.contains_key(vbase),
            |vbase| pre.pt_mem@[vbase],
        ),
    )
}

pub open spec fn step_Read(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Read(core, addr, value)
    &&& pre.happy
    &&& c.valid_core(core)
    &&& c.in_ptmem_range(addr as nat, 8)
    &&& aligned(addr as nat, 8)
    &&& pre.is_tso_read_deterministic(core, addr) ==> value & MASK_NEG_DIRTY_ACCESS
        == pre.pt_mem.read(addr) & MASK_NEG_DIRTY_ACCESS
    &&& post == pre
}

pub open spec fn step_Barrier(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Barrier(core)
    &&& pre.happy
    &&& c.valid_core(core)
    &&& post == State {
        writes: Writes {
            tso: if core == pre.writes.core {
                set![]
            } else {
                pre.writes.tso
            },
            ..pre.writes
        },
        pending_maps: if core == pre.writes.core {
            map![]
        } else {
            pre.pending_maps
        },
        ..pre
    }
}

pub open spec fn step_Stutter(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl is Tau
    &&& post == pre
}

pub open spec fn step_SadWrite(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    // If we do a write without fulfilling the right conditions, we set happy to false.
    &&& lbl matches Lbl::Write(core, addr, value)
    &&& {
        let polarity = if value & 1 == 1 {
            Polarity::Mapping
        } else {
            Polarity::Unmapping
        };
        &&& !pre.is_this_write_happy(core, addr, value, polarity)
        &&& !post.happy
    }
}

pub open spec fn step_Sadness(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    // If happy is unset, arbitrary steps are allowed.
    &&& !pre.happy
    &&& !post.happy
}

pub open spec fn next_step(pre: State, post: State, c: Constants, step: Step, lbl: Lbl) -> bool {
    match step {
        Step::Invlpg => step_Invlpg(pre, post, c, lbl),
        Step::MemOpNoTr => step_MemOpNoTr(pre, post, c, lbl),
        Step::MemOpNoTrNA { vbase } => step_MemOpNoTrNA(pre, post, c, vbase, lbl),
        Step::MemOpTLB { tlb_va } => step_MemOpTLB(pre, post, c, tlb_va, lbl),
        Step::TLBFill { core, vaddr } => step_TLBFill(pre, post, c, core, vaddr, lbl),
        Step::TLBEvict { core, tlb_va } => step_TLBEvict(pre, post, c, core, tlb_va, lbl),
        Step::TLBFillNA { core, vaddr } => step_TLBFillNA(pre, post, c, core, vaddr, lbl),
        Step::WriteNonneg => step_WriteNonneg(pre, post, c, lbl),
        Step::WriteNonpos => step_WriteNonpos(pre, post, c, lbl),
        Step::Read => step_Read(pre, post, c, lbl),
        Step::Barrier => step_Barrier(pre, post, c, lbl),
        Step::SadWrite => step_SadWrite(pre, post, c, lbl),
        Step::Sadness => step_Sadness(pre, post, c, lbl),
        Step::Stutter => step_Stutter(pre, post, c, lbl),
    }
}

pub open spec fn next(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    exists|step| next_step(pre, post, c, step, lbl)
}

pub open spec fn init(pre: State, c: Constants) -> bool {
    &&& pre.happy
    &&& pre.tlbs === Map::new(|core| c.valid_core(core), |core| map![])
    &&& pre.writes.tso === set![]
    &&& pre.writes.nonpos === set![]
    &&& pre.pending_maps === map![]
    &&& pre.pending_unmaps === map![]
    &&& pre.polarity === Polarity::Mapping
    &&& c.valid_core(pre.writes.core)
    &&& pre.pt_mem.mem === Map::new(
        |va| aligned(va as nat, 8) && c.in_ptmem_range(va as nat, 8),
        |va| 0,
    )
    &&& aligned(pre.pt_mem.pml4 as nat, 4096)
    &&& c.memories_disjoint()
    &&& pre.phys_mem.len() == c.range_mem.1
    &&& c.in_ptmem_range(pre.pt_mem.pml4 as nat, 4096)
}

//proof fn init_implies_inv(pre: State, c: Constants)
//    requires init(pre, c)
//    ensures pre.inv(c)
//{}
//
//proof fn next_step_preserves_inv(pre: State, post: State, c: Constants, step: Step, lbl: Lbl)
//    requires
//        pre.inv(c),
//        next_step(pre, post, c, step, lbl),
//    ensures post.inv(c)
//{}
} // verus!
