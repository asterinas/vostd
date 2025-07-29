#![cfg_attr(verus_keep_ghost, verus::trusted)]
// trusted: definitions for the trusted low-level hardware model

pub mod defs;
pub mod pt_mem;
pub mod rl1;
pub mod rl2;
pub mod rl3;
pub mod translation;

use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use crate::spec::mmu::defs::{
    Flags, L1_ENTRY_SIZE, L2_ENTRY_SIZE, L3_ENTRY_SIZE, MemRegion, bitmask_inc, align_to_usize,
    WORD_SIZE, PAGE_SIZE, MAX_PHYADDR,
};
use crate::spec::mmu::defs::{Core, PTE, MemOp};
use crate::spec::mmu::translation::{PDE, GPDE, l0_bits, l1_bits, l2_bits, l3_bits};

verus! {

// Only used in the simplified hardware models.
// $line_count$Trusted${$
pub enum Polarity {
    Mapping,
    Unmapping,
}

impl Polarity {
    pub open spec fn flip(self) -> Polarity {
        if self is Mapping {
            Polarity::Unmapping
        } else {
            Polarity::Mapping
        }
    }
}

// $line_count$}$
pub struct Walk {
    pub vaddr: usize,
    pub path: Seq<(usize, GPDE)>,
    pub complete: bool,
}

pub enum WalkResult {
    Valid { vbase: usize, pte: PTE },
    /// A `WalkResult::Invalid` indicates that no valid translation exists for the given (8-aligned) vaddr
    Invalid { vaddr: usize },
}

impl WalkResult {
    pub open spec fn vaddr(self) -> usize {
        match self {
            WalkResult::Valid { vbase, .. } => vbase,
            WalkResult::Invalid { vaddr, .. } => vaddr,
        }
    }
}

impl Walk {
    /// 如果path最后一个PTE是Invalid，返回invalid并将vaddr对齐到PAGE_SIZE
    /// 如果path最后一位是Page，根据path长度将vaddr对齐到L1/L2/L3_ENTRY_SIZE，作为vbase，而返回的PTE则为
    /// MemRegion{base:PDE指定的物理地址，这一映射的空间大小}｝
    pub open spec fn result(self) -> WalkResult {
        let path = self.path;
        if path.last().1 is Page {
            let (vbase, base, size) = if path.len() == 2 {
                (align_to_usize(self.vaddr, L1_ENTRY_SIZE), path[1].1->Page_addr, L1_ENTRY_SIZE)
            } else if path.len() == 3 {
                (align_to_usize(self.vaddr, L2_ENTRY_SIZE), path[2].1->Page_addr, L2_ENTRY_SIZE)
            } else if path.len() == 4 {
                (align_to_usize(self.vaddr, L3_ENTRY_SIZE), path[3].1->Page_addr, L3_ENTRY_SIZE)
            } else {
                arbitrary()
            };
            WalkResult::Valid {
                vbase,
                pte: PTE {
                    frame: MemRegion { base: base as nat, size: size as nat },
                    flags: self.flags(),
                },
            }
        } else if path.last().1 is Invalid {
            // The result holds for one page
            WalkResult::Invalid { vaddr: align_to_usize(self.vaddr, PAGE_SIZE) }
        } else {
            arbitrary()
        }
    }

    pub open spec fn flags(self) -> Flags {
        let path = self.path;
        let flags0 = Flags::from_GPDE(path[0].1);
        let flags1 = flags0.combine(Flags::from_GPDE(path[1].1));
        let flags2 = flags1.combine(Flags::from_GPDE(path[2].1));
        let flags3 = flags2.combine(Flags::from_GPDE(path[3].1));
        if path.len() == 1 {
            flags0
        } else if path.len() == 2 {
            flags1
        } else if path.len() == 3 {
            flags2
        } else if path.len() == 4 {
            flags3
        } else {
            arbitrary()
        }
    }
}

/// Each refinement layer uses the same set of constants.
pub struct Constants {
    pub node_count: nat,
    pub core_count: nat,
    /// The range of memory used for the page table
    pub range_ptmem: (nat, nat),
    /// The range of memory used for the user memory
    pub range_mem: (nat, nat),
    pub phys_mem_size: nat,
}

impl Constants {
    /// We basically never need to reason about the body of this predicate but it can cause
    /// instability in some places, hence opaque.
    #[verifier(opaque)]
    pub open spec fn valid_core(self, core: Core) -> bool {
        &&& core.node_id < self.node_count
        &&& core.core_id < self.core_count
    }

    pub open spec fn in_ptmem_range(self, addr: nat, size: nat) -> bool {
        &&& self.range_ptmem.0 <= addr
        &&& addr + size <= self.range_ptmem.1
    }

    pub open spec fn in_mem_range(self, addr: nat, size: nat) -> bool {
        &&& self.range_mem.0 <= addr
        &&& addr + size <= self.range_mem.1
    }

    /// User memory is below PT memory
    pub open spec fn memories_disjoint(self) -> bool {
        &&& self.range_mem.0 < self.range_mem.1 < self.range_ptmem.0 < self.range_ptmem.1
        &&& self.range_ptmem.1 <= MAX_PHYADDR
    }
}

pub enum Lbl {
    /// Internal event
    Tau,
    /// Memory operation on non-page-table memory
    /// Core, virtual address, memory operation
    MemOp(Core, usize, MemOp),
    /// Write to page table memory.
    /// Core, physical address, written value
    Write(Core, usize, usize),
    /// Read from page table memory.
    /// Core, physical address, read value
    Read(Core, usize, usize),
    /// Invlpg instruction
    /// Core and virtual address
    Invlpg(Core, usize),
    /// Serializing instruction
    Barrier(Core),
}

// Only used in the simplified hardware models.
// $line_count$Trusted${$
pub trait SeqTupExt: Sized {
    type A;

    spec fn contains_fst(self, fst: Self::A) -> bool;
}

impl<A, B> SeqTupExt for Seq<(A, B)> {
    type A = A;

    open spec fn contains_fst(self, fst: Self::A) -> bool {
        exists|i| 0 <= i < self.len() && #[trigger] self[i] == (fst, self[i].1)
    }
}

// $line_count$}$
} // verus!
