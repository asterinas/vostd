#![cfg_attr(verus_keep_ghost, verus::trusted)]
// Trusted: This file defines the semantics of how page table entries are interpreted by the
// hardware. This is only the semantics of how we go from bits to an interpretation; The hardware
// model in rl3.rs models the non-atomic nature of page table walks + caching + ..

use vstd::prelude::*;
use crate::spec::mmu::defs::{Flags, MAX_PHYADDR_WIDTH, bit, bitmask_inc};
#[cfg(verus_keep_ghost)]
use crate::spec::mmu::defs::{aligned, axiom_max_phyaddr_width_facts};

verus! {

pub ghost enum GPDE {
    Directory {
        addr: usize,
        /// Present; must be 1 to map a page or reference a directory
        P: bool,
        /// Read/write; if 0, writes may not be allowed to the page controlled by this entry
        RW: bool,
        /// User/supervisor; user-mode accesses are not allowed to the page controlled by this entry
        US: bool,
        /// Page-level write-through
        PWT: bool,
        /// Page-level cache disable
        PCD: bool,
        ///// Accessed; indicates whether software has accessed the page referenced by this entry
        //A: bool,
        /// If IA32_EFER.NXE = 1, execute-disable (if 1, instruction fetches are not allowed from
        /// the page controlled by this entry); otherwise, reserved (must be 0)
        XD: bool,
    },
    Page {
        addr: usize,
        /// Present; must be 1 to map a page or reference a directory
        P: bool,
        /// Read/write; if 0, writes may not be allowed to the page controlled by this entry
        RW: bool,
        /// User/supervisor; if 0, user-mode accesses are not allowed to the page controlled by this entry
        US: bool,
        /// Page-level write-through
        PWT: bool,
        /// Page-level cache disable
        PCD: bool,
        ///// Accessed; indicates whether software has accessed the page referenced by this entry
        //A: bool,
        ///// Dirty; indicates whether software has written to the page referenced by this entry
        //D: bool,
        // /// Page size; must be 1 (otherwise, this entry references a directory)
        // PS: Option<bool>,
        // PS is entirely determined by the Page variant and the layer
        /// Global; if CR4.PGE = 1, determines whether the translation is global; ignored otherwise
        G: bool,
        /// Indirectly determines the memory type used to access the page referenced by this entry
        PAT: bool,
        /// If IA32_EFER.NXE = 1, execute-disable (if 1, instruction fetches are not allowed from
        /// the page controlled by this entry); otherwise, reserved (must be 0)
        XD: bool,
    },
    /// An `Invalid` entry is an entry that does not contain a valid mapping. I.e. the entry is
    /// either empty or has a bit set that the intel manual designates as must-be-zero. Both empty
    /// and invalid entries cause a page fault if used during translation.
    Invalid,
}

// layer:
// 0 -> PML4
// 1 -> PDPT, Page Directory Pointer Table
// 2 -> PD, Page Directory
// 3 -> PT, Page Table
// MASK_FLAG_* are flags valid for entries at all levels.
pub const MASK_FLAG_P: usize = bit!(0usize);

pub const MASK_FLAG_RW: usize = bit!(1usize);

pub const MASK_FLAG_US: usize = bit!(2usize);

pub const MASK_FLAG_PWT: usize = bit!(3usize);

pub const MASK_FLAG_PCD: usize = bit!(4usize);

//pub const MASK_FLAG_A: usize = bit!(5usize);
pub const MASK_FLAG_XD: usize = bit!(63usize);

// MASK_PG_FLAG_* are flags valid for all page mapping entries, unless a specialized version for that
// layer exists, e.g. for layer 3 MASK_L3_PG_FLAG_PAT is used rather than MASK_PG_FLAG_PAT.
//pub const MASK_PG_FLAG_D: usize = bit!(6usize);
pub const MASK_PG_FLAG_G: usize = bit!(8usize);

pub const MASK_PG_FLAG_PAT: usize = bit!(12usize);

pub const MASK_L1_PG_FLAG_PS: usize = bit!(7usize);

pub const MASK_L2_PG_FLAG_PS: usize = bit!(7usize);

pub const MASK_L3_PG_FLAG_PAT: usize = bit!(7usize);

pub const MASK_DIRTY_ACCESS: usize = bit!(5) | bit!(6);

pub const MASK_NEG_DIRTY_ACCESS: usize = !MASK_DIRTY_ACCESS;

// In the implementation we can always use the 12:52 mask as the invariant guarantees that in the
// other cases, the lower bits are already zero anyway.
// We cannot use dual exec/spec constants here because for those Verus currently doesn't support
// manually guiding the no-overflow proofs.
pub spec const MASK_ADDR_SPEC: usize = bitmask_inc!(12usize, MAX_PHYADDR_WIDTH - 1);

#[verifier::when_used_as_spec(MASK_ADDR_SPEC)]
pub exec const MASK_ADDR: usize
    ensures
        MASK_ADDR == MASK_ADDR_SPEC,
{
    proof {
        axiom_max_phyaddr_width_facts();
    }
    bitmask_inc!(12usize, MAX_PHYADDR_WIDTH - 1)
}

pub spec const MASK_L1_PG_ADDR_SPEC: usize = bitmask_inc!(30usize, MAX_PHYADDR_WIDTH - 1);

#[verifier::when_used_as_spec(MASK_L1_PG_ADDR_SPEC)]
pub exec const MASK_L1_PG_ADDR: usize
    ensures
        MASK_L1_PG_ADDR == MASK_L1_PG_ADDR_SPEC,
{
    proof {
        axiom_max_phyaddr_width_facts();
    }
    bitmask_inc!(30usize, MAX_PHYADDR_WIDTH - 1)
}

pub spec const MASK_L2_PG_ADDR_SPEC: usize = bitmask_inc!(21usize, MAX_PHYADDR_WIDTH - 1);

#[verifier::when_used_as_spec(MASK_L2_PG_ADDR_SPEC)]
pub exec const MASK_L2_PG_ADDR: usize
    ensures
        MASK_L2_PG_ADDR == MASK_L2_PG_ADDR_SPEC,
{
    proof {
        axiom_max_phyaddr_width_facts();
    }
    bitmask_inc!(21usize, MAX_PHYADDR_WIDTH - 1)
}

pub spec const MASK_L3_PG_ADDR_SPEC: usize = bitmask_inc!(12usize, MAX_PHYADDR_WIDTH - 1);

#[verifier::when_used_as_spec(MASK_L3_PG_ADDR_SPEC)]
pub exec const MASK_L3_PG_ADDR: usize
    ensures
        MASK_L3_PG_ADDR == MASK_L3_PG_ADDR_SPEC,
{
    proof {
        axiom_max_phyaddr_width_facts();
    }
    bitmask_inc!(12usize, MAX_PHYADDR_WIDTH - 1)
}

pub spec const MASK_DIR_ADDR_SPEC: usize = MASK_ADDR;

#[verifier::when_used_as_spec(MASK_DIR_ADDR_SPEC)]
pub exec const MASK_DIR_ADDR: usize
    ensures
        MASK_DIR_ADDR == MASK_DIR_ADDR_SPEC,
{
    MASK_ADDR
}

#[allow(repr_transparent_external_private_fields)]
// An entry in any page directory (i.e. in PML4, PDPT, PD or PT)
#[repr(transparent)]
pub struct PDE {
    pub entry: usize,
    pub layer: Ghost<nat>,
}

// This impl defines everything necessary for the page table walk semantics.
// PDE is reused in the implementation, which has an additional impl block for it in
// `impl_u::l2_impl`.
impl PDE {
    // Could prove that the address is smaller than MAX_PHYADDR but this bound is sufficient sof ar
    pub broadcast proof fn lemma_view_addr_aligned(self)
        requires
            self.layer@ < 4,
        ensures
            #![trigger self.view()]
            self@ is Directory ==> {
                &&& aligned(self@->Directory_addr as nat, 4096)
                &&& aligned(self@->Directory_addr as nat, 8)
                &&& self@->Directory_addr < usize::MAX - 4096
            },
            self@ is Page ==> {
                &&& aligned(self@->Page_addr as nat, 4096)
                &&& aligned(self@->Page_addr as nat, 8)
                &&& self@->Page_addr < usize::MAX - 4096
            },
    {
        axiom_max_phyaddr_width_facts();
        let mw = MAX_PHYADDR_WIDTH;
        let e = self.entry;
        assert((e & bitmask_inc!(12usize, mw - 1)) % 4096 == 0) by (bit_vector);
        assert((e & bitmask_inc!(21usize, mw - 1)) % 4096 == 0) by (bit_vector);
        assert((e & bitmask_inc!(30usize, mw - 1)) % 4096 == 0) by (bit_vector);
        assert((e & bitmask_inc!(12usize, mw - 1)) < u64::MAX - 4096) by (bit_vector)
            requires
                32 <= mw <= 52,
        ;
        assert((e & bitmask_inc!(21usize, mw - 1)) < u64::MAX - 4096) by (bit_vector)
            requires
                32 <= mw <= 52,
        ;
        assert((e & bitmask_inc!(30usize, mw - 1)) < u64::MAX - 4096) by (bit_vector)
            requires
                32 <= mw <= 52,
        ;
    }

    pub broadcast proof fn lemma_view_unchanged_dirty_access(self, other: PDE)
        requires
            self.layer@ < 4,
            #[trigger] (self.entry & MASK_NEG_DIRTY_ACCESS) == #[trigger] (other.entry
                & MASK_NEG_DIRTY_ACCESS),
            self.layer == other.layer,
        ensures
            other@ == self@,
    {
        reveal(PDE::all_mb0_bits_are_zero);
        let v1 = self.entry;
        let v2 = other.entry;
        assert(forall|b: usize| 0 <= b < 5 ==> #[trigger] (v1 & bit!(b)) == v2 & bit!(b))
            by (bit_vector)
            requires
                v1 & !(bit!(5) | bit!(6)) == v2 & !(bit!(5) | bit!(6)),
        ;
        assert(forall|b: usize| 6 < b < 64 ==> #[trigger] (v1 & bit!(b)) == v2 & bit!(b))
            by (bit_vector)
            requires
                v1 & !(bit!(5) | bit!(6)) == v2 & !(bit!(5) | bit!(6)),
        ;
        axiom_max_phyaddr_width_facts();
        let mw = MAX_PHYADDR_WIDTH;

        assert(v1 & bitmask_inc!(12usize, mw - 1) == v2 & bitmask_inc!(12usize, mw - 1))
            by (bit_vector)
            requires
                v1 & !(bit!(5) | bit!(6)) == v2 & !(bit!(5) | bit!(6)),
                32 <= mw <= 52,
        ;
        assert(v1 & bitmask_inc!(21usize, mw - 1) == v2 & bitmask_inc!(21usize, mw - 1))
            by (bit_vector)
            requires
                v1 & !(bit!(5) | bit!(6)) == v2 & !(bit!(5) | bit!(6)),
                32 <= mw <= 52,
        ;
        assert(v1 & bitmask_inc!(30usize, mw - 1) == v2 & bitmask_inc!(30usize, mw - 1))
            by (bit_vector)
            requires
                v1 & !(bit!(5) | bit!(6)) == v2 & !(bit!(5) | bit!(6)),
                32 <= mw <= 52,
        ;
        assert(v1 & bitmask_inc!(mw, 51) == v2 & bitmask_inc!(mw, 51)) by (bit_vector)
            requires
                v1 & !(bit!(5) | bit!(6)) == v2 & !(bit!(5) | bit!(6)),
                32 <= mw <= 52,
        ;
        assert(v1 & bitmask_inc!(mw, 62) == v2 & bitmask_inc!(mw, 62)) by (bit_vector)
            requires
                v1 & !(bit!(5) | bit!(6)) == v2 & !(bit!(5) | bit!(6)),
                32 <= mw <= 52,
        ;
        assert(v1 & bitmask_inc!(13, 29) == v2 & bitmask_inc!(13, 29)) by (bit_vector)
            requires
                v1 & !(bit!(5) | bit!(6)) == v2 & !(bit!(5) | bit!(6)),
        ;
        assert(v1 & bitmask_inc!(13, 20) == v2 & bitmask_inc!(13, 20)) by (bit_vector)
            requires
                v1 & !(bit!(5) | bit!(6)) == v2 & !(bit!(5) | bit!(6)),
        ;
    }

    pub open spec fn view(self) -> GPDE {
        let v = self.entry;
        let P = v & MASK_FLAG_P == MASK_FLAG_P;
        let RW = v & MASK_FLAG_RW == MASK_FLAG_RW;
        let US = v & MASK_FLAG_US == MASK_FLAG_US;
        let PWT = v & MASK_FLAG_PWT == MASK_FLAG_PWT;
        let PCD = v & MASK_FLAG_PCD == MASK_FLAG_PCD;
        let XD = v & MASK_FLAG_XD == MASK_FLAG_XD;
        let G = v & MASK_PG_FLAG_G == MASK_PG_FLAG_G;
        if v & MASK_FLAG_P == MASK_FLAG_P && self.all_mb0_bits_are_zero() {
            if self.layer == 0 {
                let addr = v & MASK_ADDR;
                GPDE::Directory { addr, P, RW, US, PWT, PCD, XD }
            } else if self.layer == 1 {
                if v & MASK_L1_PG_FLAG_PS == MASK_L1_PG_FLAG_PS {
                    // super page mapping
                    let addr = v & MASK_L1_PG_ADDR;
                    let PAT = v & MASK_PG_FLAG_PAT == MASK_PG_FLAG_PAT;
                    GPDE::Page { addr, P, RW, US, PWT, PCD, G, PAT, XD }
                } else {
                    let addr = v & MASK_ADDR;
                    GPDE::Directory { addr, P, RW, US, PWT, PCD, XD }
                }
            } else if self.layer == 2 {
                if v & MASK_L2_PG_FLAG_PS == MASK_L2_PG_FLAG_PS {
                    // huge page mapping
                    let addr = v & MASK_L2_PG_ADDR;
                    let PAT = v & MASK_PG_FLAG_PAT == MASK_PG_FLAG_PAT;
                    GPDE::Page { addr, P, RW, US, PWT, PCD, G, PAT, XD }
                } else {
                    let addr = v & MASK_ADDR;
                    GPDE::Directory { addr, P, RW, US, PWT, PCD, XD }
                }
            } else if self.layer == 3 {
                let addr = v & MASK_L3_PG_ADDR;
                let PAT = v & MASK_L3_PG_FLAG_PAT == MASK_L3_PG_FLAG_PAT;
                GPDE::Page { addr, P, RW, US, PWT, PCD, G, PAT, XD }
            } else {
                arbitrary()
            }
        } else {
            GPDE::Invalid
        }
    }

    /// Returns `true` iff all must-be-zero bits for a given entry are zero.
    #[verifier::opaque]
    pub open spec fn all_mb0_bits_are_zero(self) -> bool {
        if self.layer == 0 {  // PML4, always directory
            // 51:M, 7
            &&& self.entry & bitmask_inc!(MAX_PHYADDR_WIDTH, 51) == 0
            &&& self.entry & bit!(7usize) == 0
        } else if self.layer == 1 {  // PDPT
            if self.entry & MASK_L1_PG_FLAG_PS == MASK_L1_PG_FLAG_PS {
                // 51:M, 29:13
                &&& self.entry & bitmask_inc!(MAX_PHYADDR_WIDTH, 51) == 0
                &&& self.entry & bitmask_inc!(13usize,29usize) == 0
            } else {
                // 51:M, 7
                &&& self.entry & bitmask_inc!(MAX_PHYADDR_WIDTH, 51) == 0
                &&& self.entry & bit!(7usize) == 0
            }
        } else if self.layer == 2 {  // PD
            if self.entry & MASK_L2_PG_FLAG_PS == MASK_L2_PG_FLAG_PS {
                // 62:M, 20:13
                &&& self.entry & bitmask_inc!(MAX_PHYADDR_WIDTH, 62) == 0
                &&& self.entry & bitmask_inc!(13usize,20usize) == 0
            } else {
                // 62:M, 7
                &&& self.entry & bitmask_inc!(MAX_PHYADDR_WIDTH, 62) == 0
                &&& self.entry & bit!(7usize) == 0
            }
        } else if self.layer == 3 {  // PT, always frame
            // 62:M
            self.entry & bitmask_inc!(MAX_PHYADDR_WIDTH, 62) == 0
        } else {
            arbitrary()
        }
    }

    pub open spec fn layer(self) -> nat {
        self.layer@
    }
}

impl Flags {
    //pub open spec fn from_GPDEs(pdes: Seq<GPDE>) -> Flags
    //    recommends
    //        pdes.len() > 0,
    //        forall|i| 0 <= i < pdes.len() ==> !(pdes[i] is Invalid)
    //    decreases pdes.len()
    //{
    //    if pdes.len() <= 1 {
    //        Flags::from_GPDE(pdes[0])
    //    } else {
    //        Flags::from_GPDEs(pdes.drop_first()).combine(Flags::from_GPDE(pdes[0]))
    //    }
    //}
    pub open spec fn from_GPDE(pde: GPDE) -> Flags
        recommends
            !(pde is Invalid),
    {
        match pde {
            GPDE::Directory { RW, US, XD, .. } => Flags::from_bits(RW, US, XD),
            GPDE::Page { RW, US, XD, .. } => Flags::from_bits(RW, US, XD),
            _ => arbitrary(),
        }
    }
}

#[allow(unused_macros)]
macro_rules! l0_bits {
    ($addr:expr) => { ($addr & bitmask_inc!(39usize,47usize)) >> 39usize }
}

pub(crate) use l0_bits;

#[allow(unused_macros)]
macro_rules! l1_bits {
    ($addr:expr) => { ($addr & bitmask_inc!(30usize,38usize)) >> 30usize }
}

pub(crate) use l1_bits;

#[allow(unused_macros)]
macro_rules! l2_bits {
    ($addr:expr) => { ($addr & bitmask_inc!(21usize,29usize)) >> 21usize }
}

pub(crate) use l2_bits;

#[allow(unused_macros)]
macro_rules! l3_bits {
    ($addr:expr) => { ($addr & bitmask_inc!(12usize,20usize)) >> 12usize }
}

pub(crate) use l3_bits;

// Don't broadcast this. It refuses to trigger for some reason.
pub proof fn lemma_bit_indices_less_512(va: usize)
    ensures
        l0_bits!(va) < 512,
        l1_bits!(va) < 512,
        l2_bits!(va) < 512,
        l3_bits!(va) < 512,
{
    assert(l0_bits!(va) < 512) by (bit_vector);
    assert(l1_bits!(va) < 512) by (bit_vector);
    assert(l2_bits!(va) < 512) by (bit_vector);
    assert(l3_bits!(va) < 512) by (bit_vector);
}

} // verus!
