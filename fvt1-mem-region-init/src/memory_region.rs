// SPDX-License-Identifier: MPL-2.0

//! Information of memory regions in the boot phase.
//!

use vstd::prelude::*;

use core::mem::swap;

use super::common::*;
use super::model::*;

verus! {

/// The type of initial memory regions that are needed for the kernel.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum MemoryRegionType {
    /// Maybe points to an unplugged DIMM module. It's bad anyway.
    BadMemory = 0,
    /// In ACPI spec, this area needs to be preserved when sleeping.
    NonVolatileSleep = 1,
    /// Reserved by BIOS or bootloader, do not use.
    Reserved = 2,
    /// The place where kernel sections are loaded.
    Kernel = 3,
    /// The place where kernel modules (e.g. initrd) are loaded, could be reused.
    Module = 4,
    /// The memory region provided as the framebuffer.
    Framebuffer = 5,
    /// Once used in the boot phase. Kernel can reclaim it after initialization.
    Reclaimable = 6,
    /// Directly usable by the frame allocator.
    Usable = 7,
}

impl MemoryRegionType {

    pub open spec fn is_usable(&self) -> bool {
        if let Self::Reclaimable | Self::Usable = self { true }
        else { false }
    }

    pub open spec fn is_unusable(&self) -> bool {
        if let Self::Reclaimable | Self::Usable = self { false }
        else { true }
    }

    pub open spec fn to_int(&self) -> int {
        match &self {
            MemoryRegionType::BadMemory => 0,
            MemoryRegionType::NonVolatileSleep => 1,
            MemoryRegionType::Reserved => 2,
            MemoryRegionType::Kernel => 3,
            MemoryRegionType::Module => 4,
            MemoryRegionType::Framebuffer => 5,
            MemoryRegionType::Reclaimable => 6,
            MemoryRegionType::Usable => 7,
        }
    }

}

}

verus! {

/// The information of initial memory regions that the kernel needs.
/// Regions may overlap. The region must be page aligned.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct MemoryRegion {
    pub base: usize,
    pub len: usize,
    pub typ: MemoryRegionType,
}

impl MemoryRegion {
    pub open spec fn invariants(&self, state: &MemRegionModel) -> bool {
        self.base + self.len <= MAX_PADDR &&
        self.base as int == state.base &&
        self.len as int == state.end - state.base &&
        self.typ.to_int() == state.typ &&
        state.invariants()
    }
}

impl MemoryRegion {
    fn gen_state(self) -> (res: (Self, Tracked<MemRegionModel>))
        requires
            self.base + self.len <= MAX_PADDR,
        ensures
            res.0.invariants(&res.1@),
            res.0.base == self.base,
            res.0.len == self.len,
            res.0.typ.to_int() == self.typ.to_int(),
    {
        (self, Tracked(MemRegionModel {
            base: self.base as int,
            end: self.base + self.len,
            typ: self.typ.to_int(),
        }))
    }

    /// Constructs a valid memory region.
    pub fn new(
        base: usize, len: usize, typ: MemoryRegionType
    ) -> (res: (Self, Tracked<MemRegionModel>))
        requires
            base + len <= MAX_PADDR,
        ensures
            res.0.invariants(&res.1@),
    {
        MemoryRegion { base, len, typ }.gen_state()
    }

    /// Constructs a memory region where kernel sections are loaded.
    ///
    /// Most boot protocols do not mark the place where the kernel loads as unusable. In this case,
    /// we need to explicitly construct and append this memory region.
    #[verifier::external_body]
    pub fn kernel() -> (res: (Self, Tracked<MemRegionModel>))
        ensures
            res.0.invariants(&res.1@),
    {
        // These are physical addresses provided by the linker script.
        extern "C" {
            fn __kernel_start();
            fn __kernel_end();
        }
        MemoryRegion {
            base: __kernel_start as usize - kernel_loaded_offset(),
            len: __kernel_end as usize - __kernel_start as usize,
            typ: MemoryRegionType::Kernel,
        }.gen_state()
    }

    /// The physical address of the base of the region.
    pub fn base(
        &self, state: &Tracked<MemRegionModel>
    ) -> (base: usize)
        requires
            self.invariants(&state@),
        ensures
            base == self.base,
    {
        self.base
    }

    /// The length in bytes of the region.
    pub fn len(
        &self, state: &Tracked<MemRegionModel>
    ) -> (len: usize)
        requires
            self.invariants(&state@),
        ensures
            len == self.len,
    {
        self.len
    }

    /// Checks whether the region is empty
    pub fn is_empty(
        &self, state: &Tracked<MemRegionModel>
    ) -> (is_empty: bool)
        requires
            self.invariants(&state@),
        ensures
            is_empty == (self.len == 0),
    {
        self.len == 0
    }

    /// The type of the region.
    pub fn typ(
        &self, state: &Tracked<MemRegionModel>
    ) -> (typ: MemoryRegionType)
        requires
            self.invariants(&state@),
        ensures
            typ == self.typ,
    {
        self.typ
    }

    /// Removes range `t` from self, resulting in 0, 1 or 2 truncated ranges.
    /// We need to have this method since memory regions can overlap.
    pub fn truncate(
        &self, s1: Tracked<MemRegionModel>,
        t: &MemoryRegion, s2: &Tracked<MemRegionModel>
    ) -> (regions: Vec<(MemoryRegion, Tracked<MemRegionModel>)>)
        requires
            self.invariants(&s1@),
            t.invariants(&s2@),
        ensures
            forall|i: int| #![auto]
                0 <= i < regions.len() ==>
                regions[i].0.invariants(&regions[i].1@) &&
                regions[i].1@.is_sub_region(&s1@) &&
                s2@.is_separate(&regions[i].1@),
            forall|i: int, j: int| #![auto]
                0 <= i < j < regions.len() ==>
                regions[i].1@.is_separate(&regions[j].1@),
    {
        if self.base < t.base {
            if self.base + self.len > t.base {
                if self.base + self.len > t.base + t.len {
                    vec![MemoryRegion {
                        base: self.base,
                        len: t.base - self.base,
                        typ: self.typ,
                    }.gen_state(),
                    MemoryRegion {
                        base: t.base + t.len,
                        len: self.base + self.len - (t.base + t.len),
                        typ: self.typ,
                    }.gen_state()]
                } else {
                    vec![MemoryRegion {
                        base: self.base,
                        len: t.base - self.base,
                        typ: self.typ,
                    }.gen_state()]
                }
            } else {
                vec![(*self, s1)]
            }
        } else if self.base < t.base + t.len {
            if self.base + self.len > t.base + t.len {
                vec![MemoryRegion {
                    base: t.base + t.len,
                    len: self.base + self.len - (t.base + t.len),
                    typ: self.typ,
                }.gen_state()]
            } else {
                vec![]
            }
        } else {
            vec![(*self, s1)]
        }
    }
}

}

verus! {

pub proof fn separate_transitivity(
    region: &(MemoryRegion, Tracked<MemRegionModel>),
    sub_region: &(MemoryRegion, Tracked<MemRegionModel>),
    separate_region: &(MemoryRegion, Tracked<MemRegionModel>),
)
    requires
        sub_region.1@.is_sub_region(&region.1@),
        separate_region.1@.is_separate(&region.1@),
    ensures
        separate_region.1@.is_separate(&sub_region.1@),
{}

}

verus! {

fn regions_split(
    regions: &[(MemoryRegion, Tracked<MemRegionModel>)]
) -> (res: (Vec<(MemoryRegion, Tracked<MemRegionModel>)>, Vec<(MemoryRegion, Tracked<MemRegionModel>)>))
    requires
        forall|i: int| #![trigger regions[i]]
            0 <= i < regions.len() ==>
            regions[i].0.invariants(&regions[i].1@),
    ensures
        forall|i: int| #![auto]
            0 <= i < res.0.len() ==>
            res.0[i].0.invariants(&res.0[i].1@) && res.0[i].0.typ.is_usable(),
        forall|i: int| #![auto]
            0 <= i < res.1.len() ==>
            res.1[i].0.invariants(&res.1[i].1@) && res.1[i].0.typ.is_unusable(),
{
    let mut regions_usable = Vec::<(MemoryRegion, Tracked<MemRegionModel>)>::new();
    let mut regions_unusable = Vec::<(MemoryRegion, Tracked<MemRegionModel>)>::new();

    let mut i = 0;
    while i < regions.len()
    invariant
        0 <= i <= regions.len(),
        forall|j: int| #![trigger regions[j]]
            0 <= j < regions.len() ==>
            regions[j].0.invariants(&regions[j].1@),
        forall|j: int| #![auto]
            0 <= j < regions_usable.len() ==>
            regions_usable[j].0.invariants(&regions_usable[j].1@) &&
            regions_usable[j].0.typ.is_usable(),
        forall|j: int| #![auto]
            0 <= j < regions_unusable.len() ==>
            regions_unusable[j].0.invariants(&regions_unusable[j].1@) &&
            regions_unusable[j].0.typ.is_unusable(),
    decreases
        regions.len()-i,
     {
        let r = &regions[i];
        match r.0.typ {
            MemoryRegionType::Usable | MemoryRegionType::Reclaimable => {
                regions_usable.push(r.0.gen_state());
            }
            _ => {
                regions_unusable.push(r.0.gen_state());
            }
        }
        i = i + 1;
    }

    (regions_usable, regions_unusable)
}

fn regions_append(
    mut regions_unusable: Vec<(MemoryRegion, Tracked<MemRegionModel>)>,
    mut regions_usable: Vec<(MemoryRegion, Tracked<MemRegionModel>)>,
) -> (res: Vec<(MemoryRegion, Tracked<MemRegionModel>)>)
    requires
        forall|i: int| #![auto]
            0 <= i < regions_unusable.len() ==>
            regions_unusable[i].0.invariants(&regions_unusable[i].1@) &&
            regions_unusable[i].0.typ.is_unusable(),
        forall|i: int| #![auto]
            0 <= i < regions_usable.len() ==>
            regions_usable[i].0.invariants(&regions_usable[i].1@) &&
            regions_usable[i].0.typ.is_usable(),
        forall|i: int, j: int| #![auto]
            0 <= i < regions_unusable.len() && 0 <= j < regions_usable.len() ==>
            regions_unusable[i].1@.is_separate(&regions_usable[j].1@),
    ensures
        forall|i: int| #![auto]
            0 <= i < res.len() ==>
            res[i].0.invariants(&res[i].1@),
        forall|i: int, j: int| #![auto]
            0 <= i < j < res.len() &&
            res[i].0.typ.is_unusable() &&
            res[j].0.typ.is_usable() ==>
            res[i].1@.is_separate(&res[j].1@),
{
    let mut all_regions = regions_unusable;
    all_regions.append(&mut regions_usable);
    all_regions
}

fn regions_trans(
    mut dst: Vec<(MemoryRegion, Tracked<MemRegionModel>)>,
    mut src: Vec<(MemoryRegion, Tracked<MemRegionModel>)>
) -> (res: (Vec<(MemoryRegion, Tracked<MemRegionModel>)>, Vec<(MemoryRegion, Tracked<MemRegionModel>)>))
    requires
        forall|i: int| #![auto]
            0 <= i < src.len() ==>
            src[i].0.invariants(&src[i].1@),

        dst.view() =~= Seq::<(MemoryRegion, Tracked<MemRegionModel>)>::empty(),
    ensures
        forall|i: int| #![auto]
            0 <= i < res.0.len() ==>
            res.0[i].0.invariants(&res.0[i].1@),

        res.0.view() =~= src.view(),
        res.1.view() =~= Seq::<(MemoryRegion, Tracked<MemRegionModel>)>::empty(),
{
    (src, dst)
}

fn non_overlapping_regions_from_inner(
    regions_unusable: &Vec<(MemoryRegion, Tracked<MemRegionModel>)>,
    regions_usable: Vec<(MemoryRegion, Tracked<MemRegionModel>)>,
) -> (res: Vec<(MemoryRegion, Tracked<MemRegionModel>)>)
    requires
        forall|i: int| #![auto]
            0 <= i < regions_unusable.len() ==>
            regions_unusable[i].0.invariants(&regions_unusable[i].1@) &&
            regions_unusable[i].0.typ.is_unusable(),
        forall|i: int| #![auto]
            0 <= i < regions_usable.len() ==>
            regions_usable[i].0.invariants(&regions_usable[i].1@) &&
            regions_usable[i].0.typ.is_usable(),
    ensures
        forall|i: int| #![auto]
            0 <= i < res.len() ==>
            res[i].0.invariants(&res[i].1@) && res[i].0.typ.is_usable(),
        forall|i: int, j: int| #![auto]
            0 <= i < regions_unusable.len() && 0 <= j < res.len() ==>
            regions_unusable[i].1@.is_separate(&res[j].1@),
{
    // `regions_*` are 2 rolling vectors since we are going to truncate
    // the regions in a iterative manner.
    let mut regions_src = regions_usable;
    let mut regions_dst = Vec::<(MemoryRegion, Tracked<MemRegionModel>)>::new();
    // Truncate the usable regions.
    let mut _i = 0;
    while _i < regions_unusable.len()
        invariant
            0 <= _i <= regions_unusable.len(),
            regions_dst.len() == 0,

            forall|i: int| #![auto] 0 <= i < regions_unusable.len() ==>
                regions_unusable[i].0.invariants(&regions_unusable[i].1@),
            forall|i: int| #![auto] 0 <= i < regions_src.len() ==>
                regions_src[i].0.invariants(&regions_src[i].1@) &&
                regions_src[i].0.typ.is_usable(),
            forall|i: int| #![auto] 0 <= i < regions_dst.len() ==>
                regions_dst[i].0.invariants(&regions_dst[i].1@) &&
                regions_dst[i].0.typ.is_usable(),

            forall|i: int, j: int| #![auto]
                0 <= i < _i && 0 <= j < regions_src.len() ==>
                regions_unusable[i].1@.is_separate(&regions_src[j].1@),
        decreases
            regions_unusable.len()-_i,
    {
        let mut _j = 0;
        while _j < regions_src.len()
            invariant
                0 <= _i < regions_unusable.len(),
                0 <= _j <= regions_src.len(),
                regions_unusable[_i as int].0.invariants(&regions_unusable[_i as int].1@),

                forall|i: int| #![auto] 0 <= i < regions_src.len() ==>
                    regions_src[i].0.invariants(&regions_src[i].1@) &&
                    regions_src[i].0.typ.is_usable(),
                forall|i: int| #![auto] 0 <= i < regions_dst.len() ==>
                    regions_dst[i].0.invariants(&regions_dst[i].1@) &&
                    regions_dst[i].0.typ.is_usable(),

                forall|i: int| #![auto] 0 <= i < regions_dst.len() ==>
                    regions_unusable[_i as int].1@.is_separate(&regions_dst[i].1@),
                forall|i: int, j: int| #![auto]
                    0 <= i < _i && 0 <= j < regions_src.len() ==>
                    regions_unusable[i].1@.is_separate(&regions_src[j].1@),
                forall|i: int, j: int| #![auto]
                    0 <= i < _i && 0 <= j < regions_dst.len() ==>
                    regions_unusable[i].1@.is_separate(&regions_dst[j].1@),
            decreases
                regions_src.len() - _j,
        {
            let (r_usable, s_usable) = regions_src[_j].0.gen_state();
            let mut res_vec = r_usable.truncate(s_usable, &regions_unusable[_i].0, &regions_unusable[_i].1);

            // Append two region vectors
            while res_vec.len() > 0
                invariant
                    0 <= _i < regions_unusable.len(),
                    0 <= _j < regions_src.len(),

                    forall|i: int, j: int| #![auto]
                        0 <= i < _i && 0 <= j < regions_src.len() ==>
                        regions_unusable[i].1@.is_separate(&regions_src[j].1@),

                    forall|i: int| #![auto] 0 <= i < res_vec.len() ==>
                        res_vec[i].0.invariants(&res_vec[i].1@) &&
                        res_vec[i].0.typ.is_usable() &&
                        res_vec[i].1@.is_sub_region(&regions_src[_j as int].1@) &&

                        regions_unusable[_i as int].1@.is_separate(&res_vec[i].1@),

                    forall|i: int| #![auto] 0 <= i < regions_dst.len() ==>
                        regions_dst[i].0.invariants(&regions_dst[i].1@) &&
                        regions_dst[i].0.typ.is_usable() &&

                        regions_unusable[_i as int].1@.is_separate(&regions_dst[i].1@),
                    forall|i: int, j: int| #![auto]
                        0 <= i < _i && 0 <= j < regions_dst.len() ==>
                        regions_unusable[i].1@.is_separate(&regions_dst[j].1@),
                decreases
                    res_vec.len(),
            {
                let region = res_vec.pop().unwrap();
                assert(region.1@.is_sub_region(&regions_src[_j as int].1@));
                assert(
                    forall|i: int| #![auto] 0 <= i < _i ==>
                        regions_unusable[i].1@.is_separate(&regions_src[_j as int].1@)
                );
                // Depends on lemma 'separate_transitivity', which is trivial to verus.
                assert(
                    forall|i: int| #![auto] 0 <= i < _i ==>
                        regions_unusable[i].1@.is_separate(&region.1@)
                );

                regions_dst.push(region);
            }

            _j = _j + 1
        }
        regions_src.clear();

        let res = regions_trans(regions_src, regions_dst);
        regions_src = res.0;
        regions_dst = res.1;

        _i = _i + 1;
    }

    regions_src
}

/// Truncates regions, resulting in a set of regions that does not overlap.
///
/// The truncation will be done according to the type of the regions, that
/// usable and reclaimable regions will be truncated by the unusable regions.
pub fn non_overlapping_regions_from(
    regions: &[(MemoryRegion, Tracked<MemRegionModel>)]
) -> (res: Vec<(MemoryRegion, Tracked<MemRegionModel>)>)
    requires
        forall|i: int| #![trigger regions[i]]
            0 <= i < regions.len() ==>
            regions[i].0.invariants(&regions[i].1@),
    ensures
        forall|i: int| #![auto]
            0 <= i < res.len() ==>
            res[i].0.invariants(&res[i].1@),
        forall|i: int, j: int| #![auto]
            0 <= i < j < res.len() &&
            res[i].0.typ.is_unusable() &&
            res[j].0.typ.is_usable() ==>
            res[i].1@.is_separate(&res[j].1@),

{
    // We should later use regions in `regions_unusable` to truncate all
    // regions in `regions_usable`.
    // The difference is that regions in `regions_usable` could be used by
    // the frame allocator.
    let (mut regions_usable, mut regions_unusable) = regions_split(regions);

    // `regions_*` are 2 rolling vectors since we are going to truncate
    // the regions in a iterative manner.
    let mut regions_usable =
        non_overlapping_regions_from_inner(&regions_unusable, regions_usable);

    // Combine all the regions processed.
    regions_append(regions_unusable, regions_usable)
}

}
