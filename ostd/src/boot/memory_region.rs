// SPDX-License-Identifier: MPL-2.0
//! Information of memory regions in the boot phase.
use vstd::{array::group_array_axioms, prelude::*, set_lib::lemma_len_union};
use vstd_extra::prelude::*;

use crate::{
    mm::kspace::{LINEAR_MAPPING_BASE_VADDR, VMALLOC_BASE_VADDR},
    specs::arch::*,
};

use crate::mm::{Paddr, Vaddr};
use align_ext::AlignExt;
use core::ops::Deref;

//use crate::mm::{kspace::kernel_loaded_offset, Paddr, Vaddr, PAGE_SIZE};

/// The type of initial memory regions that are needed for the kernel.
#[verus_verify]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum MemoryRegionType {
    /// Maybe points to an unplugged DIMM module. It's bad anyway.
    BadMemory = 0,
    /// Some holes not specified by the bootloader/firmware. It may be used for
    /// I/O memory but we don't know for sure.
    Unknown = 1,
    /// In ACPI spec, this area needs to be preserved when sleeping.
    NonVolatileSleep = 2,
    /// Reserved by BIOS or bootloader, do not use.
    Reserved = 3,
    /// The place where kernel sections are loaded.
    Kernel = 4,
    /// The place where kernel modules (e.g. initrd) are loaded, could be reused.
    Module = 5,
    /// The memory region provided as the framebuffer.
    Framebuffer = 6,
    /// Once used in the boot phase. Kernel can reclaim it after initialization.
    Reclaimable = 7,
    /// Directly usable by the frame allocator.
    Usable = 8,
}

/// The information of initial memory regions that are needed by the kernel.
/// Regions may overlap and have unaligned boundaries before normalization.
#[verus_verify]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct MemoryRegion {
    base: usize,
    len: usize,
    typ: MemoryRegionType,
}

verus! {

impl MemoryRegion {
    /// The page-aligned region.
    /// A `Usable` region rounds its base up and its end down. Every other type
    /// rounds its base down and its end up. The length is the distance between
    /// those endpoints, or 0 when the aligned end lies below the aligned base.
    pub open spec fn aligned_region(self) -> Self {
        let base = if self.typ() == MemoryRegionType::Usable {
            nat_align_up(self.base() as nat, PAGE_SIZE as nat)
        } else {
            nat_align_down(self.base() as nat, PAGE_SIZE as nat)
        };
        let end = if self.typ() == MemoryRegionType::Usable {
            nat_align_down((self.base() + self.len()) as nat, PAGE_SIZE as nat)
        } else {
            nat_align_up((self.base() + self.len()) as nat, PAGE_SIZE as nat)
        };
        let len = if end >= base {
            (end - base) as usize
        } else {
            0
        };
        Self::new(base as usize, len, self.typ())
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.base + self.len <= MAX_PADDR
    }

    /// Whether `self` is contained in `old_region`, with the same type.
    pub closed spec fn is_sub_region(self, old_region: Self) -> bool {
        self.typ == old_region.typ && old_region.base <= self.base && self.base + self.len
            <= old_region.base + old_region.len
    }

    /// Whether the region shares no address with `region`.
    pub closed spec fn is_separate(self, region: Self) -> bool {
        self.base + self.len <= region.base || region.base + region.len <= self.base
    }

    /// Whether both boundaries of the region are multiples of `align`.
    pub closed spec fn aligned(self, align: int) -> bool {
        self.base as int % align == 0 && (self.base + self.len) % align == 0
    }
}

} // verus!
#[verus_verify]
impl MemoryRegion {
    /// Constructs a valid memory region.
    ///
    /// # Verified Properties
    ///
    /// ## Safety
    /// - Construction preserves the region's physical-address bound.
    ///
    /// ## Functional Correctness
    /// - The result is the region with the given base, length, and type.
    ///
    /// ## Preconditions
    /// - `base + len` is at most `MAX_PADDR`.
    ///
    /// ## Postconditions
    /// - The function does not panic.
    #[verus_verify(dual_spec)]
    #[verus_spec(
        requires
            base + len <= MAX_PADDR,
        returns
            Self::new(base, len, typ),
    )]
    pub const fn new(base: Paddr, len: usize, typ: MemoryRegionType) -> Self {
        MemoryRegion { base, len, typ }
    }

    /// Constructs a bad memory region.
    ///
    /// # Verified Properties
    ///
    /// ## Safety
    /// - The empty region satisfies the physical-address bound.
    ///
    /// ## Functional Correctness
    /// - The base and length are zero, and the type is `BadMemory`.
    ///
    /// ## Preconditions
    /// - There are no caller obligations.
    ///
    /// ## Postconditions
    /// - The function does not panic.
    #[verus_verify(dual_spec)]
    #[verus_spec(
        returns Self::bad(),
    )]
    pub const fn bad() -> Self {
        MemoryRegion {
            base: 0,
            len: 0,
            typ: MemoryRegionType::BadMemory,
        }
    }

    /*
    /// Constructs a memory region where kernel sections are loaded.
    ///
    /// Most boot protocols do not mark the place where the kernel loads as unusable. In this case,
    /// we need to explicitly construct and append this memory region.
    pub fn kernel() -> Self {
        // These are physical addresses provided by the linker script.
        extern "C" {
            fn __kernel_start();
            fn __kernel_end();
        }
        MemoryRegion {
            base: __kernel_start as usize - kernel_loaded_offset(),
            len: __kernel_end as usize - __kernel_start as usize,
            typ: MemoryRegionType::Kernel,
        }
    }

    */
    /// Constructs a framebuffer memory region.
    ///
    /// # Verified Properties
    ///
    /// ## Safety
    /// - Both pixel-size multiplications are bounded, so they do not overflow.
    ///
    /// ## Functional Correctness
    /// - Converts the framebuffer's bit size to a byte range.
    ///
    /// ## Preconditions
    /// - `fb.width * fb.height` fits in `usize`.
    /// - `fb.width * fb.height * fb.bpp` fits in `usize`.
    /// - The framebuffer's physical end is at most `MAX_PADDR`.
    ///
    /// ## Postconditions
    /// - The result has base `fb.address`, length
    ///   `(width * height * bpp + 7) / 8`, and type `Framebuffer`.
    /// - The function does not panic.
    #[verus_spec(
        requires
            fb.width * fb.height <= usize::MAX,
            fb.width * fb.height * fb.bpp <= usize::MAX,
            fb.address + (fb.width * fb.height * fb.bpp + 7) / 8 <= MAX_PADDR,
        returns
            Self::new(fb.address, ((fb.width * fb.height * fb.bpp + 7) / 8) as usize,
                MemoryRegionType::Framebuffer),
    )]
    pub fn framebuffer(fb: &crate::boot::BootloaderFramebufferArg) -> Self {
        Self {
            base: fb.address,
            len: (fb.width * fb.height * fb.bpp).div_ceil(8), // round up when divide with 8 (bits/Byte)
            typ: MemoryRegionType::Framebuffer,
        }
    }

    /// Constructs a module memory region from a byte slice that lives in the linear mapping.
    ///
    /// # Panics
    ///
    /// This method will panic if the byte slice does not live in the linear mapping.
    ///
    /// # Verified Properties
    ///
    /// ## Safety
    /// - The address subtraction uses the linear-mapping precondition, so the
    ///   physical base does not underflow.
    ///
    /// ## Functional Correctness
    /// - Translates the slice into a physical `Reclaimable` region.
    ///
    /// ## Preconditions
    /// - The slice's base lies in the linear mapping, below `VMALLOC_BASE_VADDR`.
    /// - The translated physical end is at most `MAX_PADDR`.
    ///
    /// ## Postconditions
    /// - The base is the slice's physical address, and the length is the slice length.
    /// - The function does not panic when its preconditions hold.
    #[verus_spec(
        requires
            LINEAR_MAPPING_BASE_VADDR <= (bytes.as_ptr() as usize) < VMALLOC_BASE_VADDR,
            (bytes.as_ptr() as usize) - LINEAR_MAPPING_BASE_VADDR + bytes.len() <= MAX_PADDR,
        returns
            Self::new((bytes.as_ptr() as usize - LINEAR_MAPPING_BASE_VADDR) as usize,
                bytes.len(), MemoryRegionType::Reclaimable),
    )]
    pub fn module(bytes: &[u8]) -> Self {
        let vaddr = bytes.as_ptr() as Vaddr;
        assert!(crate::mm::kspace::LINEAR_MAPPING_VADDR_RANGE.contains(&vaddr));

        Self {
            base: vaddr - crate::mm::kspace::LINEAR_MAPPING_BASE_VADDR,
            len: bytes.len(),
            typ: MemoryRegionType::Reclaimable,
        }
    }

    /// The physical address of the base of the region.
    #[verus_verify(dual_spec)]
    #[verus_spec(returns self.base())]
    pub fn base(&self) -> Paddr {
        self.base
    }

    /// The length in bytes of the region.
    #[verus_verify(dual_spec)]
    #[verus_spec(returns self.len())]
    pub fn len(&self) -> usize {
        self.len
    }

    /// The physical address of the end of the region.
    #[verus_verify(dual_spec)]
    #[verus_spec(returns self.end())]
    pub fn end(&self) -> Paddr {
        proof! {
            use_type_invariant(self);
        }
        self.base + self.len
    }

    /// Checks whether the region is empty
    #[verus_verify(dual_spec)]
    #[verus_spec(returns self.is_empty())]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// The type of the region.
    #[verus_verify(dual_spec)]
    #[verus_spec(returns self.typ())]
    pub fn typ(&self) -> MemoryRegionType {
        self.typ
    }

    /// Returns the region with boundaries rounded to `PAGE_SIZE` boundaries:
    /// inward for `Usable` regions, outward for the others.
    #[verus_spec(ret =>
        ensures
            ret.aligned(PAGE_SIZE as int),
            self.typ == MemoryRegionType::Usable && ret.len() > 0 ==> ret.is_sub_region(*self),
            self.typ != MemoryRegionType::Usable ==> self.is_sub_region(ret),
        returns self.aligned_region(),
    )]
    fn as_aligned(&self) -> Self {
        proof! {
            use_type_invariant(self);
            lemma_pow2_is_pow2_to64();
        }
        // [FIXED] BUG FOUND BY FV: inward alignment can underflow the length.
        // https://github.com/asterinas/asterinas/issues/3887
        let (base, len) = match self.typ() {
            MemoryRegionType::Usable => {
                let aligned_base = self.base().align_up(PAGE_SIZE);
                let aligned_end = self.end().align_down(PAGE_SIZE);
                (aligned_base, aligned_end.saturating_sub(aligned_base))
            }
            _ => {
                let aligned_base = self.base().align_down(PAGE_SIZE);
                let aligned_end = self.end().align_up(PAGE_SIZE);
                (aligned_base, aligned_end - aligned_base)
            }
        };
        MemoryRegion {
            base,
            len,
            typ: self.typ,
        }
    }
}

/// The maximum number of regions that can be handled.
///
/// The choice of 512 is probably fine since old Linux boot protocol only
/// allows 128 regions.
//
// TODO: confirm the number or make it configurable.
pub const MAX_REGIONS: usize = 512;

/// A heapless set of memory regions.
///
/// The set cannot contain more than `LEN` regions.
#[verus_verify]
pub struct MemoryRegionArray<const LEN: usize = MAX_REGIONS> {
    regions: [MemoryRegion; LEN],
    count: usize,
}

verus! {

impl<const LEN: usize> MemoryRegionArray<LEN> {
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.count <= LEN
    }

    /// The active regions after page alignment and removal of empty regions.
    pub closed spec fn aligned_regions(self) -> Seq<MemoryRegion> {
        self@.map_values(|r: MemoryRegion| r.aligned_region()).filter(|r: MemoryRegion| r.len > 0)
    }
}

/// A contiguous, page-aligned partition of `[0, end)`.
pub closed spec fn is_partition(rs: Seq<MemoryRegion>, end: int) -> bool {
    &&& (if rs.len() == 0 {
        end == 0
    } else {
        rs[0].base == 0 && rs[rs.len() - 1].base + rs[rs.len() - 1].len == end
    })
    &&& (forall|i: int|
        0 <= i < rs.len() ==> {
            &&& #[trigger] rs[i].aligned(PAGE_SIZE as int)
            &&& rs[i].len > 0
            &&& rs[i].base + rs[i].len <= MAX_PADDR
            &&& (i > 0 ==> rs[i - 1].base + rs[i - 1].len == rs[i].base)
        })
}

/// The boundaries at which the sweep can advance.
closed spec fn region_boundaries(rs: Seq<MemoryRegion>) -> Set<int> {
    rs.map_values(|r: MemoryRegion| r.base as int).to_set().union(
        rs.map_values(|r: MemoryRegion| r.base + r.len).to_set(),
    )
}

/// The type selected by the lowest-usability covering input region.
#[verifier::opaque]
closed spec fn selected_type(rs: Seq<MemoryRegion>, addr: int, typ: MemoryRegionType) -> bool {
    &&& (rs.any(|r: MemoryRegion| r.base <= addr < r.base + r.len) ==> rs.any(
        |r: MemoryRegion| r.base <= addr < r.base + r.len && r.typ == typ,
    ))
    &&& rs.all(|r: MemoryRegion| r.base <= addr < r.base + r.len ==> typ as int <= r.typ as int)
    &&& (!rs.any(|r: MemoryRegion| r.base <= addr < r.base + r.len) ==> typ
        == MemoryRegionType::Unknown)
}

/// Every output byte carries the most restrictive covering input type.
pub closed spec fn preserves_types(output: Seq<MemoryRegion>, input: Seq<MemoryRegion>) -> bool {
    forall|i: int, addr: int|
        #![trigger output[i], selected_type(input, addr, output[i].typ)]
        0 <= i < output.len() && output[i].base <= addr < output[i].base + output[i].len
            ==> selected_type(input, addr, output[i].typ)
}

/// Adjacent regions have different types, so no further merge is possible.
#[verifier::opaque]
pub closed spec fn coalesced(rs: Seq<MemoryRegion>) -> bool {
    forall|j: int| 0 < j < rs.len() ==> #[trigger] rs[j].typ != rs[j - 1].typ
}

impl<const LEN: usize> View for MemoryRegionArray<LEN> {
    type V = Seq<MemoryRegion>;

    closed spec fn view(&self) -> Seq<MemoryRegion> {
        Seq::new(self.count as nat, |i: int| self.regions[i])
    }
}

} // verus!
#[verus_verify]
impl<const LEN: usize> Default for MemoryRegionArray<LEN> {
    /// Returns an empty set.
    ///
    /// # Verified Properties
    ///
    /// ## Safety
    /// - All array elements are initialized.
    ///
    /// ## Functional Correctness
    /// - Uses the initialization contract of [`Self::new`].
    ///
    /// ## Preconditions
    /// - There are no caller obligations.
    ///
    /// ## Postconditions
    /// - The view is the empty sequence.
    /// - The function does not panic.
    #[verus_spec(ret =>
        ensures
            ret@ == Seq::<MemoryRegion>::empty(),
    )]
    fn default() -> Self {
        Self::new()
    }
}
#[verus_verify]
impl<const LEN: usize> Deref for MemoryRegionArray<LEN> {
    type Target = [MemoryRegion];

    /// Returns the slice of active memory regions.
    #[verus_spec(ret =>
        ensures
            ret@ == self@,
    )]
    fn deref(&self) -> &Self::Target {
        proof! {
            use_type_invariant(self);
        }
        &self.regions[..self.count]
    }
}
#[verus_verify]
impl<const LEN: usize> MemoryRegionArray<LEN> {
    /// Constructs an empty set.
    ///
    /// # Verified Properties
    ///
    /// ## Safety
    /// - All array elements are initialized.
    ///
    /// ## Functional Correctness
    /// - Creates an empty collection with capacity `LEN`.
    ///
    /// ## Preconditions
    /// - There are no caller obligations.
    ///
    /// ## Postconditions
    /// - The view is the empty sequence.
    /// - The function does not panic.
    #[verus_verify(dual_spec)]
    #[verus_spec(ret =>
        ensures
            ret@ == Seq::<MemoryRegion>::empty(),
        returns Self::new(),
    )]
    pub const fn new() -> Self {
        let ret = Self {
            regions: [MemoryRegion::bad(); LEN],
            count: 0,
        };

        ret
    }

    /// Appends a region to the set.
    ///
    /// If the set is full, an error is returned.
    ///
    /// # Verified Properties
    ///
    /// ## Safety
    /// - The write is guarded by `count < regions.len()`, so it stays inside the array.
    ///
    /// ## Functional Correctness
    /// - Appends without changing existing regions.
    ///
    /// ## Preconditions
    /// - There are no caller obligations beyond the type invariant.
    ///
    /// ## Postconditions
    /// - If space remains, `region` is appended and the result is `Ok`.
    /// - If full, the view is unchanged and the result is `Err`.
    /// - The function does not panic.
    #[verus_spec(ret =>
        ensures
            old(self)@.len() < LEN ==> {
                &&& final(self)@ == old(self)@.push(region)
                &&& ret.is_ok()
            },
            old(self)@.len() == LEN ==> {
                &&& final(self)@ == old(self)@
                &&& ret.is_err()
            },
    )]
    pub fn push(&mut self, region: MemoryRegion) -> Result<(), &'static str> {
        if self.count < self.regions.len() {
            self.regions[self.count] = region;
            self.count = self.count + 1;
            Ok(())
        } else {
            Err("MemoryRegionArray is full")
        }
    }
    /// Sorts the regions and returns a full set of non-overlapping regions.
    ///
    /// If an address is in multiple regions, the region with the lowest
    /// usability will be its type.
    ///
    /// All the addresses between 0 and the end of the last region will be in
    /// the resulting set. If an address is not in any region, it will be marked
    /// as [`MemoryRegionType::Unknown`].
    ///
    /// If any of the region boundaries are not page-aligned, they will be aligned
    /// according to the type of the region.
    ///
    /// # Panics
    ///
    /// This method will panic if the number of output regions is greater than `LEN`.
    ///
    /// # Verified Properties
    ///
    /// ## Safety
    /// - Indexing uses the active count, which the type invariant keeps inside `LEN`.
    /// - Address arithmetic used to build output regions stays within `MAX_PADDR`.
    ///
    /// ## Functional Correctness
    /// - Normalizes overlaps and gaps into a coalesced memory map.
    ///
    /// ## Preconditions
    /// - `LEN` is at least twice the active input count.
    ///
    /// ## Postconditions
    /// - The result partitions the range from zero to the largest nonempty
    ///   aligned input end, or is empty if there is no such input.
    /// - Each output byte uses the most restrictive covering aligned input type,
    ///   or `Unknown` where no aligned input covers it.
    /// - Adjacent output regions have different types.
    /// - The function does not panic.
    #[verus_spec(ret =>
        requires
            LEN >= 2 * self@.len(),
        ensures
            is_partition(ret@, if ret@.len() == 0 { 0 } else { ret@.last().end() as int }),
            preserves_types(ret@, self.aligned_regions()),
            ret@.len() == 0 <==> self.aligned_regions().len() == 0,
            ret@.len() > 0 ==> self.aligned_regions().all(|r: MemoryRegion| r.end() <= ret@.last().end()),
            ret@.len() > 0 ==> self.aligned_regions().any(|r: MemoryRegion| r.end() == ret@.last().end()),
            coalesced(ret@),
    )]
    pub fn into_non_overlapping(mut self) -> Self {
        proof! {
            broadcast use group_array_axioms;
        }
        proof_decl! { let ghost original = self; }
        /* Sync asterinas/asterinas#3928 (fixes #3887): drop regions that become
         * empty after alignment before finding the sweep endpoint. The indexed
         * while loop exposes the in-place compaction invariant to Verus.
         * Origin Rust: self.regions.iter_mut().for_each(|r| *r = r.as_aligned());
         */
        let mut count = 0;
        let mut i = 0;
        #[verus_spec(
            invariant
                count <= i <= self.count == original.count <= LEN,
                self.regions@[..count] == original@[..i]
                    .map_values(|r: MemoryRegion| r.aligned_region())
                    .filter(|r: MemoryRegion| r.len > 0),
                forall|j: int| i <= j < original.count ==> #[trigger] self.regions[j] == original@[j],
                forall|j: int| #![trigger self.regions[j]] 0 <= j < count ==> {
                    &&& self.regions[j].aligned(PAGE_SIZE as int)
                    &&& self.regions[j].len > 0
                    &&& self.regions[j].base + self.regions[j].len <= MAX_PADDR
                },
            decreases self.count - i,
        )]
        while i < self.count {
            proof_decl! { let ghost previous = self.regions@; }
            let region = self.regions[i].as_aligned();
            proof! {
                use_type_invariant(&region);
                let mapped = original@[..i].map_values(|r: MemoryRegion| r.aligned_region());
                assert(original@[..i + 1].map_values(|r: MemoryRegion| r.aligned_region())
                    == mapped.push(region));
                mapped.lemma_filter_push(region, |r: MemoryRegion| r.len > 0);
            }
            if !region.is_empty() {
                self.regions[count] = region;
                proof! {
                    assert(self.regions@[..count + 1] == previous[..count].push(region));
                }
                count += 1;
            }
            i += 1;
        }
        self.count = count;
        proof_decl! { let ghost source = self@; }
        proof! {
            assert(original@[..original.count] == original@);
            assert(source == self.regions@[..count]);
            assert(source == original.aligned_regions());
            assert forall|j: int| #![trigger source[j]] 0 <= j < source.len() implies {
                &&& source[j].aligned(PAGE_SIZE as int)
                &&& source[j].len > 0
                &&& source[j].base + source[j].len <= MAX_PADDR
            } by {
                assert(source[j] == self.regions[j]);
                assert(self.regions[j].aligned(PAGE_SIZE as int));
            }
        }
        /* asterinas/asterinas#3928 computes the maximum after alignment and
         * filtering. `Iterator::max` has no model in the active vstd, so scan
         * the same active prefix and retain its zero default.
         * Origin Rust: let max_addr = self.iter().map(|r| r.end())
         *     .max().unwrap_or(0).align_down(PAGE_SIZE);
         */
        let mut max_addr = 0;
        i = 0;
        #[verus_spec(
            invariant
                i <= self.count == source.len() <= original.count <= LEN,
                self@ == source,
                source == original.aligned_regions(),
                max_addr <= MAX_PADDR,
                max_addr % PAGE_SIZE == 0,
                forall|j: int| 0 <= j < i ==> #[trigger] source[j].end() <= max_addr,
                max_addr == 0 || exists|j: int| 0 <= j < i && #[trigger] source[j].end() == max_addr,
                forall|j: int| #![trigger source[j]] 0 <= j < source.len() ==> {
                    &&& source[j].aligned(PAGE_SIZE as int)
                    &&& source[j].len > 0
                    &&& source[j].base + source[j].len <= MAX_PADDR
                },
            decreases self.count - i,
        )]
        while i < self.count {
            proof! {
                assert(source[i as int] == self.regions[i as int]);
                assert(source[i as int].aligned(PAGE_SIZE as int));
            }
            let end = self.regions[i].end();
            if end > max_addr {
                max_addr = end;
            }
            i += 1;
        }
        proof_decl! {
            let ghost bounds = region_boundaries(source);
            let ghost mut visited = Set::<int>::empty();
        }
        proof! {
            assert forall|j: int| #![trigger source[j]] 0 <= j < source.len() implies {
                &&& source[j].aligned(PAGE_SIZE as int)
                &&& source[j].len > 0
                &&& source[j].base + source[j].len <= max_addr
            } by {
                assert(source[j].end() <= max_addr);
                assert(source[j].aligned(PAGE_SIZE as int));
            }
            assert(max_addr == 0 <==> source.len() == 0) by {
                if source.len() > 0 { assert(source[0].aligned(PAGE_SIZE as int)); }
            }
            let bases = source.map_values(|r: MemoryRegion| r.base as int);
            let ends = source.map_values(|r: MemoryRegion| r.base + r.len);
            bases.lemma_cardinality_of_set();
            ends.lemma_cardinality_of_set();
            lemma_len_union(bases.to_set(), ends.to_set());
        }

        let mut result = MemoryRegionArray::<LEN>::new();

        let mut cur_right = 0;

        #[verus_spec(
            invariant
                self@ == source,
                source == original.aligned_regions(),
                max_addr == 0 <==> source.len() == 0,
                source.len() == self.count <= LEN,
                bounds == region_boundaries(source),
                bounds.len() <= LEN,
                visited.subset_of(bounds),
                visited.len() == result.count,
                forall|p: int| #[trigger] visited.contains(p) ==> p <= cur_right,
                cur_right <= max_addr <= MAX_PADDR,
                cur_right % PAGE_SIZE == 0,
                is_partition(result@, cur_right as int),
                preserves_types(result@, source),
                result.count == result@.len() <= LEN,
                max_addr == 0 || exists|j: int| 0 <= j < source.len() && #[trigger] source[j].end() == max_addr,
                forall|j: int| #![trigger source[j]] 0 <= j < source.len() ==> {
                    &&& source[j].aligned(PAGE_SIZE as int)
                    &&& source[j].len > 0
                    &&& source[j].base + source[j].len <= max_addr
                },
            decreases MAX_PADDR - cur_right,
        )]
        while cur_right < max_addr {
            /* `Iterator::min` and `filter_map` lack vstd models, so fuse their
             * read-only scans over the active prefix. Unique discriminants preserve
             * the enum's ordering and expose it to Verus.
             * Origin Rust: let typ = self.iter()
             *     .filter(|region| (region.base()..region.end()).contains(&cur_right))
             *     .map(|region| region.typ()).min().unwrap_or(MemoryRegionType::Unknown);
             * let right = self.iter().filter_map(|region| {
             *     if region.base() > cur_right { Some(region.base()) }
             *     else if region.end() > cur_right { Some(region.end()) }
             *     else { None }
             * }).min().unwrap();
             */
            // Find the most restrictive type.
            let mut typ: Option<MemoryRegionType> = None;
            let mut right: Option<usize> = None;
            i = 0;
            #[verus_spec(
                invariant
                    i <= self.count <= LEN,
                    self@ == source,
                    typ matches Some(t) ==> exists|j: int| 0 <= j < i
                        && #[trigger] source[j].base <= cur_right < source[j].end() && source[j].typ == t,
                    forall|j: int| #![trigger source[j]] 0 <= j < i
                        && source[j].base <= cur_right < source[j].end()
                        ==> (typ matches Some(least) && least as int <= source[j].typ as int),
                    cur_right < max_addr <= MAX_PADDR,
                    max_addr > 0 ==> exists|j: int| 0 <= j < source.len() && #[trigger] source[j].end() >= max_addr,
                    forall|j: int| #![trigger source[j]] 0 <= j < source.len() ==> {
                        &&& source[j].aligned(PAGE_SIZE as int)
                        &&& source[j].base + source[j].len <= max_addr <= MAX_PADDR
                    },
                    right matches Some(r) ==> {
                        &&& cur_right < r <= max_addr
                        &&& r % PAGE_SIZE == 0
                        &&& exists|j: int| 0 <= j < i && (#[trigger] source[j].base == r || source[j].end() == r)
                    },
                    forall|j: int| #![trigger source[j]] 0 <= j < i ==> {
                        &&& (source[j].base > cur_right ==> (right matches Some(bound) && bound <= source[j].base))
                        &&& (source[j].end() > cur_right ==> (right matches Some(bound) && bound <= source[j].end()))
                    },
                decreases self.count - i,
            )]
            while i < self.count {
                let region = &self.regions[i];
                proof! {
                    assert(source[i as int].aligned(PAGE_SIZE as int));
                }
                if region.base() <= cur_right && cur_right < region.end() {
                    match typ {
                        None => typ = Some(region.typ()),
                        Some(old) => {
                            if (region.typ() as u8) < old as u8 {
                                typ = Some(region.typ());
                            }
                        }
                    }
                }
                let candidate = if region.base() > cur_right {
                    Some(region.base())
                } else if region.end() > cur_right {
                    Some(region.end())
                } else {
                    None
                };
                if let Some(candidate) = candidate {
                    match right {
                        None => right = Some(candidate),
                        Some(old) => {
                            if candidate < old {
                                right = Some(candidate);
                            }
                        }
                    }
                }
                proof! {
                    assert forall|j: int| 0 <= j <= i implies {
                        &&& (#[trigger] source[j].base > cur_right ==> (right matches Some(bound) && bound <= source[j].base))
                        &&& (#[trigger] source[j].end() > cur_right ==> (right matches Some(bound) && bound <= source[j].end()))
                    } by {}
                }
                i += 1;
            }
            let right = right.unwrap();
            proof_decl! { let ghost chosen = typ; }
            let typ = typ.unwrap_or(MemoryRegionType::Unknown);
            proof! {
                assert forall|addr: int| cur_right <= addr < right implies
                    #[trigger] selected_type(source, addr, typ) by {
                    reveal(selected_type);
                    assert forall|j: int| #![trigger source[j]] 0 <= j < source.len()
                        && source[j].base <= cur_right < source[j].base + source[j].len implies
                        typ as int <= source[j].typ as int by {
                        assert(source[j].aligned(PAGE_SIZE as int));
                    }
                    if let Some(t) = chosen {
                        let j = choose|j: int| #![trigger source[j]] 0 <= j < source.len()
                            && source[j].base <= cur_right < source[j].end() && source[j].typ == t;
                        let covers_with_type = |r: MemoryRegion|
                            r.base <= addr < r.base + r.len && r.typ == typ;
                        let covers = |r: MemoryRegion| r.base <= addr < r.base + r.len;
                        assert(covers_with_type(source[j]));
                        assert(covers(source[j]));
                    } else {
                        assert forall|j: int| #![trigger source[j]] 0 <= j < source.len() implies
                            !(source[j].base <= cur_right < source[j].base + source[j].len) by {
                            assert(source[j].aligned(PAGE_SIZE as int));
                        }
                    }
                }
            }
            proof_decl! { let ghost before = result@; }
            proof! {
                let j = choose|j: int| #![auto] 0 <= j < source.len() && (source[j].base == right || source[j].end() == right);
                assert(source[j].aligned(PAGE_SIZE as int));
                if source[j].base == right {
                    assert(source.map_values(|r: MemoryRegion| r.base as int)[j] == right);
                } else {
                    assert(source.map_values(|r: MemoryRegion| r.base + r.len)[j] == right);
                }
                visited.lemma_subset_not_in_lt(bounds, right as int);
                assert(!visited.contains(right as int));
                visited = visited.insert(right as int);
            }

            result
                .push(MemoryRegion::new(cur_right, right - cur_right, typ))
                .unwrap();

            proof! {
                assert forall|j: int| 0 <= j < result@.len() implies #[trigger] result@[j].len > 0 by {
                    if j < before.len() { assert(before[j].aligned(PAGE_SIZE as int)); }
                }
                assert forall|j: int| 0 <= j < result@.len() implies #[trigger] result@[j].base + result@[j].len <= MAX_PADDR by {
                    if j < before.len() { assert(before[j].aligned(PAGE_SIZE as int)); }
                }
                assert forall|j: int| 0 < j < result@.len() implies result@[j - 1].base + result@[j - 1].len == #[trigger] result@[j].base by {
                    if j < before.len() { assert(before[j].aligned(PAGE_SIZE as int)); }
                }
            }

            cur_right = right;
        }

        /* asterinas/asterinas#3928 returns an empty map when no aligned input
         * remains, instead of treating the unused first slot as an output region.
         * Origin Rust: <none; new executable code>
         */
        if result.is_empty() {
            proof! { reveal(coalesced); }
            return result;
        }
        // Merge the adjacent regions with the same type.
        let mut merged_count = 1;
        proof_decl! { let ghost split = result@; }
        /* Use an explicit index for the compaction invariant; `result.count`
         * and the iteration order are unchanged.
         * Origin Rust: for i in 1..result.count { ... }
         */
        let mut i = 1;
        proof! {
            assert(coalesced(result.regions@[..1])) by { reveal(coalesced); }
            assert(split[0].aligned(PAGE_SIZE as int));
            assert(split.last().aligned(PAGE_SIZE as int));
        }
        #[verus_spec(
            invariant
                result.count == split.len() <= LEN,
                1 <= merged_count <= i <= split.len(),
                is_partition(split, cur_right as int),
                cur_right == max_addr,
                source == original.aligned_regions(),
                source.len() > 0,
                exists|j: int| 0 <= j < source.len() && #[trigger] source[j].end() == max_addr,
                forall|j: int| 0 <= j < source.len() ==> #[trigger] source[j].end() <= max_addr,
                coalesced(result.regions@[..merged_count]),
                preserves_types(split, source),
                preserves_types(result.regions@[..merged_count], source),
                is_partition(result.regions@[..merged_count], split[i - 1].end() as int),
                forall|j: int| i <= j < split.len() ==> #[trigger] result.regions[j] == split[j],
            decreases result.count - i,
        )]
        while i < result.count {
            proof_decl! { let ghost previous = result.regions@; let ghost old_count = merged_count; }
            proof! {
                let prefix = result.regions@[..merged_count];
                assert forall|j: int| 0 <= j < merged_count implies {
                    &&& #[trigger] previous[j].aligned(PAGE_SIZE as int)
                    &&& previous[j].len > 0
                    &&& previous[j].base + previous[j].len <= MAX_PADDR
                    &&& (j > 0 ==> previous[j - 1].base + previous[j - 1].len == previous[j].base)
                } by { assert(prefix[j].aligned(PAGE_SIZE as int)); }

                assert(split[i as int].aligned(PAGE_SIZE as int));
            }
            /* Expose equality of fieldless enum variants through their unique
             * discriminants; this is the same equality as the derived `PartialEq`.
             * Origin Rust: result[i].typ() == result.regions[merged_count - 1].typ()
             */
            if result[i].typ() as u8 == result.regions[merged_count - 1].typ() as u8 {
                result.regions[merged_count - 1] = MemoryRegion::new(
                    result.regions[merged_count - 1].base(),
                    result.regions[merged_count - 1].len() + result[i].len(),
                    result.regions[merged_count - 1].typ(),
                );
            } else {
                result.regions[merged_count] = result[i];
                merged_count += 1;
            }
            proof! {
                let prefix = result.regions@[..merged_count];
                lemma_coalesced_update(previous[..old_count], prefix);
                assert forall|j: int| 0 <= j < prefix.len() implies
                    #[trigger] prefix[j].aligned(PAGE_SIZE as int) by {
                    if j < old_count { assert(previous[j].aligned(PAGE_SIZE as int)); }
                }
                assert forall|j: int| 0 <= j < prefix.len() implies #[trigger] prefix[j].len > 0 by {
                    if j < old_count { assert(previous[j].aligned(PAGE_SIZE as int)); }
                }
                assert forall|j: int| 0 <= j < prefix.len() implies #[trigger] prefix[j].base + prefix[j].len <= MAX_PADDR by {
                    if j < old_count { assert(previous[j].aligned(PAGE_SIZE as int)); }
                }
                assert forall|j: int| 0 < j < prefix.len() implies prefix[j - 1].base + prefix[j - 1].len == #[trigger] prefix[j].base by {
                    if j < old_count { assert(previous[j].aligned(PAGE_SIZE as int)); }
                }
                assert forall|j: int, addr: int| #![trigger prefix[j], selected_type(source, addr, prefix[j].typ)]
                    0 <= j < prefix.len() && prefix[j].base <= addr < prefix[j].base + prefix[j].len
                    implies selected_type(source, addr, prefix[j].typ) by {
                    if j < old_count && addr < previous[j].base + previous[j].len {
                        assert(selected_type(source, addr, previous[..old_count][j].typ));
                    } else {
                        assert(split[i as int].base <= addr < split[i as int].base + split[i as int].len);
                    }
                }
            }
            i += 1;
        }
        result.count = merged_count;

        proof! {
            assert(result@ == result.regions@[..merged_count]);
            let j = choose|j: int| #![trigger source[j]]
                0 <= j < source.len() && source[j].end() == max_addr;
            let reaches_end = |r: MemoryRegion| r.end() == result@.last().end();
            assert(reaches_end(source[j]));
        }

        result
    }
}

// Keep the coalescing predicate's unfolding in a small solver context.
verus! {

/// Updating lengths or appending a different type preserves complete merging.
proof fn lemma_coalesced_update(before: Seq<MemoryRegion>, after: Seq<MemoryRegion>)
    requires
        coalesced(before),
        0 < before.len() <= after.len() <= before.len() + 1,
        forall|j: int| 0 <= j < before.len() ==> #[trigger] after[j].typ == before[j].typ,
        after.len() > before.len() ==> after.last().typ != before.last().typ,
    ensures
        coalesced(after),
{
    reveal(coalesced);
}

} // verus!
#[cfg(ktest)]
mod test {
    use super::*;
    use crate::prelude::ktest;

    #[ktest]
    fn test_sort_full_non_overlapping() {
        let mut regions = MemoryRegionArray::<64>::new();
        // Regions that can be combined.
        regions
            .push(MemoryRegion::new(
                0,
                PAGE_SIZE + 1,
                MemoryRegionType::Usable,
            ))
            .unwrap();
        regions
            .push(MemoryRegion::new(
                PAGE_SIZE - 1,
                PAGE_SIZE + 2,
                MemoryRegionType::Usable,
            ))
            .unwrap();
        regions
            .push(MemoryRegion::new(
                PAGE_SIZE * 2,
                PAGE_SIZE * 5,
                MemoryRegionType::Usable,
            ))
            .unwrap();
        // A punctured region.
        regions
            .push(MemoryRegion::new(
                PAGE_SIZE * 3 + 1,
                PAGE_SIZE - 2,
                MemoryRegionType::BadMemory,
            ))
            .unwrap();
        // A far region that left a hole in the middle.
        regions
            .push(MemoryRegion::new(
                PAGE_SIZE * 9,
                PAGE_SIZE * 2,
                MemoryRegionType::Usable,
            ))
            .unwrap();

        let regions = regions.into_non_overlapping();

        assert_eq!(regions.count, 5);
        assert_eq!(regions[0].base(), 0);
        assert_eq!(regions[0].len(), PAGE_SIZE * 3);
        assert_eq!(regions[0].typ(), MemoryRegionType::Usable);

        assert_eq!(regions[1].base(), PAGE_SIZE * 3);
        assert_eq!(regions[1].len(), PAGE_SIZE);
        assert_eq!(regions[1].typ(), MemoryRegionType::BadMemory);

        assert_eq!(regions[2].base(), PAGE_SIZE * 4);
        assert_eq!(regions[2].len(), PAGE_SIZE * 3);
        assert_eq!(regions[2].typ(), MemoryRegionType::Usable);

        assert_eq!(regions[3].base(), PAGE_SIZE * 7);
        assert_eq!(regions[3].len(), PAGE_SIZE * 2);
        assert_eq!(regions[3].typ(), MemoryRegionType::Unknown);

        assert_eq!(regions[4].base(), PAGE_SIZE * 9);
        assert_eq!(regions[4].len(), PAGE_SIZE * 2);
        assert_eq!(regions[4].typ(), MemoryRegionType::Usable);
    }
}
