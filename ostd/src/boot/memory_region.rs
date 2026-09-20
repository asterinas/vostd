// SPDX-License-Identifier: MPL-2.0
//! Information of memory regions in the boot phase.
use vstd::prelude::*;
use vstd_extra::prelude::*;

use crate::specs::arch::*;

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
/// The sections are **not** guaranteed to not overlap. The region must be page aligned.
#[verus_verify]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct MemoryRegion {
    base: usize,
    len: usize,
    typ: MemoryRegionType,
}

verus! {

impl MemoryRegion {
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
    #[verus_verify(dual_spec)]
    #[verus_spec(returns Self::bad())]
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

    /// Constructs a framebuffer memory region.
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
    pub fn module(bytes: &[u8]) -> Self {
        let vaddr = bytes.as_ptr() as Vaddr;
        assert!(crate::mm::kspace::LINEAR_MAPPING_VADDR_RANGE.contains(&vaddr));

        Self {
            base: vaddr - crate::mm::kspace::LINEAR_MAPPING_BASE_VADDR,
            len: bytes.len(),
            typ: MemoryRegionType::Reclaimable,
        }
    } */

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
        requires
            self.typ == MemoryRegionType::Usable
                ==> nat_align_up(self.base as nat, PAGE_SIZE as nat)
                    <= nat_align_down((self.base + self.len) as nat, PAGE_SIZE as nat),
        ensures
            ret.typ == self.typ,
            ret.aligned(PAGE_SIZE as int),
            self.typ == MemoryRegionType::Usable
                ==> ret.base == nat_align_up(self.base as nat, PAGE_SIZE as nat),
            self.typ == MemoryRegionType::Usable
                ==> ret.base + ret.len
                    == nat_align_down((self.base + self.len) as nat, PAGE_SIZE as nat),
            self.typ != MemoryRegionType::Usable
                ==> ret.base == nat_align_down(self.base as nat, PAGE_SIZE as nat),
            self.typ != MemoryRegionType::Usable
                ==> ret.base + ret.len
                    == nat_align_up((self.base + self.len) as nat, PAGE_SIZE as nat),
            self.typ == MemoryRegionType::Usable
                ==> ret.is_sub_region(*self),
            self.typ != MemoryRegionType::Usable
                ==> self.is_sub_region(ret),
    )]
    fn as_aligned(&self) -> Self {
        proof! {
            use_type_invariant(self);
            lemma_pow2_is_pow2_to64();
        }
        let (base, end) = match self.typ() {
            MemoryRegionType::Usable => (
                self.base().align_up(PAGE_SIZE),
                self.end().align_down(PAGE_SIZE),
            ),
            _ => (
                self.base().align_down(PAGE_SIZE),
                self.end().align_up(PAGE_SIZE),
            ),
        };
        MemoryRegion {
            base,
            len: end - base,
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
    #[verus_spec(ret =>
        ensures
            ret@ == Seq::<MemoryRegion>::empty()
    )]
    fn default() -> Self {
        Self::new()
    }
}
#[verus_verify]
impl<const LEN: usize> Deref for MemoryRegionArray<LEN> {
    type Target = [MemoryRegion];

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
    #[verus_spec(ret =>
        ensures
            ret@ == Seq::<MemoryRegion>::empty(),
    )]
    pub const fn new() -> Self {
        let ret = Self {
            regions: [MemoryRegion::bad(); LEN],
            count: 0,
        };

        proof! {
            assert(ret@ == Seq::<MemoryRegion>::empty());
        };

        ret
    }

    /// Appends a region to the set.
    ///
    /// If the set is full, an error is returned.
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
        proof! {
            use_type_invariant(&*self);
        }
        if self.count < self.regions.len() {
            self.regions[self.count] = region;
            self.count = self.count + 1;
            proof! {
                assert(self@ == old(self)@.push(region)) by {
                    assert (forall |i: int| 0 <= i < self@.len() ==> #[trigger] self@[i] == old(self)@.push(region)[i]);
                };
            };
            Ok(())
        } else {
            Err("MemoryRegionArray is full")
        }
    }
    /*
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
    pub fn into_non_overlapping(mut self) -> Self {
        let max_addr = self
            .iter()
            .map(|r| r.end())
            .max()
            .unwrap_or(0)
            .align_down(PAGE_SIZE);
        self.regions.iter_mut().for_each(|r| *r = r.as_aligned());

        let mut result = MemoryRegionArray::<LEN>::new();

        let mut cur_right = 0;

        while cur_right < max_addr {
            // Find the most restrictive type.
            let typ = self
                .iter()
                .filter(|region| (region.base()..region.end()).contains(&cur_right))
                .map(|region| region.typ())
                .min()
                .unwrap_or(MemoryRegionType::Unknown);

            // Find the right boundary.
            let right = self
                .iter()
                .filter_map(|region| {
                    if region.base() > cur_right {
                        Some(region.base())
                    } else if region.end() > cur_right {
                        Some(region.end())
                    } else {
                        None
                    }
                })
                .min()
                .unwrap();

            result
                .push(MemoryRegion::new(cur_right, right - cur_right, typ))
                .unwrap();

            cur_right = right;
        }

        // Merge the adjacent regions with the same type.
        let mut merged_count = 1;
        for i in 1..result.count {
            if result[i].typ() == result.regions[merged_count - 1].typ() {
                result.regions[merged_count - 1] = MemoryRegion::new(
                    result.regions[merged_count - 1].base(),
                    result.regions[merged_count - 1].len() + result[i].len(),
                    result.regions[merged_count - 1].typ(),
                );
            } else {
                result.regions[merged_count] = result[i];
                merged_count += 1;
            }
        }
        result.count = merged_count;

        result
    }*/
}

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
