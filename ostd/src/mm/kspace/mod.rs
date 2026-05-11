// SPDX-License-Identifier: MPL-2.0
//! Kernel memory space management.
//!
//! The kernel memory space is currently managed as follows, if the
//! address width is 48 bits (with 47 bits kernel space).
//!
//! TODO: the cap of linear mapping (the start of vm alloc) are raised
//! to workaround for high IO in TDX. We need actual vm alloc API to have
//! a proper fix.
//!
//! ```text
//! +-+ <- the highest used address (0xffff_ffff_ffff_0000)
//! | |         For the kernel code, 1 GiB.
//! +-+ <- 0xffff_ffff_8000_0000
//! | |
//! | |         Unused hole.
//! +-+ <- 0xffff_e100_0000_0000
//! | |         For frame metadata, 1 TiB.
//! +-+ <- 0xffff_e000_0000_0000
//! | |         For [`KVirtArea`], 32 TiB.
//! +-+ <- the middle of the higher half (0xffff_c000_0000_0000)
//! | |
//! | |
//! | |
//! | |         For linear mappings, 64 TiB.
//! | |         Mapped physical addresses are untracked.
//! | |
//! | |
//! | |
//! +-+ <- the base of high canonical address (0xffff_8000_0000_0000)
//! ```
//!
//! If the address width is (according to [`crate::arch::mm::PagingConsts`])
//! 39 bits or 57 bits, the memory space just adjust proportionally.
use core::ops::Range;
use vstd::atomic::PermissionU64;
use vstd::prelude::*;
use vstd::simple_pptr::PointsTo;

//use log::info;
use crate::sync::{OnceImpl, TrivialPred};
pub mod kvirt_area;
#[cfg(ktest)]
mod test;

use super::{
    frame::{
        meta::{mapping, AnyFrameMeta, MetaPageMeta, MetaSlot},
        Frame, Segment,
    },
    page_prop::{CachePolicy, PageFlags, PageProperty, PrivilegedPageFlags},
    page_table::{PageTable, PageTableConfig},
    Paddr, PagingConstsTrait, Vaddr,
};
use crate::mm::frame::DynFrame;
use crate::mm::page_table::RCClone;
use crate::specs::arch::mm::NR_LEVELS;
use crate::specs::mm::frame::meta_owners::MetaPerm;
use crate::specs::mm::frame::meta_owners::MetaSlotStorage;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::{
    boot::memory_region::MemoryRegionType,
    mm::{largest_pages, PagingLevel},
    specs::arch::{PageTableEntry, PagingConsts},
    //task::disable_preempt,
};

use vstd_extra::ownership::*;

verus! {

/// The shortest supported address width is 39 bits. And the literal
/// values are written for 48 bits address width. Adjust the values
/// by arithmetic left shift.
pub const ADDR_WIDTH_SHIFT: isize = 48 - 48;

/// Start of the kernel address space.
/// This is the _lowest_ address of the x86-64's _high_ canonical addresses.
#[cfg(not(target_arch = "loongarch64"))]
pub const KERNEL_BASE_VADDR: Vaddr = 0xffff_8000_0000_0000 << ADDR_WIDTH_SHIFT;

#[cfg(target_arch = "loongarch64")]
pub const KERNEL_BASE_VADDR: Vaddr = 0x9000_0000_0000_0000 << ADDR_WIDTH_SHIFT;

/// End of the kernel address space (non inclusive).
pub const KERNEL_END_VADDR: Vaddr = 0xffff_ffff_ffff_0000 << ADDR_WIDTH_SHIFT;

/*
/// The kernel code is linear mapped to this address.
///
/// FIXME: This offset should be randomly chosen by the loader or the
/// boot compatibility layer. But we disabled it because OSTD
/// doesn't support relocatable kernel yet.
pub fn kernel_loaded_offset() -> usize {
    KERNEL_CODE_BASE_VADDR
}*/

#[cfg(target_arch = "x86_64")]
pub const KERNEL_CODE_BASE_VADDR: usize = 0xffff_ffff_8000_0000 << ADDR_WIDTH_SHIFT;

#[cfg(target_arch = "riscv64")]
pub const KERNEL_CODE_BASE_VADDR: usize = 0xffff_ffff_0000_0000 << ADDR_WIDTH_SHIFT;

#[cfg(target_arch = "loongarch64")]
pub const KERNEL_CODE_BASE_VADDR: usize = 0x9000_0000_0000_0000 << ADDR_WIDTH_SHIFT;

pub const FRAME_METADATA_CAP_VADDR: Vaddr = 0xffff_fff0_8000_0000 << ADDR_WIDTH_SHIFT;

pub const FRAME_METADATA_BASE_VADDR: Vaddr = 0xffff_fff0_0000_0000 << ADDR_WIDTH_SHIFT;

pub const VMALLOC_BASE_VADDR: Vaddr = 0xffff_c000_0000_0000 << ADDR_WIDTH_SHIFT;

pub const VMALLOC_VADDR_RANGE: Range<Vaddr> = VMALLOC_BASE_VADDR..FRAME_METADATA_BASE_VADDR;

/// The base address of the linear mapping of all physical
/// memory in the kernel address space.
pub const LINEAR_MAPPING_BASE_VADDR: Vaddr = 0xffff_8000_0000_0000 << ADDR_WIDTH_SHIFT;

pub const LINEAR_MAPPING_VADDR_RANGE: Range<Vaddr> = LINEAR_MAPPING_BASE_VADDR..VMALLOC_BASE_VADDR;

/*
#[cfg(not(target_arch = "loongarch64"))]
pub const LINEAR_MAPPING_BASE_VADDR: Vaddr = 0xffff_8000_0000_0000 << ADDR_WIDTH_SHIFT;
#[cfg(target_arch = "loongarch64")]
pub const LINEAR_MAPPING_BASE_VADDR: Vaddr = 0x9000_0000_0000_0000 << ADDR_WIDTH_SHIFT;
pub const LINEAR_MAPPING_VADDR_RANGE: Range<Vaddr> = LINEAR_MAPPING_BASE_VADDR..VMALLOC_BASE_VADDR;
*/

/// Convert physical address to virtual address using offset, only available inside `ostd`
pub open spec fn paddr_to_vaddr_spec(pa: Paddr) -> usize {
    (pa + LINEAR_MAPPING_BASE_VADDR) as usize
}

#[verifier::when_used_as_spec(paddr_to_vaddr_spec)]
pub fn paddr_to_vaddr(pa: Paddr) -> usize
    requires
        pa + LINEAR_MAPPING_BASE_VADDR < usize::MAX,
    returns
        paddr_to_vaddr_spec(pa),
{
    //debug_assert!(pa < VMALLOC_BASE_VADDR - LINEAR_MAPPING_BASE_VADDR);
    pa + LINEAR_MAPPING_BASE_VADDR
}

/// The kernel page table instance.
///
/// It manages the kernel mapping of all address spaces by sharing the kernel part. And it
/// is unlikely to be activated.
#[allow(private_interfaces)]
pub exec static KERNEL_PAGE_TABLE: OnceImpl<PageTable<KernelPtConfig>, TrivialPred> = OnceImpl::new(
    Ghost(TrivialPred),
);

#[derive(Clone, Debug)]
pub(crate) struct KernelPtConfig {}

// We use the first available PTE bit to mark the frame as tracked.
// SAFETY: `item_into_raw` and `item_from_raw` are implemented correctly,
unsafe impl PageTableConfig for KernelPtConfig {
    open spec fn TOP_LEVEL_INDEX_RANGE_spec() -> Range<usize> {
        256..512
    }

    open spec fn LEADING_BITS_spec() -> usize {
        0xffff
    }

    fn TOP_LEVEL_INDEX_RANGE() -> (r: Range<usize>)
        ensures
            r == Self::TOP_LEVEL_INDEX_RANGE_spec(),
    {
        256..512
    }

    open spec fn TOP_LEVEL_CAN_UNMAP_spec() -> bool {
        false
    }

    fn TOP_LEVEL_CAN_UNMAP() -> (b: bool)
        ensures
            b == Self::TOP_LEVEL_CAN_UNMAP_spec(),
    {
        false
    }

    // The kvirt allocator (the only source of kernel-PT cursor ranges) caps
    // `range.end` at FRAME_METADATA_BASE_VADDR — see `kvirt_alloc_range_bounds`.
    open spec fn LOCKED_END_BOUND_spec() -> int {
        FRAME_METADATA_BASE_VADDR as int
    }

    type E = PageTableEntry;

    type C = PagingConsts;

    type Item = MappedItem;

    uninterp spec fn item_into_raw_spec(item: Self::Item) -> (Paddr, PagingLevel, PageProperty);

    //    #[verifier::when_used_as_spec(item_into_raw_spec)]
    #[verifier::external_body]
    fn item_into_raw(item: Self::Item) -> (res: (Paddr, PagingLevel, PageProperty))
        ensures
            1 <= res.1 <= crate::specs::arch::mm::NR_LEVELS,
            res == Self::item_into_raw_spec(item),
    {
        match item {
            MappedItem::Tracked(frame, mut prop) => {
                debug_assert!(!prop.flags.contains(PageFlags::AVAIL1()));
                prop.flags = prop.flags | PageFlags::AVAIL1();
                let level = frame.map_level();
                let paddr = frame.into_raw();
                (paddr, level, prop)
            },
            MappedItem::Untracked(pa, level, mut prop) => {
                debug_assert!(!prop.flags.contains(PageFlags::AVAIL1()));
                prop.flags = prop.flags - PageFlags::AVAIL1();
                (pa, level, prop)
            },
        }
    }

    uninterp spec fn item_from_raw_spec(
        paddr: Paddr,
        level: PagingLevel,
        prop: PageProperty,
    ) -> Self::Item;

    //#[verifier::when_used_as_spec(item_from_raw_spec)]
    #[verifier::external_body]
    fn item_from_raw(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> (res: Self::Item)
        ensures
            res == Self::item_from_raw_spec(paddr, level, prop),
    {
        if prop.flags.contains(PageFlags::AVAIL1()) {
            debug_assert_eq!(level, 1);
            // SAFETY: The caller ensures safety.
            let frame = unsafe { Frame::<MetaSlotStorage>::from_raw(paddr) };
            MappedItem::Tracked(frame, prop)
        } else {
            MappedItem::Untracked(paddr, level, prop)
        }
    }

    axiom fn axiom_nr_subpage_per_huge_eq_nr_entries();

    axiom fn item_roundtrip(item: Self::Item, paddr: Paddr, level: PagingLevel, prop: PageProperty);

    open spec fn tracked(item: Self::Item) -> bool {
        // Tracked items hold a reference; clone bumps rc. Untracked items
        // (MMIO frames) are not ref-counted; clone is a no-op.
        item is Tracked
    }

    open spec fn item_well_formed(item: Self::Item) -> bool {
        match item {
            MappedItem::Tracked(frame, _) => frame.inv(),
            MappedItem::Untracked(_, _, _) => true,
        }
    }

    proof fn item_from_raw_well_formed(pa: Paddr, level: PagingLevel, prop: PageProperty) {
        broadcast use crate::mm::frame::meta::mapping::group_page_meta;

        let item = Self::item_from_raw_spec(pa, level, prop);
        if prop.flags.contains(crate::mm::page_prop::PageFlags::AVAIL1()) {
            // Tracked branch: derive `frame.inv()` from
            //   - `item_from_raw_spec_tracked_ptr`: frame.ptr.addr() == frame_to_meta(pa).
            //   - `lemma_frame_to_meta_soundness` (broadcast): frame_to_meta(pa) is
            //     META_SLOT_SIZE-aligned and within FRAME_METADATA_RANGE.
            Self::item_from_raw_spec_tracked_ptr(pa, level, prop);
            // Now item is `MappedItem::Tracked(frame, _)` with the address fact.
            match item {
                MappedItem::Tracked(frame, _) => {
                    assert(frame.ptr.addr() == crate::mm::frame::meta::mapping::frame_to_meta(pa));
                    // frame.inv() unfolds to (alignment + range), both from the lemma.
                    assert(frame.inv());
                },
                MappedItem::Untracked(_, _, _) => {
                    // Excluded by item_from_raw_spec_tracked_ptr.
                    assert(false);
                },
            }
        } else {
            // Untracked branch: item_well_formed is `true`.
            Self::item_from_raw_spec_untracked_variant(pa, level, prop);
        }
    }

    proof fn clone_ensures_concrete(
        item: Self::Item,
        pa: Paddr,
        old_regions: MetaRegionOwners,
        new_regions: MetaRegionOwners,
        res: Self::Item,
    ) {
        // `MappedItem::clone_ensures` case-analyzes:
        //   - Tracked: `frame.clone_ensures(old, new, res_frame)` — gives per-field facts at
        //     `frame_to_index(meta_to_frame(frame.ptr.addr()))`. Bridge to `frame_to_index(pa)`.
        //   - Untracked: `old == new`. Then trait's `rc + 1` ensures becomes contradictory.
        //     This case is ASSUMED unreachable (clone_item only runs on Tracked items in
        //     the verified call chain).
        // Force the trait method's open-spec body to unfold by asserting the UFCS form.
        assert(<MappedItem as RCClone>::clone_ensures(item, old_regions, new_regions, res));
        match (item, res) {
            (MappedItem::Tracked(frame, prop_actual), MappedItem::Tracked(res_frame, _)) => {
                use crate::mm::frame::meta::mapping::{frame_to_index, meta_to_frame};
                Self::item_into_raw_spec_tracked_pa(frame, prop_actual);
                let frame_idx = frame_to_index(meta_to_frame(frame.ptr.addr()));
                assert(pa == meta_to_frame(frame.ptr.addr()));
                assert(frame_to_index(pa) == frame_idx);
                assert(frame.clone_ensures(old_regions, new_regions, res_frame));
            },
            (MappedItem::Untracked(_, _, _), _) => {
                // clone_ensures for Untracked is `old == new`; the trait's
                // `!tracked ==> slot unchanged` ensures follows directly.
                assert(old_regions == new_regions);
            },
            _ => {
                // res == item by precondition; if item is Tracked, res is Tracked too.
                // The mismatched-tag arm is unreachable.
                assert(res == item);
            },
        }
    }

    proof fn clone_requires_concrete(
        item: Self::Item,
        pa: Paddr,
        level: PagingLevel,
        prop: PageProperty,
        regions: MetaRegionOwners,
    ) {
        // `MappedItem::clone_requires` case-analyzes:
        //   - Tracked: `frame.clone_requires(regions)` — needs `frame.inv()` and the
        //     slot facts at `frame_to_index(meta_to_frame(frame.ptr.addr()))`.
        //   - Untracked: `regions.inv()`. Trivially satisfied from precondition.
        // Discharge `frame.inv()` via the trait-level structural well-formedness method.
        Self::item_from_raw_well_formed(pa, level, prop);
        match item {
            MappedItem::Tracked(frame, prop_actual) => {
                use crate::mm::frame::meta::mapping::{frame_to_index, meta_to_frame};
                Self::item_into_raw_spec_tracked_pa(frame, prop_actual);
                Self::item_roundtrip(item, pa, level, prop);
                assert(meta_to_frame(frame.ptr.addr()) == pa);
                assert(frame_to_index(meta_to_frame(frame.ptr.addr())) == frame_to_index(pa));
                // `Self::item_well_formed(item)` unfolds to `frame.inv()` for the
                // Tracked variant.
                assert(frame.inv());
            },
            MappedItem::Untracked(_, _, _) => {
                // clone_requires for Untracked is just `regions.inv()` which we have.
            },
        }
    }
}

impl KernelPtConfig {
    /// The spec agrees with the exec, which ensures 1 <= level <= NR_LEVELS.
    pub axiom fn item_into_raw_spec_level_bounds(item: MappedItem)
        ensures
            1 <= KernelPtConfig::item_into_raw_spec(item).1 <= crate::specs::arch::mm::NR_LEVELS,
    ;

    /// Tracked frames use 4K pages (level 1). Used to prove alignment in map_frames.
    pub axiom fn item_into_raw_spec_tracked_level(item: MappedItem)
        requires
            matches!(item, MappedItem::Tracked(_, _)),
        ensures
            KernelPtConfig::item_into_raw_spec(item).1 == 1,
    ;

    /// For untracked items, `item_into_raw_spec` preserves PA, level, and prop.
    /// This is correct when the AVAIL1 bit is not set in `prop`, which is assumed
    /// for untracked MMIO frames (enforced by the debug_assert in the exec).
    pub axiom fn item_into_raw_spec_untracked(pa: Paddr, level: PagingLevel, prop: PageProperty)
        ensures
            KernelPtConfig::item_into_raw_spec(MappedItem::Untracked(pa, level, prop)).0 == pa,
            KernelPtConfig::item_into_raw_spec(MappedItem::Untracked(pa, level, prop)).1 == level,
            KernelPtConfig::item_into_raw_spec(MappedItem::Untracked(pa, level, prop)).2 == prop,
    ;

    /// For tracked items, the physical address from item_into_raw_spec equals
    /// the frame's metadata-derived physical address.
    pub axiom fn item_into_raw_spec_tracked_pa(frame: DynFrame, prop: PageProperty)
        ensures
            KernelPtConfig::item_into_raw_spec(MappedItem::Tracked(frame, prop)).0
                == crate::mm::frame::meta::mapping::meta_to_frame(frame.ptr.addr()),
    ;

    /// For tracked items, item_into_raw_spec returns the same `prop` that was passed in.
    pub axiom fn item_into_raw_spec_tracked_prop(frame: DynFrame, prop: PageProperty)
        ensures
            KernelPtConfig::item_into_raw_spec(MappedItem::Tracked(frame, prop)).2 == prop,
    ;

    /// Structural shape of `item_from_raw_spec` for the Tracked branch: the reconstructed
    /// frame's pointer is `frame_to_meta(pa)`. This mirrors the exec body of `item_from_raw`,
    /// which calls `Frame::from_raw(pa)` whose ensures gives `r.ptr.addr() == frame_to_meta(pa)`.
    /// Once we have this address shape, `Frame::inv()` follows from `lemma_frame_to_meta_soundness`.
    pub axiom fn item_from_raw_spec_tracked_ptr(pa: Paddr, level: PagingLevel, prop: PageProperty)
        requires
            crate::mm::frame::meta::has_safe_slot(pa),
            prop.flags.contains(crate::mm::page_prop::PageFlags::AVAIL1()),
        ensures
            match KernelPtConfig::item_from_raw_spec(pa, level, prop) {
                MappedItem::Tracked(frame, _) => frame.ptr.addr()
                    == crate::mm::frame::meta::mapping::frame_to_meta(pa),
                MappedItem::Untracked(_, _, _) => false,
            },
    ;

    /// For untracked items, `item_from_raw_spec` returns the Untracked variant.
    /// Mirrors the exec body's branch on `prop.flags.contains(AVAIL1)`.
    pub axiom fn item_from_raw_spec_untracked_variant(
        pa: Paddr,
        level: PagingLevel,
        prop: PageProperty,
    )
        requires
            !prop.flags.contains(crate::mm::page_prop::PageFlags::AVAIL1()),
        ensures
            matches!(KernelPtConfig::item_from_raw_spec(pa, level, prop),
                MappedItem::Untracked(_, _, _)),
    ;

    /// For KernelPtConfig (x86_64): HIGHEST_TRANSLATION_LEVEL = 2 < NR_LEVELS = 4.
    pub axiom fn axiom_kernel_htl_lt_nr_levels()
        ensures
            (KernelPtConfig::HIGHEST_TRANSLATION_LEVEL() as int) < NR_LEVELS as int,
    ;
}

/*
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum MappedItem {
    Tracked(Frame<dyn AnyFrameMeta>, PageProperty),
    Untracked(Paddr, PagingLevel, PageProperty),
}
*/

pub enum MappedItem {
    Tracked(DynFrame, PageProperty),
    Untracked(Paddr, PagingLevel, PageProperty),
}

impl RCClone for MappedItem {
    open spec fn clone_requires(self, perm: MetaRegionOwners) -> bool {
        match self {
            MappedItem::Tracked(frame, _) => frame.clone_requires(perm),
            MappedItem::Untracked(_, _, _) => perm.inv(),
        }
    }

    open spec fn clone_ensures(
        self,
        old_perm: MetaRegionOwners,
        new_perm: MetaRegionOwners,
        res: Self,
    ) -> bool {
        match (self, res) {
            (
                MappedItem::Tracked(frame, _),
                MappedItem::Tracked(res_frame, _),
            ) => frame.clone_ensures(old_perm, new_perm, res_frame),
            (MappedItem::Untracked(_, _, _), _) => old_perm == new_perm,
            _ => true,
        }
    }

    #[verifier::external_body]
    fn clone(&self, Tracked(perm): Tracked<&mut MetaRegionOwners>) -> (res: Self) {
        unimplemented!();
    }
}

} // verus!
// /// Initializes the kernel page table.
// ///
// /// This function should be called after:
// ///  - the page allocator and the heap allocator are initialized;
// ///  - the memory regions are initialized.
// ///
// /// This function should be called before:
// ///  - any initializer that modifies the kernel page table.
// pub fn init_kernel_page_table(meta_pages: Segment<MetaPageMeta>) {
//     info!("Initializing the kernel page table");
//     // Start to initialize the kernel page table.
//     let kpt = PageTable::<KernelPtConfig>::new_kernel_page_table();
//     let preempt_guard = disable_preempt();
//     // In LoongArch64, we don't need to do linear mappings for the kernel because of DMW0.
//     #[cfg(not(target_arch = "loongarch64"))]
//     // Do linear mappings for the kernel.
//     {
//         let max_paddr = crate::mm::frame::max_paddr();
//         let from = LINEAR_MAPPING_BASE_VADDR..LINEAR_MAPPING_BASE_VADDR + max_paddr;
//         let prop = PageProperty {
//             flags: PageFlags::RW,
//             cache: CachePolicy::Writeback,
//             priv_flags: PrivilegedPageFlags::GLOBAL,
//         };
//         let mut cursor = kpt.cursor_mut(&preempt_guard, &from).unwrap();
//         for (pa, level) in largest_pages::<KernelPtConfig>(from.start, 0, max_paddr) {
//             // SAFETY: we are doing the linear mapping for the kernel.
//             unsafe { cursor.map(MappedItem::Untracked(pa, level, prop)) }
//                 .expect("Kernel linear address space is mapped twice");
//         }
//     }
//     // Map the metadata pages.
//     {
//         let start_va = mapping::frame_to_meta::<PagingConsts>(0);
//         let from = start_va..start_va + meta_pages.size();
//         let prop = PageProperty {
//             flags: PageFlags::RW,
//             cache: CachePolicy::Writeback,
//             priv_flags: PrivilegedPageFlags::GLOBAL,
//         };
//         let mut cursor = kpt.cursor_mut(&preempt_guard, &from).unwrap();
//         // We use untracked mapping so that we can benefit from huge pages.
//         // We won't unmap them anyway, so there's no leaking problem yet.
//         // TODO: support tracked huge page mapping.
//         let pa_range = meta_pages.into_raw();
//         for (pa, level) in
//             largest_pages::<KernelPtConfig>(from.start, pa_range.start, pa_range.len())
//         {
//             // SAFETY: We are doing the metadata mappings for the kernel.
//             unsafe { cursor.map(MappedItem::Untracked(pa, level, prop)) }
//                 .expect("Frame metadata address space is mapped twice");
//         }
//     }
//     // In LoongArch64, we don't need to do linear mappings for the kernel code because of DMW0.
//     #[cfg(not(target_arch = "loongarch64"))]
//     // Map for the kernel code itself.
//     // TODO: set separated permissions for each segments in the kernel.
//     {
//         let regions = &crate::boot::EARLY_INFO.get().unwrap().memory_regions;
//         let region = regions
//             .iter()
//             .find(|r| r.typ() == MemoryRegionType::Kernel)
//             .unwrap();
//         let offset = kernel_loaded_offset();
//         let from = region.base() + offset..region.end() + offset;
//         let prop = PageProperty {
//             flags: PageFlags::RWX,
//             cache: CachePolicy::Writeback,
//             priv_flags: PrivilegedPageFlags::GLOBAL,
//         };
//         let mut cursor = kpt.cursor_mut(&preempt_guard, &from).unwrap();
//         for (pa, level) in largest_pages::<KernelPtConfig>(from.start, region.base(), from.len()) {
//             // SAFETY: we are doing the kernel code mapping.
//             unsafe { cursor.map(MappedItem::Untracked(pa, level, prop)) }
//                 .expect("Kernel code mapped twice");
//         }
//     }
//     KERNEL_PAGE_TABLE.call_once(|| kpt);
// }
// /// Activates the kernel page table.
// ///
// /// # Safety
// ///
// /// This function should only be called once per CPU.
// pub unsafe fn activate_kernel_page_table() {
//     let kpt = KERNEL_PAGE_TABLE
//         .get()
//         .expect("The kernel page table is not initialized yet");
//     // SAFETY: the kernel page table is initialized properly.
//     unsafe {
//         kpt.first_activate_unchecked();
//         crate::arch::mm::tlb_flush_all_including_global();
//     }
//     // SAFETY: the boot page table is OK to be dismissed now since
//     // the kernel page table is activated just now.
//     unsafe {
//         crate::mm::page_table::boot_pt::dismiss();
//     }
// }
