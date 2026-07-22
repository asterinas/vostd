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
use core::{marker::PhantomData, ops::Range};
use vstd::atomic::PermissionU64;
use vstd::prelude::*;
use vstd::simple_pptr::PointsTo;

//use log::info;
use crate::sync::{OnceImpl, TrivialPred};
pub(crate) mod kvirt_area;
#[cfg(ktest)]
mod test;

use super::{
    Paddr, PagingConstsTrait, Vaddr,
    frame::{
        Frame, Segment,
        meta::{AnyFrameMeta, MetaPageMeta, MetaSlot, mapping},
    },
    page_prop::{CachePolicy, PageFlags, PageProperty, PrivilegedPageFlags},
    page_table::{PageTable, PageTableConfig},
};
use crate::mm::frame::DynFrame;
use crate::mm::page_table::RCClone;
use crate::specs::arch::*;
use crate::specs::mm::{
    frame::{
        mapping::group_page_meta, meta_owners::MetaSlotStorage,
        meta_region_owners::MetaRegionOwners,
    },
    page_table::{nr_pte_index_bits_spec, pte_index_bit_offset_spec},
};
use crate::{
    arch::mm::{PageTableEntry, PagingConsts},
    boot::memory_region::MemoryRegionType,
    mm::{PagingLevel, largest_pages},
    //task::disable_preempt,
};

use vstd_extra::ownership::*;
use vstd_extra::prelude::*;

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
const KERNEL_CODE_BASE_VADDR: usize = 0xffff_ffff_8000_0000 << ADDR_WIDTH_SHIFT;

#[cfg(target_arch = "riscv64")]
const KERNEL_CODE_BASE_VADDR: usize = 0xffff_ffff_0000_0000 << ADDR_WIDTH_SHIFT;

#[cfg(target_arch = "loongarch64")]
const KERNEL_CODE_BASE_VADDR: usize = 0x9000_0000_0000_0000 << ADDR_WIDTH_SHIFT;

pub const FRAME_METADATA_CAP_VADDR: Vaddr = 0xffff_e100_0000_0000 << ADDR_WIDTH_SHIFT;

pub const FRAME_METADATA_BASE_VADDR: Vaddr = 0xffff_e000_0000_0000 << ADDR_WIDTH_SHIFT;

pub const FRAME_METADATA_RANGE: Range<Vaddr> = 0xffff_e000_0000_0000..0xffff_e100_0000_0000;

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

#[verifier::allow(autoderive_clone_without_spec)]
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

    proof fn lemma_page_table_config_constant_requirements() {
        use crate::mm::nr_subpage_per_huge;
        use vstd::arithmetic::power2::{lemma2_to64, lemma2_to64_rest, lemma_pow2_adds, pow2};
        Self::C::lemma_paging_consts_properties();
        PageTableEntry::lemma_layout();
        lemma2_to64();
        lemma2_to64_rest();
        vstd::layout::unsigned_int_max_values();
        lemma_usize_pow2_ilog2(12);
        lemma_usize_pow2_ilog2(9);
        lemma_pow2_adds(9, 39);
        lemma_pow2_adds(8, 39);

        assert((256 * pow2(39) as int) / (pow2(47) as int) == 1);
        lemma_pow2_adds(16, 48);
    }

    fn TOP_LEVEL_INDEX_RANGE() -> (r: Range<usize>) {
        256..512
    }

    open spec fn TOP_LEVEL_CAN_UNMAP_spec() -> bool {
        false
    }

    fn TOP_LEVEL_CAN_UNMAP() -> (b: bool) {
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

    open spec fn item_into_raw_spec(item: Self::Item) -> (Paddr, PagingLevel, PageProperty) {
        match item {
            MappedItem::Tracked(frame, prop) => (
                crate::mm::frame::meta::mapping::meta_to_frame(frame.ptr.addr()),
                1,
                Self::encode_tracked_prop(prop),
            ),
            MappedItem::Untracked(pa, level, prop) => (pa, level, Self::decode_tracked_prop(prop)),
        }
    }

    #[verifier::external_body]
    fn item_into_raw(item: Self::Item) -> (res: (Paddr, PagingLevel, PageProperty)) {
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

    open spec fn item_from_raw_spec(
        paddr: Paddr,
        level: PagingLevel,
        prop: PageProperty,
    ) -> Self::Item {
        if prop.flags.contains(PageFlags::AVAIL1()) {
            MappedItem::Tracked(
                Frame::<MetaSlotStorage> {
                    ptr: vstd::simple_pptr::PPtr(mapping::frame_to_meta(paddr), PhantomData),
                    _marker: PhantomData,
                },
                Self::decode_tracked_prop(prop),
            )
        } else {
            MappedItem::Untracked(paddr, level, prop)
        }
    }

    #[verifier::external_body]
    unsafe fn item_from_raw(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> Self::Item {
        if prop.flags.contains(PageFlags::AVAIL1()) {
            debug_assert_eq!(level, 1);
            // [KNOWN] BUG FOUND BY FV: forgotting to clean `AVAIL1`. https://github.com/asterinas/vostd/issues/625
            let mut item_prop = prop;
            item_prop.flags = item_prop.flags - PageFlags::AVAIL1();
            // SAFETY: The caller ensures safety.
            let frame = unsafe { Frame::<MetaSlotStorage>::from_raw(paddr) };
            MappedItem::Tracked(frame, item_prop)
        } else {
            MappedItem::Untracked(paddr, level, prop)
        }
    }

    proof fn lemma_item_into_raw_roundtrip(pa: Paddr, level: PagingLevel, prop: PageProperty) {
        broadcast use group_page_meta;

        assert(Self::raw_item_well_formed(pa, level, prop));
        Self::lemma_item_from_raw_well_formed(pa, level, prop);
        prop.lemma_avail1_tag_encoding();
    }

    proof fn lemma_item_from_raw_roundtrip(
        item: Self::Item,
        paddr: Paddr,
        level: PagingLevel,
        prop: PageProperty,
    ) {
        broadcast use group_page_meta;

        match item {
            MappedItem::Tracked(frame, prop_actual) => {
                assert(Self::item_well_formed(item));
                prop_actual.lemma_avail1_tag_encoding();
            },
            MappedItem::Untracked(_, _, prop_actual) => {
                assert(Self::item_well_formed(item));
                prop_actual.lemma_avail1_tag_encoding();
            },
        }
    }

    open spec fn tracked(item: Self::Item) -> bool {
        // Tracked items hold a reference; clone bumps rc. Untracked items
        // (MMIO frames) are not ref-counted; clone is a no-op.
        item is Tracked
    }

    open spec fn item_well_formed(item: Self::Item) -> bool {
        match item {
            MappedItem::Tracked(frame, prop) => {
                &&& !prop.flags.contains(PageFlags::AVAIL1())
                &&& frame.inv()
            },
            MappedItem::Untracked(_, _, prop) => !prop.flags.contains(PageFlags::AVAIL1()),
        }
    }

    open spec fn raw_item_well_formed(_pa: Paddr, level: PagingLevel, prop: PageProperty) -> bool {
        prop.flags.contains(PageFlags::AVAIL1()) ==> level == 1
    }

    proof fn lemma_raw_item_well_formed_preserved(
        pa: Paddr,
        level: PagingLevel,
        old_prop: PageProperty,
        new_prop: PageProperty,
    ) {
    }

    proof fn lemma_raw_item_well_formed_split(
        pa: Paddr,
        level: PagingLevel,
        prop: PageProperty,
        child_pa: Paddr,
        child_idx: usize,
    ) {
        assert(<PageTableEntry as crate::mm::page_table::PageTableEntryTrait>::new_page_req(
            pa,
            level,
            prop,
        ));
        assert(<PageTableEntry as crate::mm::page_table::PageTableEntryTrait>::new_page_req(
            child_pa,
            (level - 1) as PagingLevel,
            prop,
        ));
    }

    proof fn lemma_item_from_raw_well_formed(pa: Paddr, level: PagingLevel, prop: PageProperty) {
        broadcast use group_page_meta;

        prop.lemma_avail1_tag_encoding();
        if prop.flags.contains(PageFlags::AVAIL1()) {
            let item = Self::item_from_raw_spec(pa, level, prop);
            assert(Self::item_well_formed(item));
        } else {
            let item = Self::item_from_raw_spec(pa, level, prop);
            assert(Self::item_well_formed(item));
        }
    }

    proof fn lemma_clone_ensures_concrete(
        item: Self::Item,
        pa: Paddr,
        old_regions: MetaRegionOwners,
        new_regions: MetaRegionOwners,
        res: Self::Item,
    ) {
        use crate::mm::frame::meta::mapping::meta_to_frame;
        use crate::specs::mm::frame::mapping::frame_to_index;

        match item {
            MappedItem::Tracked(frame, _) => {
                let frame_idx = frame_to_index(meta_to_frame(frame.ptr.addr()));
                assert(<MappedItem as RCClone>::clone_ensures(item, old_regions, new_regions, res));
            },
            MappedItem::Untracked(_, _, _) => {},
        }
    }

    proof fn lemma_clone_requires_concrete(
        item: Self::Item,
        pa: Paddr,
        level: PagingLevel,
        prop: PageProperty,
        regions: MetaRegionOwners,
    ) {
        use crate::mm::frame::meta::mapping::meta_to_frame;
        broadcast use group_page_meta;

        Self::lemma_item_from_raw_well_formed(pa, level, prop);
    }
}

impl KernelPtConfig {
    /// Adds the raw PTE bit used to identify a ref-counted mapping.
    pub open spec fn encode_tracked_prop(prop: PageProperty) -> PageProperty {
        PageProperty { flags: prop.flags.union(PageFlags::AVAIL1()), ..prop }
    }

    /// Removes the raw PTE trackedness bit from a caller-visible property.
    pub open spec fn decode_tracked_prop(prop: PageProperty) -> PageProperty {
        PageProperty { flags: prop.flags.difference(PageFlags::AVAIL1()), ..prop }
    }
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
