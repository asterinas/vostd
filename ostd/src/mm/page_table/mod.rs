// SPDX-License-Identifier: MPL-2.0
use vstd::arithmetic::power2::*;
use vstd::prelude::*;
use vstd::simple_pptr;
use vstd::atomic::PermissionU64;
use vstd::std_specs::clone::*;

use vstd_extra::prelude::lemma_usize_ilog2_ordered;

use core::{
    fmt::Debug,
    intrinsics::transmute_unchecked,
    ops::{Range, RangeInclusive},
    sync::atomic::{AtomicUsize, Ordering},
};

use crate::mm::frame::meta::MetaSlot;

use super::{
    lemma_nr_subpage_per_huge_bounded,
    kspace::KernelPtConfig,
    nr_subpage_per_huge,
    page_prop::PageProperty,
    Paddr,
    vm_space::UserPtConfig,
    PagingConstsTrait,
    PagingLevel,
    Vaddr,
};

use crate::specs::mm::page_table::*;

use crate::specs::arch::mm::*;
use crate::specs::arch::paging_consts::PagingConsts;
use crate::specs::mm::page_table::cursor::*;
use crate::specs::task::InAtomicMode;

use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::frame::meta_owners::MetaPerm;
use crate::mm::kspace::kvirt_area::disable_preempt;
use crate::specs::arch::PageTableEntry;
use vstd_extra::ownership::Inv;

mod node;
pub use node::*;
mod cursor;

pub(crate) use cursor::*;

#[cfg(ktest)]
mod test;

//pub(crate) mod boot_pt;

verus! {

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PageTableError {
    /// The provided virtual address range is invalid.
    InvalidVaddrRange(Vaddr, Vaddr),
    /// The provided virtual address is invalid.
    InvalidVaddr(Vaddr),
    /// Using virtual address not aligned.
    UnalignedVaddr,
}

pub trait RCClone: Sized {
    spec fn clone_requires(self, slot_perm: simple_pptr::PointsTo<MetaSlot>, rc_perm: PermissionU64) -> bool;

    fn clone(&self, Tracked(slot_perm): Tracked<&simple_pptr::PointsTo<MetaSlot>>, Tracked(rc_perm): Tracked<&mut PermissionU64>) -> (res: Self)
        requires
            self.clone_requires(*slot_perm, *old(rc_perm)),
            old(rc_perm).is_for(slot_perm.value().ref_count),
            old(rc_perm).value() < u64::MAX,
        ensures
            res == *self,
            rc_perm.value() == old(rc_perm).value() + 1,
            rc_perm.id() == old(rc_perm).id(),
    ;
}

/// The configurations of a page table.
///
/// It abstracts away both the usage and the architecture specifics from the
/// general page table implementation. For examples:
///  - the managed virtual address range;
///  - the trackedness of physical mappings;
///  - the PTE layout;
///  - the number of page table levels, etc.
///
/// # Safety
///
/// The implementor must ensure that the `item_into_raw` and `item_from_raw`
/// are implemented correctly so that:
///  - `item_into_raw` consumes the ownership of the item;
///  - if the provided raw form matches the item that was consumed by
///    `item_into_raw`, `item_from_raw` restores the exact item that was
///    consumed by `item_into_raw`.
pub unsafe trait PageTableConfig: Clone + Debug + Send + Sync + 'static {
    /// The index range at the top level (`C::NR_LEVELS()`) page table.
    ///
    /// When configured with this value, the [`PageTable`] instance will only
    /// be allowed to manage the virtual address range that is covered by
    /// this range. The range can be smaller than the actual allowed range
    /// specified by the hardware MMU (limited by `C::ADDRESS_WIDTH`).
    spec fn TOP_LEVEL_INDEX_RANGE_spec() -> Range<usize>;

    fn TOP_LEVEL_INDEX_RANGE() -> (r: Range<usize>)
        ensures
            r == Self::TOP_LEVEL_INDEX_RANGE_spec(),
    ;

    /// If we can remove the top-level page table entries.
    ///
    /// This is for the kernel page table, whose second-top-level page
    /// tables need `'static` lifetime to be shared with user page tables.
    /// Other page tables do not need to set this to `false`.
    open spec fn TOP_LEVEL_CAN_UNMAP_spec() -> bool {
        true
    }

    fn TOP_LEVEL_CAN_UNMAP() -> (b: bool)
        ensures
            b == Self::TOP_LEVEL_CAN_UNMAP_spec(),
    ;

    /// The type of the page table entry.
    type E: PageTableEntryTrait;

    /// The paging constants.
    type C: PagingConstsTrait;

    proof fn axiom_nr_subpage_per_huge_eq_nr_entries()
        ensures
            Self::C::BASE_PAGE_SIZE() / Self::C::PTE_SIZE() == NR_ENTRIES,
    ;

    /// The item that can be mapped into the virtual memory space using the
    /// page table.
    ///
    /// Usually, this item is a [`crate::mm::Frame`], which we call a "tracked"
    /// frame. The page table can also do "untracked" mappings that only maps
    /// to certain physical addresses without tracking the ownership of the
    /// mapped physical frame. The user of the page table APIs can choose by
    /// defining this type and the corresponding methods [`item_into_raw`] and
    /// [`item_from_raw`].
    ///
    /// [`item_from_raw`]: PageTableConfig::item_from_raw
    /// [`item_into_raw`]: PageTableConfig::item_into_raw
    type Item: RCClone;

    /// Consumes the item and returns the physical address, the paging level,
    /// and the page property.
    ///
    /// The ownership of the item will be consumed, i.e., the item will be
    /// forgotten after this function is called.
    spec fn item_into_raw_spec(item: Self::Item) -> (Paddr, PagingLevel, PageProperty);

    #[verifier::when_used_as_spec(item_into_raw_spec)]
    fn item_into_raw(item: Self::Item) -> (res: (Paddr, PagingLevel, PageProperty))
        ensures
            1 <= res.1 <= NR_LEVELS,
            res == Self::item_into_raw_spec(item),
            res.0 % crate::specs::arch::mm::PAGE_SIZE == 0,
            res.0 < crate::specs::arch::mm::MAX_PADDR,
            res.0 % crate::mm::page_table::cursor::page_size(res.1) == 0,
            res.0 + crate::mm::page_table::cursor::page_size(res.1) <= crate::specs::arch::mm::MAX_PADDR,
    ;

    /// Restores the item from the physical address and the paging level.
    ///
    /// There could be transformations after [`PageTableConfig::item_into_raw`]
    /// and before [`PageTableConfig::item_from_raw`], which include:
    ///  - splitting and coalescing the items, for example, splitting one item
    ///    into 512 `level - 1` items with and contiguous physical addresses;
    ///  - protecting the items, for example, changing the page property.
    ///
    /// Splitting and coalescing maintains ownership rules, i.e., if one
    /// physical address is within the range of one item, after splitting/
    /// coalescing, there should be exactly one item that contains the address.
    ///
    /// # Safety
    ///
    /// The caller must ensure that:
    ///  - the physical address and the paging level represent a page table
    ///    item or part of it (as described above);
    ///  - either the ownership of the item is properly transferred to the
    ///    return value, or the return value is wrapped in a
    ///    [`core::mem::ManuallyDrop`] that won't outlive the original item.
    ///
    /// A concrete trait implementation may require the caller to ensure that
    ///  - the [`super::PageFlags::AVAIL1`] flag is the same as that returned
    ///    from [`PageTableConfig::item_into_raw`].
    spec fn item_from_raw_spec(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> Self::Item;

    #[verifier::when_used_as_spec(item_from_raw_spec)]
    fn item_from_raw(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> Self::Item
        returns
            Self::item_from_raw_spec(paddr, level, prop),
    ;

    proof fn item_roundtrip(item: Self::Item, paddr: Paddr, level: PagingLevel, prop: PageProperty)
        ensures
            Self::item_into_raw_spec(item) == (paddr, level, prop) <==> Self::item_from_raw_spec(
                paddr,
                level,
                prop,
            ) == item,
    ;
}

// Implement it so that we can comfortably use low level functions
// like `page_size::<C>` without typing `C::C` everywhere.
impl<C: PageTableConfig> PagingConstsTrait for C {
    open spec fn BASE_PAGE_SIZE_spec() -> usize {
        C::C::BASE_PAGE_SIZE_spec()
    }

    fn BASE_PAGE_SIZE() -> usize {
        C::C::BASE_PAGE_SIZE()
    }

    open spec fn NR_LEVELS_spec() -> PagingLevel {
        C::C::NR_LEVELS_spec()
    }

    fn NR_LEVELS() -> PagingLevel {
        C::C::NR_LEVELS()
    }

    open spec fn HIGHEST_TRANSLATION_LEVEL_spec() -> PagingLevel {
        C::C::HIGHEST_TRANSLATION_LEVEL_spec()
    }

    fn HIGHEST_TRANSLATION_LEVEL() -> PagingLevel {
        C::C::HIGHEST_TRANSLATION_LEVEL()
    }

    open spec fn PTE_SIZE_spec() -> usize {
        C::C::PTE_SIZE_spec()
    }

    fn PTE_SIZE() -> usize {
        C::C::PTE_SIZE()
    }

    open spec fn ADDRESS_WIDTH_spec() -> usize {
        C::C::ADDRESS_WIDTH_spec()
    }

    fn ADDRESS_WIDTH() -> usize {
        C::C::ADDRESS_WIDTH()
    }

    open spec fn VA_SIGN_EXT_spec() -> bool {
        C::C::VA_SIGN_EXT_spec()
    }

    fn VA_SIGN_EXT() -> bool {
        C::C::VA_SIGN_EXT()
    }

    proof fn lemma_BASE_PAGE_SIZE_properties()
        ensures
            0 < Self::BASE_PAGE_SIZE_spec(),
            is_pow2(Self::BASE_PAGE_SIZE_spec() as int),
    {
        C::C::lemma_BASE_PAGE_SIZE_properties();
    }

    proof fn lemma_PTE_SIZE_properties()
        ensures
            0 < Self::PTE_SIZE_spec() <= Self::BASE_PAGE_SIZE(),
            is_pow2(Self::PTE_SIZE_spec() as int),
    {
        C::C::lemma_PTE_SIZE_properties();
    }
}

/// The interface for defining architecture-specific page table entries.
///
/// Note that a default PTE should be a PTE that points to nothing.
pub trait PageTableEntryTrait: Clone + Copy + Debug + Sized + Send + Sync + 'static {
    spec fn default_spec() -> Self;

    /// For implement `Default` trait.
    #[verifier::when_used_as_spec(default_spec)]
    fn default() -> (res: Self)
        ensures
            res == Self::default_spec(),
    ;

    /// Create a set of new invalid page table flags that indicates an absent page.
    ///
    /// Note that currently the implementation requires an all zero PTE to be an absent PTE.
    spec fn new_absent_spec() -> Self;

    #[verifier(when_used_as_spec(new_absent_spec))]
    fn new_absent() -> (res: Self)
        ensures
            res == Self::new_absent_spec(),
            res.paddr() % PAGE_SIZE == 0,
            res.paddr() < MAX_PADDR,
    ;

    /// If the flags are present with valid mappings.
    spec fn is_present_spec(&self) -> bool;

    #[verifier::when_used_as_spec(is_present_spec)]
    fn is_present(&self) -> (res: bool)
        ensures
            res == self.is_present_spec(),
    ;

    /// Create a new PTE with the given physical address and flags that map to a page.
    spec fn new_page_spec(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> Self;

    #[verifier::when_used_as_spec(new_page_spec)]
    fn new_page(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> (res: Self)
        requires
            paddr % PAGE_SIZE == 0,
            paddr < MAX_PADDR,
        ensures
            res == Self::new_page_spec(paddr, level, prop),
            res.paddr() == paddr,
            res.paddr() % PAGE_SIZE == 0,
            res.paddr() < MAX_PADDR,
    ;

    /// Create a new PTE that map to a child page table.
    spec fn new_pt_spec(paddr: Paddr) -> Self;

    #[verifier::when_used_as_spec(new_pt_spec)]
    fn new_pt(paddr: Paddr) -> (res: Self)
        requires
            paddr % PAGE_SIZE == 0,
            paddr < MAX_PADDR,
        ensures
            res == Self::new_pt_spec(paddr),
            res.paddr() == paddr,
            res.paddr() % PAGE_SIZE == 0,
            res.paddr() < MAX_PADDR,
    ;

    proof fn new_properties()
        ensures
            !Self::new_absent_spec().is_present(),
            forall|level: PagingLevel|
                #![trigger Self::new_absent_spec().is_last(level)]
                1 < level ==> !Self::new_absent_spec().is_last(level),
            forall|paddr: Paddr, level: PagingLevel, prop: PageProperty|
                #![trigger Self::new_page_spec(paddr, level, prop)]
                {
                    &&& Self::new_page_spec(paddr, level, prop).is_present()
                    &&& Self::new_page_spec(paddr, level, prop).paddr() == paddr
                    &&& Self::new_page_spec(paddr, level, prop).prop() == prop
                    &&& Self::new_page_spec(paddr, level, prop).is_last(level)
                },
            forall|paddr: Paddr|
                #![trigger Self::new_pt_spec(paddr)]
                {
                    &&& Self::new_pt_spec(paddr).is_present()
                    &&& Self::new_pt_spec(paddr).paddr() == paddr
                    &&& forall|level: PagingLevel| !Self::new_pt_spec(paddr).is_last(level)
                },
    ;

    /// Get the physical address from the PTE.
    /// The physical address recorded in the PTE is either:
    /// - the physical address of the next level page table;
    /// - or the physical address of the page it maps to.
    spec fn paddr_spec(&self) -> Paddr;

    #[verifier::when_used_as_spec(paddr_spec)]
    fn paddr(&self) -> (res: Paddr)
        ensures
            res == self.paddr_spec(),
    ;

    spec fn prop_spec(&self) -> PageProperty;

    #[verifier::when_used_as_spec(prop_spec)]
    fn prop(&self) -> (res: PageProperty)
        ensures
            res == self.prop_spec(),
    ;

    /// Set the page property of the PTE.
    ///
    /// This will be only done if the PTE is present. If not, this method will
    /// do nothing.
    spec fn set_prop_spec(&self, prop: PageProperty) -> Self;

    fn set_prop(&mut self, prop: PageProperty)
        ensures
            old(self).set_prop_spec(prop) == *self,
    ;

    proof fn set_prop_properties(self, prop: PageProperty)
        ensures
            self.set_prop_spec(prop).prop() == prop,
            self.set_prop_spec(prop).paddr() == self.paddr(),
            self.is_present() ==> self.set_prop_spec(prop).is_present(),
            forall|level: PagingLevel|
                #![trigger self.is_last(level)]
                self.is_last(level) ==> self.set_prop_spec(prop).is_last(level),
    ;

    /// If the PTE maps a page rather than a child page table.
    ///
    /// The level of the page table the entry resides is given since architectures
    /// like amd64 only uses a huge bit in intermediate levels.
    spec fn is_last_spec(&self, level: PagingLevel) -> bool;

    #[verifier::when_used_as_spec(is_last_spec)]
    fn is_last(&self, level: PagingLevel) -> (b: bool)
        ensures
            b == self.is_last_spec(level),
    ;

    /// Converts the PTE into its corresponding `usize` value.
    spec fn as_usize_spec(self) -> usize;

    #[verifier::external_body]
    #[verifier::when_used_as_spec(as_usize_spec)]
    fn as_usize(self) -> (res: usize)
        ensures
            res == self.as_usize_spec(),
    {
        unimplemented!()
        // SAFETY: `Self` is `Pod` and has the same memory representation as `usize`.
        //        unsafe { transmute_unchecked(self) }

    }

    /// Converts a usize `pte_raw` into a PTE.
    #[verifier::external_body]
    fn from_usize(pte_raw: usize) -> Self {
        unimplemented!()
        // SAFETY: `Self` is `Pod` and has the same memory representation as `usize`.
        //        unsafe { transmute_unchecked(pte_raw) }

    }
}

/// A handle to a page table.
/// A page table can track the lifetime of the mapped physical pages.
pub struct PageTable<C: PageTableConfig> {
    pub root: PageTableNode<C>,
}

#[verifier::inline]
pub open spec fn nr_pte_index_bits_spec<C: PagingConstsTrait>() -> usize {
    nr_subpage_per_huge::<C>().ilog2() as usize
}

/// The number of virtual address bits used to index a PTE in a page.
#[inline(always)]
#[verifier::when_used_as_spec(nr_pte_index_bits_spec)]
pub fn nr_pte_index_bits<C: PagingConstsTrait>() -> (res: usize)
    ensures
        res == nr_pte_index_bits_spec::<C>(),
{
    proof {
        lemma_nr_subpage_per_huge_bounded::<C>();
    }
    nr_subpage_per_huge::<C>().ilog2() as usize
}

pub proof fn lemma_nr_pte_index_bits_bounded<C: PagingConstsTrait>()
    ensures
        0 <= nr_pte_index_bits::<C>() <= C::BASE_PAGE_SIZE().ilog2(),
{
    lemma_nr_subpage_per_huge_bounded::<C>();
    let nr = nr_subpage_per_huge::<C>();
    assert(1 <= nr <= C::BASE_PAGE_SIZE());
    let bits = nr.ilog2();
    assert(0 <= bits) by {
        lemma_usize_ilog2_ordered(1, nr);
    }
    assert(bits <= C::BASE_PAGE_SIZE().ilog2()) by {
        lemma_usize_ilog2_ordered(nr, C::BASE_PAGE_SIZE());
    }
}

/// Splits the address range into largest page table items.
///
/// Each of the returned items is a tuple of the physical address and the
/// paging level. It is helpful when you want to map a physical address range
/// into the provided virtual address.
///
/// For example, on x86-64, `C: PageTableConfig` may specify level 1 page as
/// 4KiB, level 2 page as 2MiB, and level 3 page as 1GiB. Suppose that the
/// supplied physical address range is from `0x3fdff000` to `0x80002000`,
/// and the virtual address is also `0x3fdff000`, the following 5 items will
/// be returned:
///
/// ```text
/// 0x3fdff000                                                 0x80002000
/// start                                                             end
///   |----|----------------|--------------------------------|----|----|
///    4KiB      2MiB                       1GiB              4KiB 4KiB
/// ```
///
/// # Panics
///
/// Panics if:
///  - any of `va`, `pa`, or `len` is not aligned to the base page size;
///  - the range `va..(va + len)` is not valid for the page table.
#[verifier::external_body]
pub fn largest_pages<C: PageTableConfig>(
    mut va: Vaddr,
    mut pa: Paddr,
    mut len: usize,
) -> impl Iterator<Item = (Paddr, PagingLevel)> {
    assert_eq!(va % C::BASE_PAGE_SIZE(), 0);
    assert_eq!(pa % C::BASE_PAGE_SIZE(), 0);
    assert_eq!(len % C::BASE_PAGE_SIZE(), 0);
    assert!(is_valid_range::<C>(&(va..(va + len))));

    core::iter::from_fn(
        move ||
            {
                if len == 0 {
                    return None;
                }
                let mut level = C::HIGHEST_TRANSLATION_LEVEL();
                while page_size(level) > len || va % page_size(level) != 0 || pa % page_size(level)
                    != 0 {
                    level -= 1;
                }

                let item_start = pa;
                va += page_size(level);
                pa += page_size(level);
                len -= page_size(level);

                Some((item_start, level))
            },
    )
}

/// Gets the managed virtual addresses range for the page table.
///
/// It returns a [`RangeInclusive`] because the end address, if being
/// [`Vaddr::MAX`], overflows [`Range<Vaddr>`].
#[verifier::external_body]
fn top_level_index_width<C: PageTableConfig>() -> usize {
    C::ADDRESS_WIDTH() - pte_index_bit_offset::<C>(C::NR_LEVELS())
}

#[verifier::external_body]
fn pt_va_range_start<C: PageTableConfig>() -> Vaddr {
    C::TOP_LEVEL_INDEX_RANGE().start << pte_index_bit_offset::<C>(C::NR_LEVELS())
}

#[verifier::external_body]
fn pt_va_range_end<C: PageTableConfig>() -> Vaddr {
    C::TOP_LEVEL_INDEX_RANGE().end.unbounded_shl(
        pte_index_bit_offset::<C>(C::NR_LEVELS()) as u32,
    ).wrapping_sub(1)  // Inclusive end.

}

#[verifier::external_body]
fn sign_bit_of_va<C: PageTableConfig>(va: Vaddr) -> bool {
    (va >> (C::ADDRESS_WIDTH() - 1)) & 1 != 0
}

#[verifier::inline]
pub open spec fn pte_index_bit_offset_spec<C: PagingConstsTrait>(level: PagingLevel) -> int {
    (C::BASE_PAGE_SIZE().ilog2() as int) + (nr_pte_index_bits::<C>() as int) * (level as int - 1)
}

/// Spec for the managed virtual address range (exclusive end).
/// For configs without VA_SIGN_EXT (e.g. UserPtConfig) or when the base range has sign bit 0.
/// Configs with sign extension (e.g. KernelPtConfig) use a wrapped range in exec;
/// we use an axiom to connect that case.
#[verifier::inline]
pub open spec fn vaddr_range_spec<C: PageTableConfig>() -> Range<Vaddr> {
    let idx_range = C::TOP_LEVEL_INDEX_RANGE_spec();
    let offset = pte_index_bit_offset_spec::<C::C>(C::NR_LEVELS()) as nat;
    let start = (idx_range.start as int) * pow2(offset);
    let end_inclusive = (idx_range.end as int) * pow2(offset) - 1;
    (start as Vaddr)..((end_inclusive + 1) as Vaddr)
}

/// Spec for whether a range is within the page table's managed address space.
#[verifier::inline]
pub open spec fn is_valid_range_spec<C: PageTableConfig>(r: &Range<Vaddr>) -> bool {
    let va_range = vaddr_range_spec::<C>();
    (r.start == 0 && r.end == 0)
        || (va_range.start <= r.start && r.end > 0 && r.end - 1 <= va_range.end - 1)
}

#[verifier::external_body]
fn vaddr_range<C: PageTableConfig>() -> (ret: Range<Vaddr>)
    ensures
        ret == vaddr_range_spec::<C>(),
{
    /*    const {
        assert!(C::TOP_LEVEL_INDEX_RANGE().start < C::TOP_LEVEL_INDEX_RANGE().end);
        assert!(top_level_index_width::<C>() <= nr_pte_index_bits::<C>(),);
        assert!(C::TOP_LEVEL_INDEX_RANGE().start < 1 << top_level_index_width::<C>());
        assert!(C::TOP_LEVEL_INDEX_RANGE().end <= 1 << top_level_index_width::<C>());
    };*/
    let mut start = pt_va_range_start::<C>();
    let mut end = pt_va_range_end::<C>();

    /*    const {
        assert!(
            !C::VA_SIGN_EXT()
                || sign_bit_of_va::<C>(pt_va_range_start::<C>())
                    == sign_bit_of_va::<C>(pt_va_range_end::<C>()),
            "The sign bit of both range endpoints must be the same if sign extension is enabled"
        )
    }*/

    if C::VA_SIGN_EXT() && sign_bit_of_va::<C>(pt_va_range_start::<C>()) {
        start |= !0 ^ ((1 << C::ADDRESS_WIDTH()) - 1);
        end |= !0 ^ ((1 << C::ADDRESS_WIDTH()) - 1);
    }
    start..end + 1
}

/// Checks if the given range is covered by the valid range of the page table.
#[verifier::external_body]
fn is_valid_range<C: PageTableConfig>(r: &Range<Vaddr>) -> (ret: bool)
    ensures
        ret == is_valid_range_spec::<C>(r),
{
    let va_range = vaddr_range::<C>();
    (r.start == 0 && r.end == 0) || (va_range.start <= r.start && r.end - 1 <= va_range.end)
}

// Here are some const values that are determined by the paging constants.
/// The index of a VA's PTE in a page table node at the given level.
#[verifier::external_body]
fn pte_index<C: PagingConstsTrait>(va: Vaddr, level: PagingLevel) -> (res: usize)
    ensures
        res == AbstractVaddr::from_vaddr(va).index[level - 1],
{
    (va >> pte_index_bit_offset::<C>(level)) & (nr_subpage_per_huge::<C>() - 1)
}

/// The bit offset of the entry offset part in a virtual address.
///
/// This function returns the bit offset of the least significant bit. Take
/// x86-64 as an example, the `pte_index_bit_offset(2)` should return 21, which
/// is 12 (the 4KiB in-page offset) plus 9 (index width in the level-1 table).
#[verifier::external_body]
fn pte_index_bit_offset<C: PagingConstsTrait>(level: PagingLevel) -> usize {
    C::BASE_PAGE_SIZE().ilog2() as usize + nr_pte_index_bits::<C>() * (level as usize - 1)
}

/* TODO: stub out UserPtConfig

impl PageTable<UserPtConfig> {
    pub fn activate(&self) {
        // SAFETY: The user mode page table is safe to activate since the kernel
        // mappings are shared.
        unsafe {
            self.root.activate();
        }
    }
}*/

impl PageTable<KernelPtConfig> {
    /// Panic condition for [`Self::create_user_page_table`]:
    /// Some kernel root entry at index `i` in `TOP_LEVEL_INDEX_RANGE` is
    /// not a page table node (i.e., is absent or maps a huge frame).
    pub open spec fn create_user_pt_panic_condition(root_owner: NodeOwner<KernelPtConfig>) -> bool {
        exists|i: usize|
            #![trigger root_owner.children_perm.value()[i as int]]
            KernelPtConfig::TOP_LEVEL_INDEX_RANGE_spec().start <= i
                < KernelPtConfig::TOP_LEVEL_INDEX_RANGE_spec().end
            && {
                let pte = root_owner.children_perm.value()[i as int];
                ||| !pte.is_present()
                ||| pte.is_last(root_owner.level)
            }
    }

    /// Create a new kernel page table.
    #[verifier::external_body]
    pub(crate) fn new_kernel_page_table() -> Self {
        unimplemented!()
/*        let kpt = Self::empty();

        // Make shared the page tables mapped by the root table in the kernel space.
        {
            let preempt_guard = disable_preempt();
            let mut root_node = kpt.root.borrow().lock(&preempt_guard);

            for i in KernelPtConfig::TOP_LEVEL_INDEX_RANGE {
                let mut root_entry = root_node.entry(i);
                let _ = root_entry.alloc_if_none(&preempt_guard).unwrap();
            }
        }

        kpt*/
    }

    /// Create a new user page table.
    ///
    /// This should be the only way to create the user page table, that is to
    /// duplicate the kernel page table with all the kernel mappings shared.
    #[verus_spec(r =>
        with Tracked(kernel_owner): Tracked<&PageTableOwner<KernelPtConfig>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards_k): Tracked<&mut Guards<'static, KernelPtConfig>>,
            Tracked(guards_u): Tracked<&mut Guards<'static, UserPtConfig>>,
        requires
            kernel_owner.inv(),
            old(regions).inv(),
            kernel_owner.0.value.node is Some,
            !Self::create_user_pt_panic_condition(kernel_owner.0.value.node.unwrap()),
            // The kernel page table's root frame matches the tracked owner.
            self.root.ptr.addr() == kernel_owner.0.value.node.unwrap().meta_perm.addr(),
            // The kernel root entry is sound with respect to the meta regions.
            kernel_owner.0.value.metaregion_sound(*old(regions)),
    )]
    pub(in crate::mm) fn create_user_page_table<G: InAtomicMode + 'static>(&'static self) -> PageTable<UserPtConfig> {
        let preempt_guard: &G = disable_preempt::<G>();

        proof_decl! {
            let tracked mut new_pt_owner: Option<PageTableOwner<UserPtConfig>> = None;
        }
        let new_pt: PageTable<UserPtConfig> = PageTable::empty_with_owner(Tracked(&mut new_pt_owner));
        let new_root = new_pt.root;

        proof_decl! {
            let tracked root_owner: &NodeOwner<KernelPtConfig>
                = kernel_owner.0.borrow_value().node.tracked_borrow();
            let tracked root_perm: &MetaPerm<PageTablePageMeta<KernelPtConfig>>
                = &root_owner.meta_perm;
            let tracked mut new_pt_owner_val: PageTableOwner<UserPtConfig>
                = new_pt_owner.tracked_take();
            let tracked mut new_node_owner: NodeOwner<UserPtConfig>
                = new_pt_owner_val.0.value.node.tracked_take();
            let tracked mut root_guard_perm: GuardPerm<'static, KernelPtConfig>;
            let tracked mut new_guard_perm_lock: GuardPerm<'static, UserPtConfig>;
            let tracked mut entry_owner: &EntryOwner<KernelPtConfig>;
        }

        // borrow/lock preconditions: deeply nested chain from kernel_owner.inv()
        // + metaregion_sound + guards unlocked. Admitting for now.
        proof { admit(); }
        let root_node = {
            #[verus_spec(with Tracked(regions), Tracked(root_perm))]
            let root_ref = self.root.borrow();
            #[verus_spec(with Tracked(root_owner), Tracked(guards_k) => Tracked(root_guard_perm))]
            root_ref.lock(preempt_guard)
        };
        let new_node: vstd::simple_pptr::PPtr<PageTableGuard<'static, UserPtConfig>> = {
            #[verus_spec(with Tracked(regions), Tracked(&new_node_owner.meta_perm))]
            let new_ref = new_root.borrow();
            #[verus_spec(with Tracked(&new_node_owner), Tracked(guards_u) => Tracked(new_guard_perm_lock))]
            new_ref.lock(preempt_guard)
        };
        let mut i: usize = KernelPtConfig::TOP_LEVEL_INDEX_RANGE().start;
        while i < KernelPtConfig::TOP_LEVEL_INDEX_RANGE().end
            invariant
                kernel_owner.inv(),
                kernel_owner.0.value.node is Some,
                regions.inv(),
                !Self::create_user_pt_panic_condition(kernel_owner.0.value.node.unwrap()),
                i <= KernelPtConfig::TOP_LEVEL_INDEX_RANGE_spec().end,
            decreases KernelPtConfig::TOP_LEVEL_INDEX_RANGE_spec().end - i,
        {
            proof {
                let kern_node = kernel_owner.0.value.node.unwrap();
                assert forall |j: usize|
                    #![trigger kern_node.children_perm.value()[j as int]]
                    KernelPtConfig::TOP_LEVEL_INDEX_RANGE_spec().start <= j
                        < KernelPtConfig::TOP_LEVEL_INDEX_RANGE_spec().end
                    implies {
                        let pte = kern_node.children_perm.value()[j as int];
                        pte.is_present() && !pte.is_last(kern_node.level)
                    } by {
                        let pte = kern_node.children_perm.value()[j as int];
                        if !pte.is_present() || pte.is_last(kern_node.level) {
                            assert(Self::create_user_pt_panic_condition(kern_node));
                        }
                    }

                let tracked child_opt: &Option<OwnerSubtree<KernelPtConfig>>
                    = kernel_owner.0.children.tracked_borrow(i as int);
                let tracked child_subtree: &OwnerSubtree<KernelPtConfig>
                    = child_opt.tracked_borrow();
                entry_owner = child_subtree.borrow_value();
                admit();
            }

            #[verus_spec(with Tracked(root_owner), Tracked(entry_owner), Tracked(&root_guard_perm))]
            let root_entry = PageTableGuard::entry(root_node, i);
            #[verus_spec(with Tracked(entry_owner), Tracked(root_owner), Tracked(regions), Tracked(&root_guard_perm))]
            let child = root_entry.to_ref();

            assume(child is PageTable);
            let pt = match child {
                ChildRef::PageTable(pt) => pt,
                _ => vstd::pervasive::unreached(),
            };

            #[verus_spec(with Tracked(&entry_owner.node.tracked_borrow().meta_perm.points_to))]
            let pt_addr = pt.start_paddr();
            let pte = PageTableEntry::new_pt(pt_addr);

            let mut new_guard = new_node.take(Tracked(&mut new_guard_perm_lock));
            #[verus_spec(with Tracked(&mut new_node_owner))]
            new_guard.write_pte(i, pte);
            new_node.put(Tracked(&mut new_guard_perm_lock), new_guard);

            i = i + 1;
        }

        PageTable::<UserPtConfig> { root: new_root }
    }

    /*
    /// Protect the given virtual address range in the kernel page table.
    ///
    /// This method flushes the TLB entries when doing protection.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the protection operation does not affect
    /// the memory safety of the kernel.
    pub unsafe fn protect_flush_tlb(
        &self,
        vaddr: &Range<Vaddr>,
        mut op: impl FnMut(&mut PageProperty),
    ) -> Result<(), PageTableError> {
        let preempt_guard = disable_preempt();
        let mut cursor = CursorMut::new(self, &preempt_guard, vaddr)?;
        // SAFETY: The safety is upheld by the caller.
        while let Some(range) =
            unsafe { cursor.protect_next(vaddr.end - cursor.virt_addr(), &mut op) }
        {
            crate::arch::mm::tlb_flush_addr(range.start);
        }
        Ok(())
    }*/
}

impl<C: PageTableConfig> PageTable<C> {
    pub uninterp spec fn root_paddr_spec(&self) -> Paddr;

    /// Create a new empty page table.
    ///
    /// Useful for the IOMMU page tables only.
    #[verifier::external_body]
    pub fn empty() -> Self {
        unimplemented!()
    }

    /// Create a new empty page table together with its tracked ownership.
    /// Create a new empty page table together with its tracked ownership.
    #[verifier::external_body]
    pub fn empty_with_owner(Tracked(owner): Tracked<&mut Option<PageTableOwner<C>>>) -> (r: Self)
        ensures
            owner@ is Some,
            owner@.unwrap().inv(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub(in crate::mm) unsafe fn first_activate_unchecked(&self) {
        unimplemented!()
        // SAFETY: The safety is upheld by the caller.
        //        unsafe { self.root.first_activate() };

    }

    /// The physical address of the root page table.
    ///
    /// Obtaining the physical address of the root page table is safe, however, using it or
    /// providing it to the hardware will be unsafe since the page table node may be dropped,
    /// resulting in UAF.
    #[verifier::external_body]
    #[verifier::when_used_as_spec(root_paddr_spec)]
    pub fn root_paddr(&self) -> (r: Paddr)
        returns
            self.root_paddr_spec(),
    {
        unimplemented!()
        //        self.root.start_paddr()

    }

    /// Query about the mapping of a single byte at the given virtual address.
    ///
    /// Note that this function may fail reflect an accurate result if there are
    /// cursors concurrently accessing the same virtual address range, just like what
    /// happens for the hardware MMU walk.
    #[cfg(ktest)]
    pub fn page_walk(&self, vaddr: Vaddr) -> Option<(Paddr, PageProperty)> {
        // SAFETY: The root node is a valid page table node so the address is valid.
        unsafe { page_walk::<C>(self.root_paddr(), vaddr) }
    }

    /// Create a new cursor exclusively accessing the virtual address range for mapping.
    ///
    /// If another cursor is already accessing the range, the new cursor may wait until the
    /// previous cursor is dropped.
    #[verus_spec(r =>
        with Tracked(owner): Tracked<PageTableOwner<C>>,
            Tracked(guard_perm): Tracked<GuardPerm<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
        ensures
            Cursor::<C, G>::cursor_new_success_conditions(va) ==> {
                &&& r is Ok
                &&& r.unwrap().0.inner.invariants(*r.unwrap().1, *regions, *guards)
                &&& r.unwrap().1.metaregion_correct(*regions)
                &&& r.unwrap().1.in_locked_range()
                &&& r.unwrap().0.inner.level < r.unwrap().0.inner.guard_level
                &&& r.unwrap().0.inner.guard_level == NR_LEVELS as PagingLevel
                &&& r.unwrap().0.inner.va < r.unwrap().0.inner.barrier_va.end
                &&& r.unwrap().0.inner.va == va.start
                &&& r.unwrap().0.inner.barrier_va == *va
            },
            forall |item: C::Item| #![trigger CursorMut::<'rcu, C, G>::item_not_mapped(item, *old(regions))]
                CursorMut::<'rcu, C, G>::item_not_mapped(item, *old(regions)) ==>
                CursorMut::<'rcu, C, G>::item_not_mapped(item, *regions),
            // cursor_mut only locks page-table node slots; path_if_in_pt is unchanged for all slots.
            forall |idx: usize| #![auto]
                (*regions).slot_owners[idx].path_if_in_pt == (*old(regions)).slot_owners[idx].path_if_in_pt,
    )]
    #[verifier::external_body]
    pub fn cursor_mut<'rcu, G: InAtomicMode>(
        &'rcu self,
        guard: &'rcu G,
        va: &Range<Vaddr>,
    ) -> Result<(CursorMut<'rcu, C, G>, Tracked<CursorOwner<'rcu, C>>), PageTableError> {
        #[verus_spec(with Tracked(owner), Tracked(guard_perm), Tracked(regions), Tracked(guards))]
        CursorMut::new(self, guard, va)
    }

    /// Create a new cursor exclusively accessing the virtual address range for querying.
    ///
    /// If another cursor is already accessing the range, the new cursor may wait until the
    /// previous cursor is dropped. The modification to the mapping by the cursor may also
    /// block or be overridden by the mapping of another cursor.
    #[verus_spec(r =>
        with Tracked(owner): Tracked<PageTableOwner<C>>,
            Tracked(guard_perm): Tracked<GuardPerm<'rcu, C>>,
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(guards): Tracked<&mut Guards<'rcu, C>>
        requires
            owner.inv(),
        ensures
            Cursor::<C, G>::cursor_new_success_conditions(va) ==> r is Ok
    )]
    pub fn cursor<'rcu, G: InAtomicMode>(&'rcu self, guard: &'rcu G, va: &Range<Vaddr>)
    -> Result<(Cursor<'rcu, C, G>, Tracked<CursorOwner<'rcu, C>>), PageTableError> {
        #[verus_spec(with Tracked(owner), Tracked(guard_perm), Tracked(regions), Tracked(guards))]
        Cursor::new(self, guard, va)
    }
    
    /*
    /// Create a new reference to the same page table.
    /// The caller must ensure that the kernel page table is not copied.
    /// This is only useful for IOMMU page tables. Think twice before using it in other cases.
    pub unsafe fn shallow_copy(&self) -> Self {
        PageTable {
            root: self.root.clone(),
        }
    }
    */

}

/// A software emulation of the MMU address translation process.
///
/// This method returns the physical address of the given virtual address and
/// the page property if a valid mapping exists for the given virtual address.
///
/// # Safety
///
/// The caller must ensure that the `root_paddr` is a pointer to a valid root
/// page table node.
///
/// # Notes on the page table use-after-free problem
///
/// Neither the hardware MMU nor the software page walk method acquires the page
/// table locks while reading. They can enter a to-be-recycled page table node
/// and read the page table entries after the node is recycled and reused.
///
/// For the hardware MMU page walk, we mitigate this problem by dropping the page
/// table nodes only after the TLBs have been flushed on all the CPUs that
/// activate the page table.
///
/// For the software page walk, we only need to disable preemption at the beginning
/// since the page table nodes won't be recycled in the RCU critical section.
#[cfg(ktest)]
pub(super) unsafe fn page_walk<C: PageTableConfig>(root_paddr: Paddr, vaddr: Vaddr) -> Option<
    (Paddr, PageProperty),
> {
    use super::paddr_to_vaddr;

    let _rcu_guard = disable_preempt();

    let mut pt_addr = paddr_to_vaddr(root_paddr);
    #[verusfmt::skip]
    for cur_level in (1..= C::NR_LEVELS()).rev() {
        let offset = pte_index::<C>(vaddr, cur_level);
        // SAFETY:
        //  - The page table node is alive because (1) the root node is alive and
        //    (2) all child nodes cannot be recycled because we're in the RCU critical section.
        //  - The index is inside the bound, so the page table entry is valid.
        //  - All page table entries are aligned and accessed with atomic operations only.
        let cur_pte = unsafe { load_pte((pt_addr as *mut C::E).add(offset), Ordering::Acquire) };

        if !cur_pte.is_present() {
            return None;
        }
        if cur_pte.is_last(cur_level) {
            debug_assert!(cur_level <= C::HIGHEST_TRANSLATION_LEVEL);
            return Some(
                (cur_pte.paddr() + (vaddr & (page_size::<C>(cur_level) - 1)), cur_pte.prop()),
            );
        }
        pt_addr = paddr_to_vaddr(cur_pte.paddr());
    }

    unreachable!("All present PTEs at the level 1 must be last-level PTEs");
}

/// Loads a page table entry with an atomic instruction.
///
/// # Verification Design
/// ## Preconditions
/// - The pointer must be a valid pointer to the array that represents the page table node.
/// - The array must be initialized at the target index.
/// ## Postconditions
/// - The value is loaded from the array at the given index.
/// ## Safety
/// - We require the caller to provide a permission token to ensure that this function is only called on a valid array
/// and the pointer is in bounds.
/// - Like an `AtomicUsize::load` in normal Rust, this function assumes that the value being loaded is an integer
/// (and therefore can be safely cloned). We model the PTE as an abstract type, but in all actual implementations it is an
/// integer. Importantly, it does not include any data that is unsafe to duplicate.
#[verifier::external_body]
#[verus_spec(
    with Tracked(perm): Tracked<&vstd_extra::array_ptr::PointsTo<E, NR_ENTRIES>>
    requires
        perm.is_init(ptr.index as int),
        perm.addr() == ptr.addr(),
        0 <= ptr.index < NR_ENTRIES,
    returns
        perm.value()[ptr.index as int],
)]
pub fn load_pte<E: PageTableEntryTrait>(
    ptr: vstd_extra::array_ptr::ArrayPtr<E, NR_ENTRIES>,
    ordering: Ordering,
) -> (pte: E) {
    unimplemented!()
}

/// Stores a page table entry with an atomic instruction.
///
/// # Verification Design
/// We axiomatize this function as a store operation in the array that represents the page table node.
/// ## Preconditions
/// - The pointer must be a valid pointer to the array that represents the page table node.
/// - The array must be initialized so that the verifier knows that it remains initialized after the store.
/// ## Postconditions
/// - The new value is stored in the array at the given index.
/// ## Safety
/// - We require the caller to provide a permission token to ensure that this function is only called on a valid array
/// and the pointer is in bounds.
#[verifier::external_body]
#[verus_spec(
    with Tracked(perm): Tracked<&mut vstd_extra::array_ptr::PointsTo<E, NR_ENTRIES>>
    requires
        old(perm).addr() == ptr.addr(),
        0 <= ptr.index < NR_ENTRIES,
        old(perm).is_init_all(),
    ensures
        perm.value()[ptr.index as int] == new_val,
        perm.value() == old(perm).value().update(ptr.index as int, new_val),
        perm.addr() == old(perm).addr(),
        perm.is_init_all(),
)]
pub fn store_pte<E: PageTableEntryTrait>(
    ptr: vstd_extra::array_ptr::ArrayPtr<E, NR_ENTRIES>,
    new_val: E,
    ordering: Ordering,
);

} // verus!
