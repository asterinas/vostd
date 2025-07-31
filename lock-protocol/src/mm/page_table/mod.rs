pub mod cursor;
pub mod node;

use cursor::spec_helpers;

pub use node::*;
use core::fmt::Debug;
use std::{marker::PhantomData, ops::Range};

use crate::{
    helpers::{align_ext::align_down, math::lemma_u64_and_less_than},
    mm::{frame::allocator::AllocatorModel, BASE_PAGE_SIZE, PTE_SIZE},
};

use vstd::prelude::*;
use vstd::{
    arithmetic::{div_mod::*, logarithm::*, power::pow, power2::*},
    bits::*,
    layout::is_power_2,
};
use vstd_extra::extra_num::{
    lemma_log2_to64, lemma_pow2_is_power2_to64, lemma_usize_ilog2_ordered, lemma_usize_ilog2_to32,
    lemma_usize_is_power_2_is_ilog2_pow2, lemma_usize_pow2_ilog2, lemma_usize_shl_is_mul,
};

use super::{
    meta::AnyFrameMeta, nr_subpage_per_huge, page_prop::PageProperty, page_size, vm_space::Token,
    page_size_spec, lemma_page_size_spec_properties, Paddr, PagingLevel, Vaddr, NR_ENTRIES,
};

use crate::exec;
use crate::spec::sub_pt::SubPageTable;

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
pub  /*(crate)*/
 unsafe trait PageTableConfig {
    /// The index range at the top level (`C::NR_LEVELS`) page table.
    ///
    /// When configured with this value, the [`PageTable`] instance will only
    /// be allowed to manage the virtual address range that is covered by
    /// this range. The range can be smaller than the actual allowed range
    /// specified by the hardware MMU (limited by `C::ADDRESS_WIDTH`).
    #[verifier::when_used_as_spec(TOP_LEVEL_INDEX_RANGE_spec)]
    fn TOP_LEVEL_INDEX_RANGE() -> Range<usize>;

    spec fn TOP_LEVEL_INDEX_RANGE_spec() -> Range<usize>;

    /// If we can remove the top-level page table entries.
    ///
    /// This is for the kernel page table, whose second-top-level page
    /// tables need `'static` lifetime to be shared with user page tables.
    /// Other page tables do not need to set this to `false`.
    #[verifier::when_used_as_spec(TOP_LEVEL_CAN_UNMAP_spec)]
    fn TOP_LEVEL_CAN_UNMAP() -> bool;

    spec fn TOP_LEVEL_CAN_UNMAP_spec() -> bool;

    /// The type of the page table entry.
    type E: PageTableEntryTrait;

    /// The paging constants.
    type C: PagingConstsTrait;

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
    type Item;

    // : Clone;
    /// Consumes the item and returns the physical address, the paging level,
    /// and the page property.
    ///
    /// The ownership of the item will be consumed, i.e., the item will be
    /// forgotten after this function is called.
    fn item_into_raw(item: Self::Item) -> (res: (Paddr, PagingLevel, PageProperty))
        ensures
            res == Self::item_into_raw_spec(item),
    ;

    spec fn item_into_raw_spec(item: Self::Item) -> (Paddr, PagingLevel, PageProperty);

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
    unsafe fn item_from_raw(
        paddr: Paddr,
        level: PagingLevel,
        prop: PageProperty,
        Tracked(alloc_model): Tracked<&AllocatorModel<crate::mm::vm_space::UntypedFrameMeta>>,
    ) -> Self::Item
        requires
            alloc_model.invariants(),
    ;
}

impl<C: PageTableConfig> PagingConstsTrait for C {
    open spec fn BASE_PAGE_SIZE_SPEC() -> usize {
        C::C::BASE_PAGE_SIZE_SPEC()
    }

    fn BASE_PAGE_SIZE() -> (res: usize) {
        C::C::BASE_PAGE_SIZE()
    }

    open spec fn NR_LEVELS_SPEC() -> PagingLevel {
        C::C::NR_LEVELS_SPEC()
    }

    fn NR_LEVELS() -> (res: PagingLevel) {
        C::C::NR_LEVELS()
    }

    open spec fn HIGHEST_TRANSLATION_LEVEL_SPEC() -> PagingLevel {
        C::C::HIGHEST_TRANSLATION_LEVEL_SPEC()
    }

    fn HIGHEST_TRANSLATION_LEVEL() -> PagingLevel {
        C::C::HIGHEST_TRANSLATION_LEVEL()
    }

    open spec fn PTE_SIZE_SPEC() -> usize {
        C::C::PTE_SIZE_SPEC()
    }

    fn PTE_SIZE() -> usize {
        C::C::PTE_SIZE()
    }

    open spec fn ADDRESS_WIDTH_SPEC() -> usize {
        C::C::ADDRESS_WIDTH_SPEC()
    }

    fn ADDRESS_WIDTH() -> usize {
        C::C::ADDRESS_WIDTH()
    }

    open spec fn VA_SIGN_EXT_SPEC() -> bool {
        C::C::VA_SIGN_EXT_SPEC()
    }

    fn VA_SIGN_EXT() -> bool {
        C::C::VA_SIGN_EXT()
    }

    proof fn lemma_consts_properties() {
        C::C::lemma_consts_properties();
    }
}

pub trait PageTableEntryTrait: Clone +
// Copy +
// Default +
// Sized + Send + Sync + 'static
// Debug // TODO: Implement Debug for PageTableEntryTrait
// + Pod + PodOnce // TODO: Implement Pod and PodOnce for PageTableEntryTrait
Sized {
    /// Create a set of new invalid page table flags that indicates an absent page.
    ///
    /// Note that currently the implementation requires an all zero PTE to be an absent PTE.
    // TODO: Implement
    fn new_absent() -> (res: Self);

    /// If the flags are present with valid mappings.
    ///
    /// For PTEs created by [`Self::new_absent`], [`Self::new_token`], this
    /// method should return false. And for PTEs created by [`Self::new_page`]
    /// or [`Self::new_pt`], whatever modified with [`Self::set_prop`] or not,
    /// this method should return true.
    #[verifier::when_used_as_spec(is_present_spec)]
    fn is_present(&self) -> (res: bool);

    spec fn is_present_spec(&self) -> bool;

    /// Create a new PTE with the given physical address and flags that map to a page.
    fn new_page(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> (res: Self);

    /// Create a new PTE that map to a child page table.
    fn new_pt(paddr: Paddr) -> (res: Self);

    /// Create a new PTE with the given token value but don't map to anything.
    fn new_token(token: Token) -> Self;

    /// Get the physical address the PTE points to.
    /// The physical address recorded in the PTE is either:
    ///  - the physical address of the next level page table;
    ///  - the physical address of the page it maps to;
    ///  - the value of the token.
    #[verifier::when_used_as_spec(frame_paddr_spec)]
    fn frame_paddr(&self) -> Paddr
        returns
            self.frame_paddr_spec(),
    ;

    spec fn frame_paddr_spec(&self) -> Paddr;

    #[verifier::when_used_as_spec(pte_paddr_spec)]
    fn pte_paddr(&self) -> Paddr
        returns
            self.pte_paddr_spec(),
    ;

    spec fn pte_paddr_spec(&self) -> Paddr;

    #[verifier::when_used_as_spec(prop_spec)]
    fn prop(&self) -> PageProperty;

    spec fn prop_spec(&self) -> PageProperty;

    /// Set the page property of the PTE.
    ///
    /// This will be only done if the PTE is present. If not, this method will
    /// do nothing.
    fn set_prop(&mut self, prop: PageProperty);

    /// Set the physical address of the PTE.
    ///
    /// This can be done for both present and absent PTEs.
    fn set_paddr(&mut self, paddr: Paddr);

    /// If the PTE maps a page rather than a child page table.
    ///
    /// The level of the page table the entry resides is given since architectures
    /// like amd64 only uses a huge bit in intermediate levels.
    fn is_last(&self, level: PagingLevel) -> bool;

    // It seems we cannot specify a clone spec for a trait in Verus.
    fn clone_pte(&self) -> (res: Self)
        ensures
            self.pte_paddr() == res.pte_paddr(),
            self.is_present() == res.is_present(),
            self.prop() == res.prop(),
            self.frame_paddr() == res.frame_paddr(),
    ;
}

/// A minimal set of constants that determines the paging system.
/// This provides an abstraction over most paging modes in common architectures.
pub trait PagingConstsTrait:
    // Clone + Debug + Default + Send + Sync + 'static
Sized {
    spec fn BASE_PAGE_SIZE_SPEC() -> usize;

    // /// The smallest page size.
    // /// This is also the page size at level 1 page tables.
    #[verifier::when_used_as_spec(BASE_PAGE_SIZE_SPEC)]
    fn BASE_PAGE_SIZE() -> (res: usize)
        ensures
            res != 0,
            res == Self::BASE_PAGE_SIZE_SPEC(),
    ;

    spec fn NR_LEVELS_SPEC() -> PagingLevel;

    /// The number of levels in the page table.
    /// The numbering of levels goes from deepest node to the root node. For example,
    /// the level 1 to 5 on AMD64 corresponds to Page Tables, Page Directory Tables,
    /// Page Directory Pointer Tables, Page-Map Level-4 Table, and Page-Map Level-5
    /// Table, respectively.
    #[verifier::when_used_as_spec(NR_LEVELS_SPEC)]
    fn NR_LEVELS() -> PagingLevel
        returns
            Self::NR_LEVELS_SPEC(),
    ;

    spec fn HIGHEST_TRANSLATION_LEVEL_SPEC() -> PagingLevel;

    /// The highest level that a PTE can be directly used to translate a VA.
    /// This affects the the largest page size supported by the page table.
    #[verifier::when_used_as_spec(HIGHEST_TRANSLATION_LEVEL_SPEC)]
    fn HIGHEST_TRANSLATION_LEVEL() -> PagingLevel
        returns
            Self::HIGHEST_TRANSLATION_LEVEL_SPEC(),
    ;

    spec fn PTE_SIZE_SPEC() -> usize;

    /// The size of a PTE.
    #[verifier::when_used_as_spec(PTE_SIZE_SPEC)]
    fn PTE_SIZE() -> usize
        returns
            Self::PTE_SIZE_SPEC(),
    ;

    spec fn ADDRESS_WIDTH_SPEC() -> usize;

    /// The address width may be BASE_PAGE_SIZE.ilog2() + NR_LEVELS * IN_FRAME_INDEX_BITS.
    /// If it is shorter than that, the higher bits in the highest level are ignored.
    #[verifier::when_used_as_spec(ADDRESS_WIDTH_SPEC)]
    fn ADDRESS_WIDTH() -> usize
        returns
            Self::ADDRESS_WIDTH_SPEC(),
    ;

    spec fn VA_SIGN_EXT_SPEC() -> bool;

    /// Whether virtual addresses are sign-extended.
    ///
    /// The sign bit of a [`Vaddr`] is the bit at index [`PagingConstsTrait::ADDRESS_WIDTH`] - 1.
    /// If this constant is `true`, bits in [`Vaddr`] that are higher than the sign bit must be
    /// equal to the sign bit. If an address violates this rule, both the hardware and OSTD
    /// should reject it.
    ///
    /// Otherwise, if this constant is `false`, higher bits must be zero.
    ///
    /// Regardless of sign extension, [`Vaddr`] is always not signed upon calculation.
    /// That means, `0xffff_ffff_ffff_0000 < 0xffff_ffff_ffff_0001` is `true`.
    #[verifier::when_used_as_spec(VA_SIGN_EXT_SPEC)]
    fn VA_SIGN_EXT() -> bool
        returns
            Self::VA_SIGN_EXT_SPEC(),
    ;

    proof fn lemma_consts_properties()
        ensures
            0 < Self::PTE_SIZE() <= Self::BASE_PAGE_SIZE(),
            is_power_2(Self::BASE_PAGE_SIZE() as int),
            is_power_2(Self::PTE_SIZE() as int),
            1 <= Self::NR_LEVELS() <= 10,
            0 <= Self::BASE_PAGE_SIZE().ilog2() - Self::PTE_SIZE().ilog2() <= 16,
            Self::BASE_PAGE_SIZE().ilog2() + (Self::BASE_PAGE_SIZE().ilog2()
                - Self::PTE_SIZE().ilog2()) * Self::NR_LEVELS() == Self::ADDRESS_WIDTH()
                < usize::BITS,
    ;

    proof fn lemma_consts_properties_derived()
        ensures
            Self::BASE_PAGE_SIZE() == pow2(Self::BASE_PAGE_SIZE().ilog2() as nat),
            Self::PTE_SIZE() == pow2(Self::PTE_SIZE().ilog2() as nat),
            0 < Self::BASE_PAGE_SIZE() / Self::PTE_SIZE() == pow2(
                (Self::BASE_PAGE_SIZE().ilog2() - Self::PTE_SIZE().ilog2()) as nat,
            ) <= usize::MAX,
            Self::BASE_PAGE_SIZE() * pow2(
                ((Self::BASE_PAGE_SIZE().ilog2() - Self::PTE_SIZE().ilog2())
                    * Self::NR_LEVELS()) as nat,
            ) == pow2(Self::ADDRESS_WIDTH() as nat) <= usize::MAX,
    {
        Self::lemma_consts_properties();
        lemma_usize_is_power_2_is_ilog2_pow2(Self::BASE_PAGE_SIZE());
        lemma_usize_is_power_2_is_ilog2_pow2(Self::PTE_SIZE());
        lemma_usize_ilog2_ordered(Self::PTE_SIZE(), Self::BASE_PAGE_SIZE());
        lemma_pow2_subtracts(
            Self::PTE_SIZE().ilog2() as nat,
            Self::BASE_PAGE_SIZE().ilog2() as nat,
        );
        lemma_div_non_zero(Self::BASE_PAGE_SIZE() as int, Self::PTE_SIZE() as int);
        assert(pow2(usize::BITS as nat) as int == usize::MAX as int + 1) by {
            lemma2_to64();
        }
        lemma_pow2_strictly_increases(Self::ADDRESS_WIDTH() as nat, usize::BITS as nat);
        lemma_pow2_adds(
            Self::BASE_PAGE_SIZE().ilog2() as nat,
            ((Self::BASE_PAGE_SIZE().ilog2() - Self::PTE_SIZE().ilog2())
                * Self::NR_LEVELS()) as nat,
        );
    }
}

// TODO: This is for x86, create the arch directory and move this to x86/mod.rs
pub(crate) const NR_ENTRIES_PER_PAGE: usize = 512;

// TODO: This is for x86, create the arch directory and move this to x86/mod.rs
// #[derive(Clone, Debug, Default)]
pub struct PagingConsts {}

// TODO: This is for x86, create the arch directory and move this to x86/mod.rs
impl PagingConstsTrait for PagingConsts {
    open spec fn BASE_PAGE_SIZE_SPEC() -> usize {
        4096
    }

    fn BASE_PAGE_SIZE() -> (res: usize) {
        4096
    }

    open spec fn NR_LEVELS_SPEC() -> PagingLevel {
        4
    }

    fn NR_LEVELS() -> (res: PagingLevel) {
        4
    }

    open spec fn HIGHEST_TRANSLATION_LEVEL_SPEC() -> PagingLevel {
        2
    }

    fn HIGHEST_TRANSLATION_LEVEL() -> PagingLevel {
        2
    }

    open spec fn PTE_SIZE_SPEC() -> usize {
        8
    }

    fn PTE_SIZE() -> usize {
        proof {
            assume(core::mem::size_of::<exec::MockPageTableEntry>() == 8);
        }
        core::mem::size_of::<exec::MockPageTableEntry>()
    }

    open spec fn ADDRESS_WIDTH_SPEC() -> usize {
        48
    }

    fn ADDRESS_WIDTH() -> usize {
        48
    }

    open spec fn VA_SIGN_EXT_SPEC() -> bool {
        true
    }

    fn VA_SIGN_EXT() -> bool {
        true
    }

    proof fn lemma_consts_properties() {
        lemma_pow2_is_power2_to64();
        lemma2_to64();
        lemma_log2_to64();
    }
}

// Copied from aster_common
// TODO: Check if these are correct
// Here are some const values that are determined by the paging constants.
pub proof fn bits_of_base_page_size()
    ensures
        PagingConsts::BASE_PAGE_SIZE_SPEC().ilog2() == 12,
{
    lemma_usize_ilog2_to32();
}

pub proof fn value_of_nr_subpage_per_huge()
    ensures
        nr_subpage_per_huge::<PagingConsts>() == 512,
{
    PagingConsts::lemma_consts_properties();
    PagingConsts::lemma_consts_properties_derived();
    assert(nr_subpage_per_huge::<PagingConsts>() == PagingConsts::BASE_PAGE_SIZE()
        / PagingConsts::PTE_SIZE());
}

pub proof fn bits_of_nr_pte_index()
    ensures
        nr_pte_index_bits::<PagingConsts>() == 9,
{
    value_of_nr_subpage_per_huge();
    lemma_usize_ilog2_to32();
}

/// The number of virtual address bits used to index a PTE in a page.
#[inline(always)]
#[verifier::allow_in_spec]
pub fn nr_pte_index_bits<C: PagingConstsTrait>() -> (res: usize)
    returns
        (C::BASE_PAGE_SIZE().ilog2() - C::PTE_SIZE().ilog2()) as usize,
{
    proof {
        C::lemma_consts_properties();
        C::lemma_consts_properties_derived();
        lemma_usize_pow2_ilog2((C::BASE_PAGE_SIZE().ilog2() - C::PTE_SIZE().ilog2()) as u32);
    }
    nr_subpage_per_huge::<C>().ilog2() as usize
}

#[inline(always)]
#[verifier::allow_in_spec]
pub fn pte_index_mask<C: PagingConstsTrait>() -> (res: usize)
    returns
        low_bits_mask((C::BASE_PAGE_SIZE().ilog2() - C::PTE_SIZE().ilog2()) as nat) as usize,
{
    proof {
        C::lemma_consts_properties();
        C::lemma_consts_properties_derived();
    }
    nr_subpage_per_huge::<C>() - 1
}

pub open spec fn pte_index_spec<C: PagingConstsTrait>(va: Vaddr, level: PagingLevel) -> usize
    recommends
        0 < level <= C::NR_LEVELS_SPEC(),
{
    let base_bits = C::BASE_PAGE_SIZE_SPEC().ilog2();
    let index_bits = nr_pte_index_bits::<C>();
    let shift = base_bits + (level - 1) as u32 * index_bits as u32;
    (va >> shift) & pte_index_mask::<C>()
}

#[verifier::when_used_as_spec(pte_index_spec)]
/// The index of a VA's PTE in a page table node at the given level.
// const fn pte_index<C: PagingConstsTrait>(va: Vaddr, level: PagingLevel) -> usize
pub fn pte_index<C: PagingConstsTrait>(va: Vaddr, level: PagingLevel) -> (res:
    usize)  // TODO: type, const
    requires
        0 < level <= C::NR_LEVELS_SPEC(),
    ensures
        res == pte_index_spec::<C>(va, level),
        res < nr_subpage_per_huge::<C>(),
{
    let base_bits = C::BASE_PAGE_SIZE().ilog2();
    let index_bits = nr_pte_index_bits::<C>();
    assert(index_bits == (C::BASE_PAGE_SIZE().ilog2() - C::PTE_SIZE().ilog2()) as usize);
    proof {
        C::lemma_consts_properties();
        C::lemma_consts_properties_derived();
    }
    assert(1 <= level as u32 <= 10);
    assert(index_bits as u32 <= 16);
    assert(base_bits < usize::BITS);
    // 10000 is arbitrary, but it is enough to show the absence of overflow.
    assert((level - 1) as u32 * index_bits as u32 <= 10000) by (nonlinear_arith)
        requires
            1 <= level as u32 <= 10,
            index_bits as u32 <= 16,
            base_bits < usize::BITS,
    ;
    let shift = base_bits + (level - 1) as u32 * index_bits as u32;
    // Proof idea: transitivity of < and <=, along with nonlinear_arith
    assert(shift < usize::BITS) by {
        assert(level - 1 < C::NR_LEVELS());
        assert(base_bits + index_bits * C::NR_LEVELS() < usize::BITS);
        assert(base_bits + index_bits * (level - 1) <= base_bits + index_bits * C::NR_LEVELS())
            by (nonlinear_arith)
            requires
                level - 1 < C::NR_LEVELS(),
        ;
    }
    let res = (va >> shift) as u64 & pte_index_mask::<C>() as u64;
    assert(res <= pte_index_mask::<C>()) by {
        lemma_u64_and_less_than((va >> shift) as u64, pte_index_mask::<C>() as u64);
    };
    res as usize
}

// PTE index increment recursively
pub open spec fn pte_index_add_with_carry<C: PagingConstsTrait>(
    va: Vaddr,
    add_level: PagingLevel,
    cur_level: PagingLevel,
) -> usize
    recommends
        1 <= add_level <= cur_level <= C::NR_LEVELS_SPEC(),
    decreases cur_level,
{
    if cur_level <= add_level {
        if pte_index_spec::<C>(va, cur_level) == pte_index_mask::<C>() {
            0  // Overflow

        } else {
            (pte_index_spec::<C>(va, cur_level) + 1) as usize
        }
    } else {
        // if there's carry from the lower level
        let lower_level_has_carry = pte_index_add_with_carry::<C>(
            va,
            add_level,
            (cur_level - 1) as PagingLevel,
        ) == 0 && pte_index_spec::<C>(va, (cur_level - 1) as PagingLevel) == pte_index_mask::<C>();

        if lower_level_has_carry {
            // Carry propagates up: increment this level (or overflow to 0)
            if pte_index_spec::<C>(va, cur_level) == pte_index_mask::<C>() {
                0  // This level also overflows

            } else {
                (pte_index_spec::<C>(va, cur_level) + 1) as usize
            }
        } else {
            // No carry: this level remains unchanged
            pte_index_spec::<C>(va, cur_level)
        }
    }
}

// Adding a page size to an aligned address increments the PTE index
proof fn lemma_add_page_size_change_pte_index<C: PagingConstsTrait>(
    aligned_va: Vaddr,
    page_sz: usize,
    level: PagingLevel,
)
    requires
        1 <= level <= C::NR_LEVELS(),
        aligned_va % page_sz == 0,
        page_sz == page_size::<C>(level),
        aligned_va + page_sz < usize::MAX,
    ensures
// The result at any level >= the target level follows the carry propagation

        forall|l: PagingLevel|
            level <= l <= C::NR_LEVELS() ==> #[trigger] pte_index::<C>(
                (aligned_va + page_sz) as usize,
                l,
            ) == #[trigger] pte_index_add_with_carry::<C>(aligned_va, level, l),
{
    admit();
}

proof fn lemma_sub_mod_div_same(a: usize, b: usize)
    requires
        a >= 0,
        b > 0,
    ensures
        0 <= a / b == ((a - (a % b)) as usize) / b <= a,
{
    // int versions of a and b
    let ai = a as int;
    let bi = b as int;
    // First, prove the two inequalities
    assert(a / b == ai / bi);
    lemma_div_pos_is_pos(ai, bi);
    lemma_div_nonincreasing(ai, bi);
    assert(0 <= a / b <= a);
    // Then, tackle the equality in the middle
    // First, prove a - (a % b) does fit in usize
    assert(ai - (ai % bi) >= 0) by {
        lemma_mod_decreases(ai as nat, bi as nat);
    }
    assert(0 <= ai - (ai % bi) <= ai <= usize::MAX);
    assert(((a - (a % b)) as usize) == ai - (ai % bi));
    // Now we can do all the reasoning with the int versions, without worrying about overflow
    let di = ai / bi;
    let mi = ai % bi;
    assert(ai == bi * di + mi) by {
        lemma_fundamental_div_mod(ai, bi);
    }
    assert(ai - (ai % bi) == bi * di);
    assert(bi * di == di * bi) by (nonlinear_arith);
    lemma_div_multiples_vanish(di, bi);
    assert(ai / bi == di == (ai - (ai % bi)) / bi);
}

proof fn lemma_usize_shr_is_div(x: usize, shift: int)
    requires
        0 <= shift < usize::BITS,
    ensures
        x >> shift == x / (pow2(shift as nat) as usize),
{
    // Proof idea is to use u64 as a bridge
    assert(usize::MAX <= u64::MAX);
    assert(usize::BITS <= u64::BITS < u64::MAX);
    // Since usize <= u64, we can cast x and shift to u64 without overflow
    assert(0 <= x <= u64::MAX);
    assert(0 <= shift <= u64::MAX);
    let x_ = x as u64;
    let shift_ = shift as u64;
    lemma_u64_shr_is_div(x_, shift_);
    // Then, we show that computation done in nat and usize agree by showing there's no overflow
    assert(x >> shift == (x_ >> shift_) as usize) by {
        // The next statement is true because x_ = x as u64 -> they are equal when cast to nat,
        // and the result of lemma_u64_shr_is_div.
        assert(x_ >> shift_ == x as nat / pow2(shift_ as nat));
        lemma_pow2_pos(shift_ as nat);
        lemma_div_nonincreasing(x as int, pow2(shift_ as nat) as int);
        assert(x_ >> shift_ <= x <= usize::MAX);
    };
    assert(x as nat / pow2(shift_ as nat) == x / (pow2(shift as nat) as usize)) by {
        // In this case, need to prove pow2(shift_ as nat) fits in usize.
        lemma_pow2_pos(shift_ as nat);
        assert(pow2((usize::BITS - 1) as nat) < usize::MAX) by {
            assert(usize::BITS == 32 || usize::BITS == 64);
            if usize::BITS == 32 {
                assert(pow2(31) == 0x8000_0000 < usize::MAX) by {
                    lemma2_to64();
                }
            } else if usize::BITS == 64 {
                assert(pow2(63) == 0x8000000000000000 < usize::MAX) by {
                    lemma2_to64_rest();
                }
            }
        }
        assert(shift_ as nat <= (usize::BITS - 1) as nat);
        assert(pow2(shift_ as nat) <= pow2((usize::BITS - 1) as nat)) by {
            if (shift_ as nat == (usize::BITS - 1) as nat) {
            } else {
                lemma_pow2_strictly_increases(shift_ as nat, (usize::BITS - 1) as nat);
            }
        }
    }
}

proof fn lemma_aligned_pte_index_unchanged<C: PagingConstsTrait>(x: Vaddr, level: PagingLevel)
    requires
        1 <= level <= C::NR_LEVELS_SPEC(),
    ensures
        forall|l: PagingLevel|
            level <= l <= C::NR_LEVELS_SPEC() ==> #[trigger] pte_index::<C>(x, l) == pte_index::<C>(
                align_down(x, page_size::<C>(l)),
                l,
            ),
{
    assert forall|l: PagingLevel| level <= l <= C::NR_LEVELS_SPEC() implies #[trigger] pte_index::<
        C,
    >(x, l) == pte_index::<C>(align_down(x, page_size::<C>(l)), l) by {
        // The page size
        let pg_size = page_size_spec::<C>(l);
        lemma_page_size_spec_properties::<C>(l);
        // The values used in pte_index_spec
        let base_bits = C::BASE_PAGE_SIZE_SPEC().ilog2();
        let index_bits = nr_pte_index_bits::<C>();
        C::lemma_consts_properties();
        assert((base_bits + (l - 1) as u32 * index_bits as u32) < usize::BITS) by {
            assert(base_bits + index_bits * C::NR_LEVELS() < usize::BITS);
            assert(index_bits >= 0);
            assert(base_bits + (l - 1) * index_bits <= base_bits + index_bits * C::NR_LEVELS())
                by (nonlinear_arith)
                requires
                    1 <= l <= C::NR_LEVELS(),
                    index_bits >= 0,
            ;
            assert(base_bits + (l - 1) * index_bits < usize::BITS);
        }
        assert(base_bits + (l - 1) as u32 * index_bits as u32 == base_bits + index_bits as u32 * (l
            - 1) as u32) by (nonlinear_arith);
        // The shift local var in both pte_index calls
        let shift = base_bits + (l - 1) as u32 * index_bits as u32;
        assert(shift < usize::BITS);
        assert(shift as nat == (C::BASE_PAGE_SIZE().ilog2() + (C::BASE_PAGE_SIZE().ilog2()
            - C::PTE_SIZE().ilog2()) * (l - 1)));
        assert(pg_size == pow2(shift as nat) as usize);
        // Precondition for align_down
        assert(is_power_2(pg_size as int));
        assert(pg_size < usize::MAX);
        let aligned_x = align_down(x, pg_size);
        // Then, the property of align_down shows that aligned_x == x - (x % pg_size).
        assert(aligned_x == (x - (x % pg_size)) as usize);
        // This lemma gives x / pg_size == aligned_x / pg_size
        lemma_sub_mod_div_same(x, pg_size);
        // Show that division by pg_size is shr by shift
        lemma_usize_shr_is_div(x, shift);
        lemma_usize_shr_is_div(aligned_x, shift);
    }
}

/// A handle to a page table.
/// A page table can track the lifetime of the mapped physical pages.
// TODO: Debug for PageTable
// #[derive(Debug)]
pub struct PageTable<C: PageTableConfig> {
    root: PageTableNode<C>,
    _phantom: PhantomData<C>,
}

} // verus!
