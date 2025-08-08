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
    calc,
    layout::is_power_2,
    seq::{Seq},
};
use vstd_extra::extra_num::{
    lemma_log2_to64, lemma_pow2_is_power2_to64, lemma_usize_ilog2_ordered, lemma_usize_ilog2_to32,
    lemma_usize_is_power_2_is_ilog2_pow2, lemma_usize_pow2_ilog2, lemma_usize_shl_is_mul,
};

use super::{
    lemma_page_size_adjacent_levels, lemma_page_size_geometric, meta::AnyFrameMeta,
    nr_subpage_per_huge, page_prop::PageProperty, page_size, vm_space::Token, page_size_spec,
    lemma_page_size_spec_properties, Paddr, PagingLevel, Vaddr, NR_ENTRIES,
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

pub proof fn lemma_pte_index_alternative_spec<C: PagingConstsTrait>(va: Vaddr, level: PagingLevel)
    requires
        0 < level <= C::NR_LEVELS_SPEC(),
    ensures
        pte_index_spec::<C>(va, level) as nat == (va as nat / page_size_spec::<C>(level) as nat)
            % nr_subpage_per_huge::<C>() as nat,
        level < C::NR_LEVELS_SPEC() ==> pte_index_spec::<C>(va, level) as nat == va as nat
            % page_size_spec::<C>((level + 1) as PagingLevel) as nat / page_size_spec::<C>(
            level,
        ) as nat,
{
    assert(pte_index_spec::<C>(va, level) as nat == (va as nat / page_size_spec::<C>(level) as nat)
        % nr_subpage_per_huge::<C>() as nat) by {
        C::lemma_consts_properties();
        C::lemma_consts_properties_derived();
        // Constants computed in the body of the spec fn
        let base_bits = C::BASE_PAGE_SIZE_SPEC().ilog2();
        let index_bits = nr_pte_index_bits::<C>();
        let shift = base_bits + (level - 1) as u32 * index_bits as u32;
        let shift_nat = (base_bits + (level - 1) * index_bits) as nat;
        assert(shift as nat == shift_nat);
        lemma_page_size_spec_properties::<C>(level);
        // Then use transitivity to establish the first equality.
        calc! {
            (==)
            pte_index::<C>(va, level) as nat; {
                // This step simply expands the definition of pte_index.
            }
            ((va >> shift) & pte_index_mask::<C>()) as nat; {
                assert(pte_index_mask::<C>() == low_bits_mask(
                    (C::BASE_PAGE_SIZE().ilog2() - C::PTE_SIZE().ilog2()) as nat,
                ) as usize);
                lemma_u64_low_bits_mask_is_mod(
                    (va >> shift) as u64,
                    (C::BASE_PAGE_SIZE().ilog2() - C::PTE_SIZE().ilog2()) as nat,
                );
            }
            ((va >> shift) % pow2(
                (C::BASE_PAGE_SIZE().ilog2() - C::PTE_SIZE().ilog2()) as nat,
            ) as usize) as nat; {
                // This step follows from the definition of nr_subpage_per_huge.
            }
            ((va >> shift) % nr_subpage_per_huge::<C>()) as nat; {}
            (va >> shift) as nat % nr_subpage_per_huge::<C>() as nat; {
                assert(shift_nat < usize::BITS) by {
                    assert(shift_nat <= base_bits + C::NR_LEVELS_SPEC() * index_bits)
                        by (nonlinear_arith)
                        requires
                            base_bits == C::BASE_PAGE_SIZE_SPEC().ilog2(),
                            index_bits as int == C::BASE_PAGE_SIZE().ilog2()
                                - C::PTE_SIZE().ilog2(),
                            shift_nat == (base_bits + (level - 1) * index_bits) as nat,
                            index_bits >= 0,
                            level <= C::NR_LEVELS_SPEC(),
                    ;
                    assert(base_bits + C::NR_LEVELS_SPEC() * index_bits < usize::BITS);
                }
                lemma_usize_shr_is_div(va, shift as int);
            }
            (va as nat / pow2(shift_nat)) % nr_subpage_per_huge::<C>() as nat; {}
            (va as nat / page_size_spec::<C>(level) as nat) % nr_subpage_per_huge::<C>() as nat;
        }
    }
    // Then, we prove the second equality using properties of div and mod.
    if level < C::NR_LEVELS() {
        let a = page_size_spec::<C>(level) as int;
        let b = nr_subpage_per_huge::<C>() as int;
        let x = va as int;
        assert(a > 0 && b > 0 && x >= 0) by {
            lemma_page_size_spec_properties::<C>(level);
            C::lemma_consts_properties();
            C::lemma_consts_properties_derived();
        }
        assert(page_size_spec::<C>((level + 1) as PagingLevel) as int == a * b) by {
            assert(page_size_spec::<C>((level + 1) as PagingLevel) as int == b * a) by {
                lemma_page_size_adjacent_levels::<C>((level + 1) as PagingLevel);
            }
        }
        assert(x / a % b == x % (a * b) / a) by {
            // x % (a * b) == a * (x / a % b) + (x % a)
            lemma_breakdown(x, a, b);
            assert(0 <= x % a < a) by (nonlinear_arith)
                requires
                    a > 0,
            ;
            assert((x / a % b) == (x % (a * b)) / a) by (nonlinear_arith)
                requires
                    0 <= x % a < a,
                    x % (a * b) == a * (x / a % b) + (x % a),
            ;
        }
        // We can use transitivity again
        calc! {
            (==)
            (va as nat / page_size_spec::<C>(level) as nat) % nr_subpage_per_huge::<C>() as nat; {}
            ((x / a) % b) as nat; {}
            (x % (a * b) / a) as nat; {
                assert(x % (a * b) >= 0) by (nonlinear_arith)
                    requires
                        a > 0,
                        b > 0,
                ;
                assert(a > 0);
            }
            (x % (a * b)) as nat / a as nat; {}
            x as nat % (a * b) as nat / a as nat; {}
            va as nat % page_size_spec::<C>((level + 1) as PagingLevel) as nat / page_size_spec::<
                C,
            >(level) as nat;
        }
    }
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

proof fn lemma_addr_aligned_propagate<C: PagingConstsTrait>(va: Vaddr, level: PagingLevel)
    requires
        2 <= level <= C::NR_LEVELS_SPEC(),
        va % page_size::<C>((level - 1) as PagingLevel) == 0,
        pte_index_spec::<C>(va, (level - 1) as PagingLevel) == 0,
    ensures
        va % page_size::<C>(level) == 0,
{
    let old_level = (level - 1) as PagingLevel;
    assert(1 <= old_level < C::NR_LEVELS_SPEC());
    let old_pg_size = page_size_spec::<C>(old_level) as nat;
    let new_pg_size = page_size_spec::<C>(level) as nat;
    let diff = nr_subpage_per_huge::<C>() as nat;
    assert(old_pg_size > 0) by {
        lemma_page_size_spec_properties::<C>(old_level);
    }
    assert(diff > 0) by {
        C::lemma_consts_properties();
        C::lemma_consts_properties_derived();
    }
    assert(new_pg_size == old_pg_size * diff) by {
        lemma_page_size_adjacent_levels::<C>(level);
    }
    let van = va as nat;
    assert(van / old_pg_size % diff == 0) by {
        lemma_pte_index_alternative_spec::<C>(va, old_level);
    }
    assert(van % old_pg_size == 0) by {
        // This lemma is needed because it convinces the verifier that old_pg_size > 0
        lemma_page_size_spec_properties::<C>(old_level);
        assert(van % old_pg_size == (va % page_size::<C>(old_level)) as nat);
    }
    lemma_breakdown(van as int, old_pg_size as int, diff as int);
    // The verifier seems to be able to figure out that calculation in nat and int are the same,
    // and then it is smart enough to automatically substitute zeros into the calculation.
}

// A number x can be represented the sum of its three parts
proof fn lemma_nat_as_parts(x: nat, p: nat, q: nat)
    requires
        0 <= q <= p,
    ensures
        x == pow2(p) * (x / pow2(p)) + pow2(q) * (x % pow2(p) / pow2(q)) + (x % pow2(q)),
        0 <= x % pow2(q) < pow2(q),
        0 <= x % pow2(p) / pow2(q) < pow2((p - q) as nat),
{
    assert((x % pow2(p) % pow2(q)) == x % pow2(q)) by {
        let m = pow2(q);
        let d = pow2((p - q) as nat);
        assert(m * d == pow2(p)) by {
            assert(p - q >= 0);
            assert(pow2(p) == pow2(q + (p - q) as nat));
            lemma_pow2_adds(q as nat, (p - q) as nat);
        }
        lemma_pow2_pos(q);
        lemma_pow2_pos((p - q) as nat);
        lemma_mod_mod(x as int, m as int, d as int);
    }
    calc! {
        (==)
        x; {
            lemma_pow2_pos(p);
            lemma_fundamental_div_mod(x as int, pow2(p) as int);
        }
        pow2(p) * (x / pow2(p)) + (x % pow2(p)); {
            lemma_pow2_pos(q);
            lemma_fundamental_div_mod((x % pow2(p)) as int, pow2(q) as int);
        }
        pow2(p) * (x / pow2(p)) + pow2(q) * (x % pow2(p) / pow2(q)) + (x % pow2(q));
    }
    assert(0 <= x % pow2(q) < pow2(q)) by {
        lemma_pow2_pos(q);
        lemma_mod_bound(x as int, pow2(q) as int);
    }
    assert(0 <= x % pow2(p) / pow2(q) < pow2((p - q) as nat)) by {
        lemma_pow2_pos(p);
        lemma_pow2_pos(q);
        // This gives 0 <= x % pow2(p) < pow2(p)
        lemma_mod_bound(x as int, pow2(p) as int);
        // This gives pow2(p) / pow2(q) == pow2(p - q)
        lemma_pow2_adds(q, (p - q) as nat);
        assert((pow2(p) - 1) as nat / pow2(q) == pow2((p - q) as nat) - 1) by (nonlinear_arith)
            requires
                pow2(p) > 0,
                pow2(q) > 0,
                pow2(p) == pow2(q) * pow2((p - q) as nat),
        ;
        assert(0 <= x % pow2(p) / pow2(q) < pow2((p - q) as nat)) by (nonlinear_arith)
            requires
                0 <= x % pow2(p) <= pow2(p) - 1,
                (pow2(p) - 1) as nat / pow2(q) == pow2((p - q) as nat) - 1,
                pow2(q) > 0,
        ;
    }
}

// When doing addition by a number <= 2^q (y < x <= y + 2^q),
// if the x[0..q] == 0 and x[q..p] != 0, then the carry doesn't propagate to
// the bits higher than p.
proof fn lemma_carry_ends_at_nonzero_result_bits(
    x: nat,
    y: nat,
    p: nat,
    q: nat,
)
// This proof is going to rely heavily on nonlinear arithmetics

    by (nonlinear_arith)
    requires
        0 <= q <= p,
        y < x <= y + pow2(q),
        // The condition on the result
        x % pow2(q) == 0,
        x % pow2(p) / pow2(q) != 0,
    ensures
        x / pow2(p) == y / pow2(p),
{
    // Decompose the arguments into parts, and the range of their parts
    let a = x / pow2(p);
    let b = x % pow2(p) / pow2(q);
    assert(x == pow2(p) * a + pow2(q) * b && 1 <= b <= pow2((p - q) as nat) - 1) by {
        lemma_nat_as_parts(x, p, q);
        assert(b != 0);
    }
    let c = y / pow2(p);
    let d = y % pow2(p) / pow2(q);
    let e = y % pow2(q);
    assert(y == pow2(p) * c + pow2(q) * d + e && 0 <= e <= pow2(q) - 1 && 0 <= d <= pow2(
        (p - q) as nat,
    ) - 1) by {
        lemma_nat_as_parts(y, p, q);
    }
    let diff = x - y;
    // Equation (*)
    assert((a - c) * pow2(p) == e + diff + (d - b) * pow2(q));
    // Range of the difference
    assert(0 < diff <= pow2(q));
    // Properties about 2^p and 2^q the solver needs
    lemma_pow2_pos(q);
    lemma_pow2_adds(q, (p - q) as nat);
    // The solver seems to be able to prove these automatically
    assert(-pow2(p) < e + diff + (d - b) * pow2(q));
    assert(e + diff + (d - b) * pow2(q) < pow2(p));
    // Substitute the equation (*)
    assert(-pow2(p) < (a - c) * pow2(p) < pow2(p));
    assert(a - c == 0);
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
                align_down(x, page_size::<C>(level)),
                l,
            ),
{
    assert forall|l: PagingLevel| level <= l <= C::NR_LEVELS_SPEC() implies #[trigger] pte_index::<
        C,
    >(x, l) == pte_index::<C>(align_down(x, page_size::<C>(level)), l) by {
        // nat version of x
        let xn = x as nat;
        // The page size at level
        let pg_size_level = page_size::<C>(level) as nat;
        assert(pg_size_level > 0 && is_power_2(pg_size_level as int)) by {
            lemma_page_size_spec_properties::<C>(level);
        }
        // Aligned address and its nat version
        let aligned_x = align_down(x, page_size::<C>(level));
        let axn = aligned_x as nat;
        assert(x as int >= (xn % pg_size_level) as int) by (nonlinear_arith)
            requires
                x as int == xn as int,
                xn >= 0,
                pg_size_level > 0,
        ;
        assert(aligned_x == (x - (x % page_size::<C>(level))) as usize);
        // Then we promote the discussion to nat
        assert(axn == xn - (xn % pg_size_level));
        // The page size at l
        let pg_size_l = page_size::<C>(l) as nat;
        assert(pg_size_l > 0) by {
            lemma_page_size_spec_properties::<C>(l);
        }
        // The ratio of pg_size_l / pg_size_level
        let ratio = pow(nr_subpage_per_huge::<C>() as int, (l - level) as nat) as nat;
        assert(pg_size_l == pg_size_level * ratio) by {
            lemma_page_size_geometric::<C>(level, l);
        }
        assert(ratio > 0) by (nonlinear_arith)
            requires
                pg_size_l == pg_size_level * ratio,
                pg_size_l > 0,
                pg_size_level > 0,
        ;
        // Finally, prove that the va / page_size is the same for x and aligned_x
        calc! {
            (==)
            axn / pg_size_l; {}
            (xn - (xn % pg_size_level)) as nat / (pg_size_level * ratio); {
                lemma_div_denominator(
                    (xn - (xn % pg_size_level)) as int,
                    pg_size_level as int,
                    ratio as int,
                );
            }
            (xn - (xn % pg_size_level)) as nat / pg_size_level / ratio; {
                assert((xn - (xn % pg_size_level)) as nat / pg_size_level == xn / pg_size_level)
                    by (nonlinear_arith)
                    requires
                        xn >= 0,
                        pg_size_level > 0,
                ;
            }
            xn / pg_size_level / ratio; {
                lemma_div_denominator(xn as int, pg_size_level as int, ratio as int);
            }
            xn / (pg_size_level * ratio); {}
            xn / pg_size_l;
        }
        calc! {
            (==)
            pte_index::<C>(x, l) as nat; {
                lemma_pte_index_alternative_spec::<C>(x, l);
            }
            xn / pg_size_l % nr_subpage_per_huge::<C>() as nat; {}
            axn / pg_size_l % nr_subpage_per_huge::<C>() as nat; {
                lemma_pte_index_alternative_spec::<C>(aligned_x, l);
            }
            pte_index::<C>(aligned_x, l) as nat;
        }
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
