#![allow(hidden_glob_reexports)]

pub mod cursor;
pub mod mapping_set_lemmas;
pub mod node;
mod owners;
pub mod vaddr_range_proofs;
mod view;

use vstd::{
    arithmetic::{
        div_mod::{lemma_div_denominator, lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse},
        mul::{lemma_mul_inequality, lemma_mul_is_distributive_sub},
        power2::{lemma_pow2_adds, lemma_pow2_pos, lemma2_to64, lemma2_to64_rest, pow2},
    },
    bits::{lemma_usize_low_bits_mask_is_mod, lemma_usize_pow2_no_overflow, lemma_usize_shr_is_div},
    prelude::*,
    std_specs::range::RangeInclusiveView,
};
use vstd_extra::{
    arithmetic::*, external::ilog2::lemma_usize_is_pow2_is_ilog2_pow2,
    ownership::*, prelude::*,
};

use crate::specs::arch::*;

use crate::mm::{
    PagingConsts, PagingConstsTrait, PagingLevel, Vaddr, kspace::KernelPtConfig,
    nr_subpage_per_huge, page_size, page_table::PageTableConfig, vm_space::UserPtConfig,
};
use align_ext::AlignExt;
use core::ops::Range;
pub use cursor::*;
pub use node::*;
pub use owners::*;
pub use view::*;

verus! {

#[verifier::inline]
pub open spec fn nr_pte_index_bits_spec<C: PagingConstsTrait>() -> usize {
    nr_subpage_per_huge::<C>().ilog2() as usize
}

#[verifier::inline]
pub open spec fn pte_index_bit_offset_spec<C: PagingConstsTrait>(level: PagingLevel) -> usize {
    (C::BASE_PAGE_SIZE().ilog2() + nr_pte_index_bits_spec::<C>() * (level - 1)) as usize
}

/// Page size at `level`, derived entirely from the selected paging constants.
#[verifier::inline]
pub open spec fn page_size_for_level_spec<C: PagingConstsTrait>(level: PagingLevel) -> usize {
    (C::BASE_PAGE_SIZE() * pow2(
        (nr_pte_index_bits_spec::<C>() * (level - 1)) as nat,
    )) as usize
}

/// A configured page size is the power of two at that level's index-bit offset.
pub proof fn lemma_page_size_for_level_is_pow2<C: PagingConstsTrait>(level: PagingLevel)
    requires
        1 <= level <= C::NR_LEVELS() + 1,
    ensures
        pte_index_bit_offset_spec::<C>(level) < usize::BITS,
        pte_index_bit_offset_spec::<C>(level)
            == C::BASE_PAGE_SIZE().ilog2() + nr_pte_index_bits_spec::<C>() * (level - 1),
        0 < page_size_for_level_spec::<C>(level)
            == pow2(pte_index_bit_offset_spec::<C>(level) as nat),
{
    C::lemma_paging_consts_properties();
    let bits = nr_pte_index_bits_spec::<C>();
    assert(usize::BITS <= usize::MAX) by (compute_only);
    lemma_usize_is_pow2_is_ilog2_pow2(C::BASE_PAGE_SIZE());
    lemma_usize_is_pow2_is_ilog2_pow2(nr_subpage_per_huge::<C>());
    assert(bits == (C::BASE_PAGE_SIZE() / C::PTE_SIZE()).ilog2());
    lemma_mul_inequality(level - 1, C::NR_LEVELS() as int, bits as int);
    assert(C::BASE_PAGE_SIZE().ilog2() + bits * (level - 1) <= C::ADDRESS_WIDTH());
    assert(pte_index_bit_offset_spec::<C>(level)
        == C::BASE_PAGE_SIZE().ilog2() + bits * (level - 1));
    lemma_pow2_adds(C::BASE_PAGE_SIZE().ilog2() as nat, (bits * (level - 1)) as nat);
    lemma_usize_pow2_no_overflow(pte_index_bit_offset_spec::<C>(level) as nat);
}

/// A parent slot contains exactly one fanout of slots at the preceding level.
pub proof fn lemma_page_size_for_level_next<C: PagingConstsTrait>(level: PagingLevel)
    requires
        1 <= level <= C::NR_LEVELS(),
    ensures
        page_size_for_level_spec::<C>((level + 1) as PagingLevel)
            == page_size_for_level_spec::<C>(level) * nr_subpage_per_huge::<C>(),
        0 < page_size_for_level_spec::<C>(level)
            <= page_size_for_level_spec::<C>((level + 1) as PagingLevel),
{
    C::lemma_paging_consts_properties();
    lemma_page_size_for_level_is_pow2::<C>(level);
    lemma_page_size_for_level_is_pow2::<C>((level + 1) as PagingLevel);
    let bits = nr_pte_index_bits_spec::<C>();
    lemma_usize_is_pow2_is_ilog2_pow2(nr_subpage_per_huge::<C>());
    lemma_mul_is_distributive_sub(bits as int, level as int, 1);
    assert(pte_index_bit_offset_spec::<C>((level + 1) as PagingLevel)
        == pte_index_bit_offset_spec::<C>(level) + bits);
    lemma_pow2_adds(pte_index_bit_offset_spec::<C>(level) as nat, bits as nat);
    vstd::arithmetic::mul::lemma_mul_left_inequality(
        page_size_for_level_spec::<C>(level) as int, 1, nr_subpage_per_huge::<C>() as int,
    );
    vstd::arithmetic::mul::lemma_mul_basics(page_size_for_level_spec::<C>(level) as int);
}

/// Temporary bridge to the architecture-global `page_size` helper used by the executable code.
pub proof fn lemma_page_size_for_level_matches_page_size<C: PagingConstsTrait>(
    level: PagingLevel,
)
    requires
        1 <= level <= C::NR_LEVELS() + 1,
    ensures
        page_size_for_level_spec::<C>(level) == page_size(level),
{
    C::lemma_paging_consts_properties();
}

/// Page-table index selected by `va` at `level`.
///
/// This is the architecture-parameterized address view used by executable page-table walks. The
/// mask width and bit offset both come from `C`; callers should use this instead of decomposing a
/// virtual address into an architecture-specific ghost structure.
#[verifier::inline]
pub open spec fn pte_index_spec<C: PagingConstsTrait>(va: Vaddr, level: PagingLevel) -> usize {
    (va >> pte_index_bit_offset_spec::<C>(level)) & ((nr_subpage_per_huge::<C>() - 1) as usize)
}

/// Selecting an index is division by the slot size followed by reduction modulo the fanout.
pub proof fn lemma_pte_index_spec_is_div_mod<C: PagingConstsTrait>(va: Vaddr, level: PagingLevel)
    requires
        1 <= level <= C::NR_LEVELS(),
    ensures
        pte_index_spec::<C>(va, level)
            == (va / page_size_for_level_spec::<C>(level)) % nr_subpage_per_huge::<C>(),
{
    C::lemma_paging_consts_properties();
    lemma_page_size_for_level_is_pow2::<C>(level);
    let bits = nr_pte_index_bits_spec::<C>();
    lemma_mul_inequality(1, C::NR_LEVELS() as int, bits as int);
    lemma_usize_is_pow2_is_ilog2_pow2(nr_subpage_per_huge::<C>());
    lemma_usize_shr_is_div(va, pte_index_bit_offset_spec::<C>(level));
    lemma_usize_low_bits_mask_is_mod(
        va >> pte_index_bit_offset_spec::<C>(level),
        bits as nat,
    );
}

/// At the next aligned boundary, a terminal index carries into the parent slot.
pub proof fn lemma_next_slot_pte_index<C: PagingConstsTrait>(
    va: Vaddr,
    next: Vaddr,
    level: PagingLevel,
)
    requires
        1 <= level <= C::NR_LEVELS(),
        va < next <= va + page_size_for_level_spec::<C>(level),
        next % page_size_for_level_spec::<C>(level) == 0,
    ensures
        next == (nat_align_down(va as nat, page_size_for_level_spec::<C>(level) as nat)
            + page_size_for_level_spec::<C>(level)) as Vaddr,
        pte_index_spec::<C>(next, level) == 0 ==> {
            &&& pte_index_spec::<C>(va, level) + 1 == nr_subpage_per_huge::<C>()
            &&& next % page_size_for_level_spec::<C>((level + 1) as PagingLevel) == 0
        },
        pte_index_spec::<C>(next, level) != 0
            ==> pte_index_spec::<C>(va, level) + 1 < nr_subpage_per_huge::<C>(),
{
    C::lemma_paging_consts_properties();
    lemma_pte_index_spec_is_div_mod::<C>(va, level);
    lemma_pte_index_spec_is_div_mod::<C>(next, level);
    lemma_page_size_for_level_next::<C>(level);
    let size = page_size_for_level_spec::<C>(level) as int;
    let fanout = nr_subpage_per_huge::<C>() as int;
    let quotient = next as int / size;
    let diff = next - va;
    lemma_fundamental_div_mod(next as int, size);
    vstd::arithmetic::mul::lemma_mul_basics(size);
    vstd::arithmetic::mul::lemma_mul_is_distributive_sub_other_way(size, quotient, 1);
    lemma_fundamental_div_mod_converse(va as int, size, quotient - 1, size - diff);
    vstd::arithmetic::div_mod::lemma_mod_bound(va as int / size, fanout);
    vstd::arithmetic::div_mod::lemma_add_mod_noop_right(1, va as int / size, fanout);
    let index = pte_index_spec::<C>(va, level) as int;
    if index + 1 < fanout {
        vstd::arithmetic::div_mod::lemma_small_mod((index + 1) as nat, fanout as nat);
    } else {
        vstd::arithmetic::div_mod::lemma_mod_self_0(fanout);
    }
    if pte_index_spec::<C>(next, level) == 0 {
        vstd::arithmetic::div_mod::lemma_mod_breakdown(next as int, size, fanout);
        vstd::arithmetic::mul::lemma_mul_basics(size);
    }
}

/// Replace one page-table index while leaving the other address components unchanged.
pub open spec fn vaddr_with_pte_index_spec<C: PagingConstsTrait>(
    va: Vaddr,
    level: PagingLevel,
    index: int,
) -> Vaddr {
    (va as int + (index - pte_index_spec::<C>(va, level))
        * page_size_for_level_spec::<C>(level)) as Vaddr
}

/// Width of the complete page-table-address body, including the in-page offset and every
/// configured page-table index. Bits above this boundary are not interpreted by a page walk.
#[verifier::inline]
pub open spec fn paging_body_width_spec<C: PagingConstsTrait>() -> usize {
    (C::BASE_PAGE_SIZE().ilog2() + nr_pte_index_bits_spec::<C>() * C::NR_LEVELS()) as usize
}

/// Bits of `va` above the complete architecture-parameterized page-table-address body.
#[verifier::inline]
pub open spec fn vaddr_upper_bits_spec<C: PagingConstsTrait>(va: Vaddr) -> usize {
    va >> paging_body_width_spec::<C>()
}

/// Contribution of the uninterpreted upper virtual-address bits to the concrete address.
/// Unlike the legacy fixed `leading_bits * 2^48` expression, the boundary is derived from `C`.
#[verifier::inline]
pub open spec fn vaddr_upper_base_spec<C: PagingConstsTrait>(va: Vaddr) -> int {
    vaddr_upper_bits_spec::<C>(va) as int * pow2(paging_body_width_spec::<C>() as nat) as int
}

#[verifier::inline]
pub open spec fn top_level_index_width_spec<C: PageTableConfig>() -> usize {
    (C::ADDRESS_WIDTH_spec() - pte_index_bit_offset_spec::<C>(C::NR_LEVELS())) as usize
}

/// Canonical bounds of the VA range managed by a page-table config,
///
/// Derived from `LEADING_BITS_spec` and `TOP_LEVEL_INDEX_RANGE`. For
/// `UserPtConfig` `(LEADING_BITS=0, idx=0..256)` this is `(0, 2^47 - 1)`;
/// for `KernelPtConfig` `(LEADING_BITS=0xffff, idx=256..512)` this is
/// `(0xffff_8000_0000_0000, 0xffff_ffff_ffff_ffff)`.
#[verusfmt::skip]
pub open spec fn vaddr_range_spec<C: PageTableConfig>() -> RangeInclusiveView<Vaddr> {
    let off = pte_index_bit_offset_spec::<C>(C::NR_LEVELS()) as nat;
    let lb = C::LEADING_BITS_spec() as int;
    let base = lb * 0x1_0000_0000_0000int;
    let start = (base + (C::TOP_LEVEL_INDEX_RANGE().start) * pow2(off)) as usize;
    let end = (base + (C::TOP_LEVEL_INDEX_RANGE().end) * pow2(off) - 1) as usize;
    RangeInclusiveView { start, end, exhausted: false }
}

pub open spec fn is_valid_range_spec<C: PageTableConfig>(r: Range<Vaddr>) -> bool {
    let va_range = vaddr_range_spec::<C>();
    (r.start == 0 && r.end == 0) || (va_range.start <= r.start && r.end - 1 <= va_range.end)
}

/// Sanity-check: for x86_64 user PT, the bounds are
/// `(0, 0x0000_7FFF_FFFF_FFFF)`, i.e. the low-half 47-bit user VA space.
pub(crate) proof fn lemma_vaddr_range_spec_user()
    ensures
        vaddr_range_spec::<UserPtConfig>().start == 0,
        vaddr_range_spec::<UserPtConfig>().end == 0x0000_7FFF_FFFF_FFFF,
{
    lemma_arch_specific_consts_properties::<PagingConsts>();
}

/// Sanity-check: for x86_64 kernel PT, the bounds are the canonical
/// upper half `(0xFFFF_8000_0000_0000, 0xFFFF_FFFF_FFFF_FFFF)`.
pub(crate) proof fn lemma_vaddr_range_spec_kernel()
    ensures
        vaddr_range_spec::<KernelPtConfig>().start == 0xFFFF_8000_0000_0000,
        vaddr_range_spec::<KernelPtConfig>().end == 0xFFFF_FFFF_FFFF_FFFF,
{
    lemma_arch_specific_consts_properties::<PagingConsts>();
}

/// Temporary bridge from the architecture-parameterized index view to the legacy
/// `AbstractVaddr` representation.
///
/// New cursor proofs should use `pte_index_spec` directly. This lemma confines the current
/// architecture-specific `AbstractVaddr` layout to migration sites and can be removed together
/// with that type.
pub proof fn lemma_pte_index_spec_matches_abstract<C: PagingConstsTrait>(
    va: Vaddr,
    level: PagingLevel,
)
    requires
        1 <= level <= C::NR_LEVELS(),
    ensures
        pte_index_spec::<C>(va, level) == AbstractVaddr::from_vaddr(va).index[level - 1],
{
    C::lemma_paging_consts_properties();
    lemma_arch_specific_consts_properties::<C>();

    let offset = pte_index_bit_offset_spec::<C>(level);
    let index_bits = nr_pte_index_bits_spec::<C>();

    lemma_usize_shr_is_div(va, offset);
    vstd::bits::lemma_low_bits_mask_values();
    lemma_usize_low_bits_mask_is_mod(va >> offset, index_bits as nat);
}

/// Temporary bridge from architecture-parameterized upper bits to the legacy
/// `AbstractVaddr::leading_bits` field.
pub proof fn lemma_vaddr_upper_bits_spec_matches_abstract<C: PagingConstsTrait>(va: Vaddr)
    ensures
        vaddr_upper_bits_spec::<C>(va) == AbstractVaddr::from_vaddr(va).leading_bits,
{
    C::lemma_paging_consts_properties();
    lemma_arch_specific_consts_properties::<C>();

    let width = paging_body_width_spec::<C>();

    lemma_usize_shr_is_div(va, width);
}

/// Temporary bridge from the architecture-parameterized upper-address contribution to the
/// fixed-width arithmetic used by the legacy decomposed address proofs.
pub proof fn lemma_vaddr_upper_base_spec_matches_abstract<C: PagingConstsTrait>(va: Vaddr)
    ensures
        vaddr_upper_base_spec::<C>(va)
            == AbstractVaddr::from_vaddr(va).leading_bits * 0x1_0000_0000_0000int,
{
    C::lemma_paging_consts_properties();
    lemma_arch_specific_consts_properties::<C>();
    lemma_vaddr_upper_bits_spec_matches_abstract::<C>(va);
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma2_to64_rest();
}

/// Addresses in one aligned node select the same entries at that node and above.
pub proof fn lemma_same_node_pte_indices_match<C: PagingConstsTrait>(
    va1: Vaddr,
    va2: Vaddr,
    node_start: Vaddr,
    level: PagingLevel,
)
    requires
        1 <= level,
        level < C::NR_LEVELS(),
        node_start <= va1,
        va1 < node_start + page_size_for_level_spec::<C>((level + 1) as PagingLevel),
        node_start <= va2,
        va2 < node_start + page_size_for_level_spec::<C>((level + 1) as PagingLevel),
        node_start as nat % page_size_for_level_spec::<C>((level + 1) as PagingLevel) as nat == 0,
    ensures
        pte_index_spec::<C>(va1, (level + 1) as PagingLevel)
            == pte_index_spec::<C>(va2, (level + 1) as PagingLevel),
        forall|i: int|
            level <= i < C::NR_LEVELS() ==> (#[trigger] pte_index_spec::<C>(
                va1,
                (i + 1) as PagingLevel,
            )) == pte_index_spec::<C>(va2, (i + 1) as PagingLevel),
{
    C::lemma_paging_consts_properties();
    let small_level = (level + 1) as PagingLevel;
    lemma_page_size_for_level_is_pow2::<C>(small_level);
    let small = page_size_for_level_spec::<C>(small_level) as int;
    let quotient = node_start as int / small;
    lemma_fundamental_div_mod(node_start as int, small);
    lemma_fundamental_div_mod_converse(
        va1 as int, small, quotient, va1 - node_start,
    );
    lemma_fundamental_div_mod_converse(
        va2 as int, small, quotient, va2 - node_start,
    );
    lemma_pte_index_spec_is_div_mod::<C>(va1, small_level);
    lemma_pte_index_spec_is_div_mod::<C>(va2, small_level);

    assert forall|i: int| level <= i < C::NR_LEVELS() implies (#[trigger] pte_index_spec::<C>(
        va1, (i + 1) as PagingLevel,
    )) == pte_index_spec::<C>(va2, (i + 1) as PagingLevel) by {
        let large_level = (i + 1) as PagingLevel;
        lemma_page_size_for_level_is_pow2::<C>(large_level);
        let delta = (nr_pte_index_bits_spec::<C>() * (i - level)) as nat;
        lemma_mul_is_distributive_sub(
            nr_pte_index_bits_spec::<C>() as int, i, level as int,
        );
        assert(pte_index_bit_offset_spec::<C>(large_level)
            == pte_index_bit_offset_spec::<C>(small_level) + delta);
        lemma_pow2_adds(pte_index_bit_offset_spec::<C>(small_level) as nat, delta);
        lemma_pow2_pos(delta);
        let ratio = pow2(delta) as int;
        assert(page_size_for_level_spec::<C>(large_level) == small * ratio);
        lemma_div_denominator(va1 as int, small, ratio);
        lemma_div_denominator(va2 as int, small, ratio);
        lemma_pte_index_spec_is_div_mod::<C>(va1, large_level);
        lemma_pte_index_spec_is_div_mod::<C>(va2, large_level);
    };
}

/// Architecture-parameterized view of the uninterpreted upper bits preserved by moving within
/// one page-table node.
pub proof fn lemma_same_node_vaddr_upper_bits_match<C: PagingConstsTrait>(
    va1: Vaddr,
    va2: Vaddr,
    node_start: Vaddr,
    level: PagingLevel,
)
    requires
        1 <= level,
        level <= C::NR_LEVELS(),
        node_start <= va1,
        va1 - node_start < page_size_for_level_spec::<C>((level + 1) as PagingLevel),
        node_start <= va2,
        va2 - node_start < page_size_for_level_spec::<C>((level + 1) as PagingLevel),
        node_start as nat % page_size_for_level_spec::<C>((level + 1) as PagingLevel) as nat == 0,
    ensures
        vaddr_upper_bits_spec::<C>(va1) == vaddr_upper_bits_spec::<C>(va2),
{
    C::lemma_paging_consts_properties();
    let small_level = (level + 1) as PagingLevel;
    let body_level = (C::NR_LEVELS() + 1) as PagingLevel;
    lemma_page_size_for_level_is_pow2::<C>(small_level);
    lemma_page_size_for_level_is_pow2::<C>(body_level);
    let small = page_size_for_level_spec::<C>(small_level) as int;
    let quotient = node_start as int / small;
    lemma_fundamental_div_mod(node_start as int, small);
    lemma_fundamental_div_mod_converse(
        va1 as int, small, quotient, va1 - node_start,
    );
    lemma_fundamental_div_mod_converse(
        va2 as int, small, quotient, va2 - node_start,
    );
    let delta = (nr_pte_index_bits_spec::<C>() * (C::NR_LEVELS() - level)) as nat;
    lemma_mul_is_distributive_sub(
        nr_pte_index_bits_spec::<C>() as int, C::NR_LEVELS() as int, level as int,
    );
    assert(paging_body_width_spec::<C>()
        == pte_index_bit_offset_spec::<C>(small_level) + delta);
    lemma_pow2_adds(pte_index_bit_offset_spec::<C>(small_level) as nat, delta);
    lemma_pow2_pos(delta);
    let ratio = pow2(delta) as int;
    assert(pow2(paging_body_width_spec::<C>() as nat) == small * ratio);
    lemma_div_denominator(va1 as int, small, ratio);
    lemma_div_denominator(va2 as int, small, ratio);
    lemma_usize_shr_is_div(va1, paging_body_width_spec::<C>());
    lemma_usize_shr_is_div(va2, paging_body_width_spec::<C>());
}

/// An abstract representation of a virtual address as a sequence of indices, representing the
/// values of the bit-fields that index into each level of the page table.
/// - `offset` is the lowest 12 bits (the offset into a 4096 byte page).
/// - `index[0]` is the next 9 bits, `index[1]` the 9 above that, up to
///   `index[NR_LEVELS-1]`, covering a total of `12 + 9 * NR_LEVELS = 48` bits.
/// - `leading_bits` holds whatever's in bits `[48, 64)` of the original `Vaddr`.
///   For canonical x86_64 addresses this is either `0` (user half) or the
///   sign-extended high bits (kernel half, e.g. `0xffff`).
pub ghost struct AbstractVaddr {
    pub offset: int,
    pub index: Map<int, int>,
    pub leading_bits: int,
}

impl Inv for AbstractVaddr {
    open spec fn inv(self) -> bool {
        &&& 0 <= self.offset
            < PAGE_SIZE
        // `index` has exactly `[0, NR_LEVELS)` as its domain.
        &&& self.index.dom() =~= Set::<int>::range(0, NR_LEVELS as int)
        &&& forall|i: int|
            #![trigger self.index.contains_key(i)]
            0 <= i < NR_LEVELS ==> {
                &&& self.index.contains_key(i)
                &&& 0 <= self.index[i] < NR_ENTRIES
            }
            // `leading_bits` is the 16-bit slot above the 48-bit positional body.
        &&& 0 <= self.leading_bits < 0x1_0000int
    }
}

impl AbstractVaddr {
    /// Extract the AbstractVaddr components from a concrete virtual address.
    /// - offset = lowest 12 bits
    /// - index[i] = bits (12 + 9*i) to (12 + 9*(i+1) - 1) for each level
    /// - leading_bits = bits [48, 64)
    pub open spec fn from_vaddr(va: Vaddr) -> Self {
        AbstractVaddr {
            offset: (va % PAGE_SIZE) as int,
            index: Map::new(
                Set::<int>::range(0, NR_LEVELS as int),
                |i: int| ((va / pow2((12 + 9 * i) as nat) as usize) % NR_ENTRIES) as int,
            ),
            leading_bits: (va as int / 0x1_0000_0000_0000int),
        }
    }

    pub proof fn from_vaddr_wf(va: Vaddr)
        ensures
            AbstractVaddr::from_vaddr(va).inv(),
    {
    }

    /// Reconstruct the concrete virtual address from the AbstractVaddr components.
    /// va = offset + sum(index[i] * 2^(12 + 9*i)) + leading_bits * 2^48
    pub open spec fn to_vaddr(self) -> Vaddr {
        (self.offset + self.to_vaddr_indices(0) + self.leading_bits
            * 0x1_0000_0000_0000int) as Vaddr
    }

    /// Helper: sum of index[i] * 2^(12 + 9*i) for i in start..NR_LEVELS
    pub open spec fn to_vaddr_indices(self, start: int) -> int
        decreases NR_LEVELS - start,
        when start <= NR_LEVELS
    {
        if start >= NR_LEVELS {
            0
        } else {
            self.index[start] * pow2((12 + 9 * start) as nat) + self.to_vaddr_indices(start + 1)
        }
    }

    /// reflect(self, va) holds when self is the abstract representation of va.
    pub open spec fn reflect(self, va: Vaddr) -> bool {
        self == Self::from_vaddr(va)
    }

    /// If self reflects va, then self.to_vaddr() == va and self == from_vaddr(va).
    /// The first ensures requires proving the round-trip property: from_vaddr(va).to_vaddr() == va.
    pub broadcast proof fn reflect_prop(self, va: Vaddr)
        requires
            self.inv(),
            self.reflect(va),
        ensures
            #[trigger] self.to_vaddr() == va,
            #[trigger] Self::from_vaddr(va) == self,
    {
        // self.reflect(va) means self == from_vaddr(va)
        // So self.to_vaddr() == from_vaddr(va).to_vaddr()
        // We need: from_vaddr(va).to_vaddr() == va (round-trip property)
        Self::from_vaddr_to_vaddr_roundtrip(va);
    }

    /// Round-trip property: extracting and reconstructing a VA gives back the original.
    ///
    /// With `leading_bits` carrying the high 16 bits of the VA, this now
    /// holds **unconditionally** for any 64-bit `Vaddr` — the positional
    /// decomposition covers all 64 bits (12 offset + 4×9 index + 16 top).
    pub broadcast proof fn from_vaddr_to_vaddr_roundtrip(va: Vaddr)
        ensures
            #[trigger] Self::from_vaddr(va).to_vaddr() == va,
    {
        vstd::arithmetic::power2::lemma2_to64();
        vstd::arithmetic::power2::lemma2_to64_rest();
        let abs = Self::from_vaddr(va);

        assert(abs.to_vaddr_indices(3) == abs.index[3] * pow2(39nat) + abs.to_vaddr_indices(4));

        assert(abs.to_vaddr_indices(1) == abs.index[1] * pow2(21nat) + abs.to_vaddr_indices(2));

        assert(va == (va % 4096usize) + ((va / 4096usize) % 512usize) * 4096usize + ((va
            / 0x20_0000usize) % 512usize) * 0x20_0000usize + ((va / 0x4000_0000usize) % 512usize)
            * 0x4000_0000usize + ((va / 0x80_0000_0000usize) % 512usize) * 0x80_0000_0000usize + (va
            / 0x1_0000_0000_0000usize) * 0x1_0000_0000_0000usize) by (bit_vector);
    }

    /// from_vaddr(va) reflects va (by definition of reflect).
    pub broadcast proof fn reflect_from_vaddr(va: Vaddr)
        ensures
            #[trigger] Self::from_vaddr(va).reflect(va),
            #[trigger] Self::from_vaddr(va).inv(),
    {
    }

    /// If self.inv(), then self reflects self.to_vaddr().
    pub broadcast proof fn reflect_to_vaddr(self)
        requires
            self.inv(),
        ensures
            #[trigger] self.reflect(self.to_vaddr()),
    {
        Self::to_vaddr_from_vaddr_roundtrip(self);
    }

    /// Inverse round-trip: reconstruct then extract gives back the
    /// original `AbstractVaddr`.
    pub proof fn to_vaddr_from_vaddr_roundtrip(abs: Self)
        requires
            abs.inv(),
        ensures
            Self::from_vaddr(abs.to_vaddr()) == abs,
    {
        vstd::arithmetic::power2::lemma2_to64();
        vstd::arithmetic::power2::lemma2_to64_rest();
        abs.to_vaddr_bounded();
        assert(abs.to_vaddr_indices(4) == 0);
        assert(abs.to_vaddr_indices(3) == abs.index[3] * pow2(39nat) + abs.to_vaddr_indices(4));
        assert(abs.to_vaddr_indices(2) == abs.index[2] * pow2(30nat) + abs.to_vaddr_indices(3));
        assert(abs.to_vaddr_indices(1) == abs.index[1] * pow2(21nat) + abs.to_vaddr_indices(2));
        assert(abs.to_vaddr_indices(0) == abs.index[0] * pow2(12nat) + abs.to_vaddr_indices(1));

        assert(abs.index.contains_key(0));
        assert(abs.index.contains_key(1));
        assert(abs.index.contains_key(2));
        assert(abs.index.contains_key(3));
        let i0 = abs.index[0] as usize;
        let i1 = abs.index[1] as usize;
        let i2 = abs.index[2] as usize;
        let i3 = abs.index[3] as usize;
        let o = abs.offset as usize;
        let tb = abs.leading_bits as usize;
        let va = abs.to_vaddr();
        assert(va == o + i0 * 4096usize + i1 * 0x20_0000usize + i2 * 0x4000_0000usize + i3
            * 0x80_0000_0000usize + tb * 0x1_0000_0000_0000usize);

        assert(va % 4096usize == o) by (bit_vector)
            requires
                va == o + i0 * 4096usize + i1 * 0x20_0000usize + i2 * 0x4000_0000usize + i3
                    * 0x80_0000_0000usize + tb * 0x1_0000_0000_0000usize,
                o < 4096usize,
                i0 < 512usize,
                i1 < 512usize,
                i2 < 512usize,
                i3 < 512usize,
                tb < 0x1_0000usize,
        ;
        assert((va / 4096usize) % 512usize == i0) by (bit_vector)
            requires
                va == o + i0 * 4096usize + i1 * 0x20_0000usize + i2 * 0x4000_0000usize + i3
                    * 0x80_0000_0000usize + tb * 0x1_0000_0000_0000usize,
                o < 4096usize,
                i0 < 512usize,
                i1 < 512usize,
                i2 < 512usize,
                i3 < 512usize,
                tb < 0x1_0000usize,
        ;
        assert((va / 0x20_0000usize) % 512usize == i1) by (bit_vector)
            requires
                va == o + i0 * 4096usize + i1 * 0x20_0000usize + i2 * 0x4000_0000usize + i3
                    * 0x80_0000_0000usize + tb * 0x1_0000_0000_0000usize,
                o < 4096usize,
                i0 < 512usize,
                i1 < 512usize,
                i2 < 512usize,
                i3 < 512usize,
                tb < 0x1_0000usize,
        ;
        assert((va / 0x4000_0000usize) % 512usize == i2) by (bit_vector)
            requires
                va == o + i0 * 4096usize + i1 * 0x20_0000usize + i2 * 0x4000_0000usize + i3
                    * 0x80_0000_0000usize + tb * 0x1_0000_0000_0000usize,
                o < 4096usize,
                i0 < 512usize,
                i1 < 512usize,
                i2 < 512usize,
                i3 < 512usize,
                tb < 0x1_0000usize,
        ;
        assert((va / 0x80_0000_0000usize) % 512usize == i3) by (bit_vector)
            requires
                va == o + i0 * 4096usize + i1 * 0x20_0000usize + i2 * 0x4000_0000usize + i3
                    * 0x80_0000_0000usize + tb * 0x1_0000_0000_0000usize,
                o < 4096usize,
                i0 < 512usize,
                i1 < 512usize,
                i2 < 512usize,
                i3 < 512usize,
                tb < 0x1_0000usize,
        ;
        assert(va / 0x1_0000_0000_0000usize == tb) by (bit_vector)
            requires
                va == o + i0 * 4096usize + i1 * 0x20_0000usize + i2 * 0x4000_0000usize + i3
                    * 0x80_0000_0000usize + tb * 0x1_0000_0000_0000usize,
                o < 4096usize,
                i0 < 512usize,
                i1 < 512usize,
                i2 < 512usize,
                i3 < 512usize,
                tb < 0x1_0000usize,
        ;

        let back = Self::from_vaddr(va);
        assert forall|i: int| 0 <= i < NR_LEVELS implies #[trigger] back.index[i]
            == abs.index[i] by {
            if i == 0 {
            } else if i == 1 {
            } else if i == 2 {
            } else if i == 3 {
            }
        }
        assert(back.index == abs.index);
    }

    /// If two AbstractVaddrs reflect the same va, they are equal.
    pub broadcast proof fn reflect_eq(self, other: Self, va: Vaddr)
        requires
            #[trigger] self.reflect(va),
            #[trigger] other.reflect(va),
        ensures
            self == other,
    {
    }

    pub open spec fn align_down(self, level: int) -> Self
        decreases level,
        when level >= 1
    {
        if level == 1 {
            AbstractVaddr { offset: 0, ..self }
        } else {
            let tmp = self.align_down(level - 1);
            AbstractVaddr { index: tmp.index.insert(level - 2, 0), ..tmp }
        }
    }

    /// Updating one valid page-table index with an in-range value preserves the VA invariant.
    pub proof fn lemma_insert_preserves_inv(self, index: int, value: int)
        requires
            self.inv(),
            0 <= index < NR_LEVELS,
            0 <= value < NR_ENTRIES,
        ensures
            (AbstractVaddr { index: self.index.insert(index, value), ..self }).inv(),
    {
        let new = AbstractVaddr { index: self.index.insert(index, value), ..self };
        assert(new.index.dom() == Set::<int>::range(0, NR_LEVELS as int));
        assert forall|i: int| #![trigger new.index.contains_key(i)] 0 <= i < NR_LEVELS implies {
            &&& new.index.contains_key(i)
            &&& 0 <= new.index[i] < NR_ENTRIES
        } by {
            if i != index {
                assert(self.index.contains_key(i));
            }
        }
    }

    /// Compatibility bridge for numeric index replacement during the address-model migration.
    pub proof fn lemma_index_replacement_vaddr<C: PagingConstsTrait>(
        self,
        level: PagingLevel,
        value: int,
    )
        requires
            self.inv(),
            1 <= level <= C::NR_LEVELS(),
            0 <= value < nr_subpage_per_huge::<C>(),
        ensures
            (Self { index: self.index.insert(level - 1, value), ..self }).to_vaddr()
                == vaddr_with_pte_index_spec::<C>(self.to_vaddr(), level, value),
            0 <= self.to_vaddr() as int + (value - self.index[level - 1])
                * page_size_for_level_spec::<C>(level) <= usize::MAX,
    {
        C::lemma_paging_consts_properties();
        self.lemma_insert_preserves_inv(level - 1, value);
        self.lemma_index_replacement_sum::<C>(level - 1, value, 0);
        let replaced = Self { index: self.index.insert(level - 1, value), ..self };
        self.to_vaddr_bounded();
        replaced.to_vaddr_bounded();
        self.reflect_to_vaddr();
        lemma_pte_index_spec_matches_abstract::<C>(self.to_vaddr(), level);
    }

    proof fn lemma_index_replacement_sum<C: PagingConstsTrait>(
        self,
        index: int,
        value: int,
        start: int,
    )
        requires
            self.inv(),
            0 <= index < C::NR_LEVELS(),
            0 <= start <= C::NR_LEVELS(),
        ensures
            (Self { index: self.index.insert(index, value), ..self }).to_vaddr_indices(start)
                == self.to_vaddr_indices(start) + if start <= index {
                    (value - self.index[index]) * page_size_for_level_spec::<C>((index + 1) as PagingLevel)
                } else {
                    0
                },
        decreases C::NR_LEVELS() - start,
    {
        C::lemma_paging_consts_properties();
        lemma_arch_specific_consts_properties::<C>();
        if start < C::NR_LEVELS() {
            self.lemma_index_replacement_sum::<C>(index, value, start + 1);
            if start == index {
                lemma_page_size_for_level_is_pow2::<C>((index + 1) as PagingLevel);
                assert((value - self.index[index]) * page_size_for_level_spec::<C>((index + 1) as PagingLevel)
                    == value * page_size_for_level_spec::<C>((index + 1) as PagingLevel)
                        - self.index[index] * page_size_for_level_spec::<C>((index + 1) as PagingLevel))
                    by (nonlinear_arith);
            }
        }
    }

    proof fn lemma_insert_zero_preserves_inv(self, index: int)
        requires
            self.inv(),
            0 <= index < NR_LEVELS,
        ensures
            (AbstractVaddr { index: self.index.insert(index, 0), ..self }).inv(),
    {
        self.lemma_insert_preserves_inv(index, 0);
    }

    pub proof fn align_down_inv(self, level: int)
        requires
            1 <= level <= NR_LEVELS,
            self.inv(),
        ensures
            self.align_down(level).inv(),
            forall|i: int|
                level <= i < NR_LEVELS ==> #[trigger] self.index[i - 1] == self.align_down(
                    level,
                ).index[i - 1],
        decreases level,
    {
        if level == 1 {
        } else {
            let tmp = self.align_down(level - 1);
            self.align_down_inv(level - 1);
            tmp.lemma_insert_zero_preserves_inv(level - 2);
        }
    }

    pub proof fn align_down_leading_bits(self, level: int)
        requires
            1 <= level <= NR_LEVELS,
        ensures
            self.align_down(level).leading_bits == self.leading_bits,
        decreases level,
    {
        if level > 1 {
            self.align_down_leading_bits(level - 1);
        }
    }

    pub proof fn align_down_shape(self, level: int)
        requires
            1 <= level <= NR_LEVELS,
            self.inv(),
        ensures
            self.align_down(level).inv(),
            self.align_down(level).offset == 0,
            forall|i: int| 0 <= i < level - 1 ==> #[trigger] self.align_down(level).index[i] == 0,
            forall|i: int|
                level - 1 <= i < NR_LEVELS ==> #[trigger] self.align_down(level).index[i]
                    == self.index[i],
        decreases level,
    {
        self.align_down_inv(level);
        if level != 1 {
            self.align_down_shape(level - 1);
        }
    }

    pub proof fn to_vaddr_indices_drop_zero_range(self, from: int, to: int)
        requires
            self.inv(),
            0 <= from <= to <= NR_LEVELS,
            forall|i: int| from <= i < to ==> self.index[i] == 0,
        ensures
            self.to_vaddr_indices(from) == self.to_vaddr_indices(to),
        decreases to - from,
    {
        if from < to {
            self.to_vaddr_indices_drop_zero_range(from + 1, to);
        }
    }

    pub proof fn to_vaddr_indices_eq_if_indices_eq(self, other: Self, start: int)
        requires
            self.inv(),
            other.inv(),
            0 <= start <= NR_LEVELS,
            forall|i: int| start <= i < NR_LEVELS ==> self.index[i] == other.index[i],
        ensures
            self.to_vaddr_indices(start) == other.to_vaddr_indices(start),
        decreases NR_LEVELS - start,
    {
        if start < NR_LEVELS {
            self.to_vaddr_indices_eq_if_indices_eq(other, start + 1);
        }
    }

    /// If two AbstractVaddrs share the same indices at levels >= level-1 (i.e., index[level-1] and above),
    /// then aligning them down to `level` gives the same to_vaddr() result.
    /// This is because align_down(level) zeroes offset and indices 0 through level-2,
    /// so only indices level-1 and above affect the to_vaddr() result.
    pub proof fn align_down_to_vaddr_eq_if_upper_indices_eq(self, other: Self, level: int)
        requires
            1 <= level <= NR_LEVELS,
            self.inv(),
            other.inv(),
            // Indices at level-1 and above are equal
            forall|i: int| level - 1 <= i < NR_LEVELS ==> self.index[i] == other.index[i],
            // Both live in the same canonical half.
            self.leading_bits == other.leading_bits,
        ensures
            self.align_down(level).to_vaddr() == other.align_down(level).to_vaddr(),
        decreases level,
    {
        let lhs = self.align_down(level);
        let rhs = other.align_down(level);

        self.align_down_shape(level);
        other.align_down_shape(level);
        self.align_down_leading_bits(level);
        other.align_down_leading_bits(level);

        lhs.to_vaddr_indices_drop_zero_range(0, level - 1);
        rhs.to_vaddr_indices_drop_zero_range(0, level - 1);
        lhs.to_vaddr_indices_eq_if_indices_eq(rhs, level - 1);

    }

    /// The aligned form is a multiple of `page_size(level)` and the difference from `self.to_vaddr()`
    /// is the low-order bits (offset + indices below `level - 1`), which is strictly less than
    /// `page_size(level)`.
    proof fn align_down_to_vaddr_arith(self, level: int)
        requires
            self.inv(),
            1 <= level <= NR_LEVELS,
        ensures
            self.align_down(level).to_vaddr() as int % page_size(level as PagingLevel) as int == 0,
            0 <= self.to_vaddr() - self.align_down(level).to_vaddr(),
            self.to_vaddr() - self.align_down(level).to_vaddr() < page_size(level as PagingLevel),
    {
        let aligned = self.align_down(level);
        vstd::arithmetic::power2::lemma2_to64();
        vstd::arithmetic::power2::lemma2_to64_rest();

        vstd_extra::external::ilog2::lemma_usize_ilog2_to32();

        self.align_down_shape(level);
        self.align_down_leading_bits(level);

        // aligned.to_vaddr_indices(0) == self.to_vaddr_indices(level - 1).
        aligned.to_vaddr_indices_drop_zero_range(0, level - 1);
        aligned.to_vaddr_indices_eq_if_indices_eq(self, level - 1);

        // Unroll to_vaddr_indices against concrete pow2 values so bit_vector can reason.
        let o = self.offset;
        assert(self.index.contains_key(0));
        assert(self.index.contains_key(1));
        assert(self.index.contains_key(2));
        assert(self.index.contains_key(3));
        let i0 = self.index[0];
        let i1 = self.index[1];
        let i2 = self.index[2];
        let i3 = self.index[3];
        assert(self.to_vaddr_indices(4) == 0);
        assert(self.to_vaddr_indices(3) == i3 * 0x80_0000_0000int);
        assert(self.to_vaddr_indices(2) == i2 * 0x4000_0000int + i3 * 0x80_0000_0000int);
        assert(self.to_vaddr_indices(1) == i1 * 0x20_0000int + i2 * 0x4000_0000int + i3
            * 0x80_0000_0000int);

        let va = self.to_vaddr() as int;
        let av = aligned.to_vaddr() as int;
        let ps = page_size(level as PagingLevel) as int;

        // Both va and av fit in [0, 2^64) by to_vaddr_bounded.

        // Case-split on level to discharge the arithmetic.
        let diff = va - av;
        if level == 1 {
        } else if level == 2 {
        } else if level == 3 {
        } else {
            assert(0 <= diff < ps) by (nonlinear_arith)
                requires
                    diff == o + i0 * 0x1000int + i1 * 0x20_0000int + i2 * 0x4000_0000int,
                    0 <= o < 4096,
                    0 <= i0 < 512,
                    0 <= i1 < 512,
                    0 <= i2 < 512,
                    ps == 0x80_0000_0000,
            ;

        }
    }

    /// Concrete relation: `align_down(level).to_vaddr() == nat_align_down(to_vaddr(), page_size(level))`.
    /// Uses `align_down_to_vaddr_arith` to establish that `av` is a multiple of `ps` with
    /// `0 <= va - av < ps`, then shows `va % ps == va - av`, so `nat_align_down(va, ps) = av`.
    pub proof fn align_down_to_vaddr_nat_align_down(self, level: int)
        requires
            self.inv(),
            1 <= level <= NR_LEVELS,
        ensures
            self.align_down(level).to_vaddr() as nat == nat_align_down(
                self.to_vaddr() as nat,
                page_size(level as PagingLevel) as nat,
            ),
    {
        self.align_down_to_vaddr_arith(level);

        let va = self.to_vaddr() as int;
        let av = self.align_down(level).to_vaddr() as int;
        let ps = page_size(level as PagingLevel) as int;

        assert(av % ps == 0);
        assert(va - av < ps);

        // av = ps * q for some q, so va = ps * q + (va - av).
        // Then va % ps == (va - av) % ps == va - av (since 0 <= va - av < ps).
        // So nat_align_down(va, ps) = va - va%ps = va - (va - av) = av.
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(av, ps);
        assert(av == ps * (av / ps)) by {
            assert(av % ps == 0);
        };
        assert(va == ps * (av / ps) + (va - av));
        vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(av / ps, va - av, ps);
        assert((ps * (av / ps) + (va - av)) % ps == (va - av) % ps);
        assert(va % ps == (va - av) % ps);
        vstd::arithmetic::div_mod::lemma_small_mod((va - av) as nat, ps as nat);
        assert((va - av) % ps == va - av);
        assert(va % ps == va - av);
    }

    pub proof fn align_down_concrete(self, level: int)
        requires
            self.inv(),
            1 <= level <= NR_LEVELS,
        ensures
            self.align_down(level).reflect(
                nat_align_down(
                    self.to_vaddr() as nat,
                    page_size(level as PagingLevel) as nat,
                ) as Vaddr,
            ),
    {
        let aligned = self.align_down(level);
        self.align_down_shape(level);
        self.align_down_to_vaddr_nat_align_down(level);
        aligned.reflect_to_vaddr();
    }



    pub proof fn same_page_aligned_vaddrs_equal(va1: Vaddr, va2: Vaddr, page_start: Vaddr)
        requires
            page_start <= va1,
            va1 - page_start < PAGE_SIZE,
            page_start <= va2,
            va2 - page_start < PAGE_SIZE,
            va1 % PAGE_SIZE == 0,
            va2 % PAGE_SIZE == 0,
            page_start % PAGE_SIZE == 0,
        ensures
            va1 == va2,
    {
    }

    pub proof fn to_vaddr_indices_gap_bound(self, start: int)
        requires
            self.inv(),
            0 <= start <= NR_LEVELS,
        ensures
            0 <= self.to_vaddr_indices(start),
            self.to_vaddr_indices(start) + pow2((12 + 9 * start) as nat) <= pow2(
                (12 + 9 * NR_LEVELS) as nat,
            ),
        decreases NR_LEVELS - start,
    {
        vstd::arithmetic::power2::lemma2_to64();

        if start != NR_LEVELS {
            let shift = pow2((12 + 9 * start) as nat) as int;
            self.to_vaddr_indices_gap_bound(start + 1);
            assert(self.index.contains_key(start));
            vstd::arithmetic::power2::lemma_pow2_adds((12 + 9 * start) as nat, 9nat);
            vstd::arithmetic::mul::lemma_mul_inequality(self.index[start] + 1, 0x200int, shift);
            vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(
                shift,
                self.index[start],
                1,
            );
        }
    }

    pub proof fn to_vaddr_bounded(self)
        requires
            self.inv(),
        ensures
            0 <= self.offset + self.to_vaddr_indices(0) < 0x1_0000_0000_0000int,
            self.to_vaddr() == self.offset + self.to_vaddr_indices(0) + self.leading_bits
                * 0x1_0000_0000_0000int,
            self.offset + self.to_vaddr_indices(0) + self.leading_bits * 0x1_0000_0000_0000int
                < 0x1_0000_0000_0000_0000int,
    {
        vstd::arithmetic::power2::lemma2_to64();
        vstd::arithmetic::power2::lemma2_to64_rest();
        self.to_vaddr_indices_gap_bound(0);

    }

}

} // verus!
