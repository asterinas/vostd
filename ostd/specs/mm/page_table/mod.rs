#![allow(hidden_glob_reexports)]

pub mod cursor;
pub mod mapping_set_lemmas;
pub mod node;
mod owners;
pub mod vaddr_range_proofs;
mod view;

use vstd::{
    arithmetic::{
        div_mod::{
            lemma_div_denominator, lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse,
        },
        mul::{lemma_mul_inequality, lemma_mul_is_distributive_sub},
        power2::{lemma_pow2_adds, lemma_pow2_pos, lemma2_to64, lemma2_to64_rest, pow2},
    },
    bits::{
        lemma_usize_low_bits_mask_is_mod, lemma_usize_pow2_no_overflow, lemma_usize_shr_is_div,
    },
    prelude::*,
    std_specs::range::RangeInclusiveView,
};
use vstd_extra::{
    arithmetic::*, external::ilog2::lemma_usize_is_pow2_is_ilog2_pow2, ownership::*, prelude::*,
};

use crate::specs::arch::*;

use crate::mm::{
    PagingConsts, PagingConstsTrait, PagingLevel, Vaddr, kspace::KernelPtConfig,
    nr_subpage_per_huge, page_size, page_size_spec, page_table::PageTableConfig, vm_space::UserPtConfig,
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

/// A configured page size is the power of two at that level's index-bit offset.
pub proof fn lemma_page_size_for_level_is_pow2<C: PagingConstsTrait>(level: PagingLevel)
    requires
        1 <= level <= C::NR_LEVELS() + 1,
    ensures
        pte_index_bit_offset_spec::<C>(level) < usize::BITS,
        pte_index_bit_offset_spec::<C>(level) == C::BASE_PAGE_SIZE().ilog2()
            + nr_pte_index_bits_spec::<C>() * (level - 1),
        0 < page_size_spec::<C>(level) == pow2(
            pte_index_bit_offset_spec::<C>(level) as nat,
        ),
{
    C::lemma_paging_consts_properties();
    let bits = nr_pte_index_bits_spec::<C>();
    assert(usize::BITS <= usize::MAX) by (compute_only);
    lemma_usize_is_pow2_is_ilog2_pow2(C::BASE_PAGE_SIZE());
    lemma_usize_is_pow2_is_ilog2_pow2(nr_subpage_per_huge::<C>());
    assert(bits == (C::BASE_PAGE_SIZE() / C::PTE_SIZE()).ilog2());
    lemma_mul_inequality(level - 1, C::NR_LEVELS() as int, bits as int);
    assert(C::BASE_PAGE_SIZE().ilog2() + bits * (level - 1) <= C::ADDRESS_WIDTH());
    assert(pte_index_bit_offset_spec::<C>(level) == C::BASE_PAGE_SIZE().ilog2() + bits * (level
        - 1));
    lemma_pow2_adds(C::BASE_PAGE_SIZE().ilog2() as nat, (bits * (level - 1)) as nat);
    lemma_usize_pow2_no_overflow(pte_index_bit_offset_spec::<C>(level) as nat);
}

/// A parent slot contains exactly one fanout of slots at the preceding level.
pub proof fn lemma_page_size_for_level_next<C: PagingConstsTrait>(level: PagingLevel)
    requires
        1 <= level <= C::NR_LEVELS(),
    ensures
        page_size_spec::<C>((level + 1) as PagingLevel) == page_size_spec::<C>(
            level,
        ) * nr_subpage_per_huge::<C>(),
        0 < page_size_spec::<C>(level) <= page_size_spec::<C>(
            (level + 1) as PagingLevel,
        ),
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
        page_size_spec::<C>(level) as int,
        1,
        nr_subpage_per_huge::<C>() as int,
    );
    vstd::arithmetic::mul::lemma_mul_basics(page_size_spec::<C>(level) as int);
}

/// Configured page sizes divide the sizes of all higher-level slots.
pub proof fn lemma_page_size_for_level_divides<C: PagingConstsTrait>(
    small: PagingLevel,
    large: PagingLevel,
)
    requires
        1 <= small <= large <= C::NR_LEVELS() + 1,
    ensures
        0 < page_size_spec::<C>(small) <= page_size_spec::<C>(large),
        page_size_spec::<C>(large) % page_size_spec::<C>(small) == 0,
{
    C::lemma_paging_consts_properties();
    lemma_page_size_for_level_is_pow2::<C>(small);
    lemma_page_size_for_level_is_pow2::<C>(large);
    let delta = (nr_pte_index_bits_spec::<C>() * (large - small)) as nat;
    lemma_mul_is_distributive_sub(nr_pte_index_bits_spec::<C>() as int, large as int, small as int);
    lemma_mul_is_distributive_sub(nr_pte_index_bits_spec::<C>() as int, large as int, 1);
    lemma_mul_is_distributive_sub(nr_pte_index_bits_spec::<C>() as int, small as int, 1);
    assert(pte_index_bit_offset_spec::<C>(large) == pte_index_bit_offset_spec::<C>(small) + delta);
    lemma_pow2_adds(pte_index_bit_offset_spec::<C>(small) as nat, delta);
    lemma_pow2_pos(delta);
    let a = page_size_spec::<C>(small) as int;
    let ratio = pow2(delta) as int;
    assert(page_size_spec::<C>(large) == a * ratio);
    vstd::arithmetic::div_mod::lemma_mod_multiples_basic(ratio, a);
    vstd::arithmetic::mul::lemma_mul_is_commutative(a, ratio);
    vstd::arithmetic::mul::lemma_mul_left_inequality(a, 1, ratio);
    vstd::arithmetic::mul::lemma_mul_basics(a);
}

/// Page-table index selected by `va` at `level`.
#[verifier::inline]
pub open spec fn pte_index_spec<C: PagingConstsTrait>(va: Vaddr, level: PagingLevel) -> usize {
    (va >> pte_index_bit_offset_spec::<C>(level)) & ((nr_subpage_per_huge::<C>() - 1) as usize)
}

/// Selecting an index is division by the slot size followed by reduction modulo the fanout.
pub proof fn lemma_pte_index_spec_is_div_mod<C: PagingConstsTrait>(va: Vaddr, level: PagingLevel)
    requires
        1 <= level <= C::NR_LEVELS(),
    ensures
        pte_index_spec::<C>(va, level) == (va / page_size_spec::<C>(level))
            % nr_subpage_per_huge::<C>(),
{
    C::lemma_paging_consts_properties();
    lemma_page_size_for_level_is_pow2::<C>(level);
    let bits = nr_pte_index_bits_spec::<C>();
    lemma_mul_inequality(1, C::NR_LEVELS() as int, bits as int);
    lemma_usize_is_pow2_is_ilog2_pow2(nr_subpage_per_huge::<C>());
    lemma_usize_shr_is_div(va, pte_index_bit_offset_spec::<C>(level));
    lemma_usize_low_bits_mask_is_mod(va >> pte_index_bit_offset_spec::<C>(level), bits as nat);
}

/// Every extracted index is in the configured fanout.
pub proof fn lemma_pte_index_bound<C: PagingConstsTrait>(va: Vaddr, level: PagingLevel)
    requires
        1 <= level <= C::NR_LEVELS(),
    ensures
        pte_index_spec::<C>(va, level) < nr_subpage_per_huge::<C>(),
{
    lemma_pte_index_spec_is_div_mod::<C>(va, level);
    C::lemma_paging_consts_properties();
    vstd::arithmetic::div_mod::lemma_mod_bound(
        va as int / page_size_spec::<C>(level) as int,
        nr_subpage_per_huge::<C>() as int,
    );
}

/// The first configured level has the base-page size.
pub proof fn lemma_page_size_for_level_base<C: PagingConstsTrait>()
    ensures
        page_size_spec::<C>(1) == C::BASE_PAGE_SIZE(),
{
    reveal(vstd::arithmetic::power::pow);
    vstd::arithmetic::power2::lemma_pow2(0);
    assert(pow2(0) == 1);
    vstd::arithmetic::mul::lemma_mul_basics(nr_pte_index_bits_spec::<C>() as int);
    vstd::arithmetic::mul::lemma_mul_basics(C::BASE_PAGE_SIZE() as int);
}

/// Zero lower indices together with base-page alignment imply slot alignment.
pub proof fn lemma_lower_indices_aligned<C: PagingConstsTrait>(va: Vaddr, level: PagingLevel)
    requires
        1 <= level <= C::NR_LEVELS() + 1,
        va % C::BASE_PAGE_SIZE() == 0,
        forall|i: int| 1 <= i < level ==> #[trigger] pte_index_spec::<C>(va, i as PagingLevel) == 0,
    ensures
        va % page_size_spec::<C>(level) == 0,
    decreases level,
{
    C::lemma_paging_consts_properties();
    lemma_page_size_for_level_base::<C>();
    if level > 1 {
        let lower = (level - 1) as PagingLevel;
        lemma_lower_indices_aligned::<C>(va, lower);
        lemma_page_size_for_level_next::<C>(lower);
        lemma_pte_index_spec_is_div_mod::<C>(va, lower);
        assert(pte_index_spec::<C>(va, lower) == 0);
        vstd::arithmetic::div_mod::lemma_mod_breakdown(
            va as int,
            page_size_spec::<C>(lower) as int,
            nr_subpage_per_huge::<C>() as int,
        );
        vstd::arithmetic::mul::lemma_mul_basics(page_size_spec::<C>(lower) as int);
        assert(va % page_size_spec::<C>(level) == 0);
    } else {
        assert(page_size_spec::<C>(level) == C::BASE_PAGE_SIZE());
    }
}

/// Slot alignment makes every lower PTE index zero.
pub proof fn lemma_aligned_indices_zero<C: PagingConstsTrait>(va: Vaddr, level: PagingLevel)
    requires
        1 <= level <= C::NR_LEVELS() + 1,
        va % page_size_spec::<C>(level) == 0,
    ensures
        va % C::BASE_PAGE_SIZE() == 0,
        forall|i: int| 1 <= i < level ==> #[trigger] pte_index_spec::<C>(va, i as PagingLevel) == 0,
    decreases level,
{
    C::lemma_paging_consts_properties();
    lemma_page_size_for_level_base::<C>();
    if level > 1 {
        let lower = (level - 1) as PagingLevel;
        lemma_page_size_for_level_next::<C>(lower);
        let size = page_size_spec::<C>(lower) as int;
        let fanout = nr_subpage_per_huge::<C>() as int;
        vstd::arithmetic::div_mod::lemma_mod_mod(va as int, size, fanout);
        lemma_pte_index_spec_is_div_mod::<C>(va, lower);
        vstd::arithmetic::div_mod::lemma_mod_breakdown(va as int, size, fanout);
        vstd::arithmetic::div_mod::lemma_mod_bound(va as int / size, fanout);
        assert(pte_index_spec::<C>(va, lower) == 0) by (nonlinear_arith)
            requires
                size > 0,
                0 <= va as int / size % fanout,
                size * (va as int / size % fanout) == 0,
                pte_index_spec::<C>(va, lower) == va as int / size % fanout,
        ;
        lemma_aligned_indices_zero::<C>(va, lower);
    } else {
        assert(page_size_spec::<C>(level) == C::BASE_PAGE_SIZE());
    }
}

/// A power-of-two-aligned address leaves one complete slot before machine-word wrap.
pub proof fn lemma_aligned_vaddr_slack<C: PagingConstsTrait>(va: Vaddr, level: PagingLevel)
    requires
        1 <= level <= C::NR_LEVELS() + 1,
        va % page_size_spec::<C>(level) == 0,
    ensures
        va + page_size_spec::<C>(level) <= usize::MAX + 1,
{
    lemma_page_size_for_level_is_pow2::<C>(level);
    let size = page_size_spec::<C>(level);
    vstd::bits::lemma_usize_low_bits_mask_is_mod(
        usize::MAX,
        pte_index_bit_offset_spec::<C>(level) as nat,
    );
    vstd::bits::lemma_low_bits_mask_values();
    assert(usize::MAX & ((size - 1) as usize) == (size - 1) as usize) by (bit_vector);
    assert(usize::MAX % size == size - 1);
    lemma_fundamental_div_mod(va as int, size as int);
    lemma_fundamental_div_mod(usize::MAX as int, size as int);
    vstd::arithmetic::div_mod::lemma_div_is_ordered(va as int, usize::MAX as int, size as int);
    vstd::arithmetic::mul::lemma_mul_inequality(
        va as int / size as int,
        usize::MAX as int / size as int,
        size as int,
    );
    assert(va + size <= usize::MAX + 1) by (nonlinear_arith)
        requires
            va == (size as int) * (va as int / size as int),
            usize::MAX == (size as int) * (usize::MAX as int / size as int) + size - 1,
            0 < size,
            va as int / size as int <= usize::MAX as int / size as int,
    ;
}

/// At the next aligned boundary, a terminal index carries into the parent slot.
pub proof fn lemma_next_slot_pte_index<C: PagingConstsTrait>(
    va: Vaddr,
    next: Vaddr,
    level: PagingLevel,
)
    requires
        1 <= level <= C::NR_LEVELS(),
        va < next <= va + page_size_spec::<C>(level),
        next % page_size_spec::<C>(level) == 0,
    ensures
        next == (nat_align_down(va as nat, page_size_spec::<C>(level) as nat)
            + page_size_spec::<C>(level)) as Vaddr,
        pte_index_spec::<C>(next, level) == 0 ==> {
            &&& pte_index_spec::<C>(va, level) + 1 == nr_subpage_per_huge::<C>()
            &&& next % page_size_spec::<C>((level + 1) as PagingLevel) == 0
        },
        pte_index_spec::<C>(next, level) != 0 ==> pte_index_spec::<C>(va, level) + 1
            < nr_subpage_per_huge::<C>(),
{
    C::lemma_paging_consts_properties();
    lemma_pte_index_spec_is_div_mod::<C>(va, level);
    lemma_pte_index_spec_is_div_mod::<C>(next, level);
    lemma_page_size_for_level_next::<C>(level);
    let size = page_size_spec::<C>(level) as int;
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
pub open spec fn vaddr_replace_pte_index_spec<C: PagingConstsTrait>(
    va: Vaddr,
    level: PagingLevel,
    index: int,
) -> Vaddr {
    (va as int + (index - pte_index_spec::<C>(va, level)) * page_size_spec::<C>(
        level,
    )) as Vaddr
}

/// Number of bits occupied by all configured page-table indices and the in-page offset.
/// This need not equal the architecture's effective virtual-address width.
#[verifier::inline]
pub open spec fn page_table_vaddr_bits_spec<C: PagingConstsTrait>() -> usize {
    (C::BASE_PAGE_SIZE().ilog2() + nr_pte_index_bits_spec::<C>() * C::NR_LEVELS()) as usize
}

/// Bits of `va` above the complete configured page-table coverage.
#[verifier::inline]
pub open spec fn vaddr_upper_bits_spec<C: PagingConstsTrait>(va: Vaddr) -> usize {
    va >> page_table_vaddr_bits_spec::<C>()
}

/// Contribution of the uninterpreted upper virtual-address bits to the concrete address.
/// Unlike the legacy fixed `leading_bits * 2^48` expression, the boundary is derived from `C`.
#[verifier::inline]
pub open spec fn vaddr_upper_part_spec<C: PagingConstsTrait>(va: Vaddr) -> int {
    vaddr_upper_bits_spec::<C>(va) as int * pow2(page_table_vaddr_bits_spec::<C>() as nat) as int
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

/// Addresses in one aligned node select the same entries at that node and above.
pub proof fn lemma_same_node_pte_indices_match<C: PagingConstsTrait>(
    va1: Vaddr,
    va2: Vaddr,
    node_start: Vaddr,
    level: PagingLevel,
)
    requires
        level < C::NR_LEVELS(),
        node_start <= va1,
        va1 < node_start + page_size_spec::<C>((level + 1) as PagingLevel),
        node_start <= va2,
        va2 < node_start + page_size_spec::<C>((level + 1) as PagingLevel),
        node_start as nat % page_size_spec::<C>((level + 1) as PagingLevel) as nat == 0,
    ensures
        pte_index_spec::<C>(va1, (level + 1) as PagingLevel) == pte_index_spec::<C>(
            va2,
            (level + 1) as PagingLevel,
        ),
        forall|i: int|
            level <= i < C::NR_LEVELS() ==> (#[trigger] pte_index_spec::<C>(
                va1,
                (i + 1) as PagingLevel,
            )) == pte_index_spec::<C>(va2, (i + 1) as PagingLevel),
{
    C::lemma_paging_consts_properties();
    let small_level = (level + 1) as PagingLevel;
    lemma_page_size_for_level_is_pow2::<C>(small_level);
    let small = page_size_spec::<C>(small_level) as int;
    let quotient = node_start as int / small;
    lemma_fundamental_div_mod(node_start as int, small);
    lemma_fundamental_div_mod_converse(va1 as int, small, quotient, va1 - node_start);
    lemma_fundamental_div_mod_converse(va2 as int, small, quotient, va2 - node_start);
    lemma_pte_index_spec_is_div_mod::<C>(va1, small_level);
    lemma_pte_index_spec_is_div_mod::<C>(va2, small_level);

    assert forall|i: int| level <= i < C::NR_LEVELS() implies (#[trigger] pte_index_spec::<C>(
        va1,
        (i + 1) as PagingLevel,
    )) == pte_index_spec::<C>(va2, (i + 1) as PagingLevel) by {
        let large_level = (i + 1) as PagingLevel;
        lemma_page_size_for_level_is_pow2::<C>(large_level);
        let delta = (nr_pte_index_bits_spec::<C>() * (i - level)) as nat;
        lemma_mul_is_distributive_sub(nr_pte_index_bits_spec::<C>() as int, i, level as int);
        assert(pte_index_bit_offset_spec::<C>(large_level) == pte_index_bit_offset_spec::<C>(
            small_level,
        ) + delta);
        lemma_pow2_adds(pte_index_bit_offset_spec::<C>(small_level) as nat, delta);
        lemma_pow2_pos(delta);
        let ratio = pow2(delta) as int;
        assert(page_size_spec::<C>(large_level) == small * ratio);
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
        level <= C::NR_LEVELS(),
        node_start <= va1,
        va1 - node_start < page_size_spec::<C>((level + 1) as PagingLevel),
        node_start <= va2,
        va2 - node_start < page_size_spec::<C>((level + 1) as PagingLevel),
        node_start as nat % page_size_spec::<C>((level + 1) as PagingLevel) as nat == 0,
    ensures
        vaddr_upper_bits_spec::<C>(va1) == vaddr_upper_bits_spec::<C>(va2),
{
    C::lemma_paging_consts_properties();
    let small_level = (level + 1) as PagingLevel;
    let body_level = (C::NR_LEVELS() + 1) as PagingLevel;
    lemma_page_size_for_level_is_pow2::<C>(small_level);
    lemma_page_size_for_level_is_pow2::<C>(body_level);
    let small = page_size_spec::<C>(small_level) as int;
    let quotient = node_start as int / small;
    lemma_fundamental_div_mod(node_start as int, small);
    lemma_fundamental_div_mod_converse(va1 as int, small, quotient, va1 - node_start);
    lemma_fundamental_div_mod_converse(va2 as int, small, quotient, va2 - node_start);
    let delta = (nr_pte_index_bits_spec::<C>() * (C::NR_LEVELS() - level)) as nat;
    lemma_mul_is_distributive_sub(
        nr_pte_index_bits_spec::<C>() as int,
        C::NR_LEVELS() as int,
        level as int,
    );
    assert(page_table_vaddr_bits_spec::<C>() == pte_index_bit_offset_spec::<C>(small_level)
        + delta);
    lemma_pow2_adds(pte_index_bit_offset_spec::<C>(small_level) as nat, delta);
    lemma_pow2_pos(delta);
    let ratio = pow2(delta) as int;
    assert(pow2(page_table_vaddr_bits_spec::<C>() as nat) == small * ratio);
    lemma_div_denominator(va1 as int, small, ratio);
    lemma_div_denominator(va2 as int, small, ratio);
    lemma_usize_shr_is_div(va1, page_table_vaddr_bits_spec::<C>());
    lemma_usize_shr_is_div(va2, page_table_vaddr_bits_spec::<C>());
}

/// Upper address bits contribute the aligned base of the complete paging body.
pub proof fn lemma_vaddr_upper_part_is_align_down<C: PagingConstsTrait>(va: Vaddr)
    ensures
        vaddr_upper_part_spec::<C>(va) == nat_align_down(
            va as nat,
            page_size_spec::<C>((C::NR_LEVELS() + 1) as PagingLevel) as nat,
        ),
{
    C::lemma_paging_consts_properties();
    let level = (C::NR_LEVELS() + 1) as PagingLevel;
    lemma_page_size_for_level_is_pow2::<C>(level);
    lemma_usize_shr_is_div(va, page_table_vaddr_bits_spec::<C>());
    lemma_fundamental_div_mod(va as int, page_size_spec::<C>(level) as int);
    vstd::arithmetic::mul::lemma_mul_is_commutative(
        page_size_spec::<C>(level) as int,
        vaddr_upper_bits_spec::<C>(va) as int,
    );
}

/// Aligning down preserves all indices at and above the slot and the upper address bits.
pub proof fn lemma_align_down_indices<C: PagingConstsTrait>(va: Vaddr, level: PagingLevel)
    requires
        1 <= level <= C::NR_LEVELS(),
    ensures
        ({
            let aligned = nat_align_down(
                va as nat,
                page_size_spec::<C>(level) as nat,
            ) as Vaddr;
            &&& aligned % C::BASE_PAGE_SIZE() == 0
            &&& vaddr_upper_bits_spec::<C>(aligned) == vaddr_upper_bits_spec::<C>(va)
            &&& forall|i: int|
                1 <= i <= C::NR_LEVELS() ==> #[trigger] pte_index_spec::<C>(
                    aligned,
                    i as PagingLevel,
                ) == if i < level {
                    0
                } else {
                    pte_index_spec::<C>(va, i as PagingLevel)
                }
        }),
{
    lemma_page_size_for_level_is_pow2::<C>(level);
    let size = page_size_spec::<C>(level) as nat;
    lemma_nat_align_down_sound(va as nat, size);
    let aligned = nat_align_down(va as nat, size) as Vaddr;
    lemma_aligned_indices_zero::<C>(aligned, level);
    lemma_same_node_pte_indices_match::<C>(va, aligned, aligned, (level - 1) as PagingLevel);
    lemma_same_node_vaddr_upper_bits_match::<C>(va, aligned, aligned, (level - 1) as PagingLevel);
    assert forall|i: int| 1 <= i <= C::NR_LEVELS() implies #[trigger] pte_index_spec::<C>(
        aligned,
        i as PagingLevel,
    ) == if i < level {
        0
    } else {
        pte_index_spec::<C>(va, i as PagingLevel)
    } by {
        if i >= level {
            assert((level - 1) < i);
            assert(pte_index_spec::<C>(va, ((i - 1) + 1) as PagingLevel) == pte_index_spec::<C>(
                aligned,
                ((i - 1) + 1) as PagingLevel,
            ));
        }
    };
}

/// Advancing a nonterminal slot preserves every other index and cannot wrap the machine word.
pub proof fn lemma_inc_slot_indices<C: PagingConstsTrait>(va: Vaddr, level: PagingLevel)
    requires
        1 <= level <= C::NR_LEVELS(),
        pte_index_spec::<C>(va, level) + 1 < nr_subpage_per_huge::<C>(),
    ensures
        va + page_size_spec::<C>(level) <= usize::MAX,
        ({
            let next = (va + page_size_spec::<C>(level)) as Vaddr;
            &&& next % C::BASE_PAGE_SIZE() == va % C::BASE_PAGE_SIZE()
            &&& vaddr_upper_bits_spec::<C>(next) == vaddr_upper_bits_spec::<C>(va)
            &&& forall|i: int|
                1 <= i <= C::NR_LEVELS() ==> #[trigger] pte_index_spec::<C>(next, i as PagingLevel)
                    == pte_index_spec::<C>(va, i as PagingLevel) + if i == level {
                    1int
                } else {
                    0int
                }
        }),
{
    C::lemma_paging_consts_properties();
    lemma_page_size_for_level_next::<C>(level);
    lemma_pte_index_spec_is_div_mod::<C>(va, level);
    let size = page_size_spec::<C>(level) as int;
    let parent_size = page_size_spec::<C>((level + 1) as PagingLevel) as int;
    let fanout = nr_subpage_per_huge::<C>() as int;
    let index = pte_index_spec::<C>(va, level) as int;
    lemma_nat_align_down_sound(va as nat, parent_size as nat);
    let start = nat_align_down(va as nat, parent_size as nat) as Vaddr;
    lemma_aligned_vaddr_slack::<C>(start, (level + 1) as PagingLevel);
    vstd::arithmetic::div_mod::lemma_mod_breakdown(va as int, size, fanout);
    vstd::arithmetic::div_mod::lemma_mod_bound(va as int, size);
    assert(index == va as int / size % fanout);
    assert(va as int % parent_size == size * index + va as int % size);
    vstd::arithmetic::div_mod::lemma_mod_bound(va as int, parent_size);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(va as int, parent_size);
    lemma_fundamental_div_mod(va as int, parent_size);
    assert(va - start == va as int % parent_size);
    assert(va - start + size < parent_size) by (nonlinear_arith)
        requires
            va - start == size * index + va as int % size,
            0 <= va as int % size < size,
            index + 1 < fanout,
            parent_size == size * fanout,
    ;
    let next = (va + size) as Vaddr;
    lemma_fundamental_div_mod(va as int, size);
    vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(size, va as int / size, 1);
    lemma_fundamental_div_mod_converse(next as int, size, va as int / size + 1, va as int % size);
    lemma_pte_index_spec_is_div_mod::<C>(next, level);
    vstd::arithmetic::div_mod::lemma_add_mod_noop_right(1, va as int / size, fanout);
    vstd::arithmetic::div_mod::lemma_small_mod((index + 1) as nat, fanout as nat);
    assert(pte_index_spec::<C>(next, level) == index + 1);
    if level < C::NR_LEVELS() {
        lemma_same_node_pte_indices_match::<C>(va, next, start, level);
    }
    lemma_same_node_vaddr_upper_bits_match::<C>(va, next, start, level);
    lemma_page_size_for_level_divides::<C>(1, level);
    lemma_page_size_for_level_base::<C>();
    vstd::arithmetic::div_mod::lemma_add_mod_noop(va as int, size, C::BASE_PAGE_SIZE() as int);
    vstd::arithmetic::div_mod::lemma_mod_twice(va as int, C::BASE_PAGE_SIZE() as int);
    assert(next % C::BASE_PAGE_SIZE() == va % C::BASE_PAGE_SIZE());
    assert forall|i: int| 1 <= i < level implies #[trigger] pte_index_spec::<C>(
        next,
        i as PagingLevel,
    ) == pte_index_spec::<C>(va, i as PagingLevel) by {
        let lower = i as PagingLevel;
        let parent = (i + 1) as PagingLevel;
        lemma_page_size_for_level_divides::<C>(parent, level);
        lemma_page_size_for_level_next::<C>(lower);
        let small = page_size_spec::<C>(lower) as int;
        let block = page_size_spec::<C>(parent) as int;
        vstd::arithmetic::div_mod::lemma_add_mod_noop(va as int, size, block);
        vstd::arithmetic::div_mod::lemma_mod_twice(va as int, block);
        assert(next as int % block == va as int % block);
        vstd::arithmetic::div_mod::lemma_mod_mod(va as int, small, fanout);
        vstd::arithmetic::div_mod::lemma_mod_mod(next as int, small, fanout);
        vstd::arithmetic::div_mod::lemma_mod_breakdown(va as int, small, fanout);
        vstd::arithmetic::div_mod::lemma_mod_breakdown(next as int, small, fanout);
        lemma_pte_index_spec_is_div_mod::<C>(va, lower);
        lemma_pte_index_spec_is_div_mod::<C>(next, lower);
        assert(next as int % small == va as int % small);
        assert(small * pte_index_spec::<C>(next, lower) == small * pte_index_spec::<C>(va, lower));
        assert(pte_index_spec::<C>(next, lower) == pte_index_spec::<C>(va, lower))
            by (nonlinear_arith)
            requires
                small > 0,
                small * pte_index_spec::<C>(next, lower) == small * pte_index_spec::<C>(va, lower),
        ;
    };
    assert forall|i: int| 1 <= i <= C::NR_LEVELS() implies #[trigger] pte_index_spec::<C>(
        next,
        i as PagingLevel,
    ) == pte_index_spec::<C>(va, i as PagingLevel) + if i == level {
        1int
    } else {
        0int
    } by {
        if i > level {
            assert(level < C::NR_LEVELS());
            assert(pte_index_spec::<C>(va, ((i - 1) + 1) as PagingLevel) == pte_index_spec::<C>(
                next,
                ((i - 1) + 1) as PagingLevel,
            ));
        }
    };
}

} // verus!
