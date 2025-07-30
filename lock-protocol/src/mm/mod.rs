pub mod frame;
pub(crate) mod page_prop;
pub mod page_table;
pub mod vm_space;

use std::ops::Range;

pub use page_table::*;
pub use page_table::node::*;
pub use frame::*;

use vstd::arithmetic::power2::lemma_pow2_pos;
use vstd::prelude::*;
use vstd::{
    arithmetic::{div_mod::lemma_div_non_zero, logarithm::*, power::pow, power2::*},
    bits::*,
    layout::is_power_2,
};
use vstd_extra::extra_num::{
    lemma_pow2_increases, lemma_pow2_is_power2, lemma_pow2_is_power2_to64,
    lemma_usize_ilog2_ordered, lemma_usize_is_power_2_is_ilog2_pow2, lemma_usize_pow2_ilog2,
    lemma_usize_pow2_shl_is_pow2, lemma_usize_shl_is_mul,
};
use crate::helpers::math::lemma_page_shl;

verus! {

/// Virtual addresses.
pub type Vaddr = usize;

/// Physical addresses.
pub type Paddr = usize;

/// The level of a page table node or a frame.
pub type PagingLevel = u8;

pub const NR_ENTRIES: usize = 512;

pub const NR_LEVELS: usize = 4;

//pub const PAGE_SIZE: usize = 4096;
pub const BASE_PAGE_SIZE: usize = 4096;

pub const PTE_SIZE: usize = 8;

pub open spec fn page_size_spec<C: PagingConstsTrait>(level: PagingLevel) -> usize
    recommends
        1 <= level <= C::NR_LEVELS(),
{
    pow2(
        (C::BASE_PAGE_SIZE().ilog2() + (C::BASE_PAGE_SIZE().ilog2() - C::PTE_SIZE().ilog2()) * (
        level - 1)) as nat,
    ) as usize
}

pub proof fn lemma_page_size_spec_properties<C: PagingConstsTrait>(level: PagingLevel)
    requires
        1 <= level <= C::NR_LEVELS(),
    ensures
        page_size_spec::<C>(level) > 0,
        is_power_2(page_size_spec::<C>(level) as int),
{
    C::lemma_consts_properties();
    C::lemma_consts_properties_derived();

    let subpage_bits = C::BASE_PAGE_SIZE().ilog2() - C::PTE_SIZE().ilog2();

    assert(subpage_bits >= 0);
    assert((C::BASE_PAGE_SIZE().ilog2() + subpage_bits * (level - 1)) <= (
    C::BASE_PAGE_SIZE().ilog2() + subpage_bits * C::NR_LEVELS())) by (nonlinear_arith)
        requires
            level <= C::NR_LEVELS(),
            subpage_bits >= 0,
    ;
    lemma_pow2_increases(
        (C::BASE_PAGE_SIZE().ilog2() + subpage_bits * (level as usize - 1)) as nat,
        (C::BASE_PAGE_SIZE().ilog2() + subpage_bits * C::NR_LEVELS()) as nat,
    );
    lemma_pow2_adds(
        C::BASE_PAGE_SIZE().ilog2() as nat,
        (subpage_bits * (level as usize - 1)) as nat,
    );
    assert(C::BASE_PAGE_SIZE() == pow2(C::BASE_PAGE_SIZE().ilog2() as nat));
    assert(pow2(
        (C::BASE_PAGE_SIZE().ilog2() + (C::BASE_PAGE_SIZE().ilog2() - C::PTE_SIZE().ilog2()) * (
        level - 1)) as nat,
    ) <= usize::MAX);
    lemma_pow2_pos(
        (C::BASE_PAGE_SIZE().ilog2() + (C::BASE_PAGE_SIZE().ilog2() - C::PTE_SIZE().ilog2()) * (
        level - 1)) as nat,
    );
    lemma_pow2_is_power2(
        (C::BASE_PAGE_SIZE().ilog2() + (C::BASE_PAGE_SIZE().ilog2() - C::PTE_SIZE().ilog2()) * (
        level - 1)) as nat,
    );
}

/// The page size
// pub const PAGE_SIZE: usize = page_size::<PagingConsts>(1);
#[verifier::allow_in_spec]
pub fn PAGE_SIZE() -> (res: usize)
    ensures
        0 < res == page_size_spec::<PagingConsts>(1),
    returns
        4096usize,
{
    proof {
        PagingConsts::lemma_consts_properties();
        PagingConsts::lemma_consts_properties_derived();
        assert(PagingConsts::BASE_PAGE_SIZE() == 4096);
    }
    page_size::<PagingConsts>(1)
}

/// The page size at a given level.
#[verifier::when_used_as_spec(page_size_spec)]
pub fn page_size<C: PagingConstsTrait>(level: PagingLevel) -> (res: usize)
    requires
        1 <= level <= C::NR_LEVELS(),
    ensures
        res > 0,
        is_power_2(res as int),
    returns
        page_size_spec::<C>(level),
{
    proof {
        C::lemma_consts_properties();
        C::lemma_consts_properties_derived();

        let subpage_bits = nr_subpage_per_huge::<C>().ilog2();

        assert(subpage_bits == C::BASE_PAGE_SIZE().ilog2() - C::PTE_SIZE().ilog2()) by {
            lemma_usize_pow2_ilog2((C::BASE_PAGE_SIZE().ilog2() - C::PTE_SIZE().ilog2()) as u32);
        }
        assert(subpage_bits * (level as usize - 1) < usize::BITS) by (nonlinear_arith)
            requires
                1 <= level <= C::NR_LEVELS(),
                0 <= subpage_bits,
                C::BASE_PAGE_SIZE().ilog2() + subpage_bits * C::NR_LEVELS() < usize::BITS,
        ;
        assert(C::BASE_PAGE_SIZE() * pow2((subpage_bits * (level as usize - 1)) as nat)
            <= usize::MAX) by {
            assert(subpage_bits * (level as usize - 1) <= subpage_bits * C::NR_LEVELS())
                by (nonlinear_arith)
                requires
                    1 <= level <= C::NR_LEVELS(),
                    0 < nr_subpage_per_huge::<C>(),
            ;
            lemma_pow2_increases(
                (subpage_bits * (level as usize - 1)) as nat,
                (subpage_bits * C::NR_LEVELS()) as nat,
            );
            assert(C::BASE_PAGE_SIZE() * pow2((subpage_bits * (level as usize - 1)) as nat)
                <= C::BASE_PAGE_SIZE() * pow2((subpage_bits * C::NR_LEVELS()) as nat))
                by (nonlinear_arith)
                requires
                    0 < C::BASE_PAGE_SIZE(),
                    pow2((subpage_bits * (level as usize - 1)) as nat) <= pow2(
                        (subpage_bits * C::NR_LEVELS()) as nat,
                    ),
            ;
        };
        lemma_usize_shl_is_mul(
            C::BASE_PAGE_SIZE(),
            (subpage_bits as usize * (level as usize - 1)) as usize,
        );
        lemma_pow2_adds(
            C::BASE_PAGE_SIZE().ilog2() as nat,
            (subpage_bits * (level as usize - 1)) as nat,
        );

        assert(C::BASE_PAGE_SIZE() << (nr_subpage_per_huge::<C>().ilog2() as usize * (level as usize
            - 1)) == page_size_spec::<C>(level));
        lemma_page_size_spec_properties::<C>(level);
    }
    C::BASE_PAGE_SIZE() << (nr_subpage_per_huge::<C>().ilog2() as usize * (level as usize - 1))
}

/// The number of sub pages in a huge page.
#[verifier::allow_in_spec]
pub fn nr_subpage_per_huge<C: PagingConstsTrait>() -> (res: usize)
    ensures
        res > 0,
        res == pow2((C::BASE_PAGE_SIZE().ilog2() - C::PTE_SIZE().ilog2()) as nat) as usize,
    returns
        C::BASE_PAGE_SIZE() / C::PTE_SIZE(),
{
    proof {
        C::lemma_consts_properties();
        C::lemma_consts_properties_derived();
    }
    C::BASE_PAGE_SIZE() / C::PTE_SIZE()
}

/// The maximum virtual address of user space (non inclusive).
///
/// Typical 64-bit systems have at least 48-bit virtual address space.
/// A typical way to reserve half of the address space for the kernel is
/// to use the highest 48-bit virtual address space.
///
/// Also, the top page is not regarded as usable since it's a workaround
/// for some x86_64 CPUs' bugs. See
/// <https://github.com/torvalds/linux/blob/480e035fc4c714fb5536e64ab9db04fedc89e910/arch/x86/include/asm/page_64.h#L68-L78>
/// for the rationale.
pub const MAX_USERSPACE_VADDR: Vaddr = 0x0000_8000_0000_0000 - 4096;

/// The kernel address space.
///
/// There are the high canonical addresses defined in most 48-bit width
/// architectures.
pub const KERNEL_VADDR_RANGE: Range<Vaddr> = 0xffff_8000_0000_0000..0xffff_ffff_ffff_0000;

} // verus!
