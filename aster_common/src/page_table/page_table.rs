use vstd::prelude::*;
use vstd::arithmetic::div_mod::*;
use vstd_extra::extra_num::*;

use crate::prelude::*;

use core::marker::PhantomData;

verus! {

#[derive(Debug)]
#[rustc_has_incoherent_inherent_impls]
pub struct PageTable<M: PageTableMode> {
    pub root: RawPageTableNode,
    pub _phantom: PhantomData<M>,
}

} // verus!
verus! {

#[verifier::inline]
pub open spec fn nr_subpage_per_huge_spec<C: PagingConstsTrait>() -> usize {
    C::BASE_PAGE_SIZE() / C::PTE_SIZE()
}

/// The number of sub pages in a huge page.
#[inline(always)]
#[verifier::when_used_as_spec(nr_subpage_per_huge_spec)]
pub fn nr_subpage_per_huge<C: PagingConstsTrait>() -> (res: usize)
    ensures
        res == nr_subpage_per_huge_spec::<C>(),
        res > 0,
{
    proof {
        assume(C::BASE_PAGE_SIZE() / C::PTE_SIZE() > 0);
    }
    C::BASE_PAGE_SIZE() / C::PTE_SIZE()
}

pub proof fn lemma_nr_subpage_per_huge_bounded<C: PagingConstsTrait>()
    ensures
        0 < nr_subpage_per_huge::<C>() <= C::BASE_PAGE_SIZE(),
{
    C::lemma_PTE_SIZE_properties();
    broadcast use group_div_basics;

    assert(C::PTE_SIZE() <= C::BASE_PAGE_SIZE());
    assert(C::BASE_PAGE_SIZE() / C::PTE_SIZE() <= C::BASE_PAGE_SIZE());
    assert(C::BASE_PAGE_SIZE() / C::PTE_SIZE() > 0) by {
        lemma_div_non_zero(C::BASE_PAGE_SIZE() as int, C::PTE_SIZE() as int);
    };
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

} // verus!
verus! {

pub proof fn bits_of_base_page_size()
    ensures
        PagingConsts::BASE_PAGE_SIZE().ilog2() == 12,
{
    lemma_usize_ilog2_to32();
}

pub proof fn value_of_nr_subpage_per_huge()
    ensures
        nr_subpage_per_huge::<PagingConsts>() == 512,
{
}

pub proof fn bits_of_nr_pte_index()
    ensures
        nr_pte_index_bits::<PagingConsts>() == 9,
{
    value_of_nr_subpage_per_huge();
    lemma_usize_ilog2_to32();
}

#[verifier::inline]
pub open spec fn pte_index_mask_spec() -> usize {
    0x1ff
}

#[inline(always)]
#[verifier::when_used_as_spec(pte_index_mask_spec)]
pub fn pte_index_mask() -> (res: usize)
    ensures
        res == pte_index_mask_spec(),
{
    nr_subpage_per_huge::<PagingConsts>() - 1
}

pub open spec fn pte_index_spec(va: Vaddr, level: PagingLevel) -> usize
    recommends
        0 < level <= PagingConsts::NR_LEVELS(),
{
    let base_bits = PagingConsts::BASE_PAGE_SIZE().ilog2();
    let index_bits = nr_pte_index_bits::<PagingConsts>();
    let shift = base_bits + (level - 1) as u32 * index_bits as u32;
    (va >> shift) & pte_index_mask()
}

#[verifier::when_used_as_spec(pte_index_spec)]
pub fn pte_index(va: Vaddr, level: PagingLevel) -> (res: usize)
    requires
        0 < level <= PagingConsts::NR_LEVELS(),
    ensures
        res == pte_index_spec(va, level),
{
    let base_bits = PagingConsts::BASE_PAGE_SIZE().ilog2();
    assert(base_bits == 12) by {
        bits_of_base_page_size();
    };
    let index_bits = nr_pte_index_bits::<PagingConsts>();
    assert(index_bits == 9) by {
        bits_of_nr_pte_index();
    };
    assert(0 <= (level - 1) * index_bits <= 36);
    let shift = base_bits + (level - 1) as u32 * index_bits as u32;
    (va >> shift) & pte_index_mask()
}

pub proof fn pte_index_preserves_order(va1: Vaddr, va2: Vaddr, level: PagingLevel)
    requires
        va1 <= va2,
    ensures
        pte_index(va1, level) <= pte_index(va2, level),
{
    admit()
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PageTableError {
    /// The provided virtual address range is invalid.
    InvalidVaddrRange(Vaddr, Vaddr),
    /// The provided virtual address is invalid.
    InvalidVaddr(Vaddr),
    /// Using virtual address not aligned.
    UnalignedVaddr,
}

} // verus!
