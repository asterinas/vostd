pub mod frame;
pub(crate) mod page_prop;
pub mod page_table;
pub mod vm_space;

use std::ops::Range;

use vstd::arithmetic::logarithm::*;
use vstd::arithmetic::power::pow;
use vstd::arithmetic::power2::pow2;
use vstd::bits::*;
use vstd::layout::is_power_2;
use vstd::prelude::*;
pub use page_table::*;
pub use page_table::node::*;
pub use frame::*;

use crate::helpers::extra_num::lemma_pow2_is_power2_to64;
use crate::helpers::math::lemma_page_shl;

verus! {

/// Virtual addresses.
pub type Vaddr = usize;

/// Physical addresses.
pub type Paddr = usize;

/// The level of a page table node or a frame.
pub type PagingLevel = u8;

// TODO: Formalize these constants
pub const NR_ENTRIES: usize = 512;

pub const NR_LEVELS: usize = 4;

pub const PAGE_SIZE: usize = 4096;

pub const BASE_PAGE_SIZE: usize = 4096;

pub const PTE_SIZE: usize = 8;

/// The page size
// pub const PAGE_SIZE: usize = page_size::<PagingConsts>(1);
pub open spec fn page_size_spec<C: PagingConstsTrait>(level: PagingLevel) -> usize
    recommends
        level > 0 && level <= NR_LEVELS,
{
    // C::BASE_PAGE_SIZE << (nr_subpage_per_huge::<C>().ilog2() as usize * (level as usize - 1))
    match level {
        1 => BASE_PAGE_SIZE,
        2 => ((BASE_PAGE_SIZE as u64) << 9) as usize,
        3 => ((BASE_PAGE_SIZE as u64) << 18) as usize,
        4 => ((BASE_PAGE_SIZE as u64) << 27) as usize,
        _ => 0,
    }
}

/// The page size at a given level.
// TODO: Formalize page_size
#[verifier::when_used_as_spec(page_size_spec)]
pub const fn page_size<C: PagingConstsTrait>(level: PagingLevel) -> (res: usize)
    requires
        level > 0 && level <= NR_LEVELS,
    ensures
        res != 0,
        res == page_size_spec::<C>(level),
        is_power_2(res as int),
{
    // C::BASE_PAGE_SIZE << (nr_subpage_per_huge::<C>().ilog2() as usize * (level as usize - 1))
    let t = nr_subpage_per_huge().ilog2() as u64;
    assert(t == 9) by {
        assert(nr_subpage_per_huge() == 512);
        assert(log(2, 512) == 9) by {
            assert(512 == pow(2, 9)) by (compute_only);
            assert(log(2, 512) == 9) by { lemma_log_pow(2, 9) }
        }
    };
    let l = level as u64 - 1;
    assert(0 <= l < NR_LEVELS);
    assert(t * l == 0 || t * l == 9 || t * l == 18 || t * l == 27) by {
        assert(l == 0 || l == 1 || l == 2 || l == 3);
    };
    let res = (BASE_PAGE_SIZE as u64) << (t * l);
    proof {
        lemma_page_shl();
    }
    assert(res != 0);
    match level {
        1 => assert(res == BASE_PAGE_SIZE) by {
            assert(t * l == 0);
        },
        2 => assert(res == ((BASE_PAGE_SIZE as u64) << 9) as usize),
        3 => assert(res == ((BASE_PAGE_SIZE as u64) << 18) as usize),
        4 => assert(res == ((BASE_PAGE_SIZE as u64) << 27) as usize),
        _ => assert(false),
    };
    proof {
        lemma_pow2_is_power2_to64();
    }
    res as usize
}

pub open spec fn nr_subpage_per_huge_spec() -> usize {
    // C::BASE_PAGE_SIZE / C::PTE_SIZE
    BASE_PAGE_SIZE / PTE_SIZE
}

/// The number of sub pages in a huge page.
#[verifier::when_used_as_spec(nr_subpage_per_huge_spec)]
pub const fn nr_subpage_per_huge() -> (res: usize)
    ensures
        res != 0,
        res == nr_subpage_per_huge_spec(),
        res == BASE_PAGE_SIZE / PTE_SIZE,
{
    // C::BASE_PAGE_SIZE / C::PTE_SIZE
    BASE_PAGE_SIZE / PTE_SIZE
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
pub const MAX_USERSPACE_VADDR: Vaddr = 0x0000_8000_0000_0000 - PAGE_SIZE;

/// The kernel address space.
///
/// There are the high canonical addresses defined in most 48-bit width
/// architectures.
pub const KERNEL_VADDR_RANGE: Range<Vaddr> = 0xffff_8000_0000_0000..0xffff_ffff_ffff_0000;

} // verus!
