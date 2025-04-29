use vstd::prelude::*;
use core::ops::Range;
use crate::x86_64::mm::PAGE_SIZE;
use crate::mm::Vaddr;
use super::{TlbModel, TlbFlushOp, align::*};

verus! {

/// Flush any TLB entry that contains the map of the given virtual address.
///
/// This flush performs regardless of the global-page bit. So it can flush both global
/// and non-global entries.
#[verifier::external_body]
pub fn tlb_flush_addr(vaddr: Vaddr, Tracked(tlb): Tracked<TlbModel>) -> (res: Tracked<TlbModel>)
    requires
        va_is_aligned(vaddr as int),
    ensures
        res@ =~= tlb.flush_va(vaddr as int),
{
    // tlb::flush(VirtAddr::new(vaddr as u64));
    unimplemented!()
}

/// Flush any TLB entry that intersects with the given address range.
// TODO:
#[verifier::external_body]
pub fn tlb_flush_addr_range(range: &Range<Vaddr>, Tracked(tlb): Tracked<TlbModel>) -> (res: Tracked<
    TlbModel,
>)
    requires
        range.start <= range.end,
        va_set_is_aligned(TlbFlushOp::range_to_set(range)),
    ensures
        res@ =~= tlb.flush_va_set(va_set_expansion(TlbFlushOp::range_to_set(range))),
{
    let mut vaddr = range.start;
    while vaddr < range.end
        invariant
            va_is_aligned(vaddr as int),
    {
        let res = tlb_flush_addr(vaddr, Tracked(tlb));
        vaddr += PAGE_SIZE();
    }

    unimplemented!()
}

/// Flush all TLB entries except for the global-page entries.
#[verifier::external_body]
pub fn tlb_flush_all_excluding_global(Tracked(tlb): Tracked<TlbModel>) -> (res: Tracked<TlbModel>)
    ensures
        res@ =~= tlb.clear(),
{
    // tlb::flush_all();
    unimplemented!()
}

/// Flush all TLB entries, including global-page entries.
#[verifier::external_body]
pub fn tlb_flush_all_including_global(Tracked(tlb): Tracked<TlbModel>) -> (res: Tracked<TlbModel>)
    ensures
        res@ =~= tlb.clear(),
{
    // SAFETY: updates to CR4 here only change the global-page bit, the side effect
    // is only to invalidate the TLB, which doesn't affect the memory safety.
    // unsafe {
    //     // To invalidate all entries, including global-page
    //     // entries, disable global-page extensions (CR4.PGE=0).
    //     x86_64::registers::control::Cr4::update(|cr4| {
    //         *cr4 -= x86_64::registers::control::Cr4Flags::PAGE_GLOBAL;
    //     });
    //     x86_64::registers::control::Cr4::update(|cr4| {
    //         *cr4 |= x86_64::registers::control::Cr4Flags::PAGE_GLOBAL;
    //     });
    // }
    unimplemented!()
}

} // verus!
