// SPDX-License-Identifier: MPL-2.0
use vstd::prelude::*;
use vstd_extra::external::uefi::{
    allocate_loader_pages, into_loader_slice, panic_on_loader_allocation_error,
};

use core::mem::MaybeUninit;

use uefi::boot::AllocateType;

pub fn alloc_at(addr: usize, size: usize) -> &'static mut [MaybeUninit<u8>] {
    assert_ne!(addr, 0, "the address to allocate is zero");
    assert!(
        addr.checked_add(size).is_some(),
        "the range to allocate overflows"
    );

    let allocated = alloc_pages(AllocateType::Address(addr as u64), size);
    assert_eq!(
        allocated.as_ptr().addr(),
        addr,
        "the allocated address is not the request address"
    );

    allocated
}

#[verus_spec(ret =>
    requires size <= isize::MAX,
    ensures ret@.len() == size,
)]
pub(super) fn alloc_pages(ty: AllocateType, size: usize) -> &'static mut [MaybeUninit<u8>] {
    assert!(
        size <= isize::MAX as usize,
        "the size to allocate exceeds `isize::MAX`"
    );

    let (allocation, pages) =
        allocate_loader_pages(ty, size.div_ceil(super::efi::PAGE_SIZE as usize));
    let allocated = match allocation {
        Ok(allocated) => allocated,
        Err(error) => panic_on_loader_allocation_error(error),
    };
    proof! {
        let page_size = super::efi::PAGE_SIZE as int;
        let rounded_size = (size + page_size - 1) / page_size * page_size;
        assert(size <= rounded_size < size + page_size);
    }
    // SAFETY: The firmware allocation covers this prefix, and the slice consumes
    // the exclusive permission. The setup never frees its loader pages.
    verus_exec_expr!(unsafe {
        into_loader_slice(
            allocated.as_ptr().cast(),
            size,
            Tracked(pages.get().tracked_unwrap()),
        )
    })
}
