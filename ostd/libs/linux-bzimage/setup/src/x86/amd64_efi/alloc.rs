// SPDX-License-Identifier: MPL-2.0
use vstd::prelude::*;
use vstd_extra::external::uefi::{LoaderPages, panic_on_expect_error};

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

    /* Keep the firmware result separate from the tracked page permission and its error path.
     * Origin Rust:
     * let allocated = uefi::boot::allocate_pages(
     *     ty,
     *     uefi::boot::MemoryType::LOADER_DATA,
     *     size.div_ceil(super::efi::PAGE_SIZE as usize),
     * )
     * .expect("the UEFI allocation fails");
     */
    proof_decl! { let tracked pages: Option<LoaderPages>; }
    // The qualified path lets proof_with! resolve the generated verifier function.
    proof_with! { => Tracked(pages) }
    let allocation = vstd_extra::external::uefi::allocate_loader_pages(
        ty,
        size.div_ceil(super::efi::PAGE_SIZE as usize),
    );
    let allocated = match allocation {
        Ok(allocated) => allocated,
        Err(error) => panic_on_expect_error(Err(error), "the UEFI allocation fails"),
    };
    /* Check the exact pointer passed to the raw slice constructor.
     * Origin Rust:
     * unsafe { core::slice::from_raw_parts_mut(allocated.as_ptr().cast(), size) }
     */
    let ptr = allocated.as_ptr().cast::<MaybeUninit<u8>>();
    proof! {
        let page_size = super::efi::PAGE_SIZE as int;
        let rounded_size = (size + page_size - 1) / page_size * page_size;
        assert(size <= rounded_size < size + page_size);

        // Keep these checks when stripping proofs. The raw-slice spec leaves
        // non-nullness, bounds, range coverage, and provenance to its caller.
        let tracked pages = pages.tracked_unwrap();
        assert(ptr.addr() != 0);
        assert(ptr.addr() + size <= usize::MAX);
        assert(pages.permission().contains_range(ptr.addr() as int, size as int));
        assert(pages.permission().provenance() == ptr@.provenance);
    }

    // SAFETY:
    // 1. The address is not zero and the size is reasonable (there are less the `isize::MAX` bytes
    //    and the range won't overflow the address space), as asserted above or guaranteed by the
    //    implementation of `allocate_pages`.
    // 2. The memory region is allocated via the UEFI firmware, so it is valid for reading and
    //    writing. We will not deallocate it, so it live for `'static`.
    // 3. The type alignment is 1 and the type can contain uninitialized data.
    unsafe { core::slice::from_raw_parts_mut(ptr, size) }
}
