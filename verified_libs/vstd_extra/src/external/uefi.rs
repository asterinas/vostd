// SPDX-License-Identifier: MPL-2.0
//! UEFI 0.32.0 boot services used by the x86 bzImage setup.
//!
//! The loaded-image read borrows the options held by the current protocol.
//! The setup sets the image handle before using these services and drops the
//! protocol before exiting boot services. UEFI can panic if either boot-phase
//! prerequisite is violated independently of a firmware error return.
//!
//! AllocatePages transfers exclusive access to the successful LoaderData range
//! (UEFI 2.10, sections 7.2.1 and 7.2.2). Turning its permission into a slice
//! permanently gives up the ability to FreePages from the setup. The setup
//! keeps these ranges until control passes to the kernel.
use core::{convert::Infallible, mem::MaybeUninit, ops::Deref, ptr::NonNull};

use ::uefi::{
    Handle, Identify,
    boot::{self, AllocateType, MemoryType, ScopedProtocol},
    proto::{Protocol, ProtocolPointer, loaded_image::LoadedImage},
};
use vstd::{prelude::*, raw_ptr::PointsToRaw};

verus! {

#[verifier::external_type_specification]
pub struct ExAllocateType(AllocateType);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(D)]
pub struct ExUefiError<D: core::fmt::Debug>(::uefi::Error<D>);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExHandle(Handle);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExLoadedImage(LoadedImage);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(P)]
pub struct ExScopedProtocol<P: Protocol + ?Sized>(ScopedProtocol<P>);

#[verifier::external_trait_specification]
pub trait ExIdentify {
    type ExternalTraitSpecificationFor: Identify;
}

#[verifier::external_trait_specification]
pub trait ExProtocol: Identify {
    type ExternalTraitSpecificationFor: Protocol;
}

#[verifier::external_trait_specification]
pub trait ExProtocolPointer: Protocol {
    type ExternalTraitSpecificationFor: ProtocolPointer;
}

pub assume_specification[ boot::image_handle ]() -> Handle
;

pub assume_specification<P: ProtocolPointer + ?Sized>[ boot::open_protocol_exclusive::<P> ](
    handle: Handle,
) -> ::uefi::Result<ScopedProtocol<P>>
;

pub assume_specification<'a, P: Protocol + ?Sized>[ <ScopedProtocol<P> as Deref>::deref ](
    scope: &'a ScopedProtocol<P>,
) -> &'a <ScopedProtocol<P> as Deref>::Target
;

pub assume_specification<'a>[ LoadedImage::load_options_as_bytes ](image: &'a LoadedImage) -> (ret:
    Option<&'a [u8]>)
    ensures
        ret matches Some(bytes) ==> bytes@.len() <= u32::MAX && bytes@.len() <= isize::MAX,
    opens_invariants none
    no_unwind
;

pub assume_specification[ ::uefi::helpers::_print ](args: core::fmt::Arguments<'_>)
;

pub assume_specification[ boot::PAGE_SIZE ] -> usize
    returns
        4096usize,
;

pub tracked struct LoaderPages {
    points_to: PointsToRaw,
}

impl LoaderPages {
    pub closed spec fn permission(self) -> PointsToRaw {
        self.points_to
    }
}

} // verus!
#[verifier::external_body]
#[verus_spec(ret =>
    ensures
        (ret.0 is Ok) <==> (ret.1@ is Some),
        ret.0 matches Ok(ptr) ==> {
            let addr = ptr.as_ptr().addr();
            let len = count as int * boot::PAGE_SIZE;
            let pages = ret.1@->0;
            &&& addr != 0
            &&& addr + len <= usize::MAX
            &&& pages.permission().is_range(addr as int, len)
            &&& pages.permission().provenance() == ptr.as_ptr()@.provenance
            &&& (ty matches AllocateType::MaxAddress(max) ==> count == 0 || addr + len - 1 <= max)
            &&& (ty matches AllocateType::Address(requested) ==> count == 0 || addr == requested)
        },
)]
pub fn allocate_loader_pages(
    ty: AllocateType,
    count: usize,
) -> (::uefi::Result<NonNull<u8>>, Tracked<Option<LoaderPages>>) {
    (
        boot::allocate_pages(ty, MemoryType::LOADER_DATA, count),
        Tracked::assume_new(),
    )
}

/// Borrows a range of an EFI loader allocation for the lifetime of the setup.
///
/// # Safety
///
/// The pointer must have the provenance of the firmware allocation represented
/// by the consumed permission. The requested range must fit in that allocation
/// and in Rust's slice size limit. No reference or FreePages call may alias the
/// range while the returned borrow is live.
#[verus_spec(ret =>
    requires
        ptr.addr() != 0,
        ptr@.provenance == pages@.permission().provenance(),
        pages@.permission().contains_range(ptr.addr() as int, len as int),
        len <= isize::MAX,
        ptr.addr() + len <= usize::MAX,
    ensures ret@.len() == len,
    no_unwind
)]
pub unsafe fn into_loader_slice(
    ptr: *mut MaybeUninit<u8>,
    len: usize,
    pages: Tracked<LoaderPages>,
) -> &'static mut [MaybeUninit<u8>] {
    // SAFETY: Ownership and the exact borrowed range are checked in the contract.
    unsafe { core::slice::from_raw_parts_mut(ptr, len) }
}

#[track_caller]
#[verifier::external_body]
#[verus_spec(opens_invariants none)]
pub fn panic_on_loaded_image_error(error: ::uefi::Error) -> ! {
    match Err::<Infallible, _>(error).unwrap() {}
}

#[track_caller]
#[verifier::external_body]
#[verus_spec(opens_invariants none)]
pub fn panic_on_loader_allocation_error(error: ::uefi::Error) -> ! {
    match Err::<Infallible, _>(error).expect("the UEFI allocation fails") {}
}
