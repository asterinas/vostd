// SPDX-License-Identifier: MPL-2.0
//! UEFI 0.32.0 boot services used by the x86 bzImage setup.
//!
//! The loaded-image read borrows the options held by the current protocol.
//! The setup sets the image handle before using these services and drops the
//! protocol before exiting boot services. UEFI can panic if either boot-phase
//! prerequisite is violated independently of a firmware error return.
//!
//! AllocatePages transfers exclusive access to the successful LoaderData range
//! (UEFI 2.10, sections 7.2.1 and 7.2.2). The setup checks the pointer and
//! range against the tracked permission before constructing a slice, then
//! retains the allocation until control passes to the kernel.
use vstd::{prelude::*, raw_ptr::PointsToRaw};

use core::{
    convert::Infallible,
    fmt::{Arguments, Debug},
    ops::Deref,
    ptr::NonNull,
};

use ::uefi::{
    Error, Handle, Identify, Result as UefiResult,
    boot::{self, AllocateType, MemoryType, ScopedProtocol},
    helpers,
    proto::{Protocol, ProtocolPointer, loaded_image::LoadedImage},
};

verus! {

#[verifier::external_type_specification]
pub struct ExAllocateType(AllocateType);

/// See <https://docs.rs/uefi/0.32.0/uefi/struct.Error.html>.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(D)]
pub struct ExUefiError<D: Debug>(Error<D>);

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

/// See <https://docs.rs/uefi/0.32.0/uefi/boot/fn.image_handle.html>.
pub assume_specification[ boot::image_handle ]() -> Handle
;

/// See <https://docs.rs/uefi/0.32.0/uefi/boot/fn.open_protocol_exclusive.html>.
pub assume_specification<P: ProtocolPointer + ?Sized>[ boot::open_protocol_exclusive::<P> ](
    handle: Handle,
) -> UefiResult<ScopedProtocol<P>>
;

/// See <https://docs.rs/uefi/0.32.0/uefi/boot/struct.ScopedProtocol.html#impl-Deref-for-ScopedProtocol%3CP%3E>.
pub assume_specification<'a, P: Protocol + ?Sized>[ <ScopedProtocol<P> as Deref>::deref ](
    scope: &'a ScopedProtocol<P>,
) -> &'a <ScopedProtocol<P> as Deref>::Target
;

/// See <https://docs.rs/uefi/0.32.0/uefi/proto/loaded_image/struct.LoadedImage.html#method.load_options_as_bytes>.
pub assume_specification<'a>[ LoadedImage::load_options_as_bytes ](image: &'a LoadedImage) -> (ret:
    Option<&'a [u8]>)
    ensures
        ret matches Some(bytes) ==> bytes@.len() <= u32::MAX && bytes@.len() <= isize::MAX,
    opens_invariants none
    no_unwind
;

/// See the print helper in <https://docs.rs/uefi/0.32.0/src/uefi/helpers/println.rs.html#6>.
pub assume_specification[ helpers::_print ](args: Arguments<'_>)
;

/// See <https://docs.rs/uefi/0.32.0/uefi/boot/constant.PAGE_SIZE.html>.
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
/// Allocates pages of UEFI LoaderData memory.
/// See <https://docs.rs/uefi/0.32.0/uefi/boot/fn.allocate_pages.html>.
/* Trusted: the firmware allocation creates the exclusive page permission.
 * Origin Rust: <none; new executable wrapper>
 */
#[verifier::external_body]
#[verus_spec(ret =>
    with -> pages: Tracked<Option<LoaderPages>>,
    ensures
        (ret is Ok) <==> (pages@ is Some),
        ret matches Ok(ptr) ==> {
            let addr = ptr.as_ptr().addr();
            let len = count * boot::PAGE_SIZE;
            let pages = pages@->0;
            &&& addr != 0
            &&& addr + len <= usize::MAX
            &&& pages.permission().is_range(addr as int, len)
            &&& pages.permission().provenance() == ptr.as_ptr()@.provenance
            &&& (ty matches AllocateType::MaxAddress(max) ==> count == 0 || addr + len - 1 <= max)
            &&& (ty matches AllocateType::Address(requested) ==> count == 0 || addr == requested)
        },
)]
pub fn allocate_loader_pages(ty: AllocateType, count: usize) -> UefiResult<NonNull<u8>> {
    proof_with!(|= Tracked::assume_new());
    boot::allocate_pages(ty, MemoryType::LOADER_DATA, count)
}

/// See <https://doc.rust-lang.org/1.100.0/core/result/enum.Result.html#method.unwrap>.
/* Trusted: vstd's unwrap contract excludes Err, whose panic diagnostic this preserves.
 * Origin Rust: <none; new executable wrapper>
 */
#[track_caller]
#[verifier::external_body]
#[verus_spec(requires result is Err)]
pub fn panic_on_unwrap_error(result: UefiResult<Infallible>) -> ! {
    match result.unwrap() {}
}

/// See <https://doc.rust-lang.org/1.100.0/core/result/enum.Result.html#method.expect>.
/* Trusted: vstd's expect contract excludes Err, whose panic diagnostic this preserves.
 * Origin Rust: <none; new executable wrapper>
 */
#[track_caller]
#[verifier::external_body]
#[verus_spec(requires result is Err)]
pub fn panic_on_expect_error(result: UefiResult<Infallible>, message: &str) -> ! {
    match result.expect(message) {}
}
