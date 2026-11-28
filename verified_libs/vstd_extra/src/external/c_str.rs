// SPDX-License-Identifier: MPL-2.0
//! Byte-level specifications for the Rust 1.100.0 C string APIs used by the EFI setup.
use alloc::ffi::CString;
use core::ffi::{CStr, FromBytesUntilNulError};

use vstd::prelude::*;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExCStr(CStr);

// CString is CStr's owned counterpart in its ToOwned implementation.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExCString(CString);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExFromBytesUntilNulError(FromBytesUntilNulError);

pub uninterp spec fn bytes_with_nul(value: &CStr) -> Seq<u8>;

/// Rust 1.100.0 `core/src/ffi/c_str.rs`: the first zero byte ends the borrowed C string.
pub assume_specification<'a>[ CStr::from_bytes_until_nul ](bytes: &'a [u8]) -> (ret: Result<
    &'a CStr,
    FromBytesUntilNulError,
>)
    ensures
        ret is Ok <==> bytes@.contains(0u8),
        ret matches Ok(value) ==> {
            let prefix = bytes_with_nul(value);
            &&& 0 < prefix.len() <= bytes@.len()
            &&& prefix == bytes@[..prefix.len()]
            &&& prefix.last() == 0u8
            &&& !prefix.drop_last().contains(0u8)
        },
    opens_invariants none
    no_unwind
;

} // verus!
