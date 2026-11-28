// SPDX-License-Identifier: MPL-2.0
//! Byte-level specifications for Rust 1.100.0 C strings.
use vstd::prelude::*;

use alloc::ffi::CString;
use core::ffi::{CStr, FromBytesUntilNulError};

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

/// Rust 1.100.0 `library/core/src/ffi/c_str.rs` ends the C string at the first NUL.
/// See <https://doc.rust-lang.org/1.100.0/core/ffi/struct.CStr.html#method.from_bytes_until_nul>.
///
/// TODO: Upstream this model; remove it when equivalent vstd support is available.
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
