// SPDX-License-Identifier: MPL-2.0
//! Specifications for the UTF-8 string APIs missing from `vstd`.
//!
//! `vstd` models UTF-8 validity itself (`vstd::utf8::valid_utf8`) and specifies
//! `str::from_utf8_unchecked`, but it does not specify `core::str::from_utf8`.
use vstd::{prelude::*, string::StringSliceAdditionalSpecFns, utf8::valid_utf8};

verus! {

/// The error payload of [`core::str::from_utf8`]. It is never inspected by
/// OSTD, so it carries no specification of its own beyond being usable in
/// Verus specs.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExUtf8Error(core::str::Utf8Error);

/// Validates UTF-8 and returns a `&str` borrowing the input bytes on success.
/// See [`std::str::from_utf8`](https://doc.rust-lang.org/std/str/fn.from_utf8.html).
///
/// The result is `Ok` exactly when the input models a valid UTF-8 string
/// ([`vstd::utf8::valid_utf8`]); on `Ok`, the decoded string borrows exactly
/// the input bytes.
pub assume_specification[ core::str::from_utf8 ](v: &[u8]) -> (res: Result<
    &str,
    core::str::Utf8Error,
>)
    ensures
        res matches Ok(s) ==> {
            &&& valid_utf8(v@)
            &&& s.spec_bytes() =~= v@
        },
        res matches Err(_) ==> !valid_utf8(v@),
;

} // verus!
