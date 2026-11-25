// SPDX-License-Identifier: MPL-2.0
//! Specifications and UTF-8 helper lemmas for string APIs missing from `vstd`.
//!
//! `vstd` models UTF-8 validity itself (`vstd::utf8::valid_utf8`) and specifies
//! `str::from_utf8_unchecked`, but it does not specify `core::str::from_utf8`.
//! In addition to `core::str::from_utf8`, this module provides reusable UTF-8
//! lemmas relating `&str` byte/character views and ASCII character boundaries:
//! - [`lemma_str_bytes_eq_iff_view_eq`]
//! - [`lemma_single_byte_str`]
//! - [`lemma_encode_utf8_contains_ascii`]
//! - [`lemma_ascii_char_boundary_after`]
use vstd::{
    prelude::*,
    string::StringSliceAdditionalSpecFns,
    utf8::{
        decode_utf8, encode_scalar, encode_utf8, encode_utf8_decode_utf8, encode_utf8_first_scalar,
        has_width_1_encoding, is_ascii_chars, is_ascii_chars_encode_utf8, is_char_boundary,
        is_char_boundary_iff_not_is_continuation_byte, is_char_boundary_start_end_of_seq,
        is_continuation_byte, valid_utf8, valid_utf8_split,
    },
};

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
    no_unwind
;

/// Two string slices have equal UTF-8 bytes if and only if they have equal `char` views.
pub proof fn lemma_str_bytes_eq_iff_view_eq(a: &str, b: &str)
    ensures
        (a.spec_bytes() == b.spec_bytes()) <==> (a@ == b@),
{
    broadcast use encode_utf8_decode_utf8;

    if a.spec_bytes() == b.spec_bytes() {
        assert(decode_utf8(a.spec_bytes()) == decode_utf8(b.spec_bytes()));
    }
}

/// A single-byte string slice consists of one ASCII character whose UTF-8 encoding is that byte.
pub proof fn lemma_single_byte_str(s: &str)
    requires
        s.spec_bytes().len() == 1,
    ensures
        s@.len() == 1,
        (s@[0] as u32) < 0x80,
        s.spec_bytes() == seq![s@[0] as u8],
{
    assert(s@.len() > 0) by {
        if s@.len() == 0 {
            assert(encode_utf8(s@) == Seq::<u8>::empty());
        }
    };
    encode_utf8_first_scalar(s@);
    assert(s@.len() == 1) by {
        if s@.len() > 1 {
            encode_utf8_first_scalar(s@.drop_first());
        }
    };
    assert(is_ascii_chars(s@));
    is_ascii_chars_encode_utf8(s@);
    assert(s.spec_bytes() =~= seq![s@[0] as u8]);
}

/// An ASCII byte appears in `encode_utf8(chars)` if and only if the corresponding character is in `chars`.
pub proof fn lemma_encode_utf8_contains_ascii(chars: Seq<char>, c: char)
    requires
        (c as u32) < 0x80,
    ensures
        (exists|i: int| 0 <= i < encode_utf8(chars).len() && encode_utf8(chars)[i] == c as u8)
            <==> chars.contains(c),
    decreases chars.len(),
{
    if chars.len() > 0 {
        let head = chars[0];
        let h = head as u32;
        let rest = chars.drop_first();
        let hs = encode_scalar(h);
        let rs = encode_utf8(rest);
        encode_utf8_first_scalar(chars);
        assert(encode_utf8(chars) == hs + rs);
        lemma_encode_utf8_contains_ascii(rest, c);
        if has_width_1_encoding(h) {
            let s1 = seq![head];
            assert(is_ascii_chars(s1));
            is_ascii_chars_encode_utf8(s1);
            assert(s1.drop_first() =~= Seq::<char>::empty());
            assert(hs =~= seq![head as u8]);
            if head == c {
                assert(encode_utf8(chars)[0] == c as u8);
            }
            if encode_utf8(chars)[0] == c as u8 {
                assert(head == c);
            }
        } else {
            assert forall|k: int| 0 <= k < hs.len() implies hs[k] >= 0x80 by {
                assert(hs[k] == encode_utf8(chars)[k]);
            };
        }
        if exists|i: int| 0 <= i < encode_utf8(chars).len() && encode_utf8(chars)[i] == c as u8 {
            let i = choose|i: int|
                0 <= i < encode_utf8(chars).len() && encode_utf8(chars)[i] == c as u8;
            if i < hs.len() {
                assert(chars[0] == c);
            } else {
                assert(rs[i - hs.len()] == c as u8);
                let j = choose|j: int| 0 <= j < rest.len() && rest[j] == c;
                assert(chars[j + 1] == c);
            }
        }
        if chars.contains(c) {
            let j = choose|j: int| 0 <= j < chars.len() && chars[j] == c;
            if j == 0 {
                assert(encode_utf8(chars)[0] == c as u8);
            } else {
                assert(rest[j - 1] == c);
                let i = choose|i: int| 0 <= i < rs.len() && rs[i] == c as u8;
                assert(encode_utf8(chars)[hs.len() + i] == c as u8);
            }
        }
    }
}

/// An ASCII byte in a valid UTF-8 sequence sits on a character boundary, as does the position immediately after it.
pub proof fn lemma_ascii_char_boundary_after(b: Seq<u8>, i: int)
    requires
        valid_utf8(b),
        0 <= i < b.len(),
        b[i] < 0x80,
    ensures
        is_char_boundary(b, i),
        is_char_boundary(b, i + 1),
{
    broadcast use {
        is_char_boundary_iff_not_is_continuation_byte,
        is_char_boundary_start_end_of_seq,
        valid_utf8_split,
    };

    assert(!is_continuation_byte(b[i]));
    assert(is_char_boundary(b, i));
    if i + 1 < b.len() {
        let suffix = b[i..];
        assert(valid_utf8(suffix));
        assert(b[i + 1..] == suffix.drop_first());
        assert(valid_utf8(b[i + 1..]));
        assert(!is_continuation_byte(b[i + 1]));
    }
}

} // verus!
