// SPDX-License-Identifier: MPL-2.0
//! Trusted specifications for the `fdt` crate (0.1.5).
use vstd::{prelude::*, string::StringSliceAdditionalSpecFns, utf8::valid_utf8};

use fdt::node::NodeProperty;

verus! {

#[verifier::external_type_specification]
pub struct ExNodeProperty<'a>(NodeProperty<'a>);

/// Returns the length of `b` after stripping all trailing NUL (`0u8`) bytes.
pub open spec fn trim_trailing_nul_len(b: Seq<u8>) -> int
    decreases b.len(),
{
    if b.len() > 0 && b.last() == 0u8 {
        trim_trailing_nul_len(b.drop_last())
    } else {
        b.len() as int
    }
}

/// Proves the boundary properties of [`trim_trailing_nul_len`]: the trimmed prefix
/// ends with a non-NUL byte (or is empty) and every stripped trailing byte is `0u8`.
pub proof fn lemma_trim_trailing_nul_len(b: Seq<u8>)
    ensures
        0 <= trim_trailing_nul_len(b) <= b.len(),
        trim_trailing_nul_len(b) == 0 || b[trim_trailing_nul_len(b) - 1] != 0u8,
        forall|i: int| trim_trailing_nul_len(b) <= i < b.len() ==> b[i] == 0u8,
    decreases b.len(),
{
    if b.len() > 0 && b.last() == 0u8 {
        lemma_trim_trailing_nul_len(b.drop_last());
        assert forall|i: int| trim_trailing_nul_len(b) <= i < b.len() implies b[i] == 0u8 by {
            if i < b.len() - 1 {
                assert(b[i] == b.drop_last()[i]);
            }
        };
    }
}

/// Parses the property bytes as UTF-8 and strips trailing NUL bytes.
///
/// Audited against `fdt 0.1.5`, `src/node.rs`:
/// `core::str::from_utf8(self.value).map(|s| s.trim_end_matches('\0')).ok()`.
/// In valid UTF-8, `'\0'` is the single byte `0u8` and never appears inside a
/// multi-byte sequence, so trimming trailing `'\0'` removes the maximal trailing
/// suffix of `0u8` bytes.
pub assume_specification<'a>[ NodeProperty::<'a>::as_str ](prop: NodeProperty<'a>) -> (res: Option<
    &'a str,
>)
    ensures
        res matches Some(s) ==> {
            &&& valid_utf8(prop.value@)
            &&& s.spec_bytes() == prop.value@[..trim_trailing_nul_len(prop.value@)]
        },
        res is None ==> !valid_utf8(prop.value@),
    opens_invariants none
    no_unwind
;

} // verus!
