// SPDX-License-Identifier: MPL-2.0
//! Trusted specifications for the `fdt` crate (0.1.5).
use vstd::{prelude::*, string::StringSliceAdditionalSpecFns, utf8::valid_utf8};

use fdt::node::NodeProperty;

verus! {

#[verifier::external_type_specification]
pub struct ExNodeProperty<'a>(NodeProperty<'a>);

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
            &&& s.spec_bytes().len() <= prop.value@.len()
            &&& s.spec_bytes() == prop.value@[..s.spec_bytes().len()]
            &&& s.spec_bytes().len() == 0 || s.spec_bytes().last() != 0u8
            &&& forall|i: int|
                s.spec_bytes().len() <= i < prop.value@.len() ==> prop.value@[i] == 0u8
        },
        res is None ==> !valid_utf8(prop.value@),
    opens_invariants none
    no_unwind
;

} // verus!
