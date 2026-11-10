// SPDX-License-Identifier: MPL-2.0
//! Decimal parsing for the build-time kernel stack size.
use vstd::{prelude::*, string::StringSliceAdditionalSpecFns};

verus! {

/// The mathematical value of a decimal byte sequence; the empty sequence is zero.
pub(super) open spec fn decimal_value(bytes: Seq<u8>) -> int
    decreases bytes.len(),
{
    if bytes.len() == 0 {
        0
    } else {
        decimal_value(bytes[..bytes.len() - 1]) * 10 + (bytes.last() - b'0')
    }
}

/// Decimal input whose mathematical value fits in a `u32`, including empty input.
pub(super) open spec fn valid_decimal(bytes: Seq<u8>) -> bool {
    &&& forall|i: int| 0 <= i < bytes.len() ==> b'0' <= #[trigger] bytes[i] <= b'9'
    &&& decimal_value(bytes) <= u32::MAX
}

} // verus!
/// Parses the configured stack size, or uses the default when it is absent.
#[expect(dead_code, reason = "the kernel_stack caller is not enabled yet")]
#[verus_spec(
    requires size matches Some(value) ==> valid_decimal(value.spec_bytes()),
    returns match size {
        Some(value) => decimal_value(value.spec_bytes()) as u32,
        None => default,
    },
)]
pub(super) const fn parse_u32_or_default(size: Option<&str>, default: u32) -> u32 {
    match size {
        Some(value) => parse_u32(value),
        None => default,
    }
}

#[verus_spec(
    requires valid_decimal(input.spec_bytes()),
    returns decimal_value(input.spec_bytes()) as u32,
)]
const fn parse_u32(input: &str) -> u32 {
    let mut output: u32 = 0;
    let bytes = input.as_bytes();
    let mut i = 0;
    #[verus_spec(
        invariant
            i <= bytes.len(),
            valid_decimal(bytes@),
            bytes@ == input.spec_bytes(),
            output == decimal_value(bytes@[..i]),
        decreases bytes.len() - i,
    )]
    while i < bytes.len() {
        proof! {
            /// Every decimal prefix has a nonnegative value bounded by the complete value.
            proof fn lemma_decimal_prefix(bytes: Seq<u8>, end: int)
                requires
                    forall|i: int| 0 <= i < bytes.len() ==> b'0' <= #[trigger] bytes[i] <= b'9',
                    0 <= end <= bytes.len(),
                ensures
                    0 <= decimal_value(bytes[..end]) <= decimal_value(bytes),
                decreases bytes.len(),
            {
                assert(bytes[..bytes.len()] == bytes);
                if bytes.len() > 0 {
                    let prefix = bytes[..bytes.len() - 1];
                    lemma_decimal_prefix(
                        prefix,
                        if end < bytes.len() {
                            end
                        } else {
                            end - 1
                        },
                    );
                    if end < bytes.len() {
                        assert(prefix[..end] == bytes[..end]);
                    }
                }
            }

            lemma_decimal_prefix(bytes@, i + 1);
            assert(bytes@[..i + 1][..i] == bytes@[..i]);
        }
        let digit = (bytes[i] - b'0') as u32;
        output = output * 10 + digit;
        i += 1;
    }
    proof! {
        assert(bytes@[..i] == bytes@);
    }
    output
}
