// SPDX-License-Identifier: MPL-2.0
use vstd::{
    endian::{Base, Endian, EndianNat},
    prelude::*,
};

verus! {

pub ghost struct Base10 {}

impl Base for Base10 {
    open spec fn base() -> nat {
        10
    }

    proof fn base_min() {
    }
}

/// The mathematical value of an ASCII decimal byte sequence; empty input is zero.
pub open spec fn decimal_value(bytes: Seq<u8>) -> int {
    EndianNat::<Base10>::new(Endian::Big, bytes.map_values(|byte: u8| byte - b'0')).to_nat() as int
}

/// Decimal input whose mathematical value fits in a `u32`, including empty input.
pub open spec fn valid_decimal(bytes: Seq<u8>) -> bool {
    &&& forall|i: int| 0 <= i < bytes.len() ==> b'0' <= #[trigger] bytes[i] <= b'9'
    &&& decimal_value(bytes) <= u32::MAX
}

pub proof fn lemma_decimal_value_step(bytes: Seq<u8>)
    requires
        forall|i: int| 0 <= i < bytes.len() ==> b'0' <= #[trigger] bytes[i] <= b'9',
    ensures
        bytes.len() == 0 ==> decimal_value(bytes) == 0,
        bytes.len() > 0 ==> decimal_value(bytes) == decimal_value(bytes[..bytes.len() - 1]) * 10 + (
        bytes.last() - b'0'),
{
    reveal(EndianNat::to_nat);
    if bytes.len() > 0 {
        let digits = bytes.map_values(|byte: u8| byte - b'0');
        assert(digits.drop_last() == bytes[..bytes.len() - 1].map_values(|byte: u8| byte - b'0'));
    }
}

pub proof fn lemma_decimal_prefix(bytes: Seq<u8>, end: int)
    requires
        forall|i: int| 0 <= i < bytes.len() ==> b'0' <= #[trigger] bytes[i] <= b'9',
        0 <= end <= bytes.len(),
    ensures
        0 <= decimal_value(bytes[..end]) <= decimal_value(bytes),
    decreases bytes.len(),
{
    lemma_decimal_value_step(bytes);
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

} // verus!
