// SPDX-License-Identifier: MPL-2.0
//! This module is used to decompress payload.
use vstd::{prelude::*, std_specs::convert::TryFromSpecImpl};
use vstd_extra::external::libflate::{group_libflate_models, gzip_decoded, zlib_decoded};

extern crate alloc;

use alloc::vec::Vec;
use core::convert::TryFrom;

use libflate::{gzip, zlib};

/* libflate 2.3 uses no_std_io2. Origin Rust: use core2::io::Read; */
use no_std_io2::io::Read;

#[verus_verify]
/* Verus requires public visibility. Origin Rust: enum MagicNumber { */
pub enum MagicNumber {
    Elf,
    Gzip,
    Zlib,
}

#[verus_verify]
#[derive(Debug)]
/* Verus requires a public error type. Origin Rust: struct InvalidMagicNumber; */
pub struct InvalidMagicNumber;

#[verus_verify]
impl TryFrom<&[u8]> for MagicNumber {
    type Error = InvalidMagicNumber;

    #[verus_spec(result =>
        ensures
            result matches Ok(MagicNumber::Elf) <==>
                slice@.len() >= 4 && slice@[..4] == seq![0x7fu8, 0x45u8, 0x4cu8, 0x46u8],
            result matches Ok(MagicNumber::Gzip) <==>
                slice@.len() >= 2 && slice@[..2] == seq![0x1fu8, 0x8bu8],
            result matches Ok(MagicNumber::Zlib) <==>
                slice@.len() >= 2 && slice@[..2] == seq![0x78u8, 0x9cu8],
    )]
    fn try_from(slice: &[u8]) -> Result<Self, Self::Error> {
        proof! {

            if slice@.len() >= 4 {
                assert((slice@[..4] == seq![0x7fu8, 0x45u8, 0x4cu8, 0x46u8]) <==>
                    (slice@[0] == 0x7F && slice@[1] == 0x45
                        && slice@[2] == 0x4C && slice@[3] == 0x46)) by {
                    if slice@[0] == 0x7F && slice@[1] == 0x45
                        && slice@[2] == 0x4C && slice@[3] == 0x46 {
                        assert(slice@[..4] =~= seq![0x7fu8, 0x45u8, 0x4cu8, 0x46u8]);
                    }
                }
            }
            if slice@.len() >= 2 {
                assert((slice@[..2] == seq![0x1fu8, 0x8bu8]) <==>
                    (slice@[0] == 0x1F && slice@[1] == 0x8B)) by {
                    if slice@[0] == 0x1F && slice@[1] == 0x8B {
                        assert(slice@[..2] =~= seq![0x1fu8, 0x8bu8]);
                    }
                }
                assert((slice@[..2] == seq![0x78u8, 0x9cu8]) <==>
                    (slice@[0] == 0x78 && slice@[1] == 0x9C)) by {
                    if slice@[0] == 0x78 && slice@[1] == 0x9C {
                        assert(slice@[..2] =~= seq![0x78u8, 0x9cu8]);
                    }
                }
            }
        }
        /* Verus lacks slice rest patterns. Origin Rust:
         * match *slice {
         *     [0x7F, 0x45, 0x4C, 0x46, ..] => Ok(Self::Elf),
         *     [0x1F, 0x8B, ..] => Ok(Self::Gzip),
         *     [0x78, 0x9C, ..] => Ok(Self::Zlib),
         *     _ => Err(InvalidMagicNumber),
         * } */
        if slice.len() >= 4
            && slice[0] == 0x7F
            && slice[1] == 0x45
            && slice[2] == 0x4C
            && slice[3] == 0x46
        {
            Ok(Self::Elf)
        } else if slice.len() >= 2 && slice[0] == 0x1F && slice[1] == 0x8B {
            Ok(Self::Gzip)
        } else if slice.len() >= 2 && slice[0] == 0x78 && slice[1] == 0x9C {
            Ok(Self::Zlib)
        } else {
            Err(InvalidMagicNumber)
        }
    }
}

/// Detects the format used to encode the payload and decodes the payload accordingly.
#[verus_spec(kernel =>
    requires
        decoded_payload(payload@) is Some,
    ensures
        Some(kernel@) == decoded_payload(payload@),
)]
pub fn decode_payload(payload: &[u8]) -> Vec<u8> {
    proof! {
        broadcast use group_libflate_models;
    }
    let mut kernel = Vec::new();
    let magic = MagicNumber::try_from(payload).unwrap();
    match magic {
        MagicNumber::Elf => {
            kernel = payload.to_vec();
            proof! {
                assert forall|i: int| 0 <= i < kernel@.len() implies
                    #[trigger] kernel@[i] == payload@[i] by {
                    assert(cloned(payload@[i], kernel@[i]));
                }

            }
        }
        MagicNumber::Gzip => {
            let mut decoder = gzip::Decoder::new(payload).unwrap();
            decoder.read_to_end(&mut kernel).unwrap();
        }
        MagicNumber::Zlib => {
            let mut decoder = zlib::Decoder::new(payload).unwrap();
            decoder.read_to_end(&mut kernel).unwrap();
        }
    }
    kernel
}

verus! {

impl TryFromSpecImpl<&[u8]> for MagicNumber {
    open spec fn obeys_try_from_spec() -> bool {
        true
    }

    open spec fn try_from_spec(slice: &[u8]) -> Result<Self, Self::Error> {
        if slice@.len() >= 4 && slice@[..4] == seq![0x7fu8, 0x45u8, 0x4cu8, 0x46u8] {
            Ok(Self::Elf)
        } else if slice@.len() >= 2 && slice@[..2] == seq![0x1fu8, 0x8bu8] {
            Ok(Self::Gzip)
        } else if slice@.len() >= 2 && slice@[..2] == seq![0x78u8, 0x9cu8] {
            Ok(Self::Zlib)
        } else {
            Err(InvalidMagicNumber)
        }
    }
}

/// Raw ELF bytes pass through; compressed payloads require successful decoding.
pub closed spec fn decoded_payload(payload: Seq<u8>) -> Option<Seq<u8>> {
    if payload.len() >= 4 && payload[..4] == seq![0x7fu8, 0x45u8, 0x4cu8, 0x46u8] {
        Some(payload)
    } else if payload.len() >= 2 && payload[..2] == seq![0x1fu8, 0x8bu8] {
        gzip_decoded(payload)
    } else if payload.len() >= 2 && payload[..2] == seq![0x78u8, 0x9cu8] {
        zlib_decoded(payload)
    } else {
        None
    }
}

} // verus!
