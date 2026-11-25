// SPDX-License-Identifier: MPL-2.0
//! This module is used to compress kernel ELF.
use vstd::prelude::*;
use vstd_extra::external::libflate::{group_libflate_models, gzip_encoding, zlib_encoding};

use std::{
    ffi::{OsStr, OsString},
    io::Write,
    str::FromStr,
};

use libflate::{gzip, zlib};
use serde::{Deserialize, Serialize};

#[verus_verify(external_derive(Serialize), external_derive(Deserialize))]
#[derive(Debug, Default, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum PayloadEncoding {
    #[default]
    #[serde(rename = "raw")]
    Raw,
    #[serde(rename = "gzip")]
    Gzip,
    #[serde(rename = "zlib")]
    Zlib,
}

#[verus_verify]
impl FromStr for PayloadEncoding {
    type Err = String;

    #[verus_spec(result =>
        ensures
            if s@ == "raw"@ {
                result == Ok(Self::Raw)
            } else if s@ == "gzip"@ {
                result == Ok(Self::Gzip)
            } else if s@ == "zlib"@ {
                result == Ok(Self::Zlib)
            } else {
                result matches Err(message) && message@ == "Invalid encoding format: "@ + s@
            },
    )]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        /* Origin Rust:
        match s {
            "raw" => Ok(Self::Raw),
            "gzip" => Ok(Self::Gzip),
            "zlib" => Ok(Self::Zlib),
            _ => Err(format!("Invalid encoding format: {}", s)),
        }
        Rewritten to use existing vstd equality, to_owned, and push_str contracts.
        */
        match s {
            value if value == "raw" => Ok(Self::Raw),
            value if value == "gzip" => Ok(Self::Gzip),
            value if value == "zlib" => Ok(Self::Zlib),
            _ => {
                let mut message = "Invalid encoding format: ".to_owned();
                message.push_str(s);
                Err(message)
            }
        }
    }
}

impl From<OsString> for PayloadEncoding {
    fn from(os_string: OsString) -> Self {
        PayloadEncoding::from_str(&os_string.to_string_lossy()).unwrap()
    }
}

impl From<&OsStr> for PayloadEncoding {
    fn from(os_str: &OsStr) -> Self {
        PayloadEncoding::from_str(&os_str.to_string_lossy()).unwrap()
    }
}

/// Encoding the kernel ELF using the provided format.
#[verus_spec(result =>
    ensures
        match encoding {
            PayloadEncoding::Raw => result@ == kernel@,
            PayloadEncoding::Gzip => gzip_encoding(kernel@, result@),
            PayloadEncoding::Zlib => zlib_encoding(kernel@, result@),
        },
)]
pub fn encode_kernel(kernel: Vec<u8>, encoding: PayloadEncoding) -> Vec<u8> {
    proof! {
        broadcast use group_libflate_models;
    }
    match encoding {
        PayloadEncoding::Raw => kernel,
        PayloadEncoding::Gzip => {
            let mut encoder = gzip::Encoder::new(Vec::new()).unwrap();
            encoder.write_all(&kernel).unwrap();
            encoder.finish().into_result().unwrap()
        }
        PayloadEncoding::Zlib => {
            let mut encoder = zlib::Encoder::new(Vec::new()).unwrap();
            encoder.write_all(&kernel).unwrap();
            encoder.finish().into_result().unwrap()
        }
    }
}
