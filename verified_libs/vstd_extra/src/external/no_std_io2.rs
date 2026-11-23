// SPDX-License-Identifier: MPL-2.0
//! Trusted models for no_std_io2 0.9.4 byte readers and writers.
use vstd::prelude::*;

use alloc::vec::Vec;
use no_std_io2::io;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExIoError(io::Error);

pub ghost enum WriterState {
    Bytes(Seq<u8>),
    Gzip { prefix: Seq<u8>, plain: Seq<u8> },
    Zlib { prefix: Seq<u8>, plain: Seq<u8> },
}

pub uninterp spec fn writer_model_valid<W: ?Sized>() -> bool;

pub uninterp spec fn reader_model_valid<R: ?Sized>() -> bool;

pub broadcast axiom fn axiom_vec_writer_model()
    ensures
        #[trigger] writer_model_valid::<Vec<u8>>(),
;

pub broadcast axiom fn axiom_slice_reader_model<'a>()
    ensures
        #[trigger] reader_model_valid::<&'a [u8]>(),
;

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(WriteSpec via WriteSpecImpl)]
pub trait ExWrite {
    type ExternalTraitSpecificationFor: io::Write;

    spec fn writer_state(&self) -> WriterState;

    fn write_all(&mut self, input: &[u8]) -> (result: Result<(), io::Error>)
        ensures
            writer_model_valid::<Self>() ==> match old(self).writer_state() {
                WriterState::Gzip { prefix, plain } => {
                    &&& result is Ok
                    &&& final(self).writer_state() == WriterState::Gzip {
                        prefix,
                        plain: plain + input@,
                    }
                },
                WriterState::Zlib { prefix, plain } => {
                    &&& result is Ok
                    &&& final(self).writer_state() == WriterState::Zlib {
                        prefix,
                        plain: plain + input@,
                    }
                },
                WriterState::Bytes(bytes) => {
                    &&& result is Ok
                    &&& final(self).writer_state() == WriterState::Bytes(bytes + input@)
                },
            },
    ;
}

#[cfg(not(feature = "std"))]
impl WriteSpecImpl for Vec<u8> {
    open spec fn writer_state(&self) -> WriterState {
        WriterState::Bytes(self@)
    }
}

#[cfg(feature = "std")]
impl<A: core::alloc::Allocator> WriteSpecImpl for Vec<u8, A> {
    open spec fn writer_state(&self) -> WriterState {
        WriterState::Bytes(self@)
    }
}

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(ReadSpec via ReadSpecImpl)]
pub trait ExRead {
    type ExternalTraitSpecificationFor: io::Read;

    spec fn remaining_bytes(&self) -> Option<Seq<u8>>;

    /// libflate 2.3.2 forwards its `std` feature to no_std_io2 0.9.4, which then
    /// re-exports `std::io`. Its `read_to_end` can return an allocation error
    /// from `Vec::try_reserve` even when the input decodes successfully.
    fn read_to_end(&mut self, output: &mut Vec<u8>) -> (result: Result<usize, io::Error>)
        ensures
            reader_model_valid::<Self>() ==> (old(self).remaining_bytes() matches Some(plain) ==> {
                &&& !cfg!(feature = "std") ==> result is Ok
                &&& result matches Ok(count) ==> {
                    &&& count == plain.len()
                    &&& final(output)@ == old(output)@ + plain
                    &&& final(self).remaining_bytes() == Some(Seq::<u8>::empty())
                }
            }),
    ;
}

impl ReadSpecImpl for &[u8] {
    open spec fn remaining_bytes(&self) -> Option<Seq<u8>> {
        Some(self@)
    }
}

} // verus!
