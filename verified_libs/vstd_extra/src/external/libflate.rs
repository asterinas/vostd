// SPDX-License-Identifier: MPL-2.0
//! Trusted libflate 2.3.2/no_std_io2 0.9.4 models; codec correctness is assumed.
//! Audited libflate sources include src/{gzip,zlib,finish}.rs.
//! Validity is limited to Vec<u8>, byte slices, and their default codecs.
use vstd::prelude::*;

use alloc::vec::Vec;
use libflate::{Finish, gzip, zlib};
use no_std_io2::io;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(W)]
#[verifier::reject_recursive_types(E)]
pub struct ExGzipEncoder<W, E>(gzip::Encoder<W, E>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(W)]
#[verifier::reject_recursive_types(E)]
pub struct ExZlibEncoder<W, E>(zlib::Encoder<W, E>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(R)]
pub struct ExGzipDecoder<R>(gzip::Decoder<R>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(R)]
pub struct ExZlibDecoder<R>(zlib::Decoder<R>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(E)]
pub struct ExFinish<T, E>(Finish<T, E>);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExIoError(io::Error);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExDefaultLz77Encoder(libflate::lz77::DefaultLz77Encoder);

/// First-member decoding with checksum validation; None means invalid/incomplete data.
/// Trailing bytes are allowed.
pub uninterp spec fn gzip_decoded(stream: Seq<u8>) -> Option<Seq<u8>>;

pub uninterp spec fn zlib_decoded(stream: Seq<u8>) -> Option<Seq<u8>>;

pub open spec fn has_gzip_prefix(stream: Seq<u8>) -> bool {
    stream.len() >= 2 && stream[..2] == seq![0x1fu8, 0x8bu8]
}

pub open spec fn has_zlib_prefix(stream: Seq<u8>) -> bool {
    stream.len() >= 2 && stream[..2] == seq![0x78u8, 0x9cu8]
}

/// A relation, since gzip's default header may contain the current timestamp.
pub open spec fn gzip_encoding(plain: Seq<u8>, stream: Seq<u8>) -> bool {
    &&& has_gzip_prefix(stream)
    &&& gzip_decoded(stream) == Some(plain)
}

pub open spec fn zlib_encoding(plain: Seq<u8>, stream: Seq<u8>) -> bool {
    &&& has_zlib_prefix(stream)
    &&& zlib_decoded(stream) == Some(plain)
}

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

pub broadcast axiom fn axiom_gzip_writer_model()
    ensures
        #[trigger] writer_model_valid::<gzip::Encoder<Vec<u8>>>(),
;

pub broadcast axiom fn axiom_zlib_writer_model()
    ensures
        #[trigger] writer_model_valid::<zlib::Encoder<Vec<u8>>>(),
;

pub broadcast axiom fn axiom_slice_reader_model<'a>()
    ensures
        #[trigger] reader_model_valid::<&'a [u8]>(),
;

pub broadcast axiom fn axiom_gzip_reader_model<'a>()
    ensures
        #[trigger] reader_model_valid::<gzip::Decoder<&'a [u8]>>(),
;

pub broadcast axiom fn axiom_zlib_reader_model<'a>()
    ensures
        #[trigger] reader_model_valid::<zlib::Decoder<&'a [u8]>>(),
;

pub broadcast group group_libflate_models {
    axiom_vec_writer_model,
    axiom_gzip_writer_model,
    axiom_zlib_writer_model,
    axiom_slice_reader_model,
    axiom_gzip_reader_model,
    axiom_zlib_reader_model,
}

pub uninterp spec fn gzip_state<W, E>(encoder: &gzip::Encoder<W, E>) -> WriterState;

pub uninterp spec fn zlib_state<W, E>(encoder: &zlib::Encoder<W, E>) -> WriterState;

#[verifier::external_trait_specification]
pub trait ExLz77Encode {
    type ExternalTraitSpecificationFor: libflate::lz77::Lz77Encode;
}

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

impl<W: io::Write, E: libflate::lz77::Lz77Encode> WriteSpecImpl for gzip::Encoder<W, E> {
    open spec fn writer_state(&self) -> WriterState {
        gzip_state(self)
    }
}

impl<W: io::Write, E: libflate::lz77::Lz77Encode> WriteSpecImpl for zlib::Encoder<W, E> {
    open spec fn writer_state(&self) -> WriterState {
        zlib_state(self)
    }
}

pub assume_specification<W: io::Write>[ gzip::Encoder::<W>::new ](inner: W) -> (result: Result<
    gzip::Encoder<W>,
    io::Error,
>)
    ensures
        writer_model_valid::<W>() ==> (inner.writer_state() matches WriterState::Bytes(prefix) ==> {
            result matches Ok(encoder) && gzip_state(&encoder) == WriterState::Gzip {
                prefix,
                plain: Seq::empty(),
            }
        }),
;

pub assume_specification<W: io::Write>[ zlib::Encoder::<W>::new ](inner: W) -> (result: Result<
    zlib::Encoder<W>,
    io::Error,
>)
    ensures
        writer_model_valid::<W>() ==> (inner.writer_state() matches WriterState::Bytes(prefix) ==> {
            result matches Ok(encoder) && zlib_state(&encoder) == WriterState::Zlib {
                prefix,
                plain: Seq::empty(),
            }
        }),
;

pub uninterp spec fn finish_value<T, E>(finish: Finish<T, E>) -> T;

pub uninterp spec fn finish_error<T, E>(finish: Finish<T, E>) -> Option<E>;

pub assume_specification<W: io::Write, E: libflate::lz77::Lz77Encode>[ gzip::Encoder::<
    W,
    E,
>::finish ](encoder: gzip::Encoder<W, E>) -> (result: Finish<W, io::Error>)
    ensures
        writer_model_valid::<gzip::Encoder<W, E>>() ==> (gzip_state(
            &encoder,
        ) matches WriterState::Gzip { prefix, plain } ==> {
            &&& finish_error(result) is None
            &&& exists|stream: Seq<u8>| #[trigger]
                gzip_encoding(plain, stream) && finish_value(result).writer_state()
                    == WriterState::Bytes(prefix + stream)
        }),
;

pub assume_specification<W: io::Write, E: libflate::lz77::Lz77Encode>[ zlib::Encoder::<
    W,
    E,
>::finish ](encoder: zlib::Encoder<W, E>) -> (result: Finish<W, io::Error>)
    ensures
        writer_model_valid::<zlib::Encoder<W, E>>() ==> (zlib_state(
            &encoder,
        ) matches WriterState::Zlib { prefix, plain } ==> {
            &&& finish_error(result) is None
            &&& exists|stream: Seq<u8>| #[trigger]
                zlib_encoding(plain, stream) && finish_value(result).writer_state()
                    == WriterState::Bytes(prefix + stream)
        }),
;

pub assume_specification<T, E>[ Finish::<T, E>::into_result ](finish: Finish<T, E>) -> Result<T, E>
    returns
        match finish_error(finish) {
            None => Ok(finish_value(finish)),
            Some(error) => Err(error),
        },
;

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

pub uninterp spec fn gzip_remaining<R>(decoder: &gzip::Decoder<R>) -> Option<Seq<u8>>;

pub uninterp spec fn zlib_remaining<R>(decoder: &zlib::Decoder<R>) -> Option<Seq<u8>>;

impl<R: io::Read> ReadSpecImpl for gzip::Decoder<R> {
    open spec fn remaining_bytes(&self) -> Option<Seq<u8>> {
        gzip_remaining(self)
    }
}

impl<R: io::Read> ReadSpecImpl for zlib::Decoder<R> {
    open spec fn remaining_bytes(&self) -> Option<Seq<u8>> {
        zlib_remaining(self)
    }
}

pub assume_specification<R: io::Read>[ gzip::Decoder::<R>::new ](inner: R) -> (result: Result<
    gzip::Decoder<R>,
    io::Error,
>)
    ensures
        reader_model_valid::<R>() ==> (inner.remaining_bytes() matches Some(stream) && gzip_decoded(
            stream,
        ) matches Some(plain) ==> {
            result matches Ok(decoder) && gzip_remaining(&decoder) == Some(plain)
        }),
;

pub assume_specification<R: io::Read>[ zlib::Decoder::<R>::new ](inner: R) -> (result: Result<
    zlib::Decoder<R>,
    io::Error,
>)
    ensures
        reader_model_valid::<R>() ==> (inner.remaining_bytes() matches Some(stream) && zlib_decoded(
            stream,
        ) matches Some(plain) ==> {
            result matches Ok(decoder) && zlib_remaining(&decoder) == Some(plain)
        }),
;

} // verus!
