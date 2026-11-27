// SPDX-License-Identifier: MPL-2.0
//! Trusted libflate 2.3.2 models; codec correctness is assumed.
use vstd::prelude::*;

use alloc::vec::Vec;
use libflate::{Finish, gzip, lz77::Lz77Encode, zlib};
use no_std_io2::io;

use super::no_std_io2::{ReadSpec, ReadSpecImpl, WriteSpec, WriteSpecImpl};

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

pub open spec fn gzip_encoding(plain: Seq<u8>, stream: Seq<u8>) -> bool {
    &&& has_gzip_prefix(stream)
    &&& gzip_decoded(stream) == Some(plain)
}

pub open spec fn zlib_encoding(plain: Seq<u8>, stream: Seq<u8>) -> bool {
    &&& has_zlib_prefix(stream)
    &&& zlib_decoded(stream) == Some(plain)
}

pub broadcast axiom fn axiom_gzip_writer_model()
    ensures
        #[trigger] <gzip::Encoder<Vec<u8>> as WriteSpec>::obeys_writer_model(),
;

pub broadcast axiom fn axiom_zlib_writer_model()
    ensures
        #[trigger] <zlib::Encoder<Vec<u8>> as WriteSpec>::obeys_writer_model(),
;

pub broadcast axiom fn axiom_gzip_reader_model<'a>()
    ensures
        #[trigger] <gzip::Decoder<&'a [u8]> as ReadSpec>::obeys_reader_model(),
;

pub broadcast axiom fn axiom_zlib_reader_model<'a>()
    ensures
        #[trigger] <zlib::Decoder<&'a [u8]> as ReadSpec>::obeys_reader_model(),
;

pub broadcast group group_libflate_models {
    axiom_gzip_writer_model,
    axiom_zlib_writer_model,
    axiom_gzip_reader_model,
    axiom_zlib_reader_model,
}

pub ghost struct EncoderState<W> {
    pub initial_writer: W,
    pub plain: Seq<u8>,
}

pub uninterp spec fn gzip_state<W, E>(encoder: &gzip::Encoder<W, E>) -> Option<EncoderState<W>>;

pub uninterp spec fn zlib_state<W, E>(encoder: &zlib::Encoder<W, E>) -> Option<EncoderState<W>>;

#[verifier::external_trait_specification]
pub trait ExLz77Encode {
    type ExternalTraitSpecificationFor: Lz77Encode;
}

impl<W: io::Write, E: Lz77Encode> WriteSpecImpl for gzip::Encoder<W, E> {
    uninterp spec fn obeys_writer_model() -> bool;

    open spec fn write_all_success_condition(&self) -> bool {
        cfg!(feature = "std") && <Self as WriteSpec>::obeys_writer_model()
            && gzip_state(self) is Some
    }

    open spec fn wrote_all(&self, input: Seq<u8>, next: &Self) -> bool {
        gzip_state(self) matches Some(state) ==> gzip_state(next) == Some(
            EncoderState { plain: state.plain + input, ..state },
        )
    }
}

impl<W: io::Write, E: Lz77Encode> WriteSpecImpl for zlib::Encoder<W, E> {
    uninterp spec fn obeys_writer_model() -> bool;

    open spec fn write_all_success_condition(&self) -> bool {
        cfg!(feature = "std") && <Self as WriteSpec>::obeys_writer_model()
            && zlib_state(self) is Some
    }

    open spec fn wrote_all(&self, input: Seq<u8>, next: &Self) -> bool {
        zlib_state(self) matches Some(state) ==> zlib_state(next) == Some(
            EncoderState { plain: state.plain + input, ..state },
        )
    }
}

pub assume_specification<W: io::Write>[ gzip::Encoder::<W>::new ](inner: W) -> (result: Result<
    gzip::Encoder<W>,
    io::Error,
>)
    ensures
        <gzip::Encoder<W> as WriteSpec>::obeys_writer_model() ==> (result matches Ok(encoder)
            && gzip_state(&encoder) == Some(
            EncoderState { initial_writer: inner, plain: Seq::empty() },
        )),
;

pub assume_specification<W: io::Write>[ zlib::Encoder::<W>::new ](inner: W) -> (result: Result<
    zlib::Encoder<W>,
    io::Error,
>)
    ensures
        <zlib::Encoder<W> as WriteSpec>::obeys_writer_model() ==> (result matches Ok(encoder)
            && zlib_state(&encoder) == Some(
            EncoderState { initial_writer: inner, plain: Seq::empty() },
        )),
;

pub uninterp spec fn finish_value<T, E>(finish: Finish<T, E>) -> T;

pub uninterp spec fn finish_error<T, E>(finish: Finish<T, E>) -> Option<E>;

pub assume_specification<W: io::Write, E: Lz77Encode>[ gzip::Encoder::<W, E>::finish ](
    encoder: gzip::Encoder<W, E>,
) -> (result: Finish<W, io::Error>)
    ensures
        <gzip::Encoder<W, E> as WriteSpec>::obeys_writer_model() ==> (gzip_state(
            &encoder,
        ) matches Some(state) ==> {
            &&& finish_error(result) is None
            &&& exists|stream: Seq<u8>| #[trigger]
                gzip_encoding(state.plain, stream) && state.initial_writer.wrote_all(
                    stream,
                    &finish_value(result),
                )
        }),
;

pub assume_specification<W: io::Write, E: Lz77Encode>[ zlib::Encoder::<W, E>::finish ](
    encoder: zlib::Encoder<W, E>,
) -> (result: Finish<W, io::Error>)
    ensures
        <zlib::Encoder<W, E> as WriteSpec>::obeys_writer_model() ==> (zlib_state(
            &encoder,
        ) matches Some(state) ==> {
            &&& finish_error(result) is None
            &&& exists|stream: Seq<u8>| #[trigger]
                zlib_encoding(state.plain, stream) && state.initial_writer.wrote_all(
                    stream,
                    &finish_value(result),
                )
        }),
;

pub assume_specification<T, E>[ Finish::<T, E>::into_result ](finish: Finish<T, E>) -> Result<T, E>
    returns
        match finish_error(finish) {
            None => Ok(finish_value(finish)),
            Some(error) => Err(error),
        },
;

pub uninterp spec fn gzip_remaining<R>(decoder: &gzip::Decoder<R>) -> Option<Seq<u8>>;

pub uninterp spec fn zlib_remaining<R>(decoder: &zlib::Decoder<R>) -> Option<Seq<u8>>;

// Both decoder models are established only for byte slices. The success
// conditions retain the alloc-only model: no_std_io2 0.9.4 uses Vec::reserve,
// while std's read_to_end can return an allocation error from try_reserve.
// These conditions rely on the build keeping no_std_io2/std disabled whenever
// vstd_extra/std is disabled. Cargo feature unification can enable no_std_io2/std
// independently, selecting std::io and making the success guarantee unsound.
impl<R: io::Read> ReadSpecImpl for gzip::Decoder<R> {
    uninterp spec fn obeys_reader_model() -> bool;

    open spec fn remaining_bytes(&self) -> Option<Seq<u8>> {
        gzip_remaining(self)
    }

    open spec fn read_to_end_success_condition(&self) -> bool {
        !cfg!(feature = "std") && <Self as ReadSpec>::obeys_reader_model()
            && gzip_remaining(self) is Some
    }
}

impl<R: io::Read> ReadSpecImpl for zlib::Decoder<R> {
    uninterp spec fn obeys_reader_model() -> bool;

    open spec fn remaining_bytes(&self) -> Option<Seq<u8>> {
        zlib_remaining(self)
    }

    open spec fn read_to_end_success_condition(&self) -> bool {
        !cfg!(feature = "std") && <Self as ReadSpec>::obeys_reader_model()
            && zlib_remaining(self) is Some
    }
}

pub assume_specification<R: io::Read>[ gzip::Decoder::<R>::new ](inner: R) -> (result: Result<
    gzip::Decoder<R>,
    io::Error,
>)
    ensures
        <gzip::Decoder<R> as ReadSpec>::obeys_reader_model() && R::obeys_reader_model() ==> {
            inner.remaining_bytes() matches Some(stream) && gzip_decoded(stream) matches Some(plain) ==> {
                result matches Ok(decoder) && gzip_remaining(&decoder) == Some(plain)
            }
        },
;

pub assume_specification<R: io::Read>[ zlib::Decoder::<R>::new ](inner: R) -> (result: Result<
    zlib::Decoder<R>,
    io::Error,
>)
    ensures
        <zlib::Decoder<R> as ReadSpec>::obeys_reader_model() && R::obeys_reader_model() ==> {
            inner.remaining_bytes() matches Some(stream) && zlib_decoded(stream) matches Some(plain) ==> {
                result matches Ok(decoder) && zlib_remaining(&decoder) == Some(plain)
            }
        },
;

} // verus!
