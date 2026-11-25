// SPDX-License-Identifier: MPL-2.0
//! Trusted models for no_std_io2 0.9.4 byte readers and writers.
use vstd::prelude::*;

use alloc::vec::Vec;
use no_std_io2::io;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExIoError(io::Error);

pub uninterp spec fn obeys_writer_model<W: ?Sized>() -> bool;

pub uninterp spec fn obeys_reader_model<R: ?Sized>() -> bool;

pub broadcast axiom fn axiom_vec_writer_model()
    ensures
        #[trigger] obeys_writer_model::<Vec<u8>>(),
;

pub broadcast axiom fn axiom_slice_reader_model<'a>()
    ensures
        #[trigger] obeys_reader_model::<&'a [u8]>(),
;

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(WriteSpec via WriteSpecImpl)]
pub trait ExWrite {
    type ExternalTraitSpecificationFor: io::Write;

    spec fn wrote_all(&self, input: Seq<u8>, next: &Self) -> bool;

    fn write_all(&mut self, input: &[u8]) -> (result: Result<(), io::Error>)
        ensures
            obeys_writer_model::<Self>() ==> {
                &&& result is Ok
                &&& old(self).wrote_all(input@, final(self))
            },
    ;
}

#[cfg(not(feature = "std"))]
impl WriteSpecImpl for Vec<u8> {
    open spec fn wrote_all(&self, input: Seq<u8>, next: &Self) -> bool {
        next@ == self@ + input
    }
}

#[cfg(feature = "std")]
impl<A: core::alloc::Allocator> WriteSpecImpl for Vec<u8, A> {
    open spec fn wrote_all(&self, input: Seq<u8>, next: &Self) -> bool {
        next@ == self@ + input
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
            obeys_reader_model::<Self>() ==> (old(self).remaining_bytes() matches Some(plain) ==> {
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
