// SPDX-License-Identifier: MPL-2.0
//! Trusted models for no_std_io2 0.9.4 byte readers and writers.
use vstd::prelude::*;

use alloc::vec::Vec;
use no_std_io2::io;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExIoError(io::Error);

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(WriteSpec via WriteSpecImpl)]
pub trait ExWrite {
    type ExternalTraitSpecificationFor: io::Write;

    spec fn obeys_writer_model() -> bool;

    spec fn wrote_all(&self, input: Seq<u8>, next: &Self) -> bool;

    fn write_all(&mut self, input: &[u8]) -> (result: Result<(), io::Error>)
        ensures
            Self::obeys_writer_model() ==> {
                &&& result is Ok
                &&& old(self).wrote_all(input@, final(self))
            },
    ;
}

} // verus!
macro_rules! impl_vec_writer_model {
    ($($impl_header:tt)+) => {
        verus! {
            $($impl_header)+ {
                open spec fn obeys_writer_model() -> bool {
                    true
                }

                open spec fn wrote_all(&self, input: Seq<u8>, next: &Self) -> bool {
                    next@ == self@ + input
                }
            }
        }
    };
}

#[cfg(not(feature = "std"))]
impl_vec_writer_model!(impl WriteSpecImpl for Vec<u8>);

#[cfg(feature = "std")]
impl_vec_writer_model!(impl<A: core::alloc::Allocator> WriteSpecImpl for Vec<u8, A>);

verus! {

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(ReadSpec via ReadSpecImpl)]
pub trait ExRead {
    type ExternalTraitSpecificationFor: io::Read;

    spec fn obeys_reader_model() -> bool;

    spec fn remaining_bytes(&self) -> Option<Seq<u8>>;

    /// Sufficient for an Ok result on normal return; does not guarantee allocation or termination.
    spec fn read_to_end_success_condition(&self) -> bool;

    /// Data correctness and absence of a returned error are separate guarantees.
    fn read_to_end(&mut self, output: &mut Vec<u8>) -> (result: Result<usize, io::Error>)
        ensures
            old(self).read_to_end_success_condition() ==> result is Ok,
            Self::obeys_reader_model() ==> (old(self).remaining_bytes() matches Some(plain) ==> {
                result matches Ok(count) ==> {
                    &&& count == plain.len()
                    &&& final(output)@ == old(output)@ + plain
                    &&& final(self).remaining_bytes() == Some(Seq::<u8>::empty())
                }
            }),
    ;
}

impl ReadSpecImpl for &[u8] {
    open spec fn obeys_reader_model() -> bool {
        true
    }

    open spec fn remaining_bytes(&self) -> Option<Seq<u8>> {
        Some(self@)
    }

    open spec fn read_to_end_success_condition(&self) -> bool {
        false
    }
}

} // verus!
