//! Csum storage protocol.

use vstd::prelude::*;
use vstd::pcm::Loc;
use vstd::prelude::*;
use vstd::storage_protocol::*;
use crate::sum::*;

verus!{

/// The Csum storage protocol.
pub ghost enum CsumP<A, B> {
    Unit,
    Cinl(A),
    Cinr(B),
    CsumInvalid,
}



}