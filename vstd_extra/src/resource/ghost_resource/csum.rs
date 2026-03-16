//！ Sum types for ghost resources.
use vstd::pcm::Loc;
use vstd::prelude::*;
use vstd::storage_protocol::*;

use crate::resource::storage_protocol::csum::*;
use crate::sum::*;

use super::excl::UniqueTokenStorage;

verus! {

pub tracked struct SumResource<K,A,B,W,V> {
    pub r: StorageResource<K, Sum<W, V>, CsumP<A, B>>,
}

impl <K,W,V,A:Protocol<K,W>,B:Protocol<K,V>> SumResource<K,A,B,W,V> {

pub open spec fn id(self) -> Loc {
    self.r.loc()
}

pub open spec fn protocol_monoid(self) -> CsumP<A, B> {
    self.r.value()
}

pub open spec fn is_empty(self) -> bool {
    self.protocol_monoid() is Unit
}

pub open spec fn is_left(self) -> bool {
    self.protocol_monoid() is Cinl
}

pub open spec fn is_right(self) -> bool {
    self.protocol_monoid() is Cinr
}
}

} // verus!
