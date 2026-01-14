use core::marker::PhantomData;
use vstd::pcm::PCM;
use vstd::prelude::*;
use vstd::storage_protocol::*;

verus! {

/// The hybrid product of a PCM and a storage-protocol resource algebra.
pub tracked struct HybridProduct<P: PCM, S: Protocol<K, V>, K, V> {
    pub pcm: P,
    pub protocol: S,
    /// A Rust compiler restriction.
    pub _phantom: PhantomData<(K, V)>,
}

impl<P, S, K, V> Protocol<K, V> for HybridProduct<P, S, K, V> where P: PCM, S: Protocol<K, V> {
    open spec fn op(self, other: Self) -> Self {
        HybridProduct {
            pcm: self.pcm.op(other.pcm),
            protocol: self.protocol.op(other.protocol),
            _phantom: PhantomData,
        }
    }

    open spec fn rel(self, s: Map<K, V>) -> bool {
        self.protocol.rel(s)
    }

    open spec fn unit() -> Self {
        HybridProduct { pcm: P::unit(), protocol: S::unit(), _phantom: PhantomData }
    }

    proof fn commutative(a: Self, b: Self) {
        P::commutative(a.pcm, b.pcm);
        S::commutative(a.protocol, b.protocol);
    }

    proof fn associative(a: Self, b: Self, c: Self) {
        P::associative(a.pcm, b.pcm, c.pcm);
        S::associative(a.protocol, b.protocol, c.protocol);
    }

    proof fn op_unit(a: Self) {
        P::op_unit(a.pcm);
        S::op_unit(a.protocol);
    }
}

impl<P, S, K, V> HybridProduct<P, S, K, V> where P: PCM, S: Protocol<K, V> {
    pub open spec fn pcm(self) -> P {
        self.pcm
    }

    pub open spec fn protocol(self) -> S {
        self.protocol
    }
}

} // verus!
