//! **Probe: what the refcount protocol costs as a hand-written PCM.**
//!
//! This exists to price one decision — whether to drop `tokenized_state_machine!`
//! and build `mm`'s concurrency proof directly on the resource logic
//! (`vstd::resource::pcm::Resource`), the way `vstd_extra`'s `count.rs` does.
//!
//! It encodes just enough of [`RcState`] to state and prove **one** update —
//! `do_clone`, the `n → n+1` step — as a frame-preserving update, so it can be
//! compared line-for-line against the `#[inductive(do_clone)]` proof in
//! [`super::rc_tsm`].
//!
//! Delete once the TSM-vs-resource-logic question is settled.
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::relations::frame_preserving_update;

use super::rc_tsm::{REF_COUNT_MAX, RcState};

verus! {

/// The carrier: one authority (the band, held by the atomic invariant) plus
/// fragments (the pieces owners hold).
///
/// `Invalid` is the poison value. It is not optional bookkeeping: `op` must be
/// *associative and commutative as a total function*, so the "two authorities
/// met" case has to collapse to a single canonical element. Setting a `bad: bool`
/// flag while keeping the other fields breaks associativity when three
/// authorities compose — the two bracketings retain different `auth` fields.
pub ghost enum RcCarrier {
    Invalid,
    V { auth: Option<RcState>, readers: nat, permit: nat, unique: nat },
}

impl ResourceAlgebra for RcCarrier {
    /// Note every clause is an **inequality** (`readers <= n`), not the equation
    /// the protocol actually wants (`readers == n`).
    ///
    /// That is forced: `valid` must hold of every *sub*-composition, and the
    /// authority composed with only some of the fragments genuinely has fewer
    /// readers than the band records. Exact agreement — the `counter == |reader|`
    /// that makes the accounting theorem free in the TSM — is not expressible
    /// here without the remainder encoding (`count.rs`'s `frac`: the authority
    /// additionally holds the not-yet-handed-out shares).
    open spec fn valid(self) -> bool {
        match self {
            RcCarrier::Invalid => false,
            RcCarrier::V { auth, readers, permit, unique } => {
                &&& permit <= 1
                &&& unique <= 1
                &&& match auth {
                    Option::None => true,
                    Option::Some(RcState::Unused) => readers == 0 && permit == 0 && unique == 0,
                    Option::Some(RcState::Claimed) => readers == 0 && unique == 0,
                    Option::Some(RcState::Shared(n)) => {
                        &&& readers <= n
                        &&& 1 <= n
                        &&& n < REF_COUNT_MAX as nat
                        &&& permit == 0
                        &&& unique == 0
                    },
                    Option::Some(RcState::Unique) => readers == 0 && permit == 0,
                }
            },
        }
    }

    open spec fn op(a: Self, b: Self) -> Self {
        match (a, b) {
            (RcCarrier::Invalid, _) => RcCarrier::Invalid,
            (_, RcCarrier::Invalid) => RcCarrier::Invalid,
            (
                RcCarrier::V { auth: a_auth, readers: a_r, permit: a_p, unique: a_u },
                RcCarrier::V { auth: b_auth, readers: b_r, permit: b_p, unique: b_u },
            ) => {
                if a_auth is Some && b_auth is Some {
                    RcCarrier::Invalid
                } else {
                    RcCarrier::V {
                        auth: if a_auth is Some {
                            a_auth
                        } else {
                            b_auth
                        },
                        readers: (a_r + b_r) as nat,
                        permit: (a_p + b_p) as nat,
                        unique: (a_u + b_u) as nat,
                    }
                }
            },
        }
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }

    proof fn commutative(a: Self, b: Self) {
    }

    /// Validity is downward-closed under composition: a piece of a valid whole
    /// is valid. This is the obligation that forces every clause of `valid` to
    /// be an inequality — an equational clause would fail here.
    proof fn valid_op(a: Self, b: Self) {
    }
}

impl PCM for RcCarrier {
    open spec fn unit() -> Self {
        RcCarrier::V { auth: Option::None, readers: 0, permit: 0, unique: 0 }
    }

    proof fn op_unit(self) {
    }

    proof fn unit_valid() {
    }
}

/// The authority piece for band `s` — what the atomic invariant would hold
/// alongside the `PermissionU64`.
pub open spec fn auth(s: RcState) -> RcCarrier {
    RcCarrier::V { auth: Option::Some(s), readers: 0, permit: 0, unique: 0 }
}

/// `k` reader fragments — what handles hold.
pub open spec fn readers(k: nat) -> RcCarrier {
    RcCarrier::V { auth: Option::None, readers: k, permit: 0, unique: 0 }
}

/// **The comparison point: `do_clone` as a frame-preserving update.**
///
/// Going from "authority says `Shared(n)`, and I hold one reader" to
/// "authority says `Shared(n+1)`, and I hold two" — the `n → n+1` step, stated
/// over *arbitrary frames* rather than a fixed pre/post pair.
pub proof fn lemma_do_clone_frame_preserving(n: nat)
    requires
        1 <= n,
        n + 1 < REF_COUNT_MAX as nat,
    ensures
        frame_preserving_update(
            RcCarrier::V { auth: Option::Some(RcState::Shared(n)), readers: 1, permit: 0, unique: 0 },
            RcCarrier::V {
                auth: Option::Some(RcState::Shared((n + 1) as nat)),
                readers: 2,
                permit: 0,
                unique: 0,
            },
        ),
{
    let a = RcCarrier::V {
        auth: Option::Some(RcState::Shared(n)),
        readers: 1,
        permit: 0,
        unique: 0,
    };
    let b = RcCarrier::V {
        auth: Option::Some(RcState::Shared((n + 1) as nat)),
        readers: 2,
        permit: 0,
        unique: 0,
    };

    assert forall|c: RcCarrier| RcCarrier::op(a, c).valid() implies RcCarrier::op(b, c).valid() by {
        // The frame cannot be poison, and cannot carry a second authority —
        // either would make `op(a, c)` invalid, contradicting the premise.
        match c {
            RcCarrier::Invalid => {},
            RcCarrier::V { auth: c_auth, readers: c_r, permit: c_p, unique: c_u } => {
                if c_auth is Some {
                    // `op(a, c) == Invalid`, so the premise is false.
                } else {
                    // `op(a, c)` valid gives `1 + c_r <= n`; hence `2 + c_r <= n + 1`,
                    // and `n + 1 < REF_COUNT_MAX` is the caller's overflow guard.
                    assert(RcCarrier::op(a, c) == RcCarrier::V {
                        auth: Option::Some(RcState::Shared(n)),
                        readers: (1 + c_r) as nat,
                        permit: c_p,
                        unique: c_u,
                    });
                    assert(1 + c_r <= n);
                    assert(RcCarrier::op(b, c) == RcCarrier::V {
                        auth: Option::Some(RcState::Shared((n + 1) as nat)),
                        readers: (2 + c_r) as nat,
                        permit: c_p,
                        unique: c_u,
                    });
                }
            },
        }
    }
}

} // verus!
