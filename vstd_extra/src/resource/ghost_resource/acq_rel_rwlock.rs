//! Acquire-release ghost resources for reader-writer lock verification.
//!
//! This module packages the Leaf-style resources used to verify a reader-writer
//! lock into one reusable permission carrier.  The executable acquire/release
//! semantics are still provided by the lock's atomics; this carrier records the
//! ownership transfer facts that each successful acquire, failed acquire
//! rollback, release, and upgrade path must maintain.

use crate::resource::ghost_resource::{count::*, csum::*, excl::*, tokens::*};
use crate::sum::*;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::relations::frame_preserving_update;

verus! {

/// Standalone PCM carrier for acquire-release reader-writer lock protocols.
///
/// `Elem` counts the currently owned protocol fragments.  `phase` is ghost
/// publication metadata: it composes monotonically but does not affect validity,
/// so phase-only updates are frame-preserving.
pub ghost enum AcqRelRwPCM<const MAX_READERS: u64, const READ_RETRACT: u64> {
    Unit,
    Elem {
        readers: nat,
        upreaders: nat,
        writers: nat,
        pending_read_fails: nat,
        pending_upread_fails: nat,
        phase: nat,
    },
    Invalid,
}

impl<const MAX_READERS: u64, const READ_RETRACT: u64> AcqRelRwPCM<
    MAX_READERS,
    READ_RETRACT,
> {
    pub open spec fn elem(
        readers: nat,
        upreaders: nat,
        writers: nat,
        pending_read_fails: nat,
        pending_upread_fails: nat,
        phase: nat,
    ) -> Self {
        AcqRelRwPCM::Elem {
            readers,
            upreaders,
            writers,
            pending_read_fails,
            pending_upread_fails,
            phase,
        }
    }

    pub open spec fn wf_counts(
        readers: nat,
        upreaders: nat,
        writers: nat,
        pending_read_fails: nat,
        pending_upread_fails: nat,
    ) -> bool {
        &&& readers <= MAX_READERS
        &&& upreaders <= 1
        &&& writers <= 1
        &&& pending_read_fails <= READ_RETRACT
        &&& pending_upread_fails <= 1
        &&& upreaders + pending_upread_fails <= 1
        &&& writers > 0 ==> readers == 0 && upreaders == 0
    }

    pub open spec fn readers(self) -> nat
        recommends
            self is Elem,
    {
        self->readers
    }

    pub open spec fn upreaders(self) -> nat
        recommends
            self is Elem,
    {
        self->upreaders
    }

    pub open spec fn writers(self) -> nat
        recommends
            self is Elem,
    {
        self->writers
    }

    pub open spec fn pending_read_fails(self) -> nat
        recommends
            self is Elem,
    {
        self->pending_read_fails
    }

    pub open spec fn pending_upread_fails(self) -> nat
        recommends
            self is Elem,
    {
        self->pending_upread_fails
    }

    pub open spec fn phase(self) -> nat
        recommends
            self is Elem,
    {
        self->phase
    }
}

impl<const MAX_READERS: u64, const READ_RETRACT: u64> ResourceAlgebra for AcqRelRwPCM<
    MAX_READERS,
    READ_RETRACT,
> {
    open spec fn valid(self) -> bool {
        match self {
            AcqRelRwPCM::Unit => true,
            AcqRelRwPCM::Elem {
                readers,
                upreaders,
                writers,
                pending_read_fails,
                pending_upread_fails,
                phase: _,
            } => Self::wf_counts(
                readers,
                upreaders,
                writers,
                pending_read_fails,
                pending_upread_fails,
            ),
            AcqRelRwPCM::Invalid => false,
        }
    }

    open spec fn op(a: Self, b: Self) -> Self {
        match (a, b) {
            (AcqRelRwPCM::Invalid, _) => AcqRelRwPCM::Invalid,
            (_, AcqRelRwPCM::Invalid) => AcqRelRwPCM::Invalid,
            (AcqRelRwPCM::Unit, x) => x,
            (x, AcqRelRwPCM::Unit) => x,
            (
                AcqRelRwPCM::Elem {
                    readers: ar,
                    upreaders: au,
                    writers: aw,
                    pending_read_fails: apr,
                    pending_upread_fails: apu,
                    phase: ap,
                },
                AcqRelRwPCM::Elem {
                    readers: br,
                    upreaders: bu,
                    writers: bw,
                    pending_read_fails: bpr,
                    pending_upread_fails: bpu,
                    phase: bp,
                },
            ) => AcqRelRwPCM::Elem {
                readers: ar + br,
                upreaders: au + bu,
                writers: aw + bw,
                pending_read_fails: apr + bpr,
                pending_upread_fails: apu + bpu,
                phase: ap + bp,
            },
        }
    }

    proof fn valid_op(a: Self, b: Self) {
    }

    proof fn commutative(a: Self, b: Self) {
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }
}

impl<const MAX_READERS: u64, const READ_RETRACT: u64> PCM for AcqRelRwPCM<
    MAX_READERS,
    READ_RETRACT,
> {
    open spec fn unit() -> Self {
        AcqRelRwPCM::Unit
    }

    proof fn op_unit(self) {
    }

    proof fn unit_valid() {
    }
}

pub proof fn lemma_acq_rel_rw_pcm_phase_update<
    const MAX_READERS: u64,
    const READ_RETRACT: u64,
>(
    readers: nat,
    upreaders: nat,
    writers: nat,
    pending_read_fails: nat,
    pending_upread_fails: nat,
    old_phase: nat,
    new_phase: nat,
)
    ensures
        frame_preserving_update::<AcqRelRwPCM<MAX_READERS, READ_RETRACT>>(
            AcqRelRwPCM::elem(
                readers,
                upreaders,
                writers,
                pending_read_fails,
                pending_upread_fails,
                old_phase,
            ),
            AcqRelRwPCM::elem(
                readers,
                upreaders,
                writers,
                pending_read_fails,
                pending_upread_fails,
                new_phase,
            ),
        ),
{
    assert forall|c: AcqRelRwPCM<MAX_READERS, READ_RETRACT>|
        #![trigger
            AcqRelRwPCM::<MAX_READERS, READ_RETRACT>::op(
                AcqRelRwPCM::elem(
                    readers,
                    upreaders,
                    writers,
                    pending_read_fails,
                    pending_upread_fails,
                    old_phase,
                ),
                c,
            ),
            AcqRelRwPCM::<MAX_READERS, READ_RETRACT>::op(
                AcqRelRwPCM::elem(
                    readers,
                    upreaders,
                    writers,
                    pending_read_fails,
                    pending_upread_fails,
                    new_phase,
                ),
                c,
            )
        ]
        AcqRelRwPCM::<MAX_READERS, READ_RETRACT>::op(
            AcqRelRwPCM::elem(
                readers,
                upreaders,
                writers,
                pending_read_fails,
                pending_upread_fails,
                old_phase,
            ),
            c,
        ).valid() implies AcqRelRwPCM::<MAX_READERS, READ_RETRACT>::op(
            AcqRelRwPCM::elem(
                readers,
                upreaders,
                writers,
                pending_read_fails,
                pending_upread_fails,
                new_phase,
            ),
            c,
        ).valid() by {
    }
}

pub proof fn lemma_acq_rel_rw_pcm_release_read_update<
    const MAX_READERS: u64,
    const READ_RETRACT: u64,
>(
    readers: nat,
    upreaders: nat,
    pending_read_fails: nat,
    pending_upread_fails: nat,
    old_phase: nat,
    new_phase: nat,
)
    requires
        readers > 0,
    ensures
        frame_preserving_update::<AcqRelRwPCM<MAX_READERS, READ_RETRACT>>(
            AcqRelRwPCM::elem(
                readers,
                upreaders,
                0,
                pending_read_fails,
                pending_upread_fails,
                old_phase,
            ),
            AcqRelRwPCM::elem(
                (readers - 1) as nat,
                upreaders,
                0,
                pending_read_fails,
                pending_upread_fails,
                new_phase,
            ),
        ),
{
    assert forall|c: AcqRelRwPCM<MAX_READERS, READ_RETRACT>|
        #![trigger
            AcqRelRwPCM::<MAX_READERS, READ_RETRACT>::op(
                AcqRelRwPCM::elem(
                    readers,
                    upreaders,
                    0,
                    pending_read_fails,
                    pending_upread_fails,
                    old_phase,
                ),
                c,
            ),
            AcqRelRwPCM::<MAX_READERS, READ_RETRACT>::op(
                AcqRelRwPCM::elem(
                    (readers - 1) as nat,
                    upreaders,
                    0,
                    pending_read_fails,
                    pending_upread_fails,
                    new_phase,
                ),
                c,
            )
        ]
        AcqRelRwPCM::<MAX_READERS, READ_RETRACT>::op(
            AcqRelRwPCM::elem(
                readers,
                upreaders,
                0,
                pending_read_fails,
                pending_upread_fails,
                old_phase,
            ),
            c,
        ).valid() implies AcqRelRwPCM::<MAX_READERS, READ_RETRACT>::op(
            AcqRelRwPCM::elem(
                (readers - 1) as nat,
                upreaders,
                0,
                pending_read_fails,
                pending_upread_fails,
                new_phase,
            ),
            c,
        ).valid() by {
    }
}

pub proof fn lemma_acq_rel_rw_pcm_cancel_pending_read_update<
    const MAX_READERS: u64,
    const READ_RETRACT: u64,
>(
    readers: nat,
    upreaders: nat,
    writers: nat,
    pending_read_fails: nat,
    pending_upread_fails: nat,
    phase: nat,
)
    requires
        pending_read_fails > 0,
    ensures
        frame_preserving_update::<AcqRelRwPCM<MAX_READERS, READ_RETRACT>>(
            AcqRelRwPCM::elem(
                readers,
                upreaders,
                writers,
                pending_read_fails,
                pending_upread_fails,
                phase,
            ),
            AcqRelRwPCM::elem(
                readers,
                upreaders,
                writers,
                (pending_read_fails - 1) as nat,
                pending_upread_fails,
                phase,
            ),
        ),
{
    assert forall|c: AcqRelRwPCM<MAX_READERS, READ_RETRACT>|
        #![trigger
            AcqRelRwPCM::<MAX_READERS, READ_RETRACT>::op(
                AcqRelRwPCM::elem(
                    readers,
                    upreaders,
                    writers,
                    pending_read_fails,
                    pending_upread_fails,
                    phase,
                ),
                c,
            ),
            AcqRelRwPCM::<MAX_READERS, READ_RETRACT>::op(
                AcqRelRwPCM::elem(
                    readers,
                    upreaders,
                    writers,
                    (pending_read_fails - 1) as nat,
                    pending_upread_fails,
                    phase,
                ),
                c,
            )
        ]
        AcqRelRwPCM::<MAX_READERS, READ_RETRACT>::op(
            AcqRelRwPCM::elem(
                readers,
                upreaders,
                writers,
                pending_read_fails,
                pending_upread_fails,
                phase,
            ),
            c,
        ).valid() implies AcqRelRwPCM::<MAX_READERS, READ_RETRACT>::op(
            AcqRelRwPCM::elem(
                readers,
                upreaders,
                writers,
                (pending_read_fails - 1) as nat,
                pending_upread_fails,
                phase,
            ),
            c,
        ).valid() by {
    }
}

/// Token reserved in the lock while write permission is checked out.
pub type AcqRelNoPerm<R> = EmptyCount<R>;

/// Half of the protected permission, shared by upread and read modes.
pub type AcqRelHalfPerm<R> = Count<R>;

/// One read permission plus knowledge that the lock is in shared mode.
pub type AcqRelReadPerm<R> = (
    AcqRelHalfPerm<R>,
    OneLeftKnowledge<AcqRelHalfPerm<R>, AcqRelNoPerm<R>, 3>,
);

/// The authoritative acquire-release resource state stored under the lock
/// atomic invariant.
pub tracked struct AcqRelRwPerms<R, const MAX_READERS: u64, const READ_RETRACT: u64> {
    /// Shared-vs-writer mode and the resource owner for the protected value.
    pub core_token: SumResource<AcqRelHalfPerm<R>, AcqRelNoPerm<R>, 3>,
    /// Rollback budget for failed read attempts that have already incremented
    /// the concrete reader bits.
    pub read_retract_token: TokenResource<READ_RETRACT>,
    /// Rollback token for the failed upread path that transiently set the
    /// concrete upread bit.
    pub upread_retract_token: Option<UniqueToken>,
    /// The unique live upgradeable-reader token, when it is stored in the lock.
    pub upreader_guard_token: Option<
        OneLeftOwner<AcqRelHalfPerm<R>, AcqRelNoPerm<R>, 3>,
    >,
    /// Pool of read guard permissions, or an empty marker while a writer owns
    /// the protected resource.
    pub read_guard_token: Sum<
        CountResource<AcqRelReadPerm<R>, MAX_READERS>,
        EmptyCount<AcqRelReadPerm<R>, MAX_READERS>,
    >,
    /// Ghost publication phase.  Each release may advance this value; acquire
    /// paths carry tokens from the phase they observed.
    pub phase: nat,
    pub ghost core_token_id: vstd::resource::Loc,
    pub ghost frac_id: vstd::resource::Loc,
    pub ghost read_retract_token_id: vstd::resource::Loc,
    pub ghost upread_retract_token_id: vstd::resource::Loc,
    pub ghost read_guard_token_id: vstd::resource::Loc,
}

impl<R, const MAX_READERS: u64, const READ_RETRACT: u64> AcqRelRwPerms<
    R,
    MAX_READERS,
    READ_RETRACT,
> {
    /// Construct the initial shared-mode resource state from full ownership of
    /// the protected resource.
    pub proof fn alloc(tracked resource: R) -> (tracked result: Self)
        requires
            MAX_READERS > 0,
            READ_RETRACT > 0,
        ensures
            result.core_token_id() == result.core_token.id(),
            result.read_retract_token_id() == result.read_retract_token.id(),
            result.upread_retract_token is Some,
            result.upread_retract_token_id() == result.upread_retract_token->0.id(),
            result.read_guard_token is Left,
            result.read_guard_token_id() == result.read_guard_token.left().id(),
            result.core_token.wf(),
            result.core_token.is_left(),
            !result.core_token.is_resource_owner(),
            result.core_token.frac() == 1,
            result.read_retract_token.wf(),
            result.read_retract_token.is_full(),
            result.upread_retract_token->0.wf(),
            result.upreader_guard_token is Some,
            result.upreader_guard_token->0.id() == result.core_token_id(),
            result.upreader_guard_token->0.has_resource(),
            result.upreader_guard_token->0.resource().id() == result.frac_id(),
            result.upreader_guard_token->0.resource().resource() == resource,
            result.upreader_guard_token->0.resource().frac() == 1,
            result.upreader_guard_token->0.wf(),
            result.read_guard_token.left().wf(),
            result.read_guard_token.left().id() == result.read_guard_token_id(),
            result.read_guard_token.left().not_empty(),
            result.read_guard_token.left().resource().0.id() == result.frac_id(),
            result.read_guard_token.left().resource().0.resource() == resource,
            result.read_guard_token.left().resource().0.frac() == 1,
            result.read_guard_token.left().resource().1.id() == result.core_token_id(),
            result.phase == 0,
    {
        let tracked mut full_perm = Count::<R>::new(resource);
        let tracked read_half_perm = full_perm.split(1int);
        let ghost frac_id = full_perm.id();
        let tracked mut core_token = SumResource::alloc_left(full_perm);
        let tracked read_retract_token = TokenResource::<READ_RETRACT>::alloc(());
        let tracked upread_retract_token = UniqueToken::alloc(());
        let tracked upreader_guard_token = core_token.split_one_left_owner();
        let tracked left_token = core_token.split_one_left_knowledge();
        let tracked read_guard_token = CountResource::<AcqRelReadPerm<R>, MAX_READERS>::alloc(
            (read_half_perm, left_token),
        );
        AcqRelRwPerms {
            core_token,
            read_retract_token,
            upread_retract_token: Some(upread_retract_token),
            upreader_guard_token: Some(upreader_guard_token),
            read_guard_token: Sum::Left(read_guard_token),
            phase: 0,
            core_token_id: core_token.id(),
            frac_id,
            read_retract_token_id: read_retract_token.id(),
            upread_retract_token_id: upread_retract_token.id(),
            read_guard_token_id: read_guard_token.id(),
        }
    }

    pub closed spec fn core_token_id(self) -> vstd::resource::Loc {
        self.core_token_id
    }

    pub closed spec fn frac_id(self) -> vstd::resource::Loc {
        self.frac_id
    }

    pub closed spec fn read_retract_token_id(self) -> vstd::resource::Loc {
        self.read_retract_token_id
    }

    pub closed spec fn upread_retract_token_id(self) -> vstd::resource::Loc {
        self.upread_retract_token_id
    }

    pub closed spec fn read_guard_token_id(self) -> vstd::resource::Loc {
        self.read_guard_token_id
    }
}

} // verus!
