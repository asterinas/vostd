use core::sync::atomic::Ordering;

use vstd::prelude::*;
use vstd::resource::Loc;
use vstd::resource::ghost_var::{GhostVar, GhostVarAuth};

use crate::task::RunningTaskContext;

verus! {

pub struct CpuId(u32);

/// The fixed set of CPUs participating in system-wide protocols.
///
/// OSTD does not support CPU hotplug, so the executable `num_cpus()` value is
/// stable after boot. Keeping that set abstract here avoids exposing the
/// executable bitset representation to clients of this specification.
pub uninterp spec fn online_cpus() -> Set<CpuId>;

impl CpuId {
    #[verifier::external_body]
    pub fn current(Tracked(context): Tracked<&RunningTaskContext>) -> (res: Self)
        requires
            context.wf(),
        ensures
            res == context.cpu(),
            online_cpus().contains(res),
    {
        unimplemented!()
    }
}

/// Linear shadow state for an [`AtomicCpuSet`].
///
/// The token is deliberately separate from the executable bitset. Clients
/// that serialize all operations (the RCU monitor does so with its state
/// lock) move this token through `store`, `add`, and `load`, obtaining an exact
/// logical view despite the executable type using atomic words internally.
pub tracked struct AtomicCpuSetToken {
    identity: GhostVarAuth<()>,
    ghost cpus: Set<CpuId>,
}

impl AtomicCpuSetToken {
    pub closed spec fn id(self) -> Loc {
        self.identity.id()
    }

    pub closed spec fn cpus(self) -> Set<CpuId> {
        self.cpus
    }

    pub closed spec fn wf(self) -> bool {
        self.cpus().subset_of(online_cpus())
    }
}

pub struct AtomicCpuSet {
    tracked_identity: Tracked<Option<GhostVarAuth<()>>>,
    tracked_peer: Tracked<GhostVar<()>>,
    ghost_initial: Ghost<Set<CpuId>>,
}

impl AtomicCpuSet {
    pub closed spec fn id(self) -> Loc {
        self.tracked_peer@.id()
    }

    pub closed spec fn token_available(self) -> bool {
        self.tracked_identity@ is Some
    }

    pub closed spec fn initial_cpus(self) -> Set<CpuId> {
        self.ghost_initial@
    }

    pub closed spec fn wf(self) -> bool {
        &&& self.initial_cpus().subset_of(online_cpus())
        &&& self.token_available() ==> self.tracked_identity@->Some_0.id() == self.id()
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.wf()
    }

    pub fn new(_initial: CpuSet) -> (res: Self)
        requires
            _initial.cpus.subset_of(online_cpus()),
        ensures
            res.token_available(),
            res.initial_cpus() == _initial.cpus,
            res.wf(),
    {
        let tracked (identity, peer) = GhostVarAuth::new(());
        Self {
            tracked_identity: Tracked(Some(identity)),
            tracked_peer: Tracked(peer),
            ghost_initial: Ghost(_initial.cpus),
        }
    }

    /// Extracts the unique logical state used to verify serialized operations
    /// on this atomic set.
    pub proof fn tracked_take_token(tracked &mut self) -> (tracked res: AtomicCpuSetToken)
        requires
            old(self).token_available(),
        ensures
            !final(self).token_available(),
            final(self).id() == old(self).id(),
            final(self).initial_cpus() == old(self).initial_cpus(),
            res.id() == final(self).id(),
            res.cpus() == final(self).initial_cpus(),
            res.wf(),
    {
        use_type_invariant(&*self);
        let tracked identity = self.tracked_identity.borrow_mut().tracked_take();
        let tracked res = AtomicCpuSetToken { identity, cpus: self.ghost_initial@ };
        assert(res.id() == self.id());
        res
    }

    #[verus_spec(res =>
        with
            Tracked(token): Tracked<&AtomicCpuSetToken>,
        requires
            token.id() == self.id(),
            token.wf(),
        ensures
            res.cpus == token.cpus(),
    )]
    #[verifier::external_body]
    pub fn load(&self, _ordering: Ordering) -> CpuSet
        no_unwind
    {
        unimplemented!()
    }

    #[verus_spec(
        with
            Tracked(token): Tracked<&mut AtomicCpuSetToken>,
        requires
            old(token).id() == self.id(),
            _value.cpus.subset_of(online_cpus()),
        ensures
            final(token).id() == old(token).id(),
            final(token).cpus() == _value.cpus,
            final(token).wf(),
    )]
    pub fn store(&self, _value: &CpuSet, _ordering: Ordering)
        no_unwind
    {
        proof {
            token.cpus = _value.cpus;
        }
    }

    #[verus_spec(
        with
            Tracked(token): Tracked<&mut AtomicCpuSetToken>,
        requires
            old(token).id() == self.id(),
            old(token).wf(),
            online_cpus().contains(_cpu),
        ensures
            final(token).id() == old(token).id(),
            final(token).cpus() == old(token).cpus().insert(_cpu),
            final(token).wf(),
    )]
    pub fn add(&self, _cpu: CpuId, _ordering: Ordering)
        no_unwind
    {
        proof {
            token.cpus = token.cpus.insert(_cpu);
        }
    }
}

pub struct CpuSet {
    pub cpus: Set<CpuId>,
}

impl CpuSet {
    pub open spec fn new_empty_spec() -> Self {
        Self { cpus: Set::empty() }
    }

    #[verifier::external_body]
    #[verifier::when_used_as_spec(new_empty_spec)]
    pub fn new_empty() -> Self
        returns
            Self::new_empty_spec(),
        no_unwind
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub fn is_full(&self) -> (res: bool)
        ensures
            res == (self.cpus == online_cpus()),
        no_unwind
    {
        unimplemented!()
    }
}

pub trait PinCurrentCpu {

}

} // verus!
