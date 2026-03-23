//! Real-based fractional ghost resource.
use vstd::map::*;
use vstd::pcm::Loc;
use vstd::prelude::*;
use vstd::storage_protocol::*;

use crate::resource::storage_protocol::frac::*;

verus! {

///`FracStorage` define the actual storage resource that can be split
/// into arbitrary finite pieces for shared read access.
///
/// It can be seen as a real-based re-implementation of
/// `Frac`(https://verus-lang.github.io/verus/verusdoc/vstd/tokens/frac/struct.FracGhost.html).
use vstd::map::*;

pub struct FracStorage<T> {
    r: Option<StorageResource<(), T, FracP<T>>>,
}

impl<T> FracStorage<T> {
    #[verifier::type_invariant]
    spec fn type_inv(self) -> bool {
        &&& self.r is Some
        &&& self.protocol_monoid() is Frac
        &&& 0.0real < self.frac() && self.frac() <= 1.0real
    }

    pub closed spec fn storage_resource(self) -> StorageResource<(), T, FracP<T>> {
        self.r->Some_0
    }

    pub closed spec fn id(self) -> Loc {
        self.storage_resource().loc()
    }

    pub closed spec fn protocol_monoid(self) -> FracP<T> {
        self.storage_resource().value()
    }

    pub open spec fn resource(self) -> T {
        self.protocol_monoid().value()
    }

    pub closed spec fn frac(self) -> real {
        self.protocol_monoid().frac()
    }

    pub open spec fn has_full_frac(self) -> bool {
        self.frac() == 1.0real
    }

    /// Allocate a new fractional storage resource with full permission.
    pub proof fn alloc(tracked v: T) -> (tracked res: Self)
        ensures
            res.has_full_frac(),
    {
        let tracked mut m = Map::<(), T>::tracked_empty();
        m.tracked_insert((), v);
        let tracked resource = StorageResource::alloc(FracP::new(v), m);
        FracStorage { r: Some(resource) }
    }

    /// Split one token into two tokens whose quantities sum to the original.
    pub proof fn split(tracked &mut self) -> (tracked r: FracStorage<T>)
        ensures
            self.id() == old(self).id(),
            self.resource() == old(self).resource(),
            r.resource() == old(self).resource(),
            r.id() == old(self).id(),
            r.frac() + self.frac() == old(self).frac(),
    {
        use_type_invariant(&*self);
        Self::split_helper(&mut self.r)
    }

    /// Avoid breaking the type invariant.
    proof fn split_helper(tracked r: &mut Option<StorageResource<(), T, FracP<T>>>) -> (tracked res:
        Self)
        requires
            *old(r) is Some,
            old(r)->Some_0.value() is Frac,
            old(r)->Some_0.value().frac() > 0.0real,
            old(r)->Some_0.value().frac() <= 1.0real,
        ensures
            *r is Some,
            r->Some_0.value() is Frac,
            r->Some_0.value().frac() > 0.0real,
            r->Some_0.value().frac() <= 1.0real,
            res.id() == old(r)->Some_0.loc(),
            r->Some_0.loc() == old(r)->Some_0.loc(),
            r->Some_0.value().value() == old(r)->Some_0.value().value(),
            res.resource() == old(r)->Some_0.value().value(),
            res.frac() + r->Some_0.value().frac() == old(r)->Some_0.value().frac(),
    {
        let tracked mut storage_resource = r.tracked_take();
        let frac = storage_resource.value().frac();
        let half_frac = frac / 2.0real;
        let m = FracP::construct_frac(half_frac, storage_resource.value().value());
        let tracked (resource_1, resource_2) = storage_resource.split(m, m);
        *r = Some(resource_1);
        FracStorage { r: Some(resource_2) }
    }

    /// Obtain shared access to the underlying resource.
    pub proof fn borrow(tracked &self) -> (tracked s: &T)
        ensures
            *s == self.resource(),
    {
        use_type_invariant(self);
        let m = Map::<(), T>::empty().insert((), self.resource());
        self.protocol_monoid().lemma_guards();
        let tracked resource = StorageResource::guard(self.r.tracked_borrow(), m);
        resource.tracked_borrow(())
    }
}

} // verus!
