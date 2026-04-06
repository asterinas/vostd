use vstd::prelude::*;

verus! {

    pub trait InAtomicMode {

    }

    /// A dummy type satisfying [`InAtomicMode`], used when the concrete
    /// guard type is irrelevant (e.g. in `external_body` stubs).
    pub struct AnyAtomicGuard;
    impl InAtomicMode for AnyAtomicGuard {}

} // verus!
