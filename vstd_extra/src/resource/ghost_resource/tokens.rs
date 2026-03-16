//！ A wrapper around `vstd::tokens::FracGhost` that stores and dispatches fractional access.
use vstd::pcm::Loc;
use vstd::prelude::*;
use vstd::tokens::frac::{Empty, Frac, FracGhost};

verus! {

/// A struct that stores and dispatches `FracGhost<T>`.
/// Unlike `FracGhost`, it provides an `empty` state.
pub tracked struct FracGhostStorage<T, const TOTAL: u64> {
    tracked r: Option<FracGhost<T, TOTAL>>,
    ghost snapshot: T,
    ghost id: Loc,
}

impl<T, const TOTAL: u64> FracGhostStorage<T, TOTAL> {
    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        &&& TOTAL > 0
        &&& 0 <= self.frac() <= TOTAL
        &&& self.r is Some ==> {
            &&& self.id == self.r->Some_0.id()
            &&& self.view() == self.r->Some_0@
        }
    }

    pub open spec fn wf(self) -> bool {
        &&& TOTAL > 0
        &&& 0 <= self.frac() <= TOTAL
        &&& self.type_inv()
    }

    pub open spec fn is_empty(self) -> bool {
        self.frac() == 0
    }

    pub open spec fn not_empty(self) -> bool {
        !self.is_empty()
    }

    pub open spec fn is_full(self) -> bool {
        self.frac() == TOTAL
    }

    /// Returns the `FracGhost<T,TOTAL>` stored in this `FracGhostStorage`.
    pub closed spec fn storage(self) -> FracGhost<T, TOTAL> {
        self.r->Some_0
    }

    /// Returns the `T` stored in this `FracGhostStorage`.
    pub closed spec fn view(self) -> T {
        self.snapshot
    }

    pub closed spec fn frac(self) -> int {
        if self.r is None {
            0int
        } else {
            self.storage().frac()
        }
    }

    pub closed spec fn id(self) -> Loc {
        self.id
    }

    pub proof fn alloc(value: T) -> (tracked res: Self)
        requires
            TOTAL > 0,
        ensures
            res.not_empty(),
            res.is_full(),
            res@ == value,
            res.wf(),
    {
        let tracked r = FracGhost::new(value);
        Self { r: Some(r), snapshot: value, id: r.id() }
    }

    pub proof fn split_one(tracked &mut self) -> (tracked res: FracGhost<T, TOTAL>)
        requires
            old(self).not_empty(),
        ensures
            self.id() == old(self).id(),
            self.frac() + 1 == old(self).frac(),
            self@ == old(self)@,
            res.frac() == 1,
            res.id() == self.id(),
            res@ == self@,
            old(self).frac() == 1 ==> self.is_empty(),
            self.wf(),
    {
        use_type_invariant(&*self);
        if self.frac() == 1 {
            self.r.tracked_take()
        } else {
            self.r.tracked_borrow().bounded();
            let tracked mut r = self.r.tracked_take();
            let tracked res = r.split(1);
            self.r = Some(r);
            res
        }
    }

    pub proof fn split(tracked &mut self, n: int) -> (tracked res: FracGhost<T, TOTAL>)
        requires
            1 <= n <= old(self).frac(),
        ensures
            self.id() == old(self).id(),
            self.frac() + n == old(self).frac(),
            self@ == old(self)@,
            res.frac() == n,
            res.id() == self.id(),
            res@ == self@,
            old(self).frac() == n ==> self.is_empty(),
            self.wf(),
    {
        use_type_invariant(&*self);
        self.r.tracked_borrow().bounded();
        if self.frac() == n {
            self.r.tracked_take()
        } else {
            let tracked mut r = self.r.tracked_take();
            let tracked res = r.split(n);
            self.r = Some(r);
            res
        }
    }

    pub proof fn combine(tracked &mut self, tracked other: FracGhost<T, TOTAL>)
        requires
            old(self).id() == other.id(),
            other@ == old(self)@,
        ensures
            old(self).frac() + other.frac() > TOTAL ==> false,
            old(self).frac() + other.frac() <= TOTAL ==> {
                &&& self.id() == old(self).id()
                &&& self@ == old(self)@
                &&& self.frac() == old(self).frac() + other.frac()
                &&& self.wf()
            },
    {
        if self.is_empty() {
            other.bounded();
            self.r = Some(other);
        } else {
            use_type_invariant(&*self);
            let tracked mut r = self.r.tracked_take();
            r.combine(other);
            r.bounded();
            self.r = Some(r);
        }
    }

    pub proof fn validate(tracked &self)
        ensures
            self.wf(),
    {
        use_type_invariant(self);
    }

    pub proof fn full(tracked &self)
        requires
            self.is_full(),
        ensures
            self.not_empty(),
            self.frac() == TOTAL,
            self.wf(),
    {
        use_type_invariant(self);
        if self.is_empty() {
            assert(self.frac() == 0int);
            assert(TOTAL > 0);
            assert(false);
        }
    }

    pub proof fn update(tracked &mut self, value: T)
        requires
            old(self).is_full(),
        ensures
            self.is_full(),
            self@ == value,
            self.id() == old(self).id(),
            self.wf(),
    {
        use_type_invariant(&*self);
        let tracked mut r = self.r.tracked_take();
        r.update(value);
        self.snapshot = value;
        self.r = Some(r);
    }
}

pub type TokenStorage<const TOTAL: u64> = FracGhostStorage<(), TOTAL>;

pub type Token<const TOTAL: u64> = FracGhost<(), TOTAL>;

} // verus!
