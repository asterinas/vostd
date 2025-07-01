#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::{
    atomic_ghost::AtomicBool,
    atomic_with_ghost,
    cell::{PCell, PointsTo},
    prelude::*,
};
use aster_common::task::preempt::guard::{disable_preempt, DisabledPreemptGuard};
use super::spec::SpinLockSpec;

verus! {

/// A guardian that denotes the guard behavior for holding the spin lock.
pub trait Guardian {
    /// The guard type.
    type Guard;

    /// Creates a new guard.
    fn guard() -> Self::Guard;
}

/// A guardian that disables preemption while holding the spin lock.
pub struct PreemptDisabled;

impl Guardian for PreemptDisabled {
    type Guard = DisabledPreemptGuard;

    fn guard() -> Self::Guard {
        disable_preempt()
    }
}

} // verus!
verus! {

#[verifier::reject_recursive_types(T)]
pub struct SpinLockGuard<'a, T, G: Guardian> {
    pub tracked guard: Tracked<SpinLockSpec::guard<PointsTo<T>>>,
    pub tracked cell_perms: Tracked<PointsTo<T>>,
    pub lock: &'a SpinLock<T>,
    pub _guard: G::Guard,
}

impl<'a, T> SpinLockGuard<'a, T, PreemptDisabled> {
    pub closed spec fn inv(&self) -> bool {
        &&& self.guard@.instance_id() == self.lock.inst@.id()
        &&& self.cell_perms@.id() == self.lock.data.id()
        &&& self.lock.wf()
        &&& self.cell_perms@.is_init() ==> { self.lock.inv(self.cell_perms@.value()) }
    }

    pub fn deref(&self) -> (res: &T)
        requires
            self.inv(),
            self.cell_perms@@.value is Some,
        ensures
            self.inv(),
            *res == self.cell_perms@@.value.get_Some_0(),
    {
        self.lock.data.borrow(Tracked(self.cell_perms.borrow()))
    }

    pub fn get(&mut self) -> (res: T)
        requires
            old(self).inv(),
            old(self).cell_perms@@.value is Some,
        ensures
            self.inv(),
            self.cell_perms@@.value is None,
            res == old(self).cell_perms@@.value.get_Some_0(),
            self.lock.inv(res),
    {
        self.lock.data.take(Tracked(self.cell_perms.borrow_mut()))
    }

    pub fn put(&mut self, val: T)
        requires
            old(self).inv(),
            old(self).cell_perms@@.value is None,
            old(self).lock.inv(val),
        ensures
            self.inv(),
            self.cell_perms@@.value is Some,
            self.cell_perms@@.value.get_Some_0() == val,
            self.lock.inv(val),
    {
        self.lock.data.put(Tracked(self.cell_perms.borrow_mut()), val);
    }

    pub fn drop(self)
        requires
            self.inv(),
            self.cell_perms@@.value is Some,
    {
        self.lock.release(Tracked(self));
    }
}

// impl Drop for SpinLockGuard<'_, T, G> {
//     pub fn drop(self)
//         requires
//             self.inv(),
//             self.cell_perms@@.value is Some,
//     {
//         self._guard.drop();
//         self.lock.release(Tracked(self));
//     }
// }
struct_with_invariants!{
    #[verifier::reject_recursive_types(T)]
    pub struct SpinLock<T> {
        data: PCell<T>,
        locked: AtomicBool<_, SpinLockSpec::locked<PointsTo<T>>, _>,
        inst: Tracked<SpinLockSpec::Instance<PointsTo<T>>>,
        user_inv: Ghost<Set<T>>,
    }

    pub closed spec fn wf(&self) -> bool {
        predicate {
            forall |v: PointsTo<T>| #[trigger] self.inst@.user_inv().contains(v) <==> {
                &&& v@.pcell == self.data.id()
                &&& v@.value is Some
                &&& self.user_inv@.contains(v@.value.get_Some_0())
            }
        }

        invariant on locked with (inst) specifically (self.locked) is
            (b: bool, g: SpinLockSpec::locked<PointsTo<T>>) {
            &&& g.instance_id() == inst@.id()
            &&& g.value() == b
        }
    }
}

impl<T> SpinLock<T> {
    pub closed spec fn inv(&self, t: T) -> bool {
        self.user_inv@.contains(t)
    }

    pub closed spec fn wf_guard(&self, guard: &SpinLockGuard<T, PreemptDisabled>) -> bool {
        &&& guard.guard@.instance_id() == self.inst@.id()
        &&& guard.cell_perms@@.pcell == self.data.id()
    }

    pub fn new(t: T, inv: Ghost<spec_fn(T) -> bool>) -> (s: Self)
        requires
            inv@(t),
        ensures
            s.wf(),
            forall|v: T| s.inv(v) == inv@(v),
    {
        let tracked inst;
        let tracked locked_token;
        // create the pcell object
        let (pcell_data, Tracked(mut pcell_token)) = PCell::new(t);
        // create the set of allowed data structures
        let ghost set_inv = Set::new(inv@);
        let ghost user_inv = Set::new(
            |s: PointsTo<T>|
                {
                    &&& equal(s@.pcell, pcell_data.id())
                    &&& s@.value is Some
                    &&& set_inv.contains(s@.value.get_Some_0())
                },
        );
        proof {
            let tracked (Tracked(inst0), Tracked(locked_token0), _) =
                SpinLockSpec::Instance::initialize(
                pcell_token,
                user_inv,
                Option::Some(pcell_token),
            );
            inst = inst0;
            locked_token = locked_token0;
        }
        let tracked_inst: Tracked<SpinLockSpec::Instance<PointsTo<T>>> = Tracked(inst.clone());
        let locked_atomic = AtomicBool::new(Ghost(tracked_inst), false, Tracked(locked_token));

        SpinLock {
            user_inv: Ghost(set_inv),
            data: pcell_data,
            inst: Tracked(inst),
            locked: locked_atomic,
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn lock(&self) -> (res: Tracked<SpinLockGuard<T, PreemptDisabled>>)
        requires
            self.wf(),
        ensures
            self.wf(),
            self.wf_guard(&res@),
            res@.inv(),
            res@.lock =~= self,
    {
        let tracked mut guard: Option<Tracked<SpinLockSpec::guard<PointsTo<T>>>> = None;
        let tracked mut cell_perms: Option<PointsTo<T>> = None;
        let mut acquired = false;
        while !acquired
            invariant
                self.wf(),
                acquired ==> {
                    &&& guard is Some
                    &&& guard.get_Some_0()@.instance_id() == self.inst@.id()
                    &&& cell_perms is Some
                    &&& cell_perms.get_Some_0()@.pcell == self.data.id()
                    &&& cell_perms.get_Some_0()@.value is Some
                    &&& self.inv(cell_perms.get_Some_0()@.value.get_Some_0())
                },
        {
            let result =
                atomic_with_ghost!(
                &self.locked => compare_exchange(false, true);
                returning res;
                ghost g => {
                    if res.is_Ok() {
                        let tracked (_, Tracked(_cell_perms), _guard) =
                            self.inst.borrow().lock(&mut g);
                        guard = Some(_guard);
                        cell_perms = Some(_cell_perms);
                    }
                }
            );
            acquired = result.is_ok();
        }

        let _guard = PreemptDisabled::guard();
        // return the Guard
        Tracked(
            SpinLockGuard {
                guard: guard.tracked_unwrap(),
                cell_perms: Tracked(cell_perms.tracked_unwrap()),
                lock: self,
                _guard,
            },
        )
    }

    pub fn release(&self, guard: Tracked<SpinLockGuard<T, PreemptDisabled>>)
        requires
            self.wf(),
            self.wf_guard(&guard@),
            guard@.lock =~= self,
            guard@.inv(),
            guard@.cell_perms@@.value is Some,
            self.inv(guard@.cell_perms@@.value.get_Some_0()),
        ensures
            self.wf(),
    {
        let tracked SpinLockGuard { cell_perms, guard, lock, _guard } = guard.get();
        let res =
            atomic_with_ghost!(
            &self.locked => store(false);
            ghost g => {
                let tracked guard = guard.get();
                let tracked cell_perms = cell_perms.get();
                self.inst.borrow().release(cell_perms, cell_perms, &mut g, guard);
            }
        );
    }
}

} // verus!
