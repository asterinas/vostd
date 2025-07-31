use verus_verus_state_machines_macros::tokenized_state_machine;
use vstd::{
    atomic_ghost::AtomicBool,
    atomic_with_ghost,
    cell::{PCell, PointsTo},
    prelude::*,
};

use super::common::*;

verus! {

tokenized_state_machine!{

#[cfg_attr(verus_keep_ghost, verifier::reject_recursive_types(T))]
SpinLockSpec<T> {

fields {
    #[sharding(constant)]
    pub user_inv: Set<T>,

    #[sharding(storage_option)]
    pub storage: Option<T>,

    #[sharding(variable)]
    pub locked: bool,

    #[sharding(option)]
    pub guard: Option<()>,
}

#[invariant]
pub fn inv(&self) -> bool {
    &&& self.storage.is_Some() ==>
        self.user_inv.contains(self.storage.get_Some_0())

    &&& self.locked == false <==> self.storage.is_Some()

    &&& self.guard.is_None() <==> self.storage.is_Some()
}

init!{
    initialize(init_t: T, user_inv: Set<T>) {
        require(user_inv.contains(init_t));

        init user_inv = user_inv;
        init storage = Option::Some(init_t);
        init locked = false;
        init guard = Option::None;
    }
}

transition!{
    acquire() {
        require(pre.locked == false);
        update locked = true;
        add guard += Some(());

        birds_eye let x = pre.storage.get_Some_0();
        withdraw storage -= Some(x);
        assert(pre.user_inv.contains(x));
    }
}

transition!{
    release(t: T) {
        require(pre.user_inv.contains(t));

        update locked = false;
        remove guard -= Some(());

        deposit storage += Some(t);
    }
}

#[inductive(initialize)]
fn initialize_inductive(post: Self, init_t: T, user_inv: Set<T>) {}

#[inductive(acquire)]
fn acquire_inductive(pre: Self, post: Self) {}

#[inductive(release)]
fn release_inductive(pre: Self, post: Self, t: T) {}

}

}

} // verus!
verus! {

pub tracked struct PageLockGuard {
    tracked guard: Tracked<SpinLockSpec::guard<PagePerm>>,
    tracked perm: Tracked<PagePerm>,
}

struct_with_invariants!{
    pub struct PageLock {
        paddr: Paddr,
        locked: AtomicBool<_, SpinLockSpec::locked<PagePerm>, _>,
        inst: Tracked<SpinLockSpec::Instance<PagePerm>>,
        user_inv: Ghost<Set<PagePerm>>,
    }

    pub closed spec fn wf(&self) -> bool {
        predicate {
            forall |perm: PagePerm| #[trigger] self.inst@.user_inv().contains(perm) == (
                perm.paddr == self.paddr && self.user_inv@.contains(perm)
            )
        }

        invariant on locked with (inst) is (b: bool, g: SpinLockSpec::locked<PagePerm>) {
            &&& g.instance_id() == inst@.id()
            &&& g.value() == b
        }
    }
}

impl PageLock {
    pub closed spec fn inv(&self, perm: PagePerm) -> bool {
        self.user_inv@.contains(perm)
    }

    pub closed spec fn wf_guard(&self, guard: &PageLockGuard) -> bool {
        &&& guard.guard@.instance_id() == self.inst@.id()
        &&& guard.perm@.paddr == self.paddr
        &&& self.user_inv@.contains(guard.perm@)
    }

    pub fn new(paddr: Paddr, perm: Tracked<PagePerm>) -> (res: Self)
        requires
            perm@.paddr == paddr,
        ensures
            res.wf(),
            forall|perm: PagePerm| #![auto] res.inv(perm) <==> (perm.paddr == paddr),
    {
        let tracked perm = perm.get();

        let tracked inst;
        let tracked locked_token;
        let ghost user_inv = Set::new(|perm: PagePerm| perm.paddr == paddr);
        proof {
            let tracked (Tracked(inst0), Tracked(locked_token0), _) =
                SpinLockSpec::Instance::initialize(perm, user_inv, Some(perm));

            inst = inst0;
            locked_token = locked_token0;
        }
        let tracked_inst: Tracked<SpinLockSpec::Instance<PagePerm>> = Tracked(inst.clone());

        let locked_atomic = AtomicBool::new(Ghost(tracked_inst), false, Tracked(locked_token));

        Self { paddr, locked: locked_atomic, inst: Tracked(inst), user_inv: Ghost(user_inv) }
    }

    pub fn acquire(&self) -> (res: Tracked<PageLockGuard>)
        requires
            self.wf(),
        ensures
            self.wf_guard(&res@),
    {
        let mut acquired = false;
        let tracked mut guard: Option<SpinLockSpec::guard<PagePerm>> = None;
        let tracked mut perm: Option<PagePerm> = None;
        while !acquired
            invariant
                self.wf(),
                acquired ==> {
                    &&& guard.is_Some()
                    &&& guard.get_Some_0().instance_id() == self.inst@.id()
                    &&& perm.is_Some()
                    &&& perm.get_Some_0().paddr == self.paddr
                    &&& self.user_inv@.contains(perm.get_Some_0())
                },
        {
            let result =
                atomic_with_ghost!(
                &self.locked => compare_exchange(false, true);
                returning res;
                ghost g => {
                    if res.is_Ok() {
                        let tracked (_, Tracked(perm0), Tracked(guard0)) = self.inst.borrow().acquire(&mut g);
                        guard = Some(guard0);
                        perm = Some(perm0);
                    }
                }
            );
            acquired = result.is_ok();
        }
        let tracked guard = guard.tracked_unwrap();
        let tracked perm = perm.tracked_unwrap();
        Tracked(PageLockGuard { guard: Tracked(guard), perm: Tracked(perm) })
    }

    pub fn release(&self, guard: Tracked<PageLockGuard>)
        requires
            self.wf(),
            self.wf_guard(&guard@),
    {
        let tracked PageLockGuard { guard, perm } = guard.get();
        let tracked guard = guard.get();
        let tracked perm = perm.get();
        atomic_with_ghost!{
            &self.locked => store(false);
            ghost g => {
                self.inst.borrow().release(perm, perm, &mut g, guard);
            }
        }
    }
}

} // verus!
