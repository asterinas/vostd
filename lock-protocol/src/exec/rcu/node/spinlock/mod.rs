use core::marker::PhantomData;
use state_machines_macros::tokenized_state_machine;
use vstd::prelude::*;
use vstd::atomic_ghost::*;
use vstd::invariant::InvariantPredicate;

use vstd_extra::array_ptr::*;

use crate::spec::{common::*, utils::*, rcu::*};
use super::super::{common::*, types::*, cpu::*};
use super::super::pte::*;

tokenized_state_machine! {

SpinLockToks<K, V, Pred: InvariantPredicate<K, V>> {
    fields {
        #[sharding(constant)]
        pub k: K,

        #[sharding(constant)]
        pub pred: PhantomData<Pred>,

        #[sharding(variable)]
        pub flag: bool,

        #[sharding(storage_option)]
        pub storage: Option<V>,

        #[sharding(option)]
        pub guard: Option<()>,
    }

    #[invariant]
    pub fn inv_storage_user(&self) -> bool {
        self.storage is Some ==>
            Pred::inv(self.k, self.storage->Some_0)
    }

    #[invariant]
    pub fn inv_flag_gaurd_storage_relationship(&self) -> bool {
        &&& self.flag == false <==>
            self.storage is Some
        &&& self.flag == false <==>
            self.guard is None
    }

    init!{
        initialize(k: K, t: V) {
            require Pred::inv(k, t);
            init k = k;
            init pred = PhantomData;
            init flag = false;
            init storage = Option::Some(t);
            init guard = None;
        }
    }

    transition!{
        acquire() {
            require(pre.flag == false);

            update flag = true;

            add guard += Some(());

            birds_eye let x = pre.storage->0;
            withdraw storage -= Some(x);

            assert Pred::inv(pre.k, x);
        }
    }

    transition!{
        release(x: V) {
            require Pred::inv(pre.k, x);

            update flag = false;

            remove guard -= Some(());

            deposit storage += Some(x);
        }
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, k: K, t: V) {}

    #[inductive(acquire)]
    fn acquire_inductive(pre: Self, post: Self) {}

    #[inductive(release)]
    fn release_inductive(pre: Self, post: Self, x: V) {}
}

}

verus! {

pub tracked struct PageTableEntryPerms {
    pub inner: PointsTo<Pte, PTE_NUM>,
}

impl PageTableEntryPerms {
    pub open spec fn wf(
        &self,
        paddr: Paddr,
        level: PagingLevel,
        instance_id: InstanceId,
        nid: NodeId,
    ) -> bool
        recommends
            NodeHelper::is_not_leaf(nid),
    {
        &&& self.inner.wf()
        &&& self.inner.is_init_all()
        &&& self.inner.value().len() == 512
        // Page table well-formed.
        &&& forall|i: int|
            #![trigger self.inner.value()[i]]
            0 <= i < 512 ==> {
                &&& self.inner.value()[i].wf()
                &&& self.inner.value()[i].wf_with_node_info(level, instance_id, nid, i as nat)
            }
    }

    pub open spec fn addr(&self) -> Vaddr {
        self.inner.addr()
    }

    pub open spec fn relate_pte_state(&self, state: PteState) -> bool {
        forall|i: int|
            #![trigger self.inner.value()[i]]
            0 <= i < 512 ==> {
                self.inner.value()[i].inner.is_present() <==> state.is_alive(i as nat)
            }
    }
}

pub ghost struct SpinInternalPred;

impl InvariantPredicate<
    (InstanceId, NodeId, Paddr, PagingLevel),
    (NodeToken, PteToken, PageTableEntryPerms),
> for SpinInternalPred {
    open spec fn inv(
        k: (InstanceId, NodeId, Paddr, PagingLevel),
        v: (NodeToken, PteToken, PageTableEntryPerms),
    ) -> bool {
        &&& NodeHelper::valid_nid(k.1)
        &&& v.0.instance_id() == k.0
        &&& v.0.key() == k.1
        &&& v.0.value() is Free
        &&& v.1.instance_id() == k.0
        &&& v.1.key() == k.1
        &&& v.2.relate_pte_state(v.1.value())
        &&& v.2.wf(k.2, k.3, k.0, k.1)
        &&& v.2.addr() == paddr_to_vaddr(k.2)
    }
}

type SpinInstance = SpinLockToks::Instance<
    (InstanceId, NodeId, Paddr, PagingLevel),
    (NodeToken, PteToken, PageTableEntryPerms),
    SpinInternalPred,
>;

type SpinFlagToken = SpinLockToks::flag<
    (InstanceId, NodeId, Paddr, PagingLevel),
    (NodeToken, PteToken, PageTableEntryPerms),
    SpinInternalPred,
>;

type SpinGuardToken = SpinLockToks::guard<
    (InstanceId, NodeId, Paddr, PagingLevel),
    (NodeToken, PteToken, PageTableEntryPerms),
    SpinInternalPred,
>;

struct_with_invariants! {
    pub struct PageTablePageSpinLock {
        pub flag: AtomicBool<_, SpinFlagToken, _>,

        pub paddr: Ghost<Paddr>,
        pub level: Ghost<PagingLevel>,

        pub inst: Tracked<SpinInstance>,
        pub pt_inst: Tracked<SpecInstance>,
        pub nid: Ghost<NodeId>,
    }

    pub open spec fn wf(&self) -> bool {
        predicate {
            &&& valid_paddr(self.paddr@)
            &&& 1 <= self.level@ <= 4
            &&& self.inst@.k() ==
                (self.pt_inst@.id(), self.nid@, self.paddr@, self.level@)
            &&& self.pt_inst@.cpu_num() == GLOBAL_CPU_NUM
            &&& NodeHelper::valid_nid(self.nid@)
        }

        invariant on flag with (inst) is (v: bool, g: SpinFlagToken) {
            &&& g.instance_id() == inst@.id()
            &&& g.value() == v
        }
    }
}

pub struct SpinGuard {
    pub handle: Tracked<SpinGuardToken>,
    pub node_token: Tracked<NodeToken>,
    pub pte_token: Tracked<PteToken>,
    pub perms: Tracked<PageTableEntryPerms>,
}

impl SpinGuard {
    pub open spec fn wf(self, spinlock: &PageTablePageSpinLock) -> bool {
        &&& self.handle@.instance_id() == spinlock.inst@.id()
        &&& self.node_token@.instance_id() == spinlock.pt_inst@.id()
        &&& self.node_token@.key() == spinlock.nid@
        &&& self.node_token@.value() is Locked
        &&& self.pte_token@.instance_id() == spinlock.pt_inst@.id()
        &&& self.pte_token@.key() == spinlock.nid@
        &&& self.perms@.relate_pte_state(self.pte_token@.value())
        &&& self.perms@.wf(spinlock.paddr@, spinlock.level@, spinlock.pt_inst@.id(), spinlock.nid@)
        &&& self.perms@.addr() == paddr_to_vaddr(spinlock.paddr@)
    }

    pub open spec fn view_node_token(&self) -> NodeToken {
        self.node_token@
    }

    pub open spec fn view_pte_token(&self) -> PteToken {
        self.pte_token@
    }

    pub open spec fn view_perms(&self) -> PageTableEntryPerms {
        self.perms@
    }
}

impl PageTablePageSpinLock {
    pub open spec fn paddr_spec(&self) -> Paddr {
        self.paddr@
    }

    pub open spec fn level_spec(&self) -> PagingLevel {
        self.level@
    }

    pub open spec fn inst_id(&self) -> InstanceId {
        self.inst@.id()
    }

    pub open spec fn pt_inst_id(&self) -> InstanceId {
        self.pt_inst@.id()
    }

    pub proof fn get_pt_inst(tracked &self) -> (tracked res: SpecInstance) {
        self.pt_inst.borrow().clone()
    }

    pub open spec fn nid(&self) -> NodeId {
        self.nid@
    }

    #[verifier::external_body]
    pub fn lock(&self, m: Tracked<LockProtocolModel>) -> (res: (
        SpinGuard,
        Tracked<LockProtocolModel>,
    ))
        requires
            self.wf(),
            m@.inv(),
            m@.inst_id() == self.pt_inst_id(),
            m@.state() is Locking,
            m@.cur_node() == self.nid(),
        ensures
            res.0.wf(self),
            res.1@.inv(),
            res.1@.inst_id() == self.pt_inst_id(),
            res.1@.state() is Locking,
            res.1@.cur_node() == self.nid() + 1,
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub fn unlock(&self, guard: SpinGuard, m: Tracked<LockProtocolModel>) -> (res: Tracked<
        LockProtocolModel,
    >)
        requires
            self.wf(),
            guard.wf(self),
            m@.inv(),
            m@.inst_id() == self.pt_inst_id(),
            m@.state() is UnLocking,
            m@.cur_node() == self.nid() + 1,
        ensures
            res@.inv(),
            res@.inst_id() == self.pt_inst_id(),
            res@.state() is UnLocking,
            m@.cur_node() == self.nid() + 1,
    {
        unimplemented!()
    }
}

} // verus!
