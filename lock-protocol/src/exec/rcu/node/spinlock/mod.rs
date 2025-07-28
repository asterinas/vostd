use core::marker::PhantomData;
use state_machines_macros::tokenized_state_machine;
use vstd::prelude::*;
use vstd::atomic_ghost::*;
use vstd::invariant::InvariantPredicate;
use vstd::cell::{CellId, PointsTo as CellPointsTo};

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
    ) -> bool {
        &&& self.inner.wf()
        &&& self.inner.is_init_all()
        &&& self.inner.value().len() == 512
        // Page table well-formed.
        &&& forall|i: int|
            #![trigger self.inner.value()[i]]
            0 <= i < 512 ==> {
                &&& self.inner.value()[i].wf_with_node_info(level, instance_id, nid, i as nat)
            }
    }

    pub open spec fn addr(&self) -> Vaddr {
        self.inner.addr()
    }

    pub open spec fn relate_pte_state(&self, level: PagingLevel, state: PteState) -> bool {
        forall|i: int|
            #![trigger self.inner.value()[i].is_pt(level)]
            0 <= i < 512 ==> { self.inner.value()[i].is_pt(level) <==> state.is_alive(i as nat) }
    }

    pub open spec fn relate_pte_state_except(
        &self,
        level: PagingLevel,
        state: PteState,
        idx: nat,
    ) -> bool {
        forall|i: int|
            #![trigger self.inner.value()[i].is_pt(level)]
            0 <= i < 512 && i != idx ==> {
                self.inner.value()[i].is_pt(level) <==> state.is_alive(i as nat)
            }
    }

    pub open spec fn relate_pte(&self, pte: Pte, idx: nat) -> bool {
        pte =~= self.inner.value()[idx as int]
    }
}

pub ghost struct SpinInternalPred;

impl InvariantPredicate<
    (InstanceId, NodeId, Paddr, PagingLevel, CellId),
    (Option<NodeToken>, Option<PteArrayToken>, CellPointsTo<bool>, PageTableEntryPerms),
> for SpinInternalPred {
    open spec fn inv(
        k: (InstanceId, NodeId, Paddr, PagingLevel, CellId),
        v: (Option<NodeToken>, Option<PteArrayToken>, CellPointsTo<bool>, PageTableEntryPerms),
    ) -> bool {
        &&& NodeHelper::valid_nid(k.1)
        &&& v.0 is Some <==> v.1 is Some
        &&& v.2.value() == false <==> v.0 is Some
        &&& v.0 is Some ==> {
            &&& v.0->Some_0.instance_id() == k.0
            &&& v.0->Some_0.key() == k.1
            &&& v.0->Some_0.value() is Free
        }
        &&& v.1 is Some ==> {
            &&& v.1->Some_0.instance_id() == k.0
            &&& v.1->Some_0.key() == k.1
            &&& v.1->Some_0.value().wf()
            &&& v.3.relate_pte_state(k.3, v.1->Some_0.value())
        }
        &&& v.2.id() == k.4
        &&& v.2.is_init()
        &&& v.3.wf(k.2, k.3, k.0, k.1)
        &&& v.3.addr() == paddr_to_vaddr(k.2)
    }
}

type SpinInstance = SpinLockToks::Instance<
    (InstanceId, NodeId, Paddr, PagingLevel, CellId),
    (Option<NodeToken>, Option<PteArrayToken>, CellPointsTo<bool>, PageTableEntryPerms),
    SpinInternalPred,
>;

type SpinFlagToken = SpinLockToks::flag<
    (InstanceId, NodeId, Paddr, PagingLevel, CellId),
    (Option<NodeToken>, Option<PteArrayToken>, CellPointsTo<bool>, PageTableEntryPerms),
    SpinInternalPred,
>;

type SpinGuardToken = SpinLockToks::guard<
    (InstanceId, NodeId, Paddr, PagingLevel, CellId),
    (Option<NodeToken>, Option<PteArrayToken>, CellPointsTo<bool>, PageTableEntryPerms),
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
        pub stray_cell_id: Ghost<CellId>,
    }

    pub open spec fn wf(&self) -> bool {
        predicate {
            &&& valid_paddr(self.paddr@)
            &&& 1 <= self.level@ <= 4
            &&& self.inst@.k() == (
                self.pt_inst@.id(),
                self.nid@,
                self.paddr@,
                self.level@,
                self.stray_cell_id@
            )
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
    pub node_token: Tracked<Option<NodeToken>>,
    pub pte_token: Tracked<Option<PteArrayToken>>,
    pub stray_perm: Tracked<CellPointsTo<bool>>,
    pub perms: Tracked<PageTableEntryPerms>,
    pub in_protocol: Ghost<bool>,
}

impl SpinGuard {
    pub open spec fn wf(self, spinlock: &PageTablePageSpinLock) -> bool {
        &&& self.handle@.instance_id() == spinlock.inst@.id()
        &&& self.node_token@ is Some <==> self.pte_token@ is Some
        &&& self.stray_perm@.value() == false <==> self.node_token@ is Some
        &&& self.node_token@ is Some ==> {
            &&& self.node_token@->Some_0.instance_id() == spinlock.pt_inst@.id()
            &&& self.node_token@->Some_0.key() == spinlock.nid@
            &&& !(self.node_token@->Some_0.value() is Free)
            &&& self.in_protocol@ == true ==> self.node_token@->Some_0.value() is Locked
            &&& self.in_protocol@ == false ==> self.node_token@->Some_0.value() is LockedOutside
        }
        &&& self.pte_token@ is Some ==> {
            &&& self.pte_token@->Some_0.instance_id() == spinlock.pt_inst@.id()
            &&& self.pte_token@->Some_0.key() == spinlock.nid@
            &&& self.pte_token@->Some_0.value().wf()
            &&& self.perms@.relate_pte_state(spinlock.level@, self.pte_token@->Some_0.value())
        }
        &&& self.stray_perm@.id() == spinlock.stray_cell_id@
        &&& self.stray_perm@.is_init()
        &&& self.perms@.wf(spinlock.paddr@, spinlock.level@, spinlock.pt_inst@.id(), spinlock.nid@)
        &&& self.perms@.addr() == paddr_to_vaddr(spinlock.paddr@)
    }

    /// Used in PageTableGuard::write_pte
    pub open spec fn wf_except(self, spinlock: &PageTablePageSpinLock, idx: nat) -> bool {
        &&& self.handle@.instance_id() == spinlock.inst@.id()
        &&& self.node_token@ is Some <==> self.pte_token@ is Some
        &&& self.stray_perm@.value() == false <==> self.node_token@ is Some
        &&& self.node_token@ is Some ==> {
            &&& self.node_token@->Some_0.instance_id() == spinlock.pt_inst@.id()
            &&& self.node_token@->Some_0.key() == spinlock.nid@
            &&& !(self.node_token@->Some_0.value() is Free)
            &&& self.in_protocol@ == true ==> self.node_token@->Some_0.value() is Locked
            &&& self.in_protocol@ == false ==> self.node_token@->Some_0.value() is LockedOutside
        }
        &&& self.pte_token@ is Some ==> {
            &&& self.pte_token@->Some_0.instance_id() == spinlock.pt_inst@.id()
            &&& self.pte_token@->Some_0.key() == spinlock.nid@
            &&& self.pte_token@->Some_0.value().wf()
            &&& self.perms@.relate_pte_state_except(
                spinlock.level@,
                self.pte_token@->Some_0.value(),
                idx,
            )
        }
        &&& self.stray_perm@.id() == spinlock.stray_cell_id@
        &&& self.stray_perm@.is_init()
        &&& self.perms@.wf(spinlock.paddr@, spinlock.level@, spinlock.pt_inst@.id(), spinlock.nid@)
        &&& self.perms@.addr() == paddr_to_vaddr(spinlock.paddr@)
    }

    pub open spec fn view_node_token(&self) -> NodeToken
        recommends
            self.node_token@ is Some,
    {
        self.node_token@->Some_0
    }

    pub open spec fn view_pte_token(&self) -> PteArrayToken
        recommends
            self.pte_token@ is Some,
    {
        self.pte_token@->Some_0
    }

    pub open spec fn view_stary_perm(&self) -> CellPointsTo<bool> {
        self.stray_perm@
    }

    pub open spec fn view_perms(&self) -> PageTableEntryPerms {
        self.perms@
    }

    pub open spec fn wf_trans_lock_protocol(&self, old: &Self) -> bool {
        &&& self.handle =~= old.handle
        &&& self.pte_token =~= old.pte_token
        &&& self.stray_perm =~= old.stray_perm
        &&& self.perms =~= old.perms
    }

    #[verifier::external_body]
    pub fn trans_lock_protocol(
        self,
        spinlock: &PageTablePageSpinLock,
        m: Tracked<LockProtocolModel>,
    ) -> (res: (Self, Tracked<LockProtocolModel>))
        requires
            self.wf(spinlock),
            self.in_protocol@ == false,
            m@.inv(),
            m@.inst_id() == spinlock.pt_inst@.id(),
            m@.state() is Locking,
            m@.cur_node() == spinlock.nid@,
        ensures
            res.0.wf(spinlock),
            self.in_protocol@ == true,
            res.0.wf_trans_lock_protocol(&self),
            res.1@.inv(),
            res.1@.inst_id() == spinlock.pt_inst@.id(),
            res.1@.state() is Locking,
            res.1@.cur_node() == spinlock.nid@ + 1,
    {
        unimplemented!()
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
    pub fn normal_lock(&self) -> (res: SpinGuard)
        requires
            self.wf(),
        ensures
            res.wf(self),
            res.in_protocol@ == false,
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub fn normal_unlock(&self, guard: SpinGuard)
        requires
            self.wf(),
            guard.wf(self),
            guard.in_protocol@ == false,
    {
        unimplemented!()
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
            res.0.in_protocol@ == true,
            res.1@.inv(),
            res.1@.inst_id() == self.pt_inst_id(),
            res.1@.state() is Locking,
            res.1@.sub_tree_rt() == m@.sub_tree_rt(),
            res.1@.cur_node() == self.nid() + 1,
    {
        // let tracked m = m.get();
        // let mut guard_opt: Option<SpinGuard> = None;
        // loop
        //     invariant_except_break
        //         self.wf(),
        //         m.inv(),
        //         m.inst_id() == self.pt_inst_id(),
        //         m.state() is Locking,
        //         m.cur_node() == self.nid(),
        //         guard_opt is None,
        //     ensures
        //         m.inv(),
        //         m.inst_id() == self.pt_inst_id(),
        //         m.state() is Locking,
        //         m.cur_node() == self.nid() + 1,
        //         guard_opt is Some,
        //         guard_opt->Some_0.wf(self),
        //         guard_opt->Some_0.in_protocol@ == true,
        // {
        //     let tracked mut node_token_opt: Option<Option<NodeToken>> = None;
        //     let tracked mut pte_token_opt: Option<Option<PteArrayToken>> = None;
        //     let tracked mut stray_perm_opt: Option<CellPointsTo<bool>> = None;
        //     let tracked mut perms_opt: Option<PageTableEntryPerms> = None;
        //     let result = atomic_with_ghost!(
        //         &self.flag => compare_exchange(false, true);
        //         returning res;
        //         ghost g => {
        //             if res is Ok {
        //                 let tracked res = self.inst.borrow().acquire(&mut g);

        //             }
        //         }
        //     )

        //     match result {
        //         Result::Ok(_) => {
                    
        //         },
        //         _ => (),
        //     };
        // }
        unimplemented!();
    }

    #[verifier::external_body]
    pub fn unlock(&self, guard: SpinGuard, m: Tracked<LockProtocolModel>) -> (res: Tracked<
        LockProtocolModel,
    >)
        requires
            self.wf(),
            guard.wf(self),
            guard.in_protocol@ == true,
            m@.inv(),
            m@.inst_id() == self.pt_inst_id(),
            m@.state() is Locking,
            m@.cur_node() == self.nid() + 1,
        ensures
            res@.inv(),
            res@.inst_id() == self.pt_inst_id(),
            res@.state() is Locking,
            res@.sub_tree_rt() == m@.sub_tree_rt(),
            res@.cur_node() == self.nid(),
    {
        unimplemented!()
    }
}

} // verus!
