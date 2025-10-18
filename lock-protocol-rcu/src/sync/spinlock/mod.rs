pub mod guard_forget;

use core::marker::PhantomData;
use verus_state_machines_macros::tokenized_state_machine;
use vstd::prelude::*;
use vstd::atomic_ghost::*;
use vstd::invariant::InvariantPredicate;
use vstd::cell::CellId;

use vstd_extra::array_ptr::*;

use crate::spec::{
    rcu::{NodeToken, PteArrayToken, SpecInstance, PteArrayState},
    lock_protocol::LockProtocolModel,
    utils::NodeHelper,
    common::NodeId,
};
use crate::mm::{PagingLevel, Paddr, Vaddr};
use crate::mm::page_table::{
    PageTableEntryTrait,
    pte::Pte,
    PageTableConfig,
};
use crate::mm::page_table::node::stray::{StrayFlag, StrayPerm};
use crate::mm::page_table::node::PageTableGuard;
use crate::x86_64::kspace::paddr_to_vaddr;
use crate::configs::{PTE_NUM, GLOBAL_CPU_NUM};

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

pub tracked struct PageTableEntryPerms<C: PageTableConfig> {
    pub inner: PointsTo<Pte<C>, PTE_NUM>,
}

impl<C: PageTableConfig> PageTableEntryPerms<C> {
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

    pub open spec fn relate_nid(&self, nid: NodeId) -> bool {
        forall|i: int|
            #![trigger self.inner.value()[i]]
            0 <= i < 512 ==> {
                self.inner.value()[i].nid@ is Some ==> self.inner.value()[i].nid@->Some_0
                    == NodeHelper::get_child(nid, i as nat)
            }
    }

    pub open spec fn addr(&self) -> Vaddr {
        self.inner.addr()
    }

    pub open spec fn relate_pte_state(&self, level: PagingLevel, state: PteArrayState) -> bool {
        &&& forall|i: int|
            #![trigger self.inner.value()[i].is_pt(level)]
            0 <= i < 512 ==> { self.inner.value()[i].is_pt(level) <==> state.is_alive(i as nat) }
        &&& forall|i: int|
            #![trigger self.inner.value()[i].is_pt(level)]
            0 <= i < 512 && self.inner.value()[i].is_pt(level) ==> {
                self.inner.value()[i].inner.paddr() == state.get_paddr(i as nat)
            }
    }

    pub open spec fn relate_pte_state_except(
        &self,
        level: PagingLevel,
        state: PteArrayState,
        idx: nat,
    ) -> bool {
        &&& forall|i: int|
            #![trigger self.inner.value()[i].is_pt(level)]
            0 <= i < 512 && i != idx ==> {
                self.inner.value()[i].is_pt(level) <==> state.is_alive(i as nat)
            }
        &&& forall|i: int|
            #![trigger self.inner.value()[i].is_pt(level)]
            0 <= i < 512 && i != idx && self.inner.value()[i].is_pt(level) ==> {
                self.inner.value()[i].inner.paddr() == state.get_paddr(i as nat)
            }
    }

    pub open spec fn relate_pte(&self, pte: Pte<C>, idx: nat) -> bool {
        pte =~= self.inner.value()[idx as int]
    }
}

pub ghost struct SpinInternalPred;

impl<C: PageTableConfig> InvariantPredicate<
    (InstanceId, NodeId, Paddr, PagingLevel, CellId),
    (Option<NodeToken>, Option<PteArrayToken>, StrayPerm, PageTableEntryPerms<C>),
> for SpinInternalPred {
    open spec fn inv(
        k: (InstanceId, NodeId, Paddr, PagingLevel, CellId),
        v: (Option<NodeToken>, Option<PteArrayToken>, StrayPerm, PageTableEntryPerms<C>),
    ) -> bool {
        &&& NodeHelper::valid_nid(k.1)
        &&& v.0 is Some <==> v.1 is Some
        &&& v.2.perm.value() == false <==> v.0 is Some
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
        &&& v.2.wf_with_cell_id(k.4)
        &&& v.2.perm.is_init()
        &&& v.2.wf_with_node_info(k.0, k.1, k.2)
        &&& v.3.wf(k.2, k.3, k.0, k.1)
        &&& v.3.addr() == paddr_to_vaddr(k.2)
    }
}

type SpinInstance<C> = SpinLockToks::Instance<
    (InstanceId, NodeId, Paddr, PagingLevel, CellId),
    (Option<NodeToken>, Option<PteArrayToken>, StrayPerm, PageTableEntryPerms<C>),
    SpinInternalPred,
>;

type SpinFlagToken<C> = SpinLockToks::flag<
    (InstanceId, NodeId, Paddr, PagingLevel, CellId),
    (Option<NodeToken>, Option<PteArrayToken>, StrayPerm, PageTableEntryPerms<C>),
    SpinInternalPred,
>;

type SpinGuardToken<C> = SpinLockToks::guard<
    (InstanceId, NodeId, Paddr, PagingLevel, CellId),
    (Option<NodeToken>, Option<PteArrayToken>, StrayPerm, PageTableEntryPerms<C>),
    SpinInternalPred,
>;

struct_with_invariants! {
    pub struct PageTablePageSpinLock<C: PageTableConfig> {
        pub flag: AtomicBool<_, SpinFlagToken<C>, _>,

        pub paddr: Ghost<Paddr>,
        pub level: Ghost<PagingLevel>,

        pub inst: Tracked<SpinInstance<C>>,
        pub pt_inst: Tracked<SpecInstance>,
        pub nid: Ghost<NodeId>,
        pub stray_cell_id: Ghost<CellId>,
    }

    pub open spec fn wf(&self) -> bool {
        predicate {
            // &&& valid_paddr(self.paddr@)
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

        invariant on flag with (inst) is (v: bool, g: SpinFlagToken<C>) {
            &&& g.instance_id() == inst@.id()
            &&& g.value() == v
        }
    }
}

pub tracked struct SpinGuardGhostInner<C: PageTableConfig> {
    pub handle: SpinGuardToken<C>,
    pub node_token: Option<NodeToken>,
    pub pte_token: Option<PteArrayToken>,
    pub stray_perm: StrayPerm,
    pub perms: PageTableEntryPerms<C>,
    pub in_protocol: bool,
}

impl<C: PageTableConfig> SpinGuardGhostInner<C> {
    pub open spec fn wf(self, spinlock: &PageTablePageSpinLock<C>) -> bool {
        &&& self.handle.instance_id() == spinlock.inst@.id()
        &&& self.node_token is Some <==> self.pte_token is Some
        &&& self.stray_perm.perm.value() == false <==> self.node_token is Some
        &&& self.node_token is Some ==> {
            &&& self.node_token->Some_0.instance_id() == spinlock.pt_inst@.id()
            &&& self.node_token->Some_0.key() == spinlock.nid@
            &&& !(self.node_token->Some_0.value() is Free)
            &&& self.in_protocol == true ==> self.node_token->Some_0.value() is Locked
            &&& self.in_protocol == false ==> self.node_token->Some_0.value() is LockedOutside
        }
        &&& self.pte_token is Some ==> {
            &&& self.pte_token->Some_0.instance_id() == spinlock.pt_inst@.id()
            &&& self.pte_token->Some_0.key() == spinlock.nid@
            &&& self.pte_token->Some_0.value().wf()
            &&& self.perms.relate_pte_state(spinlock.level@, self.pte_token->Some_0.value())
        }
        &&& self.stray_perm.wf_with_cell_id(spinlock.stray_cell_id@)
        &&& self.stray_perm.perm.is_init()
        &&& self.stray_perm.wf_with_node_info(
            spinlock.pt_inst@.id(),
            spinlock.nid@,
            spinlock.paddr@,
        )
        &&& self.perms.wf(spinlock.paddr@, spinlock.level@, spinlock.pt_inst@.id(), spinlock.nid@)
        &&& self.perms.addr() == paddr_to_vaddr(spinlock.paddr@)
    }

    /// Used in PageTableGuard::write_pte
    pub open spec fn wf_except(self, spinlock: &PageTablePageSpinLock<C>, idx: nat) -> bool {
        &&& self.handle.instance_id() == spinlock.inst@.id()
        &&& self.node_token is Some <==> self.pte_token is Some
        &&& self.stray_perm.perm.value() == false <==> self.node_token is Some
        &&& self.node_token is Some ==> {
            &&& self.node_token->Some_0.instance_id() == spinlock.pt_inst@.id()
            &&& self.node_token->Some_0.key() == spinlock.nid@
            &&& !(self.node_token->Some_0.value() is Free)
            &&& self.in_protocol == true ==> self.node_token->Some_0.value() is Locked
            &&& self.in_protocol == false ==> self.node_token->Some_0.value() is LockedOutside
        }
        &&& self.pte_token is Some ==> {
            &&& self.pte_token->Some_0.instance_id() == spinlock.pt_inst@.id()
            &&& self.pte_token->Some_0.key() == spinlock.nid@
            &&& self.pte_token->Some_0.value().wf()
            &&& self.perms.relate_pte_state_except(
                spinlock.level@,
                self.pte_token->Some_0.value(),
                idx,
            )
        }
        &&& self.stray_perm.wf_with_cell_id(spinlock.stray_cell_id@)
        &&& self.stray_perm.perm.is_init()
        &&& self.stray_perm.wf_with_node_info(
            spinlock.pt_inst@.id(),
            spinlock.nid@,
            spinlock.paddr@,
        )
        &&& self.perms.wf(spinlock.paddr@, spinlock.level@, spinlock.pt_inst@.id(), spinlock.nid@)
        &&& self.perms.addr() == paddr_to_vaddr(spinlock.paddr@)
    }

    pub open spec fn relate_nid(self, nid: NodeId) -> bool {
        &&& self.node_token is Some ==> self.node_token->Some_0.key() == nid
        &&& self.pte_token is Some ==> self.pte_token->Some_0.key() == nid
        &&& self.stray_perm.nid() == nid
        &&& self.perms.relate_nid(nid)
    }
}

pub struct SpinGuard<C: PageTableConfig> {
    pub inner: Tracked<SpinGuardGhostInner<C>>,
}

impl<C: PageTableConfig> SpinGuard<C> {
    pub open spec fn wf(self, spinlock: &PageTablePageSpinLock<C>) -> bool {
        &&& self.inner@.wf(spinlock)
    }

    /// Used in PageTableGuard::write_pte
    pub open spec fn wf_except(self, spinlock: &PageTablePageSpinLock<C>, idx: nat) -> bool {
        &&& self.inner@.wf_except(spinlock, idx)
    }

    pub open spec fn handle(&self) -> SpinGuardToken<C> {
        self.inner@.handle
    }

    pub open spec fn node_token(&self) -> Option<NodeToken> {
        self.inner@.node_token
    }

    pub open spec fn view_node_token(&self) -> NodeToken
        recommends
            self.inner@.node_token is Some,
    {
        self.inner@.node_token->Some_0
    }

    pub open spec fn pte_token(&self) -> Option<PteArrayToken> {
        self.inner@.pte_token
    }

    pub open spec fn view_pte_token(&self) -> PteArrayToken
        recommends
            self.inner@.pte_token is Some,
    {
        self.inner@.pte_token->Some_0
    }

    pub open spec fn stray_perm(&self) -> StrayPerm {
        self.inner@.stray_perm
    }

    pub open spec fn perms(&self) -> PageTableEntryPerms<C> {
        self.inner@.perms
    }

    pub open spec fn in_protocol(&self) -> bool {
        self.inner@.in_protocol
    }

    pub proof fn tracked_borrow_node_token(tracked &self) -> (tracked res: &NodeToken)
        requires
            self.node_token() is Some,
        ensures
            *res =~= self.view_node_token(),
    {
        self.inner.borrow().node_token.tracked_borrow()
    }

    pub proof fn tracked_borrow_pte_token(tracked &self) -> (tracked res: &PteArrayToken)
        requires
            self.pte_token() is Some,
        ensures
            *res =~= self.view_pte_token(),
    {
        self.inner.borrow().pte_token.tracked_borrow()
    }

    pub fn take_node_token(&mut self) -> (res: Tracked<NodeToken>)
        requires
            old(self).inner@.node_token is Some,
        ensures
            res == old(self).view_node_token(),
            self.node_token() == None::<NodeToken>,
            self.pte_token() == old(self).pte_token(),
            self.stray_perm() == old(self).stray_perm(),
            self.perms() == old(self).perms(),
            self.in_protocol() == old(self).in_protocol(),
            self.handle() == old(self).handle(),
    {
        let tracked res = self.inner.borrow_mut().node_token.tracked_take();
        Tracked(res)
    }

    #[verifier::external_body]
    pub fn put_node_token(&mut self, token: Tracked<NodeToken>)
        requires
            old(self).inner@.node_token is None,
        ensures
            self.node_token() == Option::Some(token@),
            self.pte_token() == old(self).pte_token(),
            self.stray_perm() == old(self).stray_perm(),
            self.perms() == old(self).perms(),
            self.in_protocol() == old(self).in_protocol(),
            self.handle() == old(self).handle(),
    {
        unimplemented!()
    }

    //Although this function has mode exec, its operations are pure logical
    pub fn update_in_protocol(&mut self, in_protocol: Tracked<bool>)
        ensures
            self.in_protocol() == in_protocol@,
            self.node_token() == old(self).node_token(),
            self.pte_token() == old(self).pte_token(),
            self.stray_perm() == old(self).stray_perm(),
            self.perms() == old(self).perms(),
            self.handle() == old(self).handle(),
    {
        proof {
            self.inner.borrow_mut().in_protocol = in_protocol.get();
        }
    }
}

impl<C: PageTableConfig> PageTablePageSpinLock<C> {
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

    #[verifier::exec_allows_no_decreases_clause]
    pub fn normal_lock(&self) -> (res: SpinGuard<C>)
        requires
            self.wf(),
        ensures
            res.wf(self),
            res.in_protocol() == false,
    {
        let mut guard_opt: Option<SpinGuard<C>> = None;
        loop
            invariant_except_break
                self.wf(),
                guard_opt is None,
            ensures
                guard_opt is Some,
                guard_opt->Some_0.wf(self),
                guard_opt->Some_0.in_protocol() == false,
        {
            let tracked mut handle_opt: Option<SpinGuardToken<C>> = None;
            let tracked mut node_token_opt: Option<Option<NodeToken>> = None;
            let tracked mut pte_token_opt: Option<Option<PteArrayToken>> = None;
            let tracked mut stray_perm_opt: Option<StrayPerm> = None;
            let tracked mut perms_opt: Option<PageTableEntryPerms<C>> = None;
            let result =
                atomic_with_ghost!(
                &self.flag => compare_exchange(false, true);
                returning res;
                ghost g => {
                    if res is Ok {
                        let tracked res = self.inst.borrow().acquire(&mut g);
                        let tracked pair = res.1.get();
                        handle_opt = Some(res.2.get());
                        node_token_opt = Some(pair.0);
                        pte_token_opt = Some(pair.1);
                        stray_perm_opt = Some(pair.2);
                        perms_opt = Some(pair.3);
                    }
                }
            );

            match result {
                Result::Ok(_) => {
                    let tracked handle = match handle_opt {
                        Option::Some(t) => t,
                        Option::None => proof_from_false(),
                    };
                    let tracked mut node_token = match node_token_opt {
                        Option::Some(t) => t,
                        Option::None => proof_from_false(),
                    };
                    let tracked pte_token = match pte_token_opt {
                        Option::Some(t) => t,
                        Option::None => proof_from_false(),
                    };
                    let tracked stray_perm = match stray_perm_opt {
                        Option::Some(t) => t,
                        Option::None => proof_from_false(),
                    };
                    let tracked perms = match perms_opt {
                        Option::Some(t) => t,
                        Option::None => proof_from_false(),
                    };
                    proof {
                        if stray_perm.value() == false {
                            let tracked mut node_token_inner = node_token.tracked_unwrap();
                            node_token_inner =
                            self.pt_inst.borrow().normal_lock(self.nid@, node_token_inner);
                            node_token = Some(node_token_inner);
                        }
                    }
                    let guard = SpinGuard {
                        inner: Tracked(
                            SpinGuardGhostInner {
                                handle: handle,
                                node_token: node_token,
                                pte_token: pte_token,
                                stray_perm: stray_perm,
                                perms: perms,
                                in_protocol: false,
                            },
                        ),
                    };
                    assert(guard.wf(self));
                    guard_opt = Some(guard);
                    break ;
                },
                _ => (),
            };
        }
        let guard = guard_opt.unwrap();
        guard
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn normal_lock_new_allocated_node(
        &self,
        pa_pte_array_token: Tracked<&PteArrayToken>,
    ) -> (res: SpinGuard<C>)
        requires
            self.wf(),
            self.nid@ != NodeHelper::root_id(),
            pa_pte_array_token@.instance_id() == self.pt_inst_id(),
            pa_pte_array_token@.key() == NodeHelper::get_parent(self.nid@),
            pa_pte_array_token@.value().is_alive(NodeHelper::get_offset(self.nid@)),
            pa_pte_array_token@.value().get_paddr(NodeHelper::get_offset(self.nid@)) == self.paddr@,
        ensures
            res.wf(self),
            res.stray_perm().value() == false,
            res.in_protocol() == false,
    {
        let tracked pa_pte_array_token = pa_pte_array_token.get();
        let mut guard_opt: Option<SpinGuard<C>> = None;
        loop
            invariant_except_break
                self.wf(),
                self.nid@ != NodeHelper::root_id(),
                pa_pte_array_token.instance_id() == self.pt_inst_id(),
                pa_pte_array_token.key() == NodeHelper::get_parent(self.nid@),
                pa_pte_array_token.value().is_alive(NodeHelper::get_offset(self.nid@)),
                pa_pte_array_token.value().get_paddr(NodeHelper::get_offset(self.nid@))
                    == self.paddr@,
                guard_opt is None,
            ensures
                guard_opt is Some,
                guard_opt->Some_0.wf(self),
                guard_opt->Some_0.stray_perm().value() == false,
                guard_opt->Some_0.in_protocol() == false,
        {
            let tracked mut handle_opt: Option<SpinGuardToken<C>> = None;
            let tracked mut node_token_opt: Option<Option<NodeToken>> = None;
            let tracked mut pte_token_opt: Option<Option<PteArrayToken>> = None;
            let tracked mut stray_perm_opt: Option<StrayPerm> = None;
            let tracked mut perms_opt: Option<PageTableEntryPerms<C>> = None;
            let result =
                atomic_with_ghost!(
                &self.flag => compare_exchange(false, true);
                returning res;
                ghost g => {
                    if res is Ok {
                        let tracked res = self.inst.borrow().acquire(&mut g);
                        let tracked pair = res.1.get();
                        handle_opt = Some(res.2.get());
                        node_token_opt = Some(pair.0);
                        pte_token_opt = Some(pair.1);
                        stray_perm_opt = Some(pair.2);
                        perms_opt = Some(pair.3);
                    }
                }
            );

            match result {
                Result::Ok(_) => {
                    let tracked handle = match handle_opt {
                        Option::Some(t) => t,
                        Option::None => proof_from_false(),
                    };
                    let tracked node_token = match node_token_opt {
                        Option::Some(t) => t,
                        Option::None => proof_from_false(),
                    };
                    let tracked pte_token = match pte_token_opt {
                        Option::Some(t) => t,
                        Option::None => proof_from_false(),
                    };
                    let tracked stray_perm = match stray_perm_opt {
                        Option::Some(t) => t,
                        Option::None => proof_from_false(),
                    };
                    let tracked perms = match perms_opt {
                        Option::Some(t) => t,
                        Option::None => proof_from_false(),
                    };
                    proof {
                        self.pt_inst.borrow().stray_is_false(
                            self.nid@,
                            self.paddr@,
                            &pa_pte_array_token,
                            &stray_perm.token,
                        );
                        assert(stray_perm.value() == false);
                    }
                    let tracked mut node_token = node_token.tracked_unwrap();
                    let tracked mut pte_token = pte_token.tracked_unwrap();
                    proof {
                        node_token = self.pt_inst.borrow().normal_lock(self.nid@, node_token);
                    }
                    let guard = SpinGuard {
                        inner: Tracked(
                            SpinGuardGhostInner {
                                handle: handle,
                                node_token: Some(node_token),
                                pte_token: Some(pte_token),
                                stray_perm: stray_perm,
                                perms: perms,
                                in_protocol: false,
                            },
                        ),
                    };
                    assert(guard.wf(self));
                    guard_opt = Some(guard);
                    break ;
                },
                _ => (),
            };
        }
        let guard = guard_opt.unwrap();
        guard
    }

    pub fn normal_unlock(&self, guard: SpinGuard<C>)
        requires
            self.wf(),
            guard.wf(self),
            guard.in_protocol() == false,
    {
        let tracked inner = guard.inner.get();
        let tracked handle = inner.handle;
        let tracked mut node_token: Option<NodeToken> = inner.node_token;
        let tracked pte_token: Option<PteArrayToken> = inner.pte_token;
        let tracked stray_perm: StrayPerm = inner.stray_perm;
        let tracked perms: PageTableEntryPerms<C> = inner.perms;
        atomic_with_ghost!(
            &self.flag => store(false);
            ghost g => {
                if stray_perm.value() == false {
                    let tracked mut node_token_inner = node_token.tracked_unwrap();
                    node_token_inner =
                        self.pt_inst.borrow().normal_unlock(self.nid@, node_token_inner);
                    node_token = Some(node_token_inner);
                }
                let tracked pair = (
                    node_token,
                    pte_token,
                    stray_perm,
                    perms,
                );
                self.inst.borrow().release(pair, &mut g, pair, handle);
            }
        )
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn lock(
        &self,
        m: Tracked<LockProtocolModel>,
        pa_pte_array_token: Tracked<&PteArrayToken>,
    ) -> (res: (SpinGuard<C>, Tracked<LockProtocolModel>))
        requires
            self.wf(),
            m@.inv(),
            m@.inst_id() == self.pt_inst_id(),
            m@.state() is Locking,
            m@.cur_node() == self.nid(),
            NodeHelper::in_subtree_range(m@.sub_tree_rt(), self.nid()),
            pa_pte_array_token@.instance_id() == self.pt_inst_id(),
            pa_pte_array_token@.key() == NodeHelper::get_parent(self.nid@),
            m@.node_is_locked(pa_pte_array_token@.key()),
            pa_pte_array_token@.value().is_alive(NodeHelper::get_offset(self.nid@)),
            pa_pte_array_token@.value().get_paddr(NodeHelper::get_offset(self.nid@)) == self.paddr@,
        ensures
            res.0.wf(self),
            res.0.stray_perm().value() == false,
            res.0.in_protocol() == true,
            res.1@.inv(),
            res.1@.inst_id() == self.pt_inst_id(),
            res.1@.state() is Locking,
            res.1@.sub_tree_rt() == m@.sub_tree_rt(),
            res.1@.cur_node() == self.nid() + 1,
    {
        let tracked m = m.get();
        let ghost sub_tree_rt = m.sub_tree_rt();
        let tracked pa_pte_array_token = pa_pte_array_token.get();
        let mut guard_opt: Option<SpinGuard<C>> = None;
        loop
            invariant_except_break
                self.wf(),
                m.inv(),
                m.inst_id() == self.pt_inst_id(),
                m.state() is Locking,
                m.sub_tree_rt() == sub_tree_rt,
                m.cur_node() == self.nid(),
                NodeHelper::in_subtree_range(m.sub_tree_rt(), self.nid()),
                pa_pte_array_token.instance_id() == self.pt_inst_id(),
                pa_pte_array_token.key() == NodeHelper::get_parent(self.nid@),
                m.node_is_locked(pa_pte_array_token.key()),
                pa_pte_array_token.value().is_alive(NodeHelper::get_offset(self.nid@)),
                pa_pte_array_token.value().get_paddr(NodeHelper::get_offset(self.nid@))
                    == self.paddr@,
                guard_opt is None,
            ensures
                m.inv(),
                m.inst_id() == self.pt_inst_id(),
                m.state() is Locking,
                m.sub_tree_rt() == sub_tree_rt,
                m.cur_node() == self.nid() + 1,
                guard_opt is Some,
                guard_opt->Some_0.wf(self),
                guard_opt->Some_0.stray_perm().value() == false,
                guard_opt->Some_0.in_protocol() == true,
        {
            let tracked mut handle_opt: Option<SpinGuardToken<C>> = None;
            let tracked mut node_token_opt: Option<Option<NodeToken>> = None;
            let tracked mut pte_token_opt: Option<Option<PteArrayToken>> = None;
            let tracked mut stray_perm_opt: Option<StrayPerm> = None;
            let tracked mut perms_opt: Option<PageTableEntryPerms<C>> = None;
            let result =
                atomic_with_ghost!(
                &self.flag => compare_exchange(false, true);
                returning res;
                ghost g => {
                    if res is Ok {
                        let tracked res = self.inst.borrow().acquire(&mut g);
                        let tracked pair = res.1.get();
                        handle_opt = Some(res.2.get());
                        node_token_opt = Some(pair.0);
                        pte_token_opt = Some(pair.1);
                        stray_perm_opt = Some(pair.2);
                        perms_opt = Some(pair.3);
                    }
                }
            );

            match result {
                Result::Ok(_) => {
                    let tracked handle = match handle_opt {
                        Option::Some(t) => t,
                        Option::None => proof_from_false(),
                    };
                    let tracked node_token = match node_token_opt {
                        Option::Some(t) => t,
                        Option::None => proof_from_false(),
                    };
                    let tracked pte_token = match pte_token_opt {
                        Option::Some(t) => t,
                        Option::None => proof_from_false(),
                    };
                    let tracked stray_perm = match stray_perm_opt {
                        Option::Some(t) => t,
                        Option::None => proof_from_false(),
                    };
                    let tracked perms = match perms_opt {
                        Option::Some(t) => t,
                        Option::None => proof_from_false(),
                    };
                    proof {
                        self.pt_inst.borrow().stray_is_false(
                            self.nid@,
                            self.paddr@,
                            &pa_pte_array_token,
                            &stray_perm.token,
                        );
                        assert(stray_perm.value() == false);
                    }
                    let tracked mut node_token = node_token.tracked_unwrap();
                    let tracked mut pte_token = pte_token.tracked_unwrap();
                    proof {
                        assert(NodeHelper::in_subtree_range(m.sub_tree_rt(), self.nid@));
                        let tracked res = self.pt_inst.borrow().protocol_lock(
                            m.cpu,
                            self.nid@,
                            node_token,
                            m.token,
                        );
                        node_token = res.0.get();
                        m.token = res.1.get();
                    }
                    let guard = SpinGuard {
                        inner: Tracked(
                            SpinGuardGhostInner {
                                handle: handle,
                                node_token: Some(node_token),
                                pte_token: Some(pte_token),
                                stray_perm: stray_perm,
                                perms: perms,
                                in_protocol: true,
                            },
                        ),
                    };
                    assert(guard.wf(self));
                    guard_opt = Some(guard);
                    break ;
                },
                _ => (),
            };
        }
        let guard = guard_opt.unwrap();
        (guard, Tracked(m))
    }

    pub fn unlock(&self, guard: SpinGuard<C>, m: Tracked<LockProtocolModel>) -> (res: Tracked<
        LockProtocolModel,
    >)
        requires
            self.wf(),
            guard.wf(self),
            guard.stray_perm().value() == false,
            guard.in_protocol() == true,
            m@.inv(),
            m@.inst_id() == self.pt_inst_id(),
            m@.state() is Locking,
            m@.cur_node() == self.nid() + 1,
            m@.node_is_locked(self.nid()),
        ensures
            res@.inv(),
            res@.inst_id() == self.pt_inst_id(),
            res@.state() is Locking,
            res@.sub_tree_rt() == m@.sub_tree_rt(),
            res@.cur_node() == self.nid(),
    {
        let tracked m = m.get();
        let tracked inner = guard.inner.get();
        let tracked handle = inner.handle;
        let tracked mut node_token: NodeToken = inner.node_token.tracked_unwrap();
        let tracked pte_token: PteArrayToken = inner.pte_token.tracked_unwrap();
        let tracked stray_perm: StrayPerm = inner.stray_perm;
        let tracked perms: PageTableEntryPerms<C> = inner.perms;
        atomic_with_ghost!(
            &self.flag => store(false);
            ghost g => {
                let tracked res = self.pt_inst.borrow().protocol_unlock(
                    m.cpu,
                    self.nid@,
                    node_token,
                    m.token,
                );
                node_token = res.0.get();
                m.token = res.1.get();
                let tracked pair = (
                    Some(node_token),
                    Some(pte_token),
                    stray_perm,
                    perms,
                );
                self.inst.borrow().release(pair, &mut g, pair, handle);
            }
        );

        Tracked(m)
    }
}

} // verus!
