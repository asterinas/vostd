// Copied from vstd
use core::marker::PhantomData;
use verus_state_machines_macros::tokenized_state_machine;
use vstd::prelude::*;
use vstd::atomic_ghost::*;
use vstd::invariant::InvariantPredicate;
use vstd::multiset::*;
use vstd::set::*;
use vstd::rwlock::RwLockPredicate;

use vstd_extra::array_ptr::*;

use crate::spec::{common::*, utils::*, rw::*};
use super::super::{common::*, types::*, cpu::*};
use super::super::pte::Pte;

// The tokenized state machine is unchanged.
tokenized_state_machine! {

RwLockToks<K, V, Pred: InvariantPredicate<K, V>> {
    fields {
        #[sharding(constant)]
        pub k: K,

        #[sharding(constant)]
        pub pred: PhantomData<Pred>,

        #[sharding(variable)]
        pub flag_exc: bool,

        #[sharding(variable)]
        pub flag_rc: nat,

        #[sharding(variable)]
        pub flag_real_rc: nat,

        #[sharding(storage_option)]
        pub storage: Option<V>,

        #[sharding(option)]
        pub pending_writer: Option<()>,

        #[sharding(option)]
        pub writer: Option<()>,

        #[sharding(multiset)]
        pub pending_reader: Multiset<()>,

        #[sharding(multiset)]
        pub mock_reader: Multiset<()>,

        #[sharding(multiset)]
        pub reader: Multiset<V>,
    }

    init!{
        initialize_full(k: K, t: V) {
            require Pred::inv(k, t);
            init k = k;
            init pred = PhantomData;
            init flag_exc = false;
            init flag_rc = 0;
            init flag_real_rc = 0;
            init storage = Option::Some(t);
            init pending_writer = Option::None;
            init writer = Option::None;
            init pending_reader = Multiset::empty();
            init mock_reader = Multiset::empty();
            init reader = Multiset::empty();
        }
    }

    #[inductive(initialize_full)]
    fn initialize_full_inductive(post: Self, k: K, t: V) {
        broadcast use group_multiset_axioms;
    }

    /// Increment the 'rc' counter, obtain a pending_reader
    transition!{
        acquire_read_start() {
            update flag_rc = pre.flag_rc + 1;
            add pending_reader += {()};
        }
    }

    /// Exchange the pending_reader for a reader by checking
    /// that the 'exc' bit is 0
    transition!{
        acquire_read_end() {
            require(pre.flag_exc == false);

            remove pending_reader -= {()};
            add mock_reader += {()};
        }
    }

    transition!{
        inc_real_rc() {
            update flag_real_rc = pre.flag_real_rc + 1;

            remove mock_reader -= {()};

            birds_eye let x: V = pre.storage->0;
            add reader += {x};

            assert Pred::inv(pre.k, x);
        }
    }

    /// Decrement the 'rc' counter, abandon the attempt to gain
    /// the 'read' lock.
    transition!{
        acquire_read_abandon() {
            remove pending_reader -= {()};
            assert(pre.flag_rc >= 1);
            update flag_rc = (pre.flag_rc - 1) as nat;
        }
    }

    /// Atomically set 'exc' bit from 'false' to 'true'
    /// Obtain a pending_writer
    transition!{
        acquire_exc_start() {
            require(pre.flag_exc == false);
            update flag_exc = true;
            add pending_writer += Some(());
        }
    }

    /// Finish obtaining the write lock by checking that 'rc' is 0.
    /// Exchange the pending_writer for a writer and withdraw the
    /// stored object.
    transition!{
        acquire_exc_end() {
            require(pre.flag_rc == 0);

            remove pending_writer -= Some(());

            add writer += Some(());

            birds_eye let x = pre.storage->0;
            withdraw storage -= Some(x);

            assert Pred::inv(pre.k, x);
        }
    }

    /// Release the write-lock. Update the 'exc' bit back to 'false'.
    /// Return the 'writer' and also deposit an object back into storage.
    transition!{
        release_exc(x: V) {
            require Pred::inv(pre.k, x);
            remove writer -= Some(());

            update flag_exc = false;

            deposit storage += Some(x);
        }
    }

    /// Check that the 'reader' is actually a guard for the given object.
    property!{
        read_guard(x: V) {
            have reader >= {x};
            guard storage >= Some(x);
        }
    }

    property!{
        read_match(x: V, y: V) {
            have reader >= {x};
            have reader >= {y};
            assert(equal(x, y));
        }
    }

    property!{
        write_locked_implies_real_rc_is_zero() {
            have writer >= Some(());
            assert(pre.flag_real_rc == 0);
        }
    }

    #[transition]
    transition!{
        dec_real_rc(x: V) {
            remove reader -= {x};
            add mock_reader += {()};

            assert(pre.flag_real_rc >= 1) by {
                assert(equal(pre.storage, Option::Some(x)));
            };
            update flag_real_rc = (pre.flag_real_rc - 1) as nat;
        }
    }

    /// Release the reader-lock. Decrement 'rc' and return the 'reader' object.
    #[transition]
    transition!{
        release_shared() {
            remove mock_reader -= {()};

            assert(pre.flag_rc >= 1) by {
                assert(pre.storage is Some);
            };
            update flag_rc = (pre.flag_rc - 1) as nat;
        }
    }

    #[invariant]
    pub fn exc_bit_matches(&self) -> bool {
        (if self.flag_exc { 1 } else { 0 as int }) ==
            (if self.pending_writer is Some { 1 } else { 0 as int }) as int
            + (if self.writer is Some { 1 } else { 0 as int }) as int
    }

    #[invariant]
    pub fn count_matches(&self) -> bool {
        self.flag_rc == self.pending_reader.count(())
            + self.mock_reader.count(())
            + self.reader.count(self.storage->0)
    }

    #[invariant]
    pub fn real_count_matches(&self) -> bool {
        self.flag_real_rc == self.reader.count(self.storage->0)
    }

    #[invariant]
    pub fn mock_reader_implies_storage_is_some(&self) -> bool {
        self.mock_reader.count(()) > 0 ==> self.storage is Some
    }

    #[invariant]
    pub fn reader_agrees_storage(&self) -> bool {
        forall |t: V| imply(#[trigger] self.reader.count(t) > 0,
            equal(self.storage, Option::Some(t)))
    }

    #[invariant]
    pub fn writer_agrees_storage(&self) -> bool {
        imply(self.writer is Some, self.storage is None)
    }

    #[invariant]
    pub fn writer_agrees_storage_rev(&self) -> bool {
        imply(self.storage is None, self.writer is Some)
    }

    #[invariant]
    pub fn sto_user_inv(&self) -> bool {
        self.storage.is_some() ==> Pred::inv(self.k, self.storage.unwrap())
    }

    #[inductive(acquire_read_start)]
    fn acquire_read_start_inductive(pre: Self, post: Self) {
        broadcast use group_multiset_axioms;
    }

    #[inductive(acquire_read_end)]
    fn acquire_read_end_inductive(pre: Self, post: Self) {
        broadcast use group_multiset_axioms;
    }

    #[inductive(inc_real_rc)]
    fn inc_real_rc_inductive(pre: Self, post: Self) {
        broadcast use group_multiset_axioms;
    }

    #[inductive(acquire_read_abandon)]
    fn acquire_read_abandon_inductive(pre: Self, post: Self) {
        broadcast use group_multiset_axioms;
    }

    #[inductive(acquire_exc_start)]
    fn acquire_exc_start_inductive(pre: Self, post: Self) { }

    #[inductive(acquire_exc_end)]
    fn acquire_exc_end_inductive(pre: Self, post: Self) { }

    #[inductive(release_exc)]
    fn release_exc_inductive(pre: Self, post: Self, x: V) { }

    #[inductive(dec_real_rc)]
    fn dec_real_rc_inductive(pre: Self, post: Self, x: V) { }

    #[inductive(release_shared)]
    fn release_shared_inductive(pre: Self, post: Self) { }
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
            0 <= i < 512 ==> self.inner.value()[i].wf_with_node_info(
                level,
                instance_id,
                nid,
                i as nat,
            )
    }

    pub open spec fn addr(&self) -> Vaddr {
        self.inner.addr()
    }

    pub open spec fn relate_pte_state(&self, level: PagingLevel, state: PteArrayState) -> bool {
        forall|i: int|
            #![trigger self.inner.value()[i].is_pt(level)]
            0 <= i < 512 ==> { self.inner.value()[i].is_pt(level) <==> state.is_alive(i as nat) }
    }

    pub open spec fn relate_pte_state_except(
        &self,
        level: PagingLevel,
        state: PteArrayState,
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

pub ghost struct RwInternalPred;

impl InvariantPredicate<
    (InstanceId, NodeId, Paddr, PagingLevel),
    (NodeToken, PteArrayToken, PageTableEntryPerms),
> for RwInternalPred {
    open spec fn inv(
        k: (InstanceId, NodeId, Paddr, PagingLevel),
        v: (NodeToken, PteArrayToken, PageTableEntryPerms),
    ) -> bool {
        &&& v.0.instance_id() == k.0
        &&& v.0.key() == k.1
        &&& v.0.value() is WriteUnLocked
        &&& v.1.instance_id() == k.0
        &&& v.1.key() == k.1
        &&& v.1.value().wf()
        &&& v.2.relate_pte_state(k.3, v.1.value())
        &&& v.2.wf(k.2, k.3, k.0, k.1)
        &&& v.2.addr() == paddr_to_vaddr(k.2)
    }
}

type RwInstance = RwLockToks::Instance<
    (InstanceId, NodeId, Paddr, PagingLevel),
    (NodeToken, PteArrayToken, PageTableEntryPerms),
    RwInternalPred,
>;

type RwExcToken = RwLockToks::flag_exc<
    (InstanceId, NodeId, Paddr, PagingLevel),
    (NodeToken, PteArrayToken, PageTableEntryPerms),
    RwInternalPred,
>;

type RwRcToken = RwLockToks::flag_rc<
    (InstanceId, NodeId, Paddr, PagingLevel),
    (NodeToken, PteArrayToken, PageTableEntryPerms),
    RwInternalPred,
>;

type RwRealRcToken = RwLockToks::flag_real_rc<
    (InstanceId, NodeId, Paddr, PagingLevel),
    (NodeToken, PteArrayToken, PageTableEntryPerms),
    RwInternalPred,
>;

type RwWriterToken = RwLockToks::writer<
    (InstanceId, NodeId, Paddr, PagingLevel),
    (NodeToken, PteArrayToken, PageTableEntryPerms),
    RwInternalPred,
>;

type RwMockReaderToken = RwLockToks::mock_reader<
    (InstanceId, NodeId, Paddr, PagingLevel),
    (NodeToken, PteArrayToken, PageTableEntryPerms),
    RwInternalPred,
>;

type RwReaderToken = RwLockToks::reader<
    (InstanceId, NodeId, Paddr, PagingLevel),
    (NodeToken, PteArrayToken, PageTableEntryPerms),
    RwInternalPred,
>;

type RwPendingWriterToken = RwLockToks::pending_writer<
    (InstanceId, NodeId, Paddr, PagingLevel),
    (NodeToken, PteArrayToken, PageTableEntryPerms),
    RwInternalPred,
>;

type RwPendingReaderToken = RwLockToks::pending_reader<
    (InstanceId, NodeId, Paddr, PagingLevel),
    (NodeToken, PteArrayToken, PageTableEntryPerms),
    RwInternalPred,
>;

struct_with_invariants! {
    // Here all types are determined.
    pub struct PageTablePageRwLock {
        pub exc: AtomicBool<_, RwExcToken, _>,
        pub rc: AtomicU64<_, RwRcToken, _>,
        pub real_rc: AtomicU64<_, (RwRealRcToken, RcToken), _>,

        pub paddr: Ghost<Paddr>,
        pub level: Ghost<PagingLevel>,

        pub inst: Tracked<RwInstance>,
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

        invariant on exc with (inst) is (v: bool, g: RwExcToken) {
            &&& g.instance_id() == inst@.id()
            &&& g.value() == v
        }

        invariant on rc with (inst) is (v: u64, g: RwRcToken) {
            &&& g.instance_id() == inst@.id()
            &&& g.value() == v
        }

        invariant on real_rc with (inst, pt_inst, nid) is (v: u64, g: (RwRealRcToken, RcToken)) {
            &&& g.0.instance_id() == inst@.id()
            &&& g.0.value() == v
            &&& g.1.instance_id() == pt_inst@.id()
            &&& g.1.key() == nid@
            &&& g.1.value() == v
        }
    }
}

pub struct RwWriteGuard {
    pub handle: Tracked<RwWriterToken>,
    pub node_token: Tracked<NodeToken>,
    pub pte_array_token: Tracked<PteArrayToken>,
    pub perms: Tracked<PageTableEntryPerms>,
    pub in_protocol: Ghost<bool>,
}

pub struct RwReadGuard {
    pub handle: Tracked<RwReaderToken>,
}

impl RwWriteGuard {
    pub open spec fn wf(self, rwlock: &PageTablePageRwLock) -> bool {
        &&& self.handle@.instance_id() == rwlock.inst@.id()
        &&& self.node_token@.instance_id() == rwlock.pt_inst@.id()
        &&& self.node_token@.key() == rwlock.nid@
        &&& self.node_token@.value().is_write_locked()
        &&& self.pte_array_token@.instance_id() == rwlock.pt_inst@.id()
        &&& self.pte_array_token@.key() == rwlock.nid@
        &&& self.pte_array_token@.value().wf()
        &&& self.perms@.relate_pte_state(rwlock.level@, self.pte_array_token@.value())
        &&& self.perms@.wf(rwlock.paddr@, rwlock.level@, rwlock.pt_inst@.id(), rwlock.nid@)
        &&& self.perms@.addr() == paddr_to_vaddr(rwlock.paddr@)
        &&& self.in_protocol@ <==> self.node_token@.value() is InProtocolWriteLocked
    }

    /// Used in PageTableGuard::write_pte
    pub open spec fn wf_except(self, rwlock: &PageTablePageRwLock, idx: nat) -> bool {
        &&& self.handle@.instance_id() == rwlock.inst@.id()
        &&& self.node_token@.instance_id() == rwlock.pt_inst@.id()
        &&& self.node_token@.key() == rwlock.nid@
        &&& self.node_token@.value().is_write_locked()
        &&& self.pte_array_token@.instance_id() == rwlock.pt_inst@.id()
        &&& self.pte_array_token@.key() == rwlock.nid@
        &&& self.pte_array_token@.value().wf()
        &&& self.perms@.relate_pte_state_except(rwlock.level@, self.pte_array_token@.value(), idx)
        &&& self.perms@.wf(rwlock.paddr@, rwlock.level@, rwlock.pt_inst@.id(), rwlock.nid@)
        &&& self.perms@.addr() == paddr_to_vaddr(rwlock.paddr@)
        &&& self.in_protocol@ <==> self.node_token@.value() is InProtocolWriteLocked
    }

    pub open spec fn view_node_token(&self) -> NodeToken {
        self.node_token@
    }

    pub open spec fn view_pte_array_token(&self) -> PteArrayToken {
        self.pte_array_token@
    }

    pub open spec fn view_perms(&self) -> PageTableEntryPerms {
        self.perms@
    }
}

impl RwReadGuard {
    pub open spec fn wf(&self, rwlock: &PageTablePageRwLock) -> bool {
        &&& self.handle@.instance_id() == rwlock.inst@.id()
        &&& self.view_node_token().instance_id() == rwlock.pt_inst@.id()
        &&& self.view_node_token().key() == rwlock.nid@
        &&& self.view_node_token().value() is WriteUnLocked
        &&& self.view_pte_array_token().instance_id() == rwlock.pt_inst@.id()
        &&& self.view_pte_array_token().key() == rwlock.nid@
        &&& self.view_perms().relate_pte_state(rwlock.level@, self.view_pte_array_token().value())
        &&& self.view_perms().wf(rwlock.paddr@, rwlock.level@, rwlock.pt_inst@.id(), rwlock.nid@)
        &&& self.view_perms().addr() == paddr_to_vaddr(rwlock.paddr@)
    }

    pub open spec fn view_node_token(&self) -> NodeToken {
        self.handle@.element().0
    }

    pub open spec fn view_pte_array_token(&self) -> PteArrayToken {
        self.handle@.element().1
    }

    pub open spec fn view_perms(&self) -> PageTableEntryPerms {
        self.handle@.element().2
    }

    pub fn borrow(&self, rwlock: &PageTablePageRwLock) -> (res: (
        Tracked<&NodeToken>,
        Tracked<&PteArrayToken>,
        Tracked<&PageTableEntryPerms>,
    ))
        requires
            self.wf(rwlock),
        ensures
            *res.0@ =~= self.view_node_token(),
            *res.1@ =~= self.view_pte_array_token(),
            *res.2@ =~= self.view_perms(),
    {
        let tracked pair = rwlock.inst.borrow().read_guard(
            self.handle@.element(),
            self.handle.borrow(),
        );
        let tracked node_token: &NodeToken = &pair.0;
        let tracked pte_array_token: &PteArrayToken = &pair.1;
        let tracked perms: &PageTableEntryPerms = &pair.2;
        (Tracked(node_token), Tracked(pte_array_token), Tracked(perms))
    }

    pub fn borrow_node_token(&self, rwlock: &PageTablePageRwLock) -> (res: Tracked<&NodeToken>)
        requires
            self.wf(rwlock),
        ensures
            *res@ =~= self.view_node_token(),
    {
        self.borrow(rwlock).0
    }

    pub fn borrow_pte_array_token(&self, rwlock: &PageTablePageRwLock) -> (res: Tracked<
        &PteArrayToken,
    >)
        requires
            self.wf(rwlock),
        ensures
            *res@ =~= self.view_pte_array_token(),
    {
        self.borrow(rwlock).1
    }

    pub fn borrow_perms(&self, rwlock: &PageTablePageRwLock) -> (res: Tracked<&PageTableEntryPerms>)
        requires
            self.wf(rwlock),
        ensures
            *res@ =~= self.view_perms(),
    {
        self.borrow(rwlock).2
    }
}

impl PageTablePageRwLock {
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
    pub fn lock_write(&self, m: Tracked<LockProtocolModel>) -> (res: (
        RwWriteGuard,
        Tracked<LockProtocolModel>,
    ))
        requires
            self.wf(),
            m@.inv(),
            m@.inst_id() == self.pt_inst_id(),
            m@.state() is ReadLocking,
            wf_tree_path(m@.path().push(self.nid())),
        ensures
            res.0.wf(self),
            res.0.in_protocol@ == false,
            res.1@.inv(),
            res.1@.inst_id() == self.pt_inst_id(),
            res.1@.state() is WriteLocked,
            res.1@.path() =~= m@.path().push(self.nid()),
    {
        let mut done = false;
        let tracked mut pending_writer_token: Option<RwPendingWriterToken> = Option::None;
        while !done
            invariant
                done ==> {
                    &&& pending_writer_token.is_some()
                    &&& pending_writer_token->0.instance_id() == self.inst@.id()
                },
                self.wf(),
        {
            let result =
                atomic_with_ghost!(
                &self.exc => compare_exchange(false, true);
                returning res;
                ghost g => {
                    if res is Ok {
                        pending_writer_token = Option::Some(self.inst.borrow().acquire_exc_start(&mut g));
                    }
                }
            );

            done =
            match result {
                Result::Ok(_) => true,
                _ => false,
            };
        }

        let tracked mut m = m.get();
        let ghost path = m.path();
        let mut write_handle_opt: Option<RwWriteGuard> = None;
        loop
            invariant_except_break
                pending_writer_token is Some,
                pending_writer_token->0.instance_id() == self.inst@.id(),
                self.wf(),
                m.inv(),
                m.inst_id() == self.pt_inst_id(),
                m.state() is ReadLocking,
                wf_tree_path(m.path().push(self.nid())),
                path =~= m.path(),
            ensures
                write_handle_opt is Some,
                write_handle_opt->Some_0.wf(self),
                write_handle_opt->Some_0.in_protocol@ == false,
                m.inv(),
                m.inst_id() == self.pt_inst_id(),
                m.state() is WriteLocked,
                m.path() =~= path.push(self.nid()),
        {
            let tracked mut handle_opt: Option<RwWriterToken> = None;
            let tracked mut node_token_opt: Option<NodeToken> = None;
            let tracked mut pte_array_token_opt: Option<PteArrayToken> = None;
            let tracked mut perms_opt: Option<PageTableEntryPerms> = None;
            let result =
                atomic_with_ghost!(
                &self.rc => load();
                returning res;
                ghost g => {
                    if res == 0 {
                        let tracked pw_token = match pending_writer_token {
                            Option::Some(t) => t,
                            Option::None => proof_from_false(),
                        };
                        let tracked res = self.inst.borrow().acquire_exc_end(&g, pw_token);
                        let tracked pair = res.1.get();
                        let tracked exc_handle = res.2.get();
                        pending_writer_token = None;
                        handle_opt = Some(exc_handle);
                        node_token_opt = Some(pair.0);
                        pte_array_token_opt = Some(pair.1);
                        perms_opt = Some(pair.2);
                    }
                }
            );

            if result == 0 {
                let tracked handle = match handle_opt {
                    Option::Some(t) => t,
                    Option::None => proof_from_false(),
                };
                let tracked mut node_token = match node_token_opt {
                    Option::Some(t) => t,
                    Option::None => proof_from_false(),
                };
                let tracked pte_array_token = match pte_array_token_opt {
                    Option::Some(t) => t,
                    Option::None => proof_from_false(),
                };
                let tracked perms = match perms_opt {
                    Option::Some(t) => t,
                    Option::None => proof_from_false(),
                };

                let _ =
                    atomic_with_ghost!(
                    &self.real_rc => no_op();
                    ghost g => {
                        self.inst.borrow().write_locked_implies_real_rc_is_zero(&g.0, &handle);
                        assert(g.1.value() == 0);
                        let tracked res = self.pt_inst.borrow().write_lock(
                            m.cpu,
                            self.nid(),
                            node_token,
                            &g.1,
                            m.token,
                        );
                        node_token = res.0.get();
                        m.token = res.1.get();
                        assert(m.path() == path.push(self.nid()));
                    }
                );

                let write_handle = RwWriteGuard {
                    handle: Tracked(handle),
                    node_token: Tracked(node_token),
                    pte_array_token: Tracked(pte_array_token),
                    perms: Tracked(perms),
                    in_protocol: Ghost(false),
                };
                write_handle_opt = Some(write_handle);
                break ;
            }
        }

        assert(write_handle_opt is Some);
        let write_handle = write_handle_opt.unwrap();
        (write_handle, Tracked(m))
    }

    pub fn unlock_write(&self, guard: RwWriteGuard, m: Tracked<LockProtocolModel>) -> (res: Tracked<
        LockProtocolModel,
    >)
        requires
            self.wf(),
            guard.wf(self),
            guard.in_protocol@ == false,
            m@.inv(),
            m@.inst_id() == self.pt_inst_id(),
            m@.state() is WriteLocked,
            m@.path().len() > 0 && m@.path().last() == self.nid(),
        ensures
            res@.inv(),
            res@.inst_id() == self.pt_inst_id(),
            res@.state() is ReadLocking,
            res@.path() =~= m@.path().drop_last(),
    {
        let tracked mut m = m.get();
        let tracked handle = guard.handle.get();
        let tracked mut node_token = guard.node_token.get();
        let tracked pte_array_token = guard.pte_array_token.get();
        let tracked perms = guard.perms.get();
        proof {
            let tracked res = self.pt_inst.borrow().write_unlock(
                m.cpu,
                self.nid@,
                node_token,
                m.token,
            );
            node_token = res.0.get();
            m.token = res.1.get();
        }

        let tracked pair = (node_token, pte_array_token, perms);
        atomic_with_ghost!(
            &self.exc => store(false);
            ghost g => {
                self.inst.borrow().release_exc(pair, &mut g, pair, handle);
            }
        );

        Tracked(m)
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn lock_read(&self, m: Tracked<LockProtocolModel>) -> (res: (
        RwReadGuard,
        Tracked<LockProtocolModel>,
    ))
        requires
            self.wf(),
            m@.inv(),
            m@.inst_id() == self.pt_inst_id(),
            m@.state() is ReadLocking,
            m@.path().len() < 3,
            wf_tree_path(m@.path().push(self.nid())),
        ensures
            res.0.wf(self),
            res.1@.inv(),
            res.1@.inst_id() == self.pt_inst_id(),
            res.1@.state() is ReadLocking,
            res.1@.path() =~= m@.path().push(self.nid()),
    {
        let tracked mut m = m.get();
        let ghost path = m.path();
        let mut read_handle_opt: Option<RwReadGuard> = None;
        loop
            invariant_except_break
                read_handle_opt is None,
                self.wf(),
                m.inv(),
                m.inst_id() == self.pt_inst_id(),
                m.state() is ReadLocking,
                m.path().len() < 3,
                wf_tree_path(m.path().push(self.nid())),
                path =~= m.path(),
            ensures
                read_handle_opt is Some,
                read_handle_opt->Some_0.wf(self),
                m.inv(),
                m.inst_id() == self.pt_inst_id(),
                m.state() is ReadLocking,
                m.path() =~= path.push(self.nid()),
        {
            let val =
                atomic_with_ghost!(
                &self.rc => load();
                ghost g => {}
            );

            let tracked mut pending_reader_token: Option<RwPendingReaderToken> = Option::None;

            if val < u64::MAX {
                let result =
                    atomic_with_ghost!(
                    &self.rc => compare_exchange(val, val + 1);
                    returning res;
                    ghost g => {
                        if res is Ok {
                            pending_reader_token = Option::Some(
                                self.inst.borrow().acquire_read_start(&mut g)
                            );
                        }
                    }
                );

                match result {
                    Result::Ok(_) => {
                        let tracked mut mock_handle_opt: Option<RwMockReaderToken> = None;

                        let result =
                            atomic_with_ghost!(
                            &self.exc => load();
                            returning res;
                            ghost g => {
                                if res == false {
                                    let tracked pr_token = match pending_reader_token {
                                        Option::Some(t) => t,
                                        Option::None => proof_from_false(),
                                    };
                                    let tracked mock_handle =
                                        self.inst.borrow().acquire_read_end(&g, pr_token);
                                    pending_reader_token = None;
                                    mock_handle_opt = Some(mock_handle);
                                }
                            }
                        );

                        if result == false {
                            // The loop is unnecessary, since the property of real_rc
                            // guarantees that it will never overflow. But it's very hard
                            // to prove this in Verus. So we made this compromise.
                            loop
                                invariant_except_break
                                    mock_handle_opt is Some,
                                    mock_handle_opt->Some_0.instance_id() == self.inst_id(),
                                    read_handle_opt is None,
                                    self.wf(),
                                    m.inv(),
                                    m.inst_id() == self.pt_inst_id(),
                                    m.state() is ReadLocking,
                                    m.path().len() < 3,
                                    wf_tree_path(m.path().push(self.nid())),
                                    path =~= m.path(),
                                ensures
                                    read_handle_opt is Some,
                                    read_handle_opt->Some_0.wf(self),
                                    m.inv(),
                                    m.inst_id() == self.pt_inst_id(),
                                    m.state() is ReadLocking,
                                    m.path() =~= path.push(self.nid@),
                            {
                                let tracked mut handle_opt: Option<RwReaderToken> = None;

                                let val =
                                    atomic_with_ghost!(
                                    &self.real_rc => load();
                                    ghost g => {}
                                );

                                if val < u64::MAX {
                                    let result =
                                        atomic_with_ghost!(
                                        &self.real_rc => compare_exchange(val, val + 1);
                                        returning res;
                                        ghost g => {
                                            if res is Ok {
                                                let tracked mock_handle = mock_handle_opt.tracked_take();
                                                let tracked (_, Tracked(handle)) =
                                                    self.inst.borrow().inc_real_rc(&mut g.0, mock_handle);
                                                let tracked (node_token, _, _) =
                                                    self.inst.borrow().read_guard(
                                                        handle.element(), &handle,
                                                    );
                                                let tracked res = self.pt_inst.borrow().read_lock(
                                                    m.cpu, self.nid@, &node_token, g.1, m.token,
                                                );
                                                handle_opt = Option::Some(handle);
                                                g.1 = res.0.get();
                                                m.token = res.1.get();
                                            }
                                        }
                                    );

                                    match result {
                                        Result::Ok(_) => {
                                            let tracked handle = match handle_opt {
                                                Option::Some(t) => t,
                                                Option::None => proof_from_false(),
                                            };
                                            read_handle_opt =
                                            Some(RwReadGuard { handle: Tracked(handle) });
                                            break ;
                                        },
                                        _ => {},
                                    }
                                }
                            }

                            break ;
                        } else {
                            let _ =
                                atomic_with_ghost!(
                                &self.rc => fetch_sub(1);
                                ghost g => {
                                    let tracked pr_token = match pending_reader_token {
                                        Option::Some(t) => t,
                                        Option::None => proof_from_false(),
                                    };
                                    self.inst.borrow().acquire_read_abandon(&mut g, pr_token);
                                }
                            );
                        }
                    },
                    _ => {},
                }
            }
        }

        assert(read_handle_opt is Some);
        let read_handle = read_handle_opt.unwrap();
        (read_handle, Tracked(m))
    }

    pub fn unlock_read(&self, guard: RwReadGuard, m: Tracked<LockProtocolModel>) -> (res: Tracked<
        LockProtocolModel,
    >)
        requires
            self.wf(),
            guard.wf(self),
            m@.inv(),
            m@.inst_id() == self.pt_inst_id(),
            m@.state() is ReadLocking,
            m@.path().len() > 0 && m@.path().last() == self.nid(),
        ensures
            res@.inv(),
            res@.inst_id() == self.pt_inst_id(),
            res@.state() is ReadLocking,
            res@.path() =~= m@.path().drop_last(),
    {
        let tracked mut m = m.get();
        let RwReadGuard { handle: Tracked(handle) } = guard;
        let tracked mut mock_handle_opt: Option<RwMockReaderToken> = Option::None;

        let _ =
            atomic_with_ghost!(
            &self.real_rc => fetch_sub(1);
            ghost g => {
                let tracked mock_handle =
                    self.inst.borrow().dec_real_rc(handle.element(), &mut g.0, handle);
                mock_handle_opt = Option::Some(mock_handle);

                let tracked res = self.pt_inst.borrow().read_unlock(
                    m.cpu, self.nid@, g.1, m.token,
                );
                let tracked (Tracked(rc_token), Tracked(cursor_token)) = res;
                g.1 = rc_token;
                m.token = cursor_token;
            }
        );

        let tracked mock_handle = match mock_handle_opt {
            Option::Some(t) => t,
            Option::None => proof_from_false(),
        };
        let _ =
            atomic_with_ghost!(
            &self.rc => fetch_sub(1);
            ghost g => {
                self.inst.borrow().release_shared(&mut g, mock_handle);
            }
        );

        Tracked(m)
    }

    #[verifier::external_body]
    #[verifier::exec_allows_no_decreases_clause]
    pub fn in_protocol_lock_write(&self, m: Tracked<&LockProtocolModel>) -> (res: RwWriteGuard)
        requires
            self.wf(),
            m@.inv(),
            m@.inst_id() == self.pt_inst_id(),
            m@.state() is WriteLocked,
            m@.node_is_locked(NodeHelper::get_parent(self.nid@)),
        ensures
            res.wf(self),
            res.in_protocol@ == true,
    {
        let mut done = false;
        let tracked mut pending_writer_token: Option<RwPendingWriterToken> = Option::None;
        while !done
            invariant
                done ==> {
                    &&& pending_writer_token.is_some()
                    &&& pending_writer_token->0.instance_id() == self.inst@.id()
                },
                self.wf(),
        {
            let result =
                atomic_with_ghost!(
                &self.exc => compare_exchange(false, true);
                returning res;
                ghost g => {
                    if res is Ok {
                        pending_writer_token = Option::Some(self.inst.borrow().acquire_exc_start(&mut g));
                    }
                }
            );

            done =
            match result {
                Result::Ok(_) => true,
                _ => false,
            };
        }

        let tracked mut m = m.get();
        let mut write_handle_opt: Option<RwWriteGuard> = None;
        loop
            invariant_except_break
                pending_writer_token is Some,
                pending_writer_token->0.instance_id() == self.inst@.id(),
                self.wf(),
                m.inv(),
                m.inst_id() == self.pt_inst_id(),
                m.state() is WriteLocked,
                m.node_is_locked(NodeHelper::get_parent(self.nid@)),
            ensures
                write_handle_opt is Some,
                write_handle_opt->Some_0.wf(self),
                write_handle_opt->Some_0.in_protocol@ == true,
        {
            let tracked mut handle_opt: Option<RwWriterToken> = None;
            let tracked mut node_token_opt: Option<NodeToken> = None;
            let tracked mut pte_array_token_opt: Option<PteArrayToken> = None;
            let tracked mut perms_opt: Option<PageTableEntryPerms> = None;

            let result =
                atomic_with_ghost!(
                &self.rc => load();
                returning res;
                ghost g => {
                    if res == 0 {
                        let tracked pw_token = match pending_writer_token {
                            Option::Some(t) => t,
                            Option::None => proof_from_false(),
                        };
                        let tracked res = self.inst.borrow().acquire_exc_end(&g, pw_token);
                        let tracked pair = res.1.get();
                        let tracked exc_handle = res.2.get();
                        pending_writer_token = None;
                        handle_opt = Some(exc_handle);
                        node_token_opt = Some(pair.0);
                        pte_array_token_opt = Some(pair.1);
                        perms_opt = Some(pair.2);
                    }
                }
            );

            if result == 0 {
                let tracked handle = match handle_opt {
                    Option::Some(t) => t,
                    Option::None => proof_from_false(),
                };
                let tracked mut node_token = match node_token_opt {
                    Option::Some(t) => t,
                    Option::None => proof_from_false(),
                };
                let tracked pte_array_token = match pte_array_token_opt {
                    Option::Some(t) => t,
                    Option::None => proof_from_false(),
                };
                let tracked perms = match perms_opt {
                    Option::Some(t) => t,
                    Option::None => proof_from_false(),
                };

                proof {
                    node_token =
                    self.pt_inst.borrow().in_protocol_write_lock(
                        m.cpu,
                        self.nid(),
                        node_token,
                        &m.token,
                    );
                }

                let write_handle = RwWriteGuard {
                    handle: Tracked(handle),
                    node_token: Tracked(node_token),
                    pte_array_token: Tracked(pte_array_token),
                    perms: Tracked(perms),
                    in_protocol: Ghost(true),
                };
                write_handle_opt = Some(write_handle);
                break ;
            }
        }

        assert(write_handle_opt is Some);
        let write_handle = write_handle_opt.unwrap();
        write_handle
    }

    #[verifier::external_body]
    pub fn in_protocol_unlock_write(&self, guard: RwWriteGuard, m: Tracked<&LockProtocolModel>)
        requires
            self.wf(),
            guard.wf(self),
            guard.in_protocol@ == true,
            m@.inv(),
            m@.inst_id() == self.pt_inst_id(),
            m@.state() is WriteLocked,
            m@.node_is_locked(NodeHelper::get_parent(self.nid@)),
    {
        let tracked m = m.get();
        let tracked handle = guard.handle.get();
        let tracked mut node_token = guard.node_token.get();
        let tracked pte_array_token = guard.pte_array_token.get();
        let tracked perms = guard.perms.get();
        proof {
            node_token =
            self.pt_inst.borrow().in_protocol_write_unlock(m.cpu, self.nid@, node_token, &m.token);
        }

        let tracked pair = (node_token, pte_array_token, perms);
        atomic_with_ghost!(
            &self.exc => store(false);
            ghost g => {
                self.inst.borrow().release_exc(pair, &mut g, pair, handle);
            }
        );
    }
}

} // verus!
