// Copied from vstd

use core::marker::PhantomData;
use state_machines_macros::tokenized_state_machine;
use vstd::prelude::*;
use vstd::atomic_ghost::*;
use vstd::cell::{CellId, PCell, PointsTo};
use vstd::invariant::InvariantPredicate;
use vstd::multiset::*;
use vstd::set::*;
use vstd::rwlock::RwLockPredicate;

use crate::spec::{common::*, utils::*, tree::*};
use super::super::{common::*, utils::*, types::*, cpu::*};

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
                assert(pre.storage.is_Some());
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
        self.mock_reader.count(()) > 0 ==> self.storage.is_Some()
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
    fn dec_real_rc_inductive(pre: Self, post: Self, x: V) {
        broadcast use group_multiset_axioms;
        assert(equal(pre.storage, Option::Some(x)));
    }

    #[inductive(release_shared)]
    fn release_shared_inductive(pre: Self, post: Self) {
        broadcast use group_multiset_axioms;
        assert(pre.storage.is_Some());
    }
}

}

verus! {

ghost struct RwInternalPred;

impl InvariantPredicate<(InstanceId, NodeId), NodeToken> for RwInternalPred {
    open spec fn inv(k: (InstanceId, NodeId), v: NodeToken) -> bool {
        &&& v.instance_id() == k.0
        &&& NodeHelper::valid_nid(k.1)
        &&& v.key() == k.1
        &&& v.value() is WriteUnLocked
    }
}

type RwInstance = 
    RwLockToks::Instance<(InstanceId, NodeId), NodeToken, RwInternalPred>;
type RwExcToken = 
    RwLockToks::flag_exc<(InstanceId, NodeId), NodeToken, RwInternalPred>;
type RwRcToken = 
    RwLockToks::flag_rc<(InstanceId, NodeId), NodeToken, RwInternalPred>;
type RwRealRcToken =
    RwLockToks::flag_real_rc<(InstanceId, NodeId), NodeToken, RwInternalPred>;
type RwWriterToken = 
    RwLockToks::writer<(InstanceId, NodeId), NodeToken, RwInternalPred>;
type RwMockReaderToken =
    RwLockToks::mock_reader<(InstanceId, NodeId), NodeToken, RwInternalPred>;
type RwReaderToken =
    RwLockToks::reader<(InstanceId, NodeId), NodeToken, RwInternalPred>;
type RwPendingWriterToken = 
    RwLockToks::pending_writer<(InstanceId, NodeId), NodeToken, RwInternalPred>;
type RwPendingReaderToken =
    RwLockToks::pending_reader<(InstanceId, NodeId), NodeToken, RwInternalPred>;

struct_with_invariants! {
    // Here all types are determined.
    pub struct PageTablePageRwLock {
        exc: AtomicBool<_, RwExcToken, _>,
        rc: AtomicU64<_, RwRcToken, _>,
        real_rc: AtomicU64<_, (RwRealRcToken, RcToken), _>,
        inst: Tracked<RwInstance>,
        pt_inst: Tracked<SpecInstance>,
        nid: Ghost<NodeId>,
    }

    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        predicate {
            &&& self.inst@.k() == (self.pt_inst@.id(), self.nid@)
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

/// Handle obtained for an exclusive write-lock from an [`RwLock`].
///
/// Note that this handle does not contain a reference to the lock-protected object;
/// ownership of the object is obtained separately from [`RwLock::acquire_write`].
/// This may be changed in the future.
///
/// **Warning:** The lock is _NOT_ released automatically when the handle
/// is dropped. You must call [`release_write`](WriteHandle::release_write).
/// Verus does not check that lock is released.
pub struct WriteHandle<'a> {
    handle: Tracked<RwWriterToken>,
    token: Tracked<NodeToken>,
    rwlock: &'a PageTablePageRwLock,
}

/// Handle obtained for a shared read-lock from an [`RwLock`].
///
/// **Warning:** The lock is _NOT_ released automatically when the handle
/// is dropped. You must call [`release_read`](ReadHandle::release_read).
/// Verus does not check that lock is released.
pub struct ReadHandle<'a> {
    handle: Tracked<RwReaderToken>,
    rwlock: &'a PageTablePageRwLock,
}

impl<'a> WriteHandle<'a> {
    #[verifier::type_invariant]
    spec fn wf_write_handle(self) -> bool {
        &&& self.handle@.instance_id() == self.rwlock.inst@.id()
        &&& self.token@.instance_id() == self.rwlock.pt_inst@.id()
        &&& self.token@.key() == self.rwlock.nid@
        &&& self.token@.value() is WriteLocked
        &&& self.rwlock.wf()
    }

    pub closed spec fn rwlock(self) -> PageTablePageRwLock {
        *self.rwlock
    }

    pub closed spec fn pt_inst_id(self) -> InstanceId {
        self.rwlock.pt_inst@.id()
    }

    pub closed spec fn nid(self) -> NodeId {
        self.rwlock.nid@
    }

    pub closed spec fn token(&self) -> NodeToken {
        self.token@
    }

    pub fn release_write(
        self,
        m: Tracked<LockProtocolModel>,
    ) -> (res: Tracked<LockProtocolModel>)
        requires
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
        proof {
            use_type_invariant(&self);
        }

        let tracked mut m = m.get();
        let WriteHandle { 
            handle: Tracked(handle), 
            token: Tracked(mut token), 
            rwlock 
        } = self;

        proof {
            let tracked res = self.rwlock.pt_inst.borrow().write_unlock(
                m.cpu, self.rwlock().nid@, token, m.token,
            );
            let tracked (Tracked(node_token), Tracked(cursor_token)) = res;
            token = node_token;
            m.token = cursor_token;
        }

        atomic_with_ghost!(
            &rwlock.exc => store(false);
            ghost g => {
                self.rwlock.inst.borrow().release_exc(token, &mut g, token, handle);
            }
        );

        Tracked(m)
    }
}

impl<'a> ReadHandle<'a> {
    #[verifier::type_invariant]
    spec fn wf_read_handle(self) -> bool {
        &&& self.handle@.instance_id() == self.rwlock.inst@.id()
        &&& self.handle@.element().instance_id() == self.rwlock.pt_inst@.id()
        &&& self.handle@.element().key() == self.rwlock.nid@
        &&& self.handle@.element().value() is WriteUnLocked
        &&& self.rwlock.wf()
    }

    pub closed spec fn view(self) -> NodeToken {
        self.handle@.element()
    }

    pub closed spec fn rwlock(self) -> PageTablePageRwLock {
        *self.rwlock
    }

    pub closed spec fn pt_inst_id(self) -> InstanceId {
        self.rwlock.pt_inst@.id()
    }

    pub closed spec fn nid(self) -> NodeId {
        self.rwlock.nid@
    }

    // /// Obtain a shared reference to the object contained in the lock.
    // pub fn borrow<'b>(&'b self) -> (val: &'b Tracked<NodeToken>)
    //     ensures
    //         val == self.view(),
    // {
    //     proof {
    //         use_type_invariant(self);
    //     }
    //     let tracked token = self.rwlock.inst.borrow().read_guard(
    //         self.handle@.element(),
    //         self.handle.borrow(),
    //     );
    //     Tracked(token)
    // }

    pub proof fn lemma_readers_match(
        tracked read_handle1: &ReadHandle,
        tracked read_handle2: &ReadHandle,
    )
        requires
            read_handle1.rwlock() == read_handle2.rwlock(),
        ensures
            (equal(read_handle1.view(), read_handle2.view())),
    {
        use_type_invariant(read_handle1);
        use_type_invariant(read_handle2);
        read_handle1.rwlock.inst.borrow().read_match(
            read_handle1.handle@.element(),
            read_handle2.handle@.element(),
            &read_handle1.handle.borrow(),
            &read_handle2.handle.borrow(),
        );
    }

    pub fn release_read(
        self,
        m: Tracked<LockProtocolModel>,
    ) -> (res: Tracked<LockProtocolModel>)
        requires
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
        proof {
            use_type_invariant(&self);
        }

        let tracked mut m = m.get();
        let ReadHandle { handle: Tracked(handle), rwlock } = self;
        let tracked mut mock_handle_opt: Option<RwMockReaderToken> = Option::None;

        let _ = atomic_with_ghost!(
            &rwlock.real_rc => fetch_sub(1);
            ghost g => {
                let tracked mock_handle = 
                    rwlock.inst.borrow().dec_real_rc(handle.element(), &mut g.0, handle);
                mock_handle_opt = Option::Some(mock_handle);

                let tracked res = rwlock.pt_inst.borrow().read_unlock(
                    m.cpu, rwlock.nid@, g.1, m.token,
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
        let _ = atomic_with_ghost!(
            &rwlock.rc => fetch_sub(1);
            ghost g => {
                rwlock.inst.borrow().release_shared(&mut g, mock_handle);
            }
        );

        Tracked(m)
    }
}

impl PageTablePageRwLock {
    pub open spec fn inner_inv(&self, token: NodeToken) -> bool {
        token.value() is WriteUnLocked
    }

    pub closed spec fn inst_id(&self) -> InstanceId {
        self.inst@.id()
    }

    pub closed spec fn pt_inst_id(&self) -> InstanceId {
        self.pt_inst@.id()
    }

    pub closed spec fn nid(&self) -> NodeId {
        self.nid@
    }

    // pub fn new(val: V, Ghost(pred): Ghost<Pred>) -> (s: Self)
    //     requires
    //         pred.inv(val),
    //     ensures
    //         s.pred() == pred,
    // {
    //     let (cell, Tracked(perm)) = PCell::<V>::new(val);

    //     let tracked (Tracked(inst), Tracked(flag_exc), Tracked(flag_rc), _, _, _, _) =
    //         RwLockToks::Instance::<
    //         (Pred, CellId),
    //         PointsTo<V>,
    //         InternalPred<V, Pred>,
    //     >::initialize_full((pred, cell.id()), perm, Option::Some(perm));
    //     let inst = Tracked(inst);

    //     let exc = AtomicBool::new(Ghost(inst), false, Tracked(flag_exc));
    //     let rc = AtomicUsize::new(Ghost(inst), 0, Tracked(flag_rc));

    //     RwLock { cell, exc, rc, inst, pred: Ghost(pred) }
    // }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn acquire_write(
        &self, 
        m: Tracked<LockProtocolModel>
    ) -> (res: (WriteHandle, Tracked<LockProtocolModel>))
        requires
            m@.inv(),
            m@.inst_id() == self.pt_inst_id(),
            m@.state() is ReadLocking,
            wf_tree_path(m@.path().push(self.nid())),
        ensures
            res.0.rwlock() == *self,
            res.1@.inv(),
            res.1@.inst_id() == self.pt_inst_id(),
            res.1@.state() is WriteLocked,
            res.1@.path() =~= m@.path().push(self.nid()),
    {
        proof {
            use_type_invariant(self);
        }
        
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
            let result = atomic_with_ghost!(
                &self.exc => compare_exchange(false, true);
                returning res;
                ghost g => {
                    if res is Ok {
                        pending_writer_token = Option::Some(self.inst.borrow().acquire_exc_start(&mut g));
                    }
                }
            );

            done = match result {
                Result::Ok(_) => true,
                _ => false,
            };
        }

        let tracked mut m = m.get();
        let ghost path = m.path();
        let mut write_handle_opt: Option<WriteHandle> = None;
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
                write_handle_opt.is_Some(),
                write_handle_opt->Some_0.rwlock() == *self,
                m.inv(),
                m.inst_id() == self.pt_inst_id(),
                m.state() is WriteLocked,
                m.path() =~= path.push(self.nid()),
        {
            let tracked mut token_opt: Option<NodeToken> = None;
            let tracked mut handle_opt: Option<RwWriterToken> = None;

            let result = atomic_with_ghost!(
                &self.rc => load();
                returning res;
                ghost g => {
                    if res == 0 {
                        let tracked pw_token = match pending_writer_token { 
                            Option::Some(t) => t,
                            Option::None => proof_from_false(),
                        };
                        let tracked res = self.inst.borrow().acquire_exc_end(&g, pw_token);
                        let tracked (_, Tracked(node_token), Tracked(exc_handle)) = res;
                        pending_writer_token = None;
                        token_opt = Some(node_token);
                        handle_opt = Some(exc_handle);
                    }
                }
            );

            if result == 0 {
                let tracked mut token = match token_opt {
                    Option::Some(t) => t,
                    Option::None => proof_from_false(),
                };
                let tracked handle = match handle_opt {
                    Option::Some(t) => t,
                    Option::None => proof_from_false(),
                };

                let _ = atomic_with_ghost!(
                    &self.real_rc => no_op();
                    ghost g => {
                        self.inst.borrow().write_locked_implies_real_rc_is_zero(&g.0, &handle);
                        assert(g.1.value() == 0);
                        let tracked res = self.pt_inst.borrow().write_lock(
                            m.cpu, self.nid(), token, &g.1, m.token,
                        );
                        let tracked (Tracked(node_token), Tracked(cursor_token)) = res;
                        assert(cursor_token.value() is WriteLocked);
                        assert(cursor_token.value()->WriteLocked_0 == m.path().push(self.nid()));
                        token = node_token;
                        m.token = cursor_token;
                        assert(m.path() == path.push(self.nid()));
                    }
                );

                let write_handle = WriteHandle {
                    handle: Tracked(handle),
                    token: Tracked(token),
                    rwlock: self,
                };
                write_handle_opt = Some(write_handle);
                break;
            }
        }

        assert(write_handle_opt.is_Some());
        let write_handle = write_handle_opt.unwrap();
        (write_handle, Tracked(m))
    }

    /// Acquires a shared read-lock. To release it, use [`ReadHandle::release_read`].
    ///
    /// **Warning:** The lock is _NOT_ released automatically when the handle
    /// is dropped. You must call [`ReadHandle::release_read`].
    /// Verus does not check that lock is released.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn acquire_read(
        &self,
        m: Tracked<LockProtocolModel>,
    ) -> (res: (ReadHandle, Tracked<LockProtocolModel>))
        requires
            m@.inv(),
            m@.inst_id() == self.pt_inst_id(),
            m@.state() is ReadLocking,
            m@.path().len() < 3,
            wf_tree_path(m@.path().push(self.nid())),
        ensures
            res.0.rwlock() == *self,
            self.inner_inv(res.0.view()),
            res.1@.inv(),
            res.1@.inst_id() == self.pt_inst_id(),
            res.1@.state() is ReadLocking,
            res.1@.path() =~= m@.path().push(self.nid()),
    {
        proof {
            use_type_invariant(self);
        }

        let tracked mut m = m.get();
        let ghost path = m.path();
        let mut read_handle_opt: Option<ReadHandle> = None;
        loop
            invariant_except_break
                self.wf(),
                m.inv(),
                m.inst_id() == self.pt_inst_id(),
                m.state() is ReadLocking,
                m.path().len() < 3,
                wf_tree_path(m.path().push(self.nid())),
                path =~= m.path(),
            ensures
                read_handle_opt.is_Some(),
                read_handle_opt->Some_0.rwlock() == *self,
                self.inner_inv(read_handle_opt->Some_0.view()),
                m.inv(),
                m.inst_id() == self.pt_inst_id(),
                m.state() is ReadLocking,
                m.path() =~= path.push(self.nid()),
        {
            let val = atomic_with_ghost!(
                &self.rc => load(); 
                ghost g => {}
            );

            let tracked mut pending_reader_token: Option<RwPendingReaderToken> = Option::None;

            if val < u64::MAX {
                let result = atomic_with_ghost!(
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

                        let result = atomic_with_ghost!(
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
                            let tracked mut handle_opt: Option<RwReaderToken> = None;

                            // The loop is unnecessary, since the property of real_rc 
                            // guarantees that it will never overflow. But it's very hard 
                            // to prove this in Verus. So we made this compromise.
                            loop
                                invariant_except_break
                                    self.wf(),
                                    m.inv(),
                                    m.inst_id() == self.pt_inst_id(),
                                    m.state() is ReadLocking,
                                    m.path().len() < 3,
                                    wf_tree_path(m.path().push(self.nid())),
                                    path =~= m.path(),
                                    mock_handle_opt.is_Some(),
                                    mock_handle_opt->Some_0.instance_id() == self.inst_id(),
                                ensures
                                    self.inner_inv(handle_opt->Some_0.element()),
                                    m.inv(),
                                    m.inst_id() == self.pt_inst_id(),
                                    m.state() is ReadLocking,
                                    m.path() =~= path.push(self.nid()),
                                    handle_opt.is_Some(),
                                    handle_opt->Some_0.instance_id() == self.inst_id(),
                                    handle_opt->Some_0.element().instance_id() == self.pt_inst_id(),
                                    handle_opt->Some_0.element().key() == self.nid(),
                            {
                                let val = atomic_with_ghost!(
                                    &self.real_rc => load(); 
                                    ghost g => {}
                                );

                                if val < u64::MAX {
                                    let result = atomic_with_ghost!(
                                        &self.real_rc => compare_exchange(val, val + 1);
                                        returning res;
                                        ghost g => {
                                            if res is Ok {
                                                let tracked mock_handle = mock_handle_opt.tracked_take();
                                                let tracked (_, Tracked(handle)) = 
                                                    self.inst.borrow().inc_real_rc(&mut g.0, mock_handle);
                                                let tracked node_token = 
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
                                        Result::Ok(_) => { break; },
                                        _ => {},
                                    }
                                }
                            }

                            let tracked handle = match handle_opt {
                                Option::Some(t) => t,
                                Option::None => proof_from_false(),
                            };
                            let read_handle = ReadHandle { 
                                handle: Tracked(handle), 
                                rwlock: self,
                            };
                            read_handle_opt = Some(read_handle);
                            break;
                        } else {
                            let _ = atomic_with_ghost!(
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

        assert(read_handle_opt.is_Some());
        let read_handle = read_handle_opt.unwrap();
        (read_handle, Tracked(m))
    }
}

} // verus!