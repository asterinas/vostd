// SPDX-License-Identifier: MPL-2.0
use vstd::atomic_ghost::*;
use vstd::cell::{self, pcell::*};
use vstd::pcm::Loc;
use vstd::prelude::*;
use vstd::tokens::frac::{Frac, FracGhost};
use vstd_extra::prelude::*;
use vstd_extra::resource::*;

use alloc::sync::Arc;
use core::char::MAX;
use core::{
    cell::UnsafeCell,
    fmt,
    marker::PhantomData,
    ops::{Deref, DerefMut},
    sync::atomic::{
        // AtomicUsize,
        Ordering::{AcqRel, Acquire, Relaxed, Release},
    },
};

use super::{
    guard::{/*GuardTransfer,*/ SpinGuardian},
    //PreemptDisabled,
};
//use crate::task::atomic_mode::AsAtomicModeGuard;

verus! {

broadcast use group_deref_spec;

type RwFrac<T> = Frac<PointsTo<T>, V_MAX_PERM_FRACS>;

spec const V_MAX_PERM_FRACS_SPEC: u64 = (MAX_READER + 1) as u64;

#[verifier::when_used_as_spec(V_MAX_PERM_FRACS_SPEC)]
exec const V_MAX_PERM_FRACS: u64 
ensures
    V_MAX_PERM_FRACS == V_MAX_PERM_FRACS_SPEC,
    V_MAX_PERM_FRACS == MAX_READER + 1,
    V_MAX_PERM_FRACS < u64::MAX,
{ 
    assert(MAX_READER + 1 < u64::MAX) by (compute_only);
    (MAX_READER + 1) as u64
}

tracked struct RwPerms<T> {
    cell_perm: Option<RwFrac<T>>,
    upgrade_retract_token: FracGhost<()>,
    read_retract_token: FracGhost<(),V_MAX_PERM_FRACS>,
}

ghost struct RwId {
    upgrade_retract_token_id: Loc,
    read_retract_token_id: Loc,
}

/// The number of concurrent readers will not exceed `2*MAX_READER` is necessary to ensure the correctness of the implementation.
/// **NOTE**: We *ASSUME* this property always holds without proving it. The implementation will not work correctly because of overflow caused by 
/// more than `2*MAX_READER` concurrent `RwLock::try_read` operations, but it will never happen in the real world 
/// because it will require more than `2^61` threads.
pub closed spec fn no_max_reader_overflow(v: usize) -> bool {
    let has_max_reader: bool = (v & MAX_READER) != 0usize;
    let reader_count: usize = v & READER_MASK;
    if has_max_reader {
        reader_count + READER <= MAX_READER
    } else {
        true
    }
}

struct_with_invariants! {
/// Spin-based Read-write Lock
///
/// # Overview
///
/// This lock allows for multiple readers, or at most one writer to access
/// at any point in time. The writer of this lock has exclusive access to
/// modify the underlying data, while the readers are allowed shared and
/// read-only access.
///
/// The writing and reading portions cannot be active simultaneously, when
/// one portion is in progress, the other portion will spin-wait. This is
/// suitable for scenarios where the lock is expected to be held for short
/// periods of time, and the overhead of context switching is higher than
/// the cost of spinning.
///
/// In addition to traditional read and write locks, this implementation
/// provides the upgradeable read lock (`upread lock`). The `upread lock`
/// can be upgraded to write locks atomically, useful in scenarios
/// where a decision to write is made after reading.
///
/// The type parameter `T` represents the data that this lock is protecting.
/// It is necessary for `T` to satisfy [`Send`] to be shared across tasks and
/// [`Sync`] to permit concurrent access via readers. The [`Deref`] method (and
/// [`DerefMut`] for the writer) is implemented for the RAII guards returned
/// by the locking methods, which allows for the access to the protected data
/// while the lock is held.
///
/// # Usage
/// The lock can be used in scenarios where data needs to be read frequently
/// but written to occasionally.
///
/// Use `upread lock` in scenarios where related checking is performed before
/// modification to effectively avoid deadlocks and improve efficiency.
///
/// This lock should not be used in scenarios where lock-holding times are
/// long as it can lead to CPU resource wastage due to spinning.
///
/// # About Guard
///
/// See the comments of [`SpinLock`].
///
/// # Examples
///
/// ```
/// use ostd::sync::RwLock;
///
/// let lock = RwLock::new(5)
///
/// // many read locks can be held at once
/// {
///     let r1 = lock.read();
///     let r2 = lock.read();
///     assert_eq!(*r1, 5);
///     assert_eq!(*r2, 5);
///
///     // Upgradeable read lock can share access to data with read locks
///     let r3 = lock.upread();
///     assert_eq!(*r3, 5);
///     drop(r1);
///     drop(r2);
///     // read locks are dropped at this point
///
///     // An upread lock can only be upgraded successfully after all the
///     // read locks are released, otherwise it will spin-wait.
///     let mut w1 = r3.upgrade();
///     *w1 += 1;
///     assert_eq!(*w1, 6);
/// }   // upread lock are dropped at this point
///
/// {
///     // Only one write lock can be held at a time
///     let mut w2 = lock.write();
///     *w2 += 1;
///     assert_eq!(*w2, 7);
/// }   // write lock is dropped at this point
/// ```
///
/// [`SpinLock`]: super::SpinLock
pub struct RwLock<T  /* : ?Sized*/ , Guard  /* = PreemptDisabled*/ > {
    guard: PhantomData<Guard>,
    /// The internal representation of the lock state is as follows:
    /// - **Bit 63:** Writer lock.
    /// - **Bit 62:** Upgradeable reader lock.
    /// - **Bit 61:** Indicates if an upgradeable reader is being upgraded.
    /// - **Bits 60-0:** Reader lock count.
    lock: AtomicUsize<_, RwPerms<T>,_>,
    // val: UnsafeCell<T>,
    val: PCell<T>,
    v_id: Ghost<RwId>,
}

/// This invariant holds at any time, i.e. not violated during any method execution.
closed spec fn wf(self) -> bool {
    invariant on lock with (val, guard, v_id) is (v:usize, g: RwPerms<T>) {
        let has_writer: bool = (v & WRITER) != 0usize;
        let has_upgrade: bool = (v & UPGRADEABLE_READER) != 0usize;
        let has_max_reader: bool = (v & MAX_READER) != 0usize;
        // The value of the reader count bits.
        // NOTE: This does not mean there are actually `v & READER_MASK` `RwLockReadGuard`s, some of them may be in the middle of being created.
        // Even if `MAX_READER` is set, it is not necessary to have `MAX_READER - 1` `RwLockReadGuard`s.
        let reader_count: usize = v & READER_MASK;
        // The value of the upgradeable reader bit.
        // NOTE: This does not mean there is actually an `RwLockUpgradeableGuard`, it may be in the middle of creating one.
        let upgrade_reader_count: int = if has_upgrade && !has_writer { 1int } else { 0int };
        // The total number of readers, considering normal `RwLockReadGuard`s and the `RwLockUpgradeableGuard`. 
        // NOTE: This does not mean there are actually `total_readers` guards, it is an upper bound.
        let total_readers: int = reader_count + upgrade_reader_count;
        // The total number of reader creation attempts, including created `RwLockReadGuard`s and those who are trying.
        let total_reader_attempts: int = reader_count + if has_max_reader { MAX_READER } else { 0 };
        // The remaining permissions in the `RwLock` to create new read guards, it serves as an upper bound of the number of new `RwLockReadGuard` and `RwLockUpgradeableGuard` that can be successfully created.
        let remaining_pcell_perms: int = if g.cell_perm is Some { g.cell_perm->Some_0.frac() } else { 0 };
        // Invariant: The sum of all reader attempts, remaining permissions and the upgrade reader should be equal to the maximum permissions.
        &&& total_reader_attempts + g.read_retract_token.frac() + upgrade_reader_count + remaining_pcell_perms == V_MAX_PERM_FRACS + if g.cell_perm is Some {V_MAX_PERM_FRACS} else { 0 }
        // Not checked
        //&&& ((v & BEING_UPGRADED) != 0usize ==> (v & UPGRADEABLE_READER) != 0usize)
        &&& v_id@.upgrade_retract_token_id == g.upgrade_retract_token.id()
        &&& v_id@.read_retract_token_id == g.read_retract_token.id()
        &&& g.upgrade_retract_token.frac() == if has_writer && has_upgrade {
            1int
        } else {
            2int
        }
        &&& match g.cell_perm {
            None => {
                &&& has_writer
                &&& reader_count == 0
                &&& (v & BEING_UPGRADED) == 0usize
            }
            Some(perm) => {
                &&& !has_writer
                &&& perm.resource().id() == val.id()
                &&& perm.frac() >= V_MAX_PERM_FRACS - total_readers
            }
        }
    }
}

}

const READER: usize = 1;

const WRITER: usize = 1 << (usize::BITS - 1);

const UPGRADEABLE_READER: usize = 1 << (usize::BITS - 2);

const BEING_UPGRADED: usize = 1 << (usize::BITS - 3);

const MAX_READER: usize = 1 << (usize::BITS - 4);

const READER_MASK: usize = (!0usize) >> 4;

impl<T, G> RwLock<T, G> {
    /// Returns the unique [`CellId`](https://verus-lang.github.io/verus/verusdoc/vstd/cell/struct.CellId.html) of the internal `PCell<T>`.
    pub closed spec fn cell_id(self) -> cell::CellId {
        self.val.id()
    }

    pub closed spec fn upgrade_retract_token_id(self) -> Loc {
        self.v_id@.upgrade_retract_token_id
    }

    /// Encapsulates the invariant described in the *Invariant* section of [`RwLock`].
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.wf()
    }
}

/*#[verus_verify]
impl<T, G> RwLock<T, G> {
    /// Creates a new spin-based read-write lock with an initial value.
    #[verus_verify]
    pub const fn new(val: T) -> Self {
        let (val, Tracked(perm)) = PCell::new(val);

        // Proof code
        let tracked frac_perm = RwFrac::<T>::new(perm);
        proof {
            lemma_consts_properties();
        }

        Self {
            guard: PhantomData,
            //lock: AtomicUsize::new(0),
            lock: AtomicUsize::new(Ghost((val, PhantomData)), 0, Tracked(Some(frac_perm))),
            val: val,
            //val: UnsafeCell::new(val),
        }
    }
}*/

} // verus!

verus!{
#[verus_verify]
impl<T /*: ?Sized*/, G: SpinGuardian> RwLock<T, G> {
    /// Acquires a read lock and spin-wait until it can be acquired.
    ///
    /// The calling thread will spin-wait until there are no writers or
    /// upgrading upreaders present. There is no guarantee for the order
    /// in which other readers or writers waiting simultaneously will
    /// obtain the lock.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn read(&self) -> RwLockReadGuard<T, G> {
        loop {
            if let Some(readguard) = self.try_read() {
                return readguard;
            } else {
                core::hint::spin_loop();
            }
        }
    }

    /// Acquires a read lock through an [`Arc`].
    ///
    /// The method is similar to [`read`], but it doesn't have the requirement
    /// for compile-time checked lifetimes of the read guard.
    ///
    /// [`read`]: Self::read
    #[verifier::exec_allows_no_decreases_clause]
    pub fn read_arc(self: &Arc<Self>) -> ArcRwLockReadGuard<T, G> {
        loop {
            if let Some(readguard) = self.try_read_arc() {
                return readguard;
            } else {
                core::hint::spin_loop();
            }
        }
    }

    /// Acquires a write lock and spin-wait until it can be acquired.
    ///
    /// The calling thread will spin-wait until there are no other writers,
    /// upreaders or readers present. There is no guarantee for the order
    /// in which other readers or writers waiting simultaneously will
    /// obtain the lock.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn write(&self) -> RwLockWriteGuard<T, G> {
        loop {
            if let Some(writeguard) = self.try_write() {
                return writeguard;
            } else {
                core::hint::spin_loop();
            }
        }
    }

    /// Acquires a write lock through an [`Arc`].
    ///
    /// The method is similar to [`write`], but it doesn't have the requirement
    /// for compile-time checked lifetimes of the lock guard.
    ///
    /// [`write`]: Self::write
    #[verifier::exec_allows_no_decreases_clause]
    pub fn write_arc(self: &Arc<Self>) -> ArcRwLockWriteGuard<T, G> {
        loop {
            if let Some(writeguard) = self.try_write_arc() {
                return writeguard;
            } else {
                core::hint::spin_loop();
            }
        }
    }

    /// Acquires an upreader and spin-wait until it can be acquired.
    ///
    /// The calling thread will spin-wait until there are no other writers,
    /// or upreaders. There is no guarantee for the order in which other
    /// readers or writers waiting simultaneously will obtain the lock.
    ///
    /// Upreader will not block new readers until it tries to upgrade. Upreader
    /// and reader do not differ before invoking the upgrade method. However,
    /// only one upreader can exist at any time to avoid deadlock in the
    /// upgrade method.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn upread(&self) -> RwLockUpgradeableGuard<T, G> {
        loop {
            if let Some(guard) = self.try_upread() {
                return guard;
            } else {
                core::hint::spin_loop();
            }
        }
    }

    /// Acquires an upgradeable read lock through an [`Arc`].
    ///
    /// The method is similar to [`upread`], but it doesn't have the requirement
    /// for compile-time checked lifetimes of the lock guard.
    ///
    /// [`upread`]: Self::upread
    #[verifier::exec_allows_no_decreases_clause]
    pub fn upread_arc(self: &Arc<Self>) -> ArcRwLockUpgradeableGuard<T, G> {
        loop {
            if let Some(guard) = self.try_upread_arc() {
                return guard;
            } else {
                core::hint::spin_loop();
            }
        }
    }

    /// Attempts to acquire a read lock.
    ///
    /// This function will never spin-wait and will return immediately.
    #[verifier::external_body]
    pub fn try_read(&self) -> Option<RwLockReadGuard<T, G>> {
        let guard = G::read_guard();
        // let lock = self.lock.fetch_add(READER, Acquire);
        let lock = atomic_with_ghost!(
            self.lock => fetch_add(READER);
            returning res;
            ghost g => { }
        );
        if lock & (WRITER | MAX_READER | BEING_UPGRADED) == 0 {
            Some(RwLockReadGuard {
                inner: self,
                guard,
                v_perm: Tracked::assume_new(),
            })
        } else {
            // self.lock.fetch_sub(READER, Release);
            atomic_with_ghost!(
                self.lock => fetch_sub(READER);
                ghost g => { }
            );
            None
        }
    }

    /// Attempts to acquire an read lock through an [`Arc`].
    ///
    /// The method is similar to [`try_read`], but it doesn't have the requirement
    /// for compile-time checked lifetimes of the lock guard.
    ///
    /// [`try_read`]: Self::try_read
    #[verifier::external_body]
    pub fn try_read_arc(self: &Arc<Self>) -> Option<ArcRwLockReadGuard<T, G>> {
        let guard = G::read_guard();
        // let lock = self.lock.fetch_add(READER, Acquire);
        let lock = atomic_with_ghost!(
            self.lock => fetch_add(READER);
            returning res;
            ghost g => { }
        );
        if lock & (WRITER | MAX_READER | BEING_UPGRADED) == 0 {
            Some(ArcRwLockReadGuard {
                inner: self.clone(),
                guard,
                v_perm: Tracked::assume_new(),
            })
        } else {
            // self.lock.fetch_sub(READER, Release);
            atomic_with_ghost!(
                self.lock => fetch_sub(READER);
                ghost g => { }
            );
            None
        }
    }

    /// Attempts to acquire a write lock.
    ///
    /// This function will never spin-wait and will return immediately.
    #[verus_spec]
    pub fn try_write(&self) -> Option<RwLockWriteGuard<T, G>> {
        let guard = G::guard();
        // if self
        //     .lock
        //     .compare_exchange(0, WRITER, Acquire, Relaxed)
        //     .is_ok()
        proof_decl!{
            let tracked mut perm: Option<PointsTo<T>> = None;
        }
        proof!{ 
            use_type_invariant(self);
            lemma_consts_properties();
        }
        if atomic_with_ghost!(
            self.lock => compare_exchange(0, WRITER);
            returning res;
            ghost g=> { 
                if res is Ok {
                    let tracked frac_perm = g.cell_perm.tracked_take();
                    frac_perm.bounded();
                    let tracked (full_perm, _empty) = frac_perm.take_resource();
                    perm = Some(full_perm);
                }
            }
        )
        .is_ok()
        {
            Some(RwLockWriteGuard { inner: self, guard, v_perm: Tracked(perm.tracked_unwrap()) })
        } else {
            None
        }
    }

    /// Attempts to acquire a write lock through an [`Arc`].
    ///
    /// The method is similar to [`try_write`], but it doesn't have the requirement
    /// for compile-time checked lifetimes of the lock guard.
    ///
    /// [`try_write`]: Self::try_write
    #[verus_spec]
    fn try_write_arc(self: &Arc<Self>) -> Option<ArcRwLockWriteGuard<T, G>> {
        let guard = G::guard();
        // if self
        //     .lock
        //     .compare_exchange(0, WRITER, Acquire, Relaxed)
        //     .is_ok()
        proof_decl!{
            let tracked mut perm: Option<PointsTo<T>> = None;
        }
        proof!{
            use_type_invariant(self);
            lemma_consts_properties();
        }
        if atomic_with_ghost!(
            self.lock => compare_exchange(0, WRITER);
            returning res;
            ghost g => {
                if res is Ok {
                    let tracked frac_perm = g.cell_perm.tracked_take();
                    frac_perm.bounded();
                    let tracked (full_perm, _) = frac_perm.take_resource();
                    perm = Some(full_perm);
                }
            }
        )
        .is_ok()
        {
            Some(ArcRwLockWriteGuard {
                inner: self.clone(),
                guard,
                v_perm: Tracked(perm.tracked_unwrap()),
            })
        } else {
            None
        }
    }

    /// Attempts to acquire an upread lock.
    ///
    /// This function will never spin-wait and will return immediately.
    #[verus_spec]
    pub fn try_upread(&self) -> Option<RwLockUpgradeableGuard<T, G>> {
        let guard = G::guard();
        proof_decl!{
            let tracked mut perm: Option<RwFrac<T>> = None;
            let tracked mut retract_upgrade_token: Option<FracGhost<()>> = None;
        }
        proof!{
            use_type_invariant(self);
            lemma_consts_properties();
        }
        // let lock = self.lock.fetch_or(UPGRADEABLE_READER, Acquire) & (WRITER | UPGRADEABLE_READER);
        let lock = atomic_with_ghost!(
            self.lock => fetch_or(UPGRADEABLE_READER);
            update prev -> next;
            ghost g => { 
                lemma_consts_properties_prev_next(prev, next);
                if prev & (WRITER | UPGRADEABLE_READER) == 0 {
                    if g.cell_perm is None {
                        assert (prev & (WRITER | UPGRADEABLE_READER) != 0usize) by (bit_vector)
                        requires
                            prev & WRITER != 0usize;
                        assert(false);
                    }
                    assert (prev & UPGRADEABLE_READER == 0) by (bit_vector)
                    requires
                        prev & (WRITER | UPGRADEABLE_READER) == 0;
                    let tracked mut tmp = g.cell_perm.tracked_take();                
                    let tracked frac_perm = tmp.split(1int);
                    g.cell_perm = Some(tmp);
                    perm = Some(frac_perm);
                }
                else if prev & (WRITER | UPGRADEABLE_READER) == WRITER {
                    assert (prev & UPGRADEABLE_READER == 0 && prev & WRITER == WRITER) by (bit_vector)
                    requires
                        prev & (WRITER | UPGRADEABLE_READER) == WRITER;
                    let tracked mut tmp = g.upgrade_retract_token.split(1int);
                    retract_upgrade_token = Some(tmp);
                }
                else {
                    assert (prev & UPGRADEABLE_READER != 0) by (bit_vector)
                    requires
                        !(prev & (WRITER | UPGRADEABLE_READER) == 0),
                        !(prev & (WRITER | UPGRADEABLE_READER) == WRITER);
                }
            }
        ) & (WRITER | UPGRADEABLE_READER);
        if lock == 0 {
            return Some(RwLockUpgradeableGuard { inner: self, guard, v_perm: Tracked(perm.tracked_unwrap()) });
        } else if lock == WRITER {
            // self.lock.fetch_sub(UPGRADEABLE_READER, Release);
            atomic_with_ghost!(
                self.lock => fetch_sub(UPGRADEABLE_READER);
                update prev -> next;
                ghost g => {
                    let prev_usize = prev as usize;
                    let next_usize = next as usize;
                    if (prev_usize & UPGRADEABLE_READER) == 0 {
                        assert(g.upgrade_retract_token.frac() == 2int);
                        g.upgrade_retract_token.combine(retract_upgrade_token.tracked_unwrap());
                        g.upgrade_retract_token.bounded();
                        assert(false);
                    } else {
                        assert(prev_usize >= UPGRADEABLE_READER) by (bit_vector)
                            requires (prev_usize & UPGRADEABLE_READER != 0);
                        assert(next == prev - UPGRADEABLE_READER);
                        lemma_consts_properties_prev_next(prev_usize, next_usize); 
                        let frac = g.upgrade_retract_token.frac();
                        assert(frac == 1int || frac == 2int);
                        g.upgrade_retract_token.combine(retract_upgrade_token.tracked_unwrap());
                        if frac == 2int {
                            g.upgrade_retract_token.bounded();
                            assert(false);
                        } else
                        {
                            assert(g.upgrade_retract_token.frac() == 2int);
                        }
                    }
                }
            );
        }
        None
    }

    /// Attempts to acquire an upgradeable read lock through an [`Arc`].
    ///
    /// The method is similar to [`try_upread`], but it doesn't have the requirement
    /// for compile-time checked lifetimes of the lock guard.
    ///
    /// [`try_upread`]: Self::try_upread
    #[verus_spec]
    pub fn try_upread_arc(self: &Arc<Self>) -> Option<ArcRwLockUpgradeableGuard<T, G>> {
        let guard = G::guard();
        proof_decl!{
            let tracked mut perm: Option<RwFrac<T>> = None;
            let tracked mut retract_upgrade_token: Option<FracGhost<()>> = None;
        }
        proof!{
            use_type_invariant(self);
            lemma_consts_properties();
        }
        // let lock = self.lock.fetch_or(UPGRADEABLE_READER, Acquire) & (WRITER | UPGRADEABLE_READER);
        let lock = atomic_with_ghost!(
            self.lock => fetch_or(UPGRADEABLE_READER);
            update prev -> next;
            ghost g => {
                lemma_consts_properties_prev_next(prev, next);
                if prev & (WRITER | UPGRADEABLE_READER) == 0 {
                    if g.cell_perm is None {
                        assert (prev & (WRITER | UPGRADEABLE_READER) != 0usize) by (bit_vector)
                        requires
                            prev & WRITER != 0usize;
                        assert(false);
                    }
                    assert (prev & UPGRADEABLE_READER == 0) by (bit_vector)
                    requires
                        prev & (WRITER | UPGRADEABLE_READER) == 0;
                    let tracked mut tmp = g.cell_perm.tracked_take();
                    let tracked frac_perm = tmp.split(1int);
                    g.cell_perm = Some(tmp);
                    perm = Some(frac_perm);
                }
                else if prev & (WRITER | UPGRADEABLE_READER) == WRITER {
                    assert (prev & UPGRADEABLE_READER == 0 && prev & WRITER == WRITER) by (bit_vector)
                    requires
                        prev & (WRITER | UPGRADEABLE_READER) == WRITER;
                    let tracked mut tmp = g.upgrade_retract_token.split(1int);
                    retract_upgrade_token = Some(tmp);
                }
                else {
                    assert (prev & UPGRADEABLE_READER != 0) by (bit_vector)
                    requires
                        !(prev & (WRITER | UPGRADEABLE_READER) == 0),
                        !(prev & (WRITER | UPGRADEABLE_READER) == WRITER);
                }
            }
        ) & (WRITER | UPGRADEABLE_READER);
        if lock == 0 {
            return Some(ArcRwLockUpgradeableGuard {
                inner: self.clone(),
                guard,
                v_perm: Tracked(perm.tracked_unwrap()),
            });
        } else if lock == WRITER {
            // self.lock.fetch_sub(UPGRADEABLE_READER, Release);
            atomic_with_ghost!(
                self.lock => fetch_sub(UPGRADEABLE_READER);
                update prev -> next;
                ghost g => {
                    let prev_usize = prev as usize;
                    let next_usize = next as usize;
                    if (prev_usize & UPGRADEABLE_READER) == 0 {
                        assert(g.upgrade_retract_token.frac() == 2int);
                        g.upgrade_retract_token.combine(retract_upgrade_token.tracked_unwrap());
                        g.upgrade_retract_token.bounded();
                        assert(false);
                    } else {
                        assert(prev_usize >= UPGRADEABLE_READER) by (bit_vector)
                            requires (prev_usize & UPGRADEABLE_READER != 0);
                        assert(next == prev - UPGRADEABLE_READER);
                        lemma_consts_properties_prev_next(prev_usize, next_usize);
                        let frac = g.upgrade_retract_token.frac();
                        assert(frac == 1int || frac == 2int);
                        g.upgrade_retract_token.combine(retract_upgrade_token.tracked_unwrap());
                        if frac == 2int {
                            g.upgrade_retract_token.bounded();
                            assert(false);
                        } else
                        {
                            assert(g.upgrade_retract_token.frac() == 2int);
                        }
                    }
                }
            );
        }
        None
    }
}
}

impl<T, G: SpinGuardian> RwLock<T, G> {
    /// Returns a mutable reference to the underlying data.
    ///
    /// This method is zero-cost: By holding a mutable reference to the lock, the compiler has
    /// already statically guaranteed that access to the data is exclusive.
    pub fn get_mut(&mut self) -> &mut T {
        // self.val.get_mut()
        // `PCell<T>` is implemented using an `UnsafeCell<T>` internally; we do an unchecked
        // cast here since `PCell` doesn't expose `UnsafeCell`-style accessors.
        unsafe {
            let ucell: *mut UnsafeCell<T> = (&mut self.val as *mut PCell<T>).cast();
            &mut *(*ucell).get()
        }
    }

    /// Returns a raw pointer to the underlying data.
    ///
    /// This method is safe, but it's up to the caller to ensure that access to the data behind it
    /// is still safe.
    pub(super) fn as_ptr(&self) -> *mut T {
        // self.val.get()
        unsafe {
            let ucell: *const UnsafeCell<T> = (&self.val as *const PCell<T>).cast();
            (*ucell).get()
        }
    }
}

/*
impl<T: ?Sized + fmt::Debug, G> fmt::Debug for RwLock<T, G> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.val, f)
    }
}

/// Because there can be more than one readers to get the T's immutable ref,
/// so T must be Sync to guarantee the sharing safety.
unsafe impl<T: ?Sized + Send, G> Send for RwLock<T, G> {}
unsafe impl<T: ?Sized + Send + Sync, G> Sync for RwLock<T, G> {}

impl<T: ?Sized, R: Deref<Target = RwLock<T, G>> + Clone, G: SpinGuardian> !Send
    for RwLockWriteGuard_<T, R, G>
{
}
unsafe impl<T: ?Sized + Sync, R: Deref<Target = RwLock<T, G>> + Clone + Sync, G: SpinGuardian> Sync
    for RwLockWriteGuard_<T, R, G>
{
}

impl<T: ?Sized, R: Deref<Target = RwLock<T, G>> + Clone, G: SpinGuardian> !Send
    for RwLockReadGuard_<T, R, G>
{
}
unsafe impl<T: ?Sized + Sync, R: Deref<Target = RwLock<T, G>> + Clone + Sync, G: SpinGuardian> Sync
    for RwLockReadGuard_<T, R, G>
{
}

impl<T: ?Sized, R: Deref<Target = RwLock<T, G>> + Clone, G: SpinGuardian> !Send
    for RwLockUpgradeableGuard_<T, R, G>
{
}
unsafe impl<T: ?Sized + Sync, R: Deref<Target = RwLock<T, G>> + Clone + Sync, G: SpinGuardian> Sync
    for RwLockUpgradeableGuard_<T, R, G>
{
}*/
/// A guard that provides immutable data access.
#[clippy::has_significant_drop]
#[must_use]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(G)]
#[verus_verify]
pub struct RwLockReadGuard_<
    T, /*: ?Sized*/
    R: Deref<Target = RwLock<T, G>> + Clone,
    G: SpinGuardian,
> {
    guard: G::ReadGuard,
    inner: R,
    v_perm: Tracked<RwFrac<T>>,
}

/*
impl<T: ?Sized, R: Deref<Target = RwLock<T, G>> + Clone, G: SpinGuardian> AsAtomicModeGuard
    for RwLockReadGuard_<T, R, G>
{
    fn as_atomic_mode_guard(&self) -> &dyn crate::task::atomic_mode::InAtomicMode {
        self.guard.as_atomic_mode_guard()
    }
}
*/

/// A guard that provides shared read access to the data protected by a [`RwLock`].
pub type RwLockReadGuard<'a, T, G> = RwLockReadGuard_<T, &'a RwLock<T, G>, G>;

/// A guard that provides shared read access to the data protected by a `Arc<RwLock>`.
pub type ArcRwLockReadGuard<T, G> = RwLockReadGuard_<T, Arc<RwLock<T, G>>, G>;

verus! {

impl<T, R: Deref<Target = RwLock<T, G>> + Clone, G: SpinGuardian> RwLockReadGuard_<T, R, G> {
    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        &&& self.inner.deref_spec().cell_id() == self.v_perm@.resource().id()
        &&& self.v_perm@.frac() == 1
    }
}

} // verus!
/*
impl<T: ?Sized, R: Deref<Target = RwLock<T, G>> + Clone, G: SpinGuardian> Deref
    for RwLockReadGuard_<T, R, G>
{
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { &*self.inner.val.get() }
    }
}

impl<T: ?Sized, R: Deref<Target = RwLock<T, G>> + Clone, G: SpinGuardian> Drop
    for RwLockReadGuard_<T, R, G>
{
    fn drop(&mut self) {
        self.inner.lock.fetch_sub(READER, Release);
    }
}

impl<T: ?Sized + fmt::Debug, R: Deref<Target = RwLock<T, G>> + Clone, G: SpinGuardian> fmt::Debug
    for RwLockReadGuard_<T, R, G>
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}*/
/// A guard that provides mutable data access.
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(G)]
#[verus_verify]
pub struct RwLockWriteGuard_<
    T, /*: ?Sized*/
    R: Deref<Target = RwLock<T, G>> + Clone,
    G: SpinGuardian,
> {
    guard: G::Guard,
    inner: R,
    /// Ghost permission for verification
    v_perm: Tracked<PointsTo<T>>,
}

verus!{
impl<T, R: Deref<Target = RwLock<T, G>> + Clone, G: SpinGuardian> RwLockWriteGuard_<T, R, G> {
    #[verifier::type_invariant]
    spec fn type_inv(self) -> bool {
        self.inner.deref_spec().cell_id() == self.v_perm@.id()
    }
}
}
/*
impl<T: ?Sized, R: Deref<Target = RwLock<T, G>> + Clone, G: SpinGuardian> AsAtomicModeGuard
    for RwLockWriteGuard_<T, R, G>
{
    fn as_atomic_mode_guard(&self) -> &dyn crate::task::atomic_mode::InAtomicMode {
        self.guard.as_atomic_mode_guard()
    }
}*/

/// A guard that provides exclusive write access to the data protected by a [`RwLock`].
pub type RwLockWriteGuard<'a, T, G> = RwLockWriteGuard_<T, &'a RwLock<T, G>, G>;
/// A guard that provides exclusive write access to the data protected by a `Arc<RwLock>`.
pub type ArcRwLockWriteGuard<T, G> = RwLockWriteGuard_<T, Arc<RwLock<T, G>>, G>;

/*
impl<T: ?Sized, R: Deref<Target = RwLock<T, G>> + Clone, G: SpinGuardian> Deref
    for RwLockWriteGuard_<T, R, G>
{
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { &*self.inner.val.get() }
    }
}

/*
impl<T: ?Sized, R: Deref<Target = RwLock<T, G>> + Clone, G: SpinGuardian>
    RwLockWriteGuard_<T, R, G>
{
    /// Atomically downgrades a write guard to an upgradeable reader guard.
    ///
    /// This method always succeeds because the lock is exclusively held by the writer.
    pub fn downgrade(mut self) -> RwLockUpgradeableGuard_<T, R, G> {
        loop {
            self = match self.try_downgrade() {
                Ok(guard) => return guard,
                Err(e) => e,
            };
        }
    }

    /// This is not exposed as a public method to prevent intermediate lock states from affecting the
    /// downgrade process.
    fn try_downgrade(mut self) -> Result<RwLockUpgradeableGuard_<T, R, G>, Self> {
        let inner = self.inner.clone();
        let res = self
            .inner
            .lock
            .compare_exchange(WRITER, UPGRADEABLE_READER, AcqRel, Relaxed);
        if res.is_ok() {
            let guard = self.guard.transfer_to();
            drop(self);
            Ok(RwLockUpgradeableGuard_ { inner, guard })
        } else {
            Err(self)
        }
    }
}

impl<T: ?Sized, R: Deref<Target = RwLock<T, G>> + Clone, G: SpinGuardian> DerefMut
    for RwLockWriteGuard_<T, R, G>
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.inner.val.get() }
    }
}

impl<T: ?Sized, R: Deref<Target = RwLock<T, G>> + Clone, G: SpinGuardian> Drop
    for RwLockWriteGuard_<T, R, G>
{
    fn drop(&mut self) {
        self.inner.lock.fetch_and(!WRITER, Release);
    }

impl<T: ?Sized + fmt::Debug, R: Deref<Target = RwLock<T, G>> + Clone, G: SpinGuardian> fmt::Debug
    for RwLockWriteGuard_<T, R, G>
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}
*/
*/
/// A guard that provides immutable data access but can be atomically
/// upgraded to `RwLockWriteGuard`.
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(G)]
#[verus_verify]
pub struct RwLockUpgradeableGuard_<
    T, /*: ?Sized*/
    R: Deref<Target = RwLock<T, G>> + Clone,
    G: SpinGuardian,
> {
    guard: G::Guard,
    inner: R,
    v_perm: Tracked<RwFrac<T>>,
}
/*
impl<T: ?Sized, R: Deref<Target = RwLock<T, G>> + Clone, G: SpinGuardian> AsAtomicModeGuard
    for RwLockUpgradeableGuard_<T, R, G>
{
    fn as_atomic_mode_guard(&self) -> &dyn crate::task::atomic_mode::InAtomicMode {
        self.guard.as_atomic_mode_guard()
    }
}*/

/// A upgradable guard that provides read access to the data protected by a [`RwLock`].
pub type RwLockUpgradeableGuard<'a, T, G> = RwLockUpgradeableGuard_<T, &'a RwLock<T, G>, G>;
/// A upgradable guard that provides read access to the data protected by a `Arc<RwLock>`.
pub type ArcRwLockUpgradeableGuard<T, G> = RwLockUpgradeableGuard_<T, Arc<RwLock<T, G>>, G>;

verus! {

impl<T, R: Deref<Target = RwLock<T, G>> + Clone, G: SpinGuardian> RwLockUpgradeableGuard_<T, R, G> {
    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        &&& self.inner.deref_spec().cell_id() == self.v_perm@.resource().id()
        &&& self.v_perm@.frac() == 1
    }
}

}

/*
/*
impl<T: ?Sized, R: Deref<Target = RwLock<T, G>> + Clone, G: SpinGuardian>
    RwLockUpgradeableGuard_<T, R, G>
{
    /// Upgrades this upread guard to a write guard atomically.
    ///
    /// After calling this method, subsequent readers will be blocked
    /// while previous readers remain unaffected. The calling thread
    /// will spin-wait until previous readers finish.
    pub fn upgrade(mut self) -> RwLockWriteGuard_<T, R, G> {
        self.inner.lock.fetch_or(BEING_UPGRADED, Acquire);
        loop {
            self = match self.try_upgrade() {
                Ok(guard) => return guard,
                Err(e) => e,
            };
        }
    }
    /// Attempts to upgrade this upread guard to a write guard atomically.
    ///
    /// This function will never spin-wait and will return immediately.
    pub fn try_upgrade(mut self) -> Result<RwLockWriteGuard_<T, R, G>, Self> {
        let res = self.inner.lock.compare_exchange(
            UPGRADEABLE_READER | BEING_UPGRADED,
            WRITER | UPGRADEABLE_READER,
            AcqRel,
            Relaxed,
        );
        if res.is_ok() {
            let inner = self.inner.clone();
            let guard = self.guard.transfer_to();
            drop(self);
            Ok(RwLockWriteGuard_ { inner, guard })
        } else {
            Err(self)
        }
    }
}*/

impl<T: ?Sized, R: Deref<Target = RwLock<T, G>> + Clone, G: SpinGuardian> Deref
    for RwLockUpgradeableGuard_<T, R, G>
{
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { &*self.inner.val.get() }
    }
}

impl<T: ?Sized, R: Deref<Target = RwLock<T, G>> + Clone, G: SpinGuardian> Drop
    for RwLockUpgradeableGuard_<T, R, G>
{
    fn drop(&mut self) {
        self.inner.lock.fetch_sub(UPGRADEABLE_READER, Release);
    }
}

impl<T: ?Sized + fmt::Debug, R: Deref<Target = RwLock<T, G>> + Clone, G: SpinGuardian> fmt::Debug
    for RwLockUpgradeableGuard_<T, R, G>
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}
*/

verus! {

proof fn lemma_consts_properties()
    ensures
        0 & WRITER == 0,
        0 & UPGRADEABLE_READER == 0,
        0 & BEING_UPGRADED == 0,
        0 & READER_MASK == 0,
        0 & MAX_READER == 0,
        0 & READER == 0,
        WRITER == 0x8000_0000_0000_0000,
        UPGRADEABLE_READER == 0x4000_0000_0000_0000,
        BEING_UPGRADED == 0x2000_0000_0000_0000,
        READER_MASK == 0x0FFF_FFFF_FFFF_FFFF,
        MAX_READER == 0x1000_0000_0000_0000,
        WRITER & WRITER == WRITER,
        WRITER & BEING_UPGRADED == 0,
        WRITER & READER_MASK == 0,
        WRITER & MAX_READER == 0,
        WRITER & UPGRADEABLE_READER == 0,
{
    assert(0 & WRITER == 0) by (compute_only);
    assert(0 & UPGRADEABLE_READER == 0) by (compute_only);
    assert(0 & BEING_UPGRADED == 0) by (compute_only);
    assert(0 & READER_MASK == 0) by (compute_only);
    assert(0 & MAX_READER == 0) by (compute_only);
    assert(0 & READER == 0) by (compute_only);
    assert(WRITER == 0x8000_0000_0000_0000) by (compute_only);
    assert(UPGRADEABLE_READER == 0x4000_0000_0000_0000) by (compute_only);
    assert(BEING_UPGRADED == 0x2000_0000_0000_0000) by (compute_only);
    assert(READER_MASK == 0x0FFF_FFFF_FFFF_FFFF) by (compute_only);
    assert(MAX_READER == 0x1000_0000_0000_0000) by (compute_only);
    assert(WRITER & WRITER == WRITER) by (compute_only);
    assert(WRITER & BEING_UPGRADED == 0) by (compute_only);
    assert(WRITER & READER_MASK == 0) by (compute_only);
    assert(WRITER & MAX_READER == 0) by (compute_only);
    assert(WRITER & UPGRADEABLE_READER == 0) by (compute_only);
}

proof fn lemma_consts_properties_prev_next(prev: usize, next: usize)
    ensures
        prev & READER_MASK < MAX_READER,
        next == prev | UPGRADEABLE_READER ==> {
            &&& next & UPGRADEABLE_READER != 0
            &&& next & WRITER == prev & WRITER
            &&& next & READER_MASK == prev & READER_MASK
            &&& next & MAX_READER == prev & MAX_READER
            &&& next & BEING_UPGRADED == prev & BEING_UPGRADED
        },
        next == prev - UPGRADEABLE_READER && prev & UPGRADEABLE_READER != 0 ==> {
            &&& next & UPGRADEABLE_READER == 0
            &&& next & WRITER == prev & WRITER
            &&& next & READER_MASK == prev & READER_MASK
            &&& next & MAX_READER == prev & MAX_READER
            &&& next & BEING_UPGRADED == prev & BEING_UPGRADED
        },
        next == prev - READER && prev & READER_MASK != 0 ==> {
            &&& next & READER_MASK == (prev & READER_MASK) - READER
            &&& next & UPGRADEABLE_READER == prev & UPGRADEABLE_READER
            &&& next & WRITER == prev & WRITER
            &&& next & MAX_READER == prev & MAX_READER
            &&& next & BEING_UPGRADED == prev & BEING_UPGRADED
        },
        next == prev + READER && if prev & MAX_READER != 0 { ((prev & READER_MASK) + READER) < MAX_READER } else { true } ==> {
            &&& next & READER_MASK == if prev & READER_MASK == MAX_READER - READER {
                    0
                } else {
                    (prev & READER_MASK) + READER
                }
            &&& next & UPGRADEABLE_READER == prev & UPGRADEABLE_READER
            &&& next & WRITER == prev & WRITER
            &&& next & MAX_READER == if prev & READER_MASK == MAX_READER - READER {
                    MAX_READER
                } else {
                    prev & MAX_READER
                }
            &&& next & BEING_UPGRADED == prev & BEING_UPGRADED
        },
    {
        assert(prev & READER_MASK < MAX_READER) by (bit_vector);
        if next == prev | UPGRADEABLE_READER {
            assert(next & UPGRADEABLE_READER != 0) by (bit_vector)
                requires
                    next == prev | UPGRADEABLE_READER;
            assert(next & WRITER == prev & WRITER) by (bit_vector)
                requires
                    next == prev | UPGRADEABLE_READER;
            assert(next & READER_MASK == prev & READER_MASK) by (bit_vector)
                requires
                    next == prev | UPGRADEABLE_READER;
            assert(next & MAX_READER == prev & MAX_READER) by (bit_vector)
                requires
                    next == prev | UPGRADEABLE_READER;
            assert(next & BEING_UPGRADED == prev & BEING_UPGRADED) by (bit_vector)
                requires
                    next == prev | UPGRADEABLE_READER;    
        }
        if next == prev - UPGRADEABLE_READER && prev & UPGRADEABLE_READER != 0 {
            assert(next & UPGRADEABLE_READER == 0) by (bit_vector)
                requires
                    next == prev - UPGRADEABLE_READER && prev & UPGRADEABLE_READER != 0;
            assert(next & WRITER == prev & WRITER) by (bit_vector)
                requires
                    next == prev - UPGRADEABLE_READER && prev & UPGRADEABLE_READER != 0;
            assert(next & READER_MASK == prev & READER_MASK) by (bit_vector)
                requires
                    next == prev - UPGRADEABLE_READER && prev & UPGRADEABLE_READER != 0;
            assert(next & MAX_READER == prev & MAX_READER) by (bit_vector)
                requires
                    next == prev - UPGRADEABLE_READER && prev & UPGRADEABLE_READER != 0;
            assert(next & BEING_UPGRADED == prev & BEING_UPGRADED) by (bit_vector)
                requires
                    next == prev - UPGRADEABLE_READER && prev & UPGRADEABLE_READER != 0;    
        }
        if next == prev - READER && prev & READER_MASK != 0 {
            assert(next & READER_MASK == (prev & READER_MASK) - READER) by (bit_vector)
                requires
                    next == prev - READER && prev & READER_MASK != 0;
            assert(next & UPGRADEABLE_READER == prev & UPGRADEABLE_READER) by (bit_vector)
                requires
                    next == prev - READER && prev & READER_MASK != 0;
            assert(next & WRITER == prev & WRITER) by (bit_vector)
                requires
                    next == prev - READER && prev & READER_MASK != 0;
            assert(next & MAX_READER == prev & MAX_READER) by (bit_vector)
                requires
                    next == prev - READER && prev & READER_MASK != 0;
            assert(next & BEING_UPGRADED == prev & BEING_UPGRADED) by (bit_vector)
                requires
                    next == prev - READER && prev & READER_MASK != 0;    
        }
        if next == prev + READER && if prev & MAX_READER != 0 { ((prev & READER_MASK) + READER) < MAX_READER } else { true } {
            assert(next & READER_MASK == if prev & READER_MASK == MAX_READER - READER {
                    0
                } else {
                    (prev & READER_MASK) + READER
                }) by (bit_vector)
                requires
                    next == prev + READER && if prev & MAX_READER != 0 { ((prev & READER_MASK) + READER) < MAX_READER } else { true };
            assert(next & UPGRADEABLE_READER == prev & UPGRADEABLE_READER) by (bit_vector)
                requires
                    next == prev + READER && if prev & MAX_READER != 0 { ((prev & READER_MASK) + READER) < MAX_READER } else { true };
            assert(next & WRITER == prev & WRITER) by (bit_vector)
                requires
                    next == prev + READER && if prev & MAX_READER != 0 { ((prev & READER_MASK) + READER) < MAX_READER } else { true };
            assert(next & MAX_READER == if prev & READER_MASK == MAX_READER - READER {
                    MAX_READER
                } else {
                    prev & MAX_READER
                }) by (bit_vector)
                requires
                    next == prev + READER && if prev & MAX_READER != 0 { ((prev & READER_MASK) + READER) < MAX_READER } else { true };
            assert(next & BEING_UPGRADED == prev & BEING_UPGRADED) by (bit_vector)
                requires
                    next == prev + READER && if prev & MAX_READER != 0 { ((prev & READER_MASK) + READER) < MAX_READER } else { true };    
        }
}

} // verus!
