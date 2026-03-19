// SPDX-License-Identifier: MPL-2.0
use vstd::atomic_ghost::*;
use vstd::cell::{self, pcell::*};
use vstd::pcm::Loc;
use vstd::prelude::*;
use vstd::tokens::frac::{Empty, Frac, FracGhost};
use vstd_extra::prelude::*;
use vstd_extra::resource::ghost_resource::{csum::*,excl::*, tokens::*};
use vstd_extra::sum::*;

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
    guard::{GuardTransfer, SpinGuardian},
    PreemptDisabled,
};
//use crate::task::atomic_mode::AsAtomicModeGuard;

verus! {

axiom fn is_exclusive<T>(tracked value: &mut PointsTo<T>, tracked other: & PointsTo<T>)
    ensures
        *value == *old(value),
        value.id() != other.id(),
;

type RwFrac<T> = Frac<PointsTo<T>, V_MAX_PERM_FRACS>;

type NoPerm<T> = Empty<PointsTo<T>, V_MAX_PERM_FRACS>;

type ReadRetractToken = TokenStorage<V_MAX_READ_RETRACT_FRACS>;

spec const V_MAX_PERM_FRACS_SPEC: u64 = (MAX_READER + 2) as u64;

#[verifier::when_used_as_spec(V_MAX_PERM_FRACS_SPEC)]
exec const V_MAX_PERM_FRACS: u64
    ensures
        V_MAX_PERM_FRACS == V_MAX_PERM_FRACS_SPEC,
        V_MAX_PERM_FRACS == MAX_READER + 2,
        V_MAX_PERM_FRACS < u64::MAX,
{
    assert(MAX_READER + 2 < u64::MAX) by (compute_only);
    (MAX_READER + 2) as u64
}

spec const V_MAX_READ_RETRACT_FRACS_SPEC: u64 = (MAX_READER_MASK + 1) as u64;

#[verifier::when_used_as_spec(V_MAX_READ_RETRACT_FRACS_SPEC)]
exec const V_MAX_READ_RETRACT_FRACS: u64
    ensures
        V_MAX_READ_RETRACT_FRACS == V_MAX_READ_RETRACT_FRACS_SPEC,
        V_MAX_READ_RETRACT_FRACS == MAX_READER_MASK + 1,
        V_MAX_READ_RETRACT_FRACS < u64::MAX,
{
    assert(MAX_READER_MASK + 1 < u64::MAX) by (compute_only);
    (MAX_READER_MASK + 1) as u64
}

spec const V_MAX_READ_GUARDS_SPEC: u64 = MAX_READER as u64;

#[verifier::when_used_as_spec(V_MAX_READ_GUARDS_SPEC)]
exec const V_MAX_READ_GUARDS: u64
    ensures
        V_MAX_READ_GUARDS == V_MAX_READ_GUARDS_SPEC,
        V_MAX_READ_GUARDS == MAX_READER,
        V_MAX_READ_GUARDS < u64::MAX,
{
    assert(MAX_READER < u64::MAX) by (compute_only);
    MAX_READER as u64
}

tracked struct RwPerms<T> {
    /// The permission of the `PCell<T>`. 
    /// In the reading state, it can be splited up to `V_MAX_PERM_FRACS:= MAX_READER + 2` pieces,
    /// which allows at most `MAX_READER` `RwLockReadGuard`s and 1 `RwLockUpgradeableGuard`, and 1 reserved in the lock atomic.
    /// It will be switched out when there is a writer, leaving `NoPerm` in the lock.
    cell_perm_resource: SumResource<RwFrac<T>, NoPerm<T>, V_MAX_PERM_FRACS>,
    /// The permission to retract a `READER` count. Its total quantity tracks the gap between
    /// the number of `try_read` increments recorded in the lock atomic and the number of active
    /// `RwLockReadGuard`s (created and ongoing creation that will succeed) represented by `cell_perm`.
    /// It can be splited up to `V_MAX_READ_RETRACT_FRACS:= 2 * MAX_READER` pieces,
    /// which allows at most `2*MAX_READER - 1` `try_read` attempts that will fail to acquire the lock, and 1 reserved in the lock atomic.
    read_retract_token: ReadRetractToken,
    /// The permission to retract the set of `UPGRADEABLE_READER` bit, it can be spilit at two pieces,
    /// which allows at most 1 failing `try_upread` to subtract the `UPGRADEABLE_READER` bit, and 1 reserved in the lock atomic.
    upread_retract_token: UniqueTokenStorage,
    /// Tracks whether there is a live `RwLockUpgradeableGuard`.
    upreader_guard_token: UniqueTokenStorage,
    /// Tracks the number of live `RwLockReadGuard`s.
    read_guard_token: TokenStorage<V_MAX_READ_GUARDS>,
}

ghost struct RwId {
    cell_perm_resource_id: Loc,
    frac_id: Loc,
    upread_retract_token_id: Loc,
    upreader_guard_token_id: Loc,
    read_retract_token_id: Loc,
    read_guard_token_id: Loc,
}

/// The number of `try_read` operations recorded in the lock atomic (created and ongoing) can never reach `2*MAX_READER` to avoid overflow.
/// **NOTE**: We *ASSUME* this property always holds without any proof. We believe this is true in practice because:
/// - More than `2^61` `try_read` operations are required to trigger the overflow concurrently, which is absurd in real world scenarios.
/// - If one tries to create a huge number (more than `2*MAX_READER`) of `RwLockReadGuard`s in a loop with `mem::forget`, it will take years and
/// will be prevented by the `MAX_READER` check.
pub closed spec fn no_max_reader_overflow(v: usize) -> bool {
    v & MAX_READER_MASK < MAX_READER_MASK
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
pub struct RwLock<T  /* : ?Sized*/ , Guard /* = PreemptDisabled*/ > {
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
    invariant on lock with (val, guard, v_id) is (v: usize, g: RwPerms<T>) {
        // BITS VALUE
        let has_writer_bit: bool = (v & WRITER) != 0;
        let has_upgrade_bit: bool = (v & UPGRADEABLE_READER) != 0;
        let has_max_reader_bit: bool = (v & MAX_READER) != 0;
        // The total number of `try_read` attempts recorded in the lock atomic, including created `RwLockReadGuard`s
        // and those who are trying, no matter they will succeed or fail.
        let total_reader_bits: int = (v & MAX_READER_MASK) as int;
        // The clamped value represented in the counter bits. This counts the maximum number of active `RwLockReadGuard`s.
        // NOTE: This does not mean there are actually this number of active `RwLockReadGuard`s. The actual number of successfully
        // created/creating `RwLockReadGuard`s can be smaller than this number, because previously created `RwLockReadGuard`s may be dropped.
        let reader_bits: int = if has_max_reader_bit { MAX_READER as int } else { (v & READER_MASK) as int };
        // ACTUAL NUMBER OF ACTIVE GUARDS.
        // The number is tracked by the ghost resources remained in the lock.
        // By active, we mean from the perspective the lock, the permissions for these guards are given out.
        // The actual guards may be still being created, but they must be successfully created finally.
        // This invariant maintains the consistency between the ghost resources and the lock atomic value.

        // Whether there is an active writer
        let active_writer: bool = g.cell_perm_resource.is_right();
        // Remaining fractional permissions in the lock to access the protected data.
        let remaining_pcell_perms: int = if !active_writer { g.cell_perm_resource.resource()->Left_0.frac() } else { 0 };
        // The number of active readers, including both `RwLockReadGuard`s and `RwLockUpgradeableGuard`s.
        let total_active_readers: int = if !active_writer { (V_MAX_PERM_FRACS as int) - remaining_pcell_perms } else { 0 };
        // The number of active `RwLockUpgradeableGuard`, which can only be 0 or 1.
        let active_upgrade_guard: bool = g.upreader_guard_token.is_empty();
        // The number of active `RwLockReadGuard`s.
        let active_read_guards: int = V_MAX_READ_GUARDS - g.read_guard_token.frac();
        // The first `try_upread` that fails, which has not returned yet.
        let pending_failed_upread_attempt: bool = g.upread_retract_token.is_empty();
        // The number of `try_read` attempts that will fail.
        let failed_reader_attempts: int = V_MAX_READ_RETRACT_FRACS - g.read_retract_token.frac();

        // The `UPGRADEABLE_READER` bit is set iff there is an active `RwLockUpgradeableGuard` or a pending failed `try_upread` attempt.
        &&& has_upgrade_bit <==> (active_upgrade_guard || pending_failed_upread_attempt)
        // An active `RwLockUpgradeableGuard` cannot coexist with a pending failed `try_upread` attempt.
        &&& !(active_upgrade_guard && pending_failed_upread_attempt)
        // Active readers are split into plain readers plus at most one upgradeable reader.
        &&& total_active_readers == active_read_guards + if active_upgrade_guard { 1int } else { 0 }
        // The `READER` bits count the number of all active readers and pending failed `try_read` attempts.
        &&& total_reader_bits + if active_upgrade_guard { 1int } else {0} == total_active_readers +  failed_reader_attempts
        // There is an active `RwLockWriteGuard` iff the `WRITER` bit is set.
        &&& active_writer <==> has_writer_bit
        // The number of active `RwLockReadGaurd`s is less than or equal to the `READER` bits.
        &&& 0 <= active_read_guards <= reader_bits <= total_reader_bits
        // The core invariant of `RwLock`: there are no simultaneous active writers and readers.
        &&& !(active_writer && total_active_readers > 0)
        &&& g.read_retract_token.wf()
        &&& g.cell_perm_resource.wf()
        &&& g.upread_retract_token.wf()
        &&& g.upreader_guard_token.wf()
        &&& g.read_guard_token.wf()
        &&& g.cell_perm_resource.is_resource_owner() 
        &&& g.cell_perm_resource.has_resource()
        &&& g.cell_perm_resource.is_left() ==> {
            let perm = g.cell_perm_resource.resource()->Left_0;
            &&& perm.id() == v_id@.frac_id
            &&& perm.resource().id() == val.id()
            &&& g.cell_perm_resource.frac() == remaining_pcell_perms
        }
        &&& g.cell_perm_resource.is_right() ==> {
            let empty = g.cell_perm_resource.resource()->Right_0;
            &&& empty.id() == v_id@.frac_id
            &&& g.cell_perm_resource.frac() == V_MAX_PERM_FRACS - 1
        }
        &&& v_id@.upread_retract_token_id == g.upread_retract_token.id()
        &&& v_id@.upreader_guard_token_id == g.upreader_guard_token.id()
        &&& v_id@.read_retract_token_id == g.read_retract_token.id()
        &&& v_id@.read_guard_token_id == g.read_guard_token.id()
        &&& v_id@.cell_perm_resource_id == g.cell_perm_resource.id()
    }
}

}

const READER: usize = 1;
const WRITER: usize = 1 << (usize::BITS - 1);
const UPGRADEABLE_READER: usize = 1 << (usize::BITS - 2);
const BEING_UPGRADED: usize = 1 << (usize::BITS - 3);

/// This bit is reserved as an overflow sentinel.
/// We intentionally cap read guards before counter growth can affect
/// `BEING_UPGRADED` / `UPGRADEABLE_READER` / `WRITER` bits.
/// This is defense-in-depth with no extra runtime cost.
///
/// This follows the same strategy as Rust std's `Arc`,
/// which uses `isize::MAX` as a sentinel to prevent its reference count
/// from overflowing into values that could compromise safety.
///
/// On 64-bit platforms (the only targets Asterinas supports),
/// a counter overflow is not a practical concern:
/// incrementing one-by-one from zero to `MAX_READER` (2^60)
/// would take hundreds of years even at billions of increments per second.
/// Nevertheless, this sentinel provides an extra layer of safety at no runtime cost.
const MAX_READER: usize = 1 << (usize::BITS - 4);

/// Used only in verification. Excluding the `MAX_READER` bit.
const READER_MASK: usize = usize::MAX >> 4;
/// Used only in verification. Including the `MAX_READER` bit.
const MAX_READER_MASK: usize = usize::MAX >> 3;

impl<T, G> RwLock<T, G> {
    /// Returns the unique [`CellId`](https://verus-lang.github.io/verus/verusdoc/vstd/cell/struct.CellId.html) of the internal `PCell<T>`.
    pub closed spec fn cell_id(self) -> cell::CellId {
        self.val.id()
    }

    pub closed spec fn cell_perm_resource_id(self) -> Loc {
        self.v_id@.cell_perm_resource_id
    }

    pub closed spec fn frac_id(self) -> Loc {
        self.v_id@.frac_id
    }

    pub closed spec fn upread_retract_token_id(self) -> Loc {
        self.v_id@.upread_retract_token_id
    }

    pub closed spec fn upreader_guard_token_id(self) -> Loc {
        self.v_id@.upreader_guard_token_id
    }

    pub closed spec fn read_guard_token_id(self) -> Loc {
        self.v_id@.read_guard_token_id
    }

    /// Encapsulates the invariant described in the *Invariant* section of [`RwLock`].
    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        self.wf()
    }
}

#[verus_verify]
impl<T, G> RwLock<T, G> {
    /// Creates a new spin-based read-write lock with an initial value.
     #[verus_verify]
    pub const fn new(val: T) -> Self {
        let (val, Tracked(perm)) = PCell::new(val);

        // Proof code
        proof {lemma_consts_properties();}
        let tracked frac_perm = RwFrac::<T>::new(perm);
        let ghost frac_id = frac_perm.id();
        let tracked cell_perm_resource = SumResource::alloc_left(frac_perm);
        proof_decl!{
            let tracked read_retract_token = TokenStorage::<V_MAX_READ_RETRACT_FRACS>::alloc(());
            let tracked upread_retract_token = UniqueTokenStorage::alloc(());
            let tracked upreader_guard_token = UniqueTokenStorage::alloc(());
            let tracked read_guard_token = TokenStorage::<V_MAX_READ_GUARDS>::alloc(());
        }
        let ghost v_id = RwId {
            frac_id,
            cell_perm_resource_id: cell_perm_resource.id(),
            upread_retract_token_id: upread_retract_token.id(),
            upreader_guard_token_id: upreader_guard_token.id(),
            read_retract_token_id: read_retract_token.id(),
            read_guard_token_id: read_guard_token.id(),
        };
        let tracked perms = RwPerms {
            cell_perm_resource,
            read_retract_token,
            upread_retract_token,
            upreader_guard_token,
            read_guard_token,
        };

        Self {
            guard: PhantomData,
            //lock: AtomicUsize::new(0),
            lock: AtomicUsize::new(Ghost((val, PhantomData, Ghost(v_id))), 0, Tracked(perms)),
            //val: UnsafeCell::new(val),
            val: val,
            v_id: Ghost(v_id),
        }
    }
}

#[verus_verify]
impl<T  /*: ?Sized*/ , G: SpinGuardian> RwLock<T, G> {
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

    /// Attempts to acquire a read lock.
    ///
    /// This function will never spin-wait and will return immediately.
    #[verus_spec]
    pub fn try_read(&self) -> Option<RwLockReadGuard<T, G>> {
        proof_decl!{
            let tracked mut perm: Option<RwFrac<T>> = None;
            let tracked mut retract_read_token: Option<Token<V_MAX_READ_RETRACT_FRACS>> = None;
            let tracked mut left_token = None;
            let tracked mut read_guard_token: Option<Token<V_MAX_READ_GUARDS>> = None;
        }
        proof!{
            use_type_invariant(self);
            lemma_consts_properties();
        }
        let guard = G::read_guard();

        // let lock = self.lock.fetch_add(READER, Acquire);
        let lock =
            atomic_with_ghost!(
            self.lock => fetch_add(READER);
            update prev -> next;
            ghost g => {
                let prev_usize = prev as usize;
                let next_usize = next as usize;
                assume (no_max_reader_overflow(prev_usize));
                lemma_consts_properties_value(prev_usize);
                lemma_consts_properties_prev_next(prev_usize, next_usize);
                if prev_usize & (WRITER | MAX_READER | BEING_UPGRADED) == 0 {
                    let tracked mut tmp = g.cell_perm_resource.take_resource_left();
                    perm = Some(tmp.split(1int));
                    g.cell_perm_resource.put_resource_left(tmp);
                    left_token = Some(g.cell_perm_resource.split_left_without_resource(1int));
                    read_guard_token = Some(g.read_guard_token.split_one());
                } else {
                    retract_read_token = Some(g.read_retract_token.split_one());
                }
            }
        );
        if lock & (WRITER | MAX_READER | BEING_UPGRADED) == 0 {
            Some(RwLockReadGuard {
                inner: self,
                guard,
                v_perm: Tracked(perm.tracked_unwrap()),
                v_cell_token: Tracked(left_token.tracked_unwrap()),
                v_read_token: Tracked(read_guard_token.tracked_unwrap()),
            })
        } else {
            // self.lock.fetch_sub(READER, Release);
            atomic_with_ghost!(
                self.lock => fetch_sub(READER);
                update prev -> next;
                ghost g => {
                    let prev_usize = prev as usize;
                    let next_usize = next as usize;
                    lemma_consts_properties_value(next_usize);
                    lemma_consts_properties_prev_next(prev_usize, next_usize);
                    let tracked token = retract_read_token.tracked_unwrap();
                    g.read_retract_token.combine(token);
                }
            );
            None
        }
    }

    /// Attempts to acquire a write lock.
    ///
    /// This function will never spin-wait and will return immediately.
    #[verus_spec]
    pub fn try_write(&self) -> Option<RwLockWriteGuard<T, G>> {
        proof_decl!{
            let tracked mut perm: Option<PointsTo<T>> = None;
            let tracked mut right_token: Option<Right<RwFrac<T>, NoPerm<T>, V_MAX_PERM_FRACS>> = None;
        }
        proof!{
            use_type_invariant(self);
            lemma_consts_properties();
        }

        let guard = G::guard();
        // if self
        //     .lock
        //     .compare_exchange(0, WRITER, Acquire, Relaxed)
        //     .is_ok()
        if atomic_with_ghost!(
            self.lock => compare_exchange(0, WRITER);
            returning res;
            ghost g => {
                if res is Ok {
                    let tracked full_frac_perm = g.cell_perm_resource.take_resource_left();
                    let tracked (pointsto, empty) = full_frac_perm.take_resource();
                    perm = Some(pointsto);
                    g.cell_perm_resource.change_to_right(empty);
                    right_token = Some(g.cell_perm_resource.split_right_without_resource(1int));
                }
            }
        ).is_ok() {
            Some(RwLockWriteGuard { inner: self, guard, v_perm: Tracked(perm.tracked_unwrap()), v_cell_token: Tracked(right_token.tracked_unwrap()) })
        } else {
            None
        }
    }
    
    /// Attempts to acquire an upread lock.
    ///
    /// This function will never spin-wait and will return immediately.
    #[verus_spec]
    pub fn try_upread(&self) -> Option<RwLockUpgradeableGuard<T, G>> {
        proof_decl!{
            let tracked mut perm: Option<RwFrac<T>> = None;
            let tracked mut upreader_guard_token: Option<UniqueToken> = None;
            let tracked mut retract_upgrade_token: Option<UniqueToken> = None;
            let tracked mut left_token = None;
        }
        proof!{
            use_type_invariant(self);
            lemma_consts_properties();
        }
        let guard = G::guard();
        // let lock = self.lock.fetch_or(UPGRADEABLE_READER, Acquire) & (WRITER | UPGRADEABLE_READER);
        let lock =
            atomic_with_ghost!(
            self.lock => fetch_or(UPGRADEABLE_READER);
            update prev -> next;
            ghost g => {
                lemma_consts_properties_value(prev);
                lemma_consts_properties_prev_next(prev, next);
                if prev & (WRITER | UPGRADEABLE_READER) == 0 {
                    let tracked mut tmp = g.cell_perm_resource.take_resource_left();
                    perm = Some(tmp.split(1int));
                    g.cell_perm_resource.put_resource_left(tmp);
                    upreader_guard_token = Some(g.upreader_guard_token.take());
                    left_token = Some(g.cell_perm_resource.split_left_without_resource(1int));
                }
                else if prev & (WRITER | UPGRADEABLE_READER) == WRITER {
                    retract_upgrade_token = Some(g.upread_retract_token.take());
                }
            }
        ) & (WRITER | UPGRADEABLE_READER);
        if lock == 0 {
            return Some(
                RwLockUpgradeableGuard {
                    inner: self,
                    guard,
                    v_perm: Tracked(perm.tracked_unwrap()),
                    v_guard_token: Tracked(upreader_guard_token.tracked_unwrap()),
                    v_cell_perm_token: Tracked(left_token.tracked_unwrap()),
                },
            );
        } else if lock == WRITER {
            // self.lock.fetch_sub(UPGRADEABLE_READER, Release);
            atomic_with_ghost!(
                self.lock => fetch_sub(UPGRADEABLE_READER);
                update prev -> next;
                ghost g => {
                    let prev_usize = prev as usize;
                    let next_usize = next as usize;
                    lemma_consts_properties_value(prev_usize);
                    lemma_consts_properties_prev_next(prev_usize, next_usize);
                    g.upread_retract_token.join(retract_upgrade_token.tracked_unwrap());
                }
            );
        }
        None
    }
}
} // verus!

/*
impl<T, G: SpinGuardian> RwLock<T, G> {
    /// Returns a mutable reference to the underlying data.
    ///
    /// This method is zero-cost: By holding a mutable reference to the lock, the compiler has
    /// already statically guaranteed that access to the data is exclusive.
    pub fn get_mut(&mut self) -> &mut T {
        self.val.get_mut()
    }

    /// Returns a raw pointer to the underlying data.
    ///
    /// This method is safe, but it's up to the caller to ensure that access to the data behind it
    /// is still safe.
    pub(super) fn as_ptr(&self) -> *mut T {
        self.val.get()
    }
}*/

/* the trait `core::fmt::Debug` is not implemented for `vstd::cell::pcell::PCell<T>`
impl<T: ?Sized + fmt::Debug, G> fmt::Debug for RwLock<T, G> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.val, f)
    }
}*/

/// Because there can be more than one readers to get the T's immutable ref,
/// so T must be Sync to guarantee the sharing safety.
#[verifier::external]
unsafe impl<T: /*?Sized +*/ Send, G> Send for RwLock<T, G> {}

#[verifier::external]
unsafe impl<T: /*?Sized +*/ Send + Sync, G> Sync for RwLock<T, G> {}

#[verus_verify]
impl<T: /*?Sized*/, G: SpinGuardian> !Send for RwLockWriteGuard<'_, T, G> {}
#[verifier::external]
unsafe impl<T: /*?Sized +*/ Sync, G: SpinGuardian> Sync for RwLockWriteGuard<'_, T, G> {}

#[verus_verify]
impl<T: /*?Sized*/, G: SpinGuardian> !Send for RwLockReadGuard<'_, T, G> {}
#[verifier::external]
unsafe impl<T: /*?Sized +*/ Sync, G: SpinGuardian> Sync for RwLockReadGuard<'_, T, G> {}

#[verus_verify]
impl<T: /*?Sized*/, G: SpinGuardian> !Send for RwLockUpgradeableGuard<'_, T, G> {}
#[verifier::external]
unsafe impl<T: /*?Sized +*/ Sync, G: SpinGuardian> Sync for RwLockUpgradeableGuard<'_, T, G> {}

/// A guard that provides immutable data access.
#[clippy::has_significant_drop]
#[must_use]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(G)]
#[verus_verify]
pub struct RwLockReadGuard<'a, T /*: ?Sized*/, G: SpinGuardian> {
    guard: G::ReadGuard,
    inner: &'a RwLock<T, G>,
    v_perm: Tracked<RwFrac<T>>,
    v_cell_token: Tracked<Left<RwFrac<T>,NoPerm<T>,V_MAX_PERM_FRACS>>,
    v_read_token: Tracked<Token<V_MAX_READ_GUARDS>>,
}

/*
impl<T: ?Sized, G: SpinGuardian> AsAtomicModeGuard for RwLockReadGuard<'_, T, G> {
    fn as_atomic_mode_guard(&self) -> &dyn crate::task::atomic_mode::InAtomicMode {
        self.guard.as_atomic_mode_guard()
    }
}
*/

verus! {

impl<'a, T, G: SpinGuardian> RwLockReadGuard<'a, T, G> {
    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        &&& self.inner.cell_perm_resource_id() == self.v_cell_token@.id()
        &&& self.inner.frac_id() == self.v_perm@.id()
        &&& self.inner.cell_id() == self.v_perm@.resource().id()
        &&& self.inner.read_guard_token_id() == self.v_read_token@.id()
        &&& self.v_perm@.frac() == 1
        &&& self.v_cell_token@.frac() == 1
        &&& self.v_read_token@.frac() == 1
        &&& !self.v_cell_token@.is_resource_owner()
    }
}

 
#[verus_verify]
impl<T /*: ?Sized*/, G: SpinGuardian> Deref for RwLockReadGuard<'_, T, G>
{
    type Target = T;

    #[verus_spec]
    fn deref(&self) -> &T {
        proof_decl! {
            let tracked read_perm = self.v_perm.borrow().borrow();
        }
        proof!{
            use_type_invariant(self);
        }
        // unsafe { &*self.inner.val.get() }
        // The internal implementation of `PCell<T>::borrow` is exactly unsafe { &(*(*self.ucell).get()) },
        // and here we verify that we have the permission to call `borrow`.
        self.inner.val.borrow(Tracked(read_perm))
    }
}
}

/* impl<T: ?Sized, R: Deref<Target = RwLock<T, G>> + Clone, G: SpinGuardian> Drop
    for RwLockReadGuard_<T, R, G>
{
    fn drop(&mut self) {
        self.inner.lock.fetch_sub(READER, Release);
    }
} */

verus!{
#[verus_verify]
impl<T /*: ?Sized*/, G: SpinGuardian> RwLockReadGuard<'_, T, G>
{
    /// VERUS LIMITATION: We implement `drop` and call it manually because Verus's support for `Drop` is incomplete for now.
    #[verus_spec]
    fn drop(self)
    {
        proof! {
            use_type_invariant(&self);
            use_type_invariant(self.inner);
            lemma_consts_properties();
        }
        let Tracked(perm) = self.v_perm;
        let Tracked(token) = self.v_cell_token;
        let Tracked(read_token) = self.v_read_token;
        // self.inner.lock.fetch_sub(READER, Release);
        atomic_with_ghost!(
            self.inner.lock => fetch_sub(READER);
            update prev -> next;
            ghost g => {
                let prev_usize = #[verifier::truncate] (prev as usize);
                let next_usize = #[verifier::truncate] (next as usize);
                assume (no_max_reader_overflow(prev_usize));
                lemma_consts_properties_value(prev_usize);
                lemma_consts_properties_value(next_usize);
                lemma_consts_properties_prev_next(prev_usize, next_usize);
                g.read_guard_token.combine(read_token);
                g.cell_perm_resource.validate_with_left(&token);
                g.cell_perm_resource.join_left(token);
                let tracked mut rem = g.cell_perm_resource.take_resource_left();
                rem.combine(perm);
                rem.bounded();
                g.cell_perm_resource.put_resource_left(rem);
            }
        );
    }
}
}

/*
impl<T: ?Sized + fmt::Debug, G: SpinGuardian> fmt::Debug for RwLockReadGuard<'_, T, G> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}*/

/// A guard that provides mutable data access.
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(G)]
#[verus_verify]
pub struct RwLockWriteGuard<'a, T/*: ?Sized*/, G: SpinGuardian> {
    guard: G::Guard,
    inner: &'a RwLock<T, G>,
    /// Ghost permission for verification
    v_perm: Tracked<PointsTo<T>>,
    v_cell_token: Tracked<Right<RwFrac<T>,NoPerm<T>,V_MAX_PERM_FRACS>>
}

verus! {

impl<'a, T, G: SpinGuardian> RwLockWriteGuard<'a, T, G> {
    #[verifier::type_invariant]
    spec fn type_inv(self) -> bool {
        &&& self.inner.cell_id() == self.v_perm@.id()
        &&& self.inner.cell_perm_resource_id() == self.v_cell_token@.id()
        &&& !self.v_cell_token@.is_resource_owner()
        &&& self.v_cell_token@.frac() == 1
    }
}


/*
impl<T: ?Sized, G: SpinGuardian> AsAtomicModeGuard for RwLockWriteGuard<'_, T, G> {
    fn as_atomic_mode_guard(&self) -> &dyn crate::task::atomic_mode::InAtomicMode {
        self.guard.as_atomic_mode_guard()
    }
}*/

#[verus_verify]
impl<T /*: ?Sized*/, G: SpinGuardian> Deref for RwLockWriteGuard<'_, T, G>
{
    type Target = T;

    #[verus_spec]
    fn deref(&self) -> &T {
        proof_decl! {
            let tracked read_perm = self.v_perm.borrow();
        }
        proof!{
            use_type_invariant(self);
        }
        // unsafe { &*self.inner.val.get() }
        // The internal implementation of `PCell<T>::borrow` is exactly unsafe { &(*(*self.ucell).get()) },
        // and here we verify that we have the permission to call `borrow`.
        self.inner.val.borrow(Tracked(read_perm))
    }
}
} // verus!

/*
impl<T: ?Sized, G: SpinGuardian> DerefMut for RwLockWriteGuard<'_, T, G> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.inner.val.get() }
    }
}

impl<T: ?Sized, G: SpinGuardian> Drop for RwLockWriteGuard<'_, T, G> {
    fn drop(&mut self) {
        self.inner.lock.fetch_and(!WRITER, Release);
    }
}*/

verus!{
#[verus_verify]
impl<T /*: ?Sized*/, G: SpinGuardian> RwLockWriteGuard<'_, T, G>
{
    /// VERUS LIMITATION: We implement `drop` and call it manually because Verus's support for `Drop` is incomplete for now.
    #[verus_spec]
    pub fn drop(self) {
        proof!{
            use_type_invariant(&self);
            use_type_invariant(self.inner);
            lemma_consts_properties();
        }
        let Tracked(mut perm) = self.v_perm;
        let Tracked(token) = self.v_cell_token;
        //self.inner.lock.fetch_and(!WRITER, Release);
        atomic_with_ghost!{
            self.inner.lock => fetch_and(!WRITER);
            update prev -> next;
            ghost g => {
                lemma_consts_properties_prev_next(prev, next);
                g.cell_perm_resource.validate_with_right(&token);
                g.cell_perm_resource.join_right(token);
                let tracked empty = g.cell_perm_resource.take_resource_right();
                let tracked full = empty.put_resource(perm);
                g.cell_perm_resource.change_to_left(full);
            }
        };
    }
}
}

/* 
impl<T: ?Sized + fmt::Debug, G: SpinGuardian> fmt::Debug for RwLockWriteGuard<'_, T, G> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}*/

/// A guard that provides immutable data access but can be atomically
/// upgraded to `RwLockWriteGuard`.
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(G)]
#[verus_verify]
pub struct RwLockUpgradeableGuard<'a, T/*: ?Sized*/, G: SpinGuardian> {
    guard: G::Guard,
    inner: &'a RwLock<T, G>,
    v_perm: Tracked<RwFrac<T>>,
    v_guard_token: Tracked<UniqueToken>,
    v_cell_perm_token: Tracked<Left<RwFrac<T>,NoPerm<T>,V_MAX_PERM_FRACS>>,
}
/*
impl<T: ?Sized, G: SpinGuardian> AsAtomicModeGuard for RwLockUpgradeableGuard<'_, T, G> {
    fn as_atomic_mode_guard(&self) -> &dyn crate::task::atomic_mode::InAtomicMode {
        self.guard.as_atomic_mode_guard()
    }
}*/

verus! {

impl<'a, T, G: SpinGuardian> RwLockUpgradeableGuard<'a, T, G> {
    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        &&& self.inner.cell_perm_resource_id() == self.v_cell_perm_token@.id()
        &&& self.inner.frac_id() == self.v_perm@.id()
        &&& self.inner.cell_id() == self.v_perm@.resource().id()
        &&& self.v_perm@.frac() == 1
        &&& self.v_cell_perm_token@.frac() == 1
        &&& self.inner.upreader_guard_token_id() == self.v_guard_token@.id()
    }
}

#[verus_verify]
impl<'a, T /*: ?Sized*/, G: SpinGuardian> RwLockUpgradeableGuard<'a, T, G>
{
    /// Upgrades this upread guard to a write guard atomically.
    ///
    /// After calling this method, subsequent readers will be blocked
    /// while previous readers remain unaffected. The calling thread
    /// will spin-wait until previous readers finish.
    #[verus_spec]
    #[verifier::exec_allows_no_decreases_clause]
    pub fn upgrade(/* mut */ self) -> RwLockWriteGuard<'a, T, G> {
        let mut this = self;
        let lock = this.inner;
        proof! {
            use_type_invariant(&this);
            use_type_invariant(lock);
            lemma_consts_properties();
        }
        // self.inner.lock.fetch_or(BEING_UPGRADED, Acquire);
        atomic_with_ghost!(
            &lock.lock => fetch_or(BEING_UPGRADED);
            update prev -> next;
            ghost g => {
                lemma_consts_properties_prev_next(prev, next);
            }
        );
        loop {
            // self = match self.try_upgrade() {
            this = match this.try_upgrade() {
                Ok(guard) => return guard,
                Err(e) => e,
            };
        }
    }

    /// Attempts to upgrade this upread guard to a write guard atomically.
    ///
    /// This function will never spin-wait and will return immediately.
    ///
    /// This function is not exposed publicly because the `BEING_UPGRADED` bit
    /// is set only in [`Self::upgrade`].
    #[verus_spec]
    fn try_upgrade(/* mut */ self) -> Result<RwLockWriteGuard<'a, T, G>, Self> {
        proof! {
            use_type_invariant(&self);
            use_type_invariant(self.inner);
            lemma_consts_properties();
        }
        let RwLockUpgradeableGuard {
            mut guard,
            inner,
            v_perm: Tracked(guard_perm0),
            v_guard_token: Tracked(guard_token0),
            v_cell_perm_token: Tracked(cell_perm_token0),
        } = self;
        proof_decl! {
            let tracked mut write_perm: Option<PointsTo<T>> = None;
            let tracked mut guard_perm: Option<RwFrac<T>> = Some(guard_perm0);
            let tracked mut err_guard_perm: Option<RwFrac<T>> = None;
            let tracked mut guard_token: Option<UniqueToken> = Some(guard_token0);
            let tracked mut err_guard_token: Option<UniqueToken> = None;
            let tracked mut retract_upgrade_token: Option<UniqueToken> = None;
            let tracked mut left_token: Option<Left<RwFrac<T>,NoPerm<T>,V_MAX_PERM_FRACS>> = Some(cell_perm_token0);
            let tracked mut err_left_token: Option<Left<RwFrac<T>,NoPerm<T>,V_MAX_PERM_FRACS>> = None;
            let tracked mut right_token = None;
        }

        // let res = self.inner.lock.compare_exchange(
        //     UPGRADEABLE_READER | BEING_UPGRADED,
        //     WRITER | UPGRADEABLE_READER,
        //     AcqRel,
        //     Relaxed,
        // );
        let res = atomic_with_ghost!(
            inner.lock => compare_exchange(UPGRADEABLE_READER | BEING_UPGRADED, WRITER | UPGRADEABLE_READER);
            update prev -> next;
            returning res;
            ghost g => {
                lemma_consts_properties_prev_next(prev, next);
                if res is Ok {
                    g.upreader_guard_token.join(guard_token.tracked_unwrap());
                    retract_upgrade_token = Some(g.upread_retract_token.take());
                    g.cell_perm_resource.validate_with_left(left_token.tracked_borrow());
                    g.cell_perm_resource.join_left(left_token.tracked_unwrap());
                    let tracked mut rem = g.cell_perm_resource.take_resource_left();
                    rem.combine(guard_perm.tracked_unwrap());
                    let tracked (full_perm, empty) = rem.take_resource();
                    write_perm = Some(full_perm);
                    g.cell_perm_resource.change_to_right(empty);
                    right_token = Some(g.cell_perm_resource.split_right_without_resource(1int));

                } else {
                    err_guard_perm = guard_perm;
                    err_guard_token = guard_token;
                    err_left_token = left_token;
                }
            }
        );
        if res.is_ok() {
            let guard = guard.transfer_to();
            // drop(self);
            atomic_with_ghost!(
                inner.lock => fetch_sub(UPGRADEABLE_READER);
                update prev -> next;
                ghost g => {
                    let prev_usize = prev as usize;
                    let next_usize = next as usize;
                    lemma_consts_properties_value(prev_usize);
                    lemma_consts_properties_prev_next(prev_usize, next_usize);
                    let tracked token = retract_upgrade_token.tracked_unwrap();
                    let tracked mut perm = write_perm.tracked_unwrap();
                    g.upread_retract_token.join(token);
                    write_perm = Some(perm);
                }
            );
            Ok(RwLockWriteGuard { inner, guard, v_perm: Tracked(write_perm.tracked_unwrap()), v_cell_token: Tracked(right_token.tracked_unwrap()) })
        } else {
            Err(RwLockUpgradeableGuard {
                inner,
                guard,
                v_perm: Tracked(err_guard_perm.tracked_unwrap()),
                v_guard_token: Tracked(err_guard_token.tracked_unwrap()),
                v_cell_perm_token: Tracked(err_left_token.tracked_unwrap()),
            })
        }
    }

}

#[verus_verify]
impl<T /*: ?Sized*/, G: SpinGuardian> Deref for RwLockUpgradeableGuard<'_, T, G>
{
    type Target = T;

    #[verus_spec]
    fn deref(&self) -> &T {
        proof_decl! {
            let tracked read_perm = self.v_perm.borrow().borrow();
        }
        proof!{
            use_type_invariant(self);
        }
        // unsafe { &*self.inner.val.get() }
        // The internal implementation of `PCell<T>::borrow` is exactly unsafe { &(*(*self.ucell).get()) },
        // and here we verify that we have the permission to call `borrow`.
        self.inner.val.borrow(Tracked(read_perm))
    }
}
} // verus!

/*
impl<T: ?Sized, G: SpinGuardian> Drop for RwLockUpgradeableGuard<'_, T, G> {
    fn drop(&mut self) {
        self.inner.lock.fetch_sub(UPGRADEABLE_READER, Release);
    }
}*/

verus! {
#[verus_verify]
impl<T /*: ?Sized*/, G: SpinGuardian> RwLockUpgradeableGuard<'_, T, G>
{
    /// VERUS LIMITATION: We implement `drop` and call it manually because Verus's support for `Drop` is incomplete for now.
    #[verus_spec]
    pub fn drop(self) {
        proof! {
            use_type_invariant(&self);
            use_type_invariant(self.inner);
            lemma_consts_properties();
        }
        let Tracked(perm) = self.v_perm;
        let Tracked(guard_token) = self.v_guard_token;
        let Tracked(cell_perm_token) = self.v_cell_perm_token;
        //self.inner.lock.fetch_sub(UPGRADEABLE_READER, Release);
        atomic_with_ghost!(
            self.inner.lock => fetch_sub(UPGRADEABLE_READER);
            update prev -> next;
            ghost g => {
                let prev_usize = prev as usize;
                let next_usize = next as usize;
                lemma_consts_properties_value(prev_usize);
                lemma_consts_properties_prev_next(prev_usize, next_usize);
                g.upreader_guard_token.join(guard_token);
                g.cell_perm_resource.validate_with_left(&cell_perm_token);
                let tracked mut rem = g.cell_perm_resource.take_resource_left();
                rem.combine(perm);
                g.cell_perm_resource.put_resource_left(rem);
                g.cell_perm_resource.join_left(cell_perm_token);
            }
        );
    }
}
}

/*
impl<T: ?Sized + fmt::Debug, G: SpinGuardian> fmt::Debug for RwLockUpgradeableGuard<'_, T, G> {
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
        0 & MAX_READER_MASK == 0,
        0 & MAX_READER == 0,
        0 & READER == 0,
        WRITER == 0x8000_0000_0000_0000,
        UPGRADEABLE_READER == 0x4000_0000_0000_0000,
        BEING_UPGRADED == 0x2000_0000_0000_0000,
        READER_MASK == 0x0FFF_FFFF_FFFF_FFFF,
        MAX_READER_MASK == 0x1FFF_FFFF_FFFF_FFFF,
        MAX_READER == 0x1000_0000_0000_0000,
        WRITER & WRITER == WRITER,
        WRITER & !WRITER == 0,
        WRITER & BEING_UPGRADED == 0,
        WRITER & READER_MASK == 0,
        WRITER & MAX_READER_MASK == 0,
        WRITER & MAX_READER == 0,
        WRITER & UPGRADEABLE_READER == 0,
        BEING_UPGRADED & WRITER == 0,
        BEING_UPGRADED & UPGRADEABLE_READER == 0,
        UPGRADEABLE_READER & BEING_UPGRADED == 0,
        UPGRADEABLE_READER & READER_MASK == 0,
        UPGRADEABLE_READER & MAX_READER_MASK == 0,
        UPGRADEABLE_READER & MAX_READER == 0,
        BEING_UPGRADED & READER_MASK == 0,
        BEING_UPGRADED & MAX_READER_MASK == 0,
        BEING_UPGRADED & MAX_READER == 0,
        (UPGRADEABLE_READER | BEING_UPGRADED) & WRITER == 0,
        (UPGRADEABLE_READER | BEING_UPGRADED) & UPGRADEABLE_READER == UPGRADEABLE_READER,
        (UPGRADEABLE_READER | BEING_UPGRADED) & BEING_UPGRADED == BEING_UPGRADED,
        (UPGRADEABLE_READER | BEING_UPGRADED) & READER_MASK == 0,
        (UPGRADEABLE_READER | BEING_UPGRADED) & MAX_READER_MASK == 0,
        (UPGRADEABLE_READER | BEING_UPGRADED) & MAX_READER == 0,
        (WRITER | UPGRADEABLE_READER) & WRITER == WRITER,
        (WRITER | UPGRADEABLE_READER) & UPGRADEABLE_READER == UPGRADEABLE_READER,
        (WRITER | UPGRADEABLE_READER) & BEING_UPGRADED == 0,
        (WRITER | UPGRADEABLE_READER) & READER_MASK == 0,
        (WRITER | UPGRADEABLE_READER) & MAX_READER_MASK == 0,
        (WRITER | UPGRADEABLE_READER) & MAX_READER == 0,
{
    assert(0 & WRITER == 0) by (compute_only);
    assert(0 & UPGRADEABLE_READER == 0) by (compute_only);
    assert(0 & BEING_UPGRADED == 0) by (compute_only);
    assert(0 & READER_MASK == 0) by (compute_only);
    assert(0 & MAX_READER == 0) by (compute_only);
    assert(0 & MAX_READER_MASK == 0) by (compute_only);
    assert(0 & READER == 0) by (compute_only);
    assert(WRITER == 0x8000_0000_0000_0000) by (compute_only);
    assert(UPGRADEABLE_READER == 0x4000_0000_0000_0000) by (compute_only);
    assert(BEING_UPGRADED == 0x2000_0000_0000_0000) by (compute_only);
    assert(READER_MASK == 0x0FFF_FFFF_FFFF_FFFF) by (compute_only);
    assert(MAX_READER == 0x1000_0000_0000_0000) by (compute_only);
    assert(MAX_READER_MASK == 0x1FFF_FFFF_FFFF_FFFF) by (compute_only);
    assert(WRITER & WRITER == WRITER) by (compute_only);
    assert(WRITER & !WRITER == 0) by (compute_only);
    assert(WRITER & BEING_UPGRADED == 0) by (compute_only);
    assert(WRITER & READER_MASK == 0) by (compute_only);
    assert(WRITER & MAX_READER_MASK == 0) by (compute_only);
    assert(WRITER & MAX_READER == 0) by (compute_only);
    assert(WRITER & UPGRADEABLE_READER == 0) by (compute_only);
    assert(BEING_UPGRADED & WRITER == 0) by (compute_only);
    assert(BEING_UPGRADED & UPGRADEABLE_READER == 0) by (compute_only);
    assert(UPGRADEABLE_READER & BEING_UPGRADED == 0) by (compute_only);
    assert(UPGRADEABLE_READER & READER_MASK == 0) by (compute_only);
    assert(UPGRADEABLE_READER & MAX_READER_MASK == 0) by (compute_only);
    assert(UPGRADEABLE_READER & MAX_READER == 0) by (compute_only);
    assert(BEING_UPGRADED & READER_MASK == 0) by (compute_only);
    assert(BEING_UPGRADED & MAX_READER_MASK == 0) by (compute_only);
    assert(BEING_UPGRADED & MAX_READER == 0) by (compute_only);
    assert((UPGRADEABLE_READER | BEING_UPGRADED) & WRITER == 0) by (compute_only);
    assert((UPGRADEABLE_READER | BEING_UPGRADED) & UPGRADEABLE_READER == UPGRADEABLE_READER) by (compute_only);
    assert((UPGRADEABLE_READER | BEING_UPGRADED) & BEING_UPGRADED == BEING_UPGRADED) by (compute_only);
    assert((UPGRADEABLE_READER | BEING_UPGRADED) & READER_MASK == 0) by (compute_only);
    assert((UPGRADEABLE_READER | BEING_UPGRADED) & MAX_READER_MASK == 0) by (compute_only);
    assert((UPGRADEABLE_READER | BEING_UPGRADED) & MAX_READER == 0) by (compute_only);
    assert((WRITER | UPGRADEABLE_READER) & WRITER == WRITER) by (compute_only);
    assert((WRITER | UPGRADEABLE_READER) & UPGRADEABLE_READER == UPGRADEABLE_READER) by (compute_only);
    assert((WRITER | UPGRADEABLE_READER) & BEING_UPGRADED == 0) by (compute_only);
    assert((WRITER | UPGRADEABLE_READER) & READER_MASK == 0) by (compute_only);
    assert((WRITER | UPGRADEABLE_READER) & MAX_READER_MASK == 0) by (compute_only);
    assert((WRITER | UPGRADEABLE_READER) & MAX_READER == 0) by (compute_only);
}

proof fn lemma_consts_properties_value(prev: usize)
    ensures
        no_max_reader_overflow(prev) ==> prev + READER <= usize::MAX,
        prev & (WRITER | MAX_READER | BEING_UPGRADED) == 0 ==>
        {
            &&& prev & WRITER == 0
            &&& prev & BEING_UPGRADED == 0
            &&& prev & MAX_READER == 0
        },
        prev & (WRITER | UPGRADEABLE_READER) == 0 ==> {
                &&& prev & WRITER == 0
                &&& prev & UPGRADEABLE_READER == 0
        },
        prev & MAX_READER == 0 ==> prev & READER_MASK == prev & MAX_READER_MASK,
        prev & MAX_READER != 0 ==> prev & MAX_READER_MASK >= MAX_READER,
        prev & (WRITER | UPGRADEABLE_READER) == WRITER ==> {
            &&& prev & UPGRADEABLE_READER == 0
            &&& prev & WRITER == WRITER
        },
        prev & UPGRADEABLE_READER != 0 ==> prev >= UPGRADEABLE_READER,
        prev & UPGRADEABLE_READER == 0 ==> {
            ||| prev & (WRITER | UPGRADEABLE_READER) == 0
            ||| prev & (WRITER | UPGRADEABLE_READER) == WRITER
        }
{
    if no_max_reader_overflow(prev) {
        assert(prev + READER <= usize::MAX) by (bit_vector)
            requires
                prev & MAX_READER_MASK < MAX_READER_MASK,
        ;
    }
    if prev & (WRITER | MAX_READER | BEING_UPGRADED) == 0 {
        assert(prev & WRITER == 0) by (bit_vector)
            requires
                prev & (WRITER | MAX_READER | BEING_UPGRADED) == 0,
        ;
        assert(prev & BEING_UPGRADED == 0) by (bit_vector)
            requires
                prev & (WRITER | MAX_READER | BEING_UPGRADED) == 0,
        ;
        assert(prev & MAX_READER == 0) by (bit_vector)
            requires
                prev & (WRITER | MAX_READER | BEING_UPGRADED) == 0,
        ;
    }
    if prev & (WRITER | UPGRADEABLE_READER) == 0 {
        assert(prev & WRITER == 0) by (bit_vector)
            requires
                prev & (WRITER | UPGRADEABLE_READER) == 0,
        ;
        assert(prev & UPGRADEABLE_READER == 0) by (bit_vector)
            requires
                prev & (WRITER | UPGRADEABLE_READER) == 0,
        ;
    }
    if prev & MAX_READER == 0 {
        assert(prev & READER_MASK == prev & MAX_READER_MASK) by (bit_vector)
            requires
                prev & MAX_READER == 0,
        ;
    }
    if prev & MAX_READER != 0 {
        assert(prev & MAX_READER_MASK >= MAX_READER) by (bit_vector)
            requires
                prev & MAX_READER != 0,
        ;
    }
    if prev & (WRITER | UPGRADEABLE_READER) == WRITER {
        assert(prev & UPGRADEABLE_READER == 0 && prev & WRITER == WRITER) by (bit_vector)
            requires
                prev & (WRITER | UPGRADEABLE_READER) == WRITER,
        ;
    }
    if prev & UPGRADEABLE_READER != 0 {
        assert(prev >= UPGRADEABLE_READER) by (bit_vector)
            requires
                prev & UPGRADEABLE_READER != 0,
        ;
    }
    if prev & UPGRADEABLE_READER == 0 {
        assert(prev & (WRITER | UPGRADEABLE_READER) == 0 || prev & (WRITER | UPGRADEABLE_READER) == WRITER) by (bit_vector)
            requires
                prev & UPGRADEABLE_READER == 0,
        ;
    }
}

proof fn lemma_consts_properties_prev_next(prev: usize, next: usize)
    ensures
        prev & READER_MASK < MAX_READER,
        next == prev | UPGRADEABLE_READER ==> {
            &&& next & UPGRADEABLE_READER != 0
            &&& next & WRITER == prev & WRITER
            &&& next & READER_MASK == prev & READER_MASK
            &&& next & MAX_READER_MASK == prev & MAX_READER_MASK
            &&& next & MAX_READER == prev & MAX_READER
            &&& next & BEING_UPGRADED == prev & BEING_UPGRADED
        },
        next == prev | BEING_UPGRADED ==> {
            &&& next & BEING_UPGRADED != 0
            &&& next & WRITER == prev & WRITER
            &&& next & UPGRADEABLE_READER == prev & UPGRADEABLE_READER
            &&& next & READER_MASK == prev & READER_MASK
            &&& next & MAX_READER_MASK == prev & MAX_READER_MASK
            &&& next & MAX_READER == prev & MAX_READER
        },
        next == prev - UPGRADEABLE_READER && prev & UPGRADEABLE_READER != 0 ==> {
            &&& next & UPGRADEABLE_READER == 0
            &&& next & WRITER == prev & WRITER
            &&& next & READER_MASK == prev & READER_MASK
            &&& next & MAX_READER_MASK == prev & MAX_READER_MASK
            &&& next & MAX_READER == prev & MAX_READER
            &&& next & BEING_UPGRADED == prev & BEING_UPGRADED
        },
        next == prev - READER && prev & READER_MASK != 0 ==> {
            &&& next & READER_MASK == (prev & READER_MASK) - READER
            &&& next & MAX_READER_MASK == (prev & MAX_READER_MASK) - READER
            &&& next & UPGRADEABLE_READER == prev & UPGRADEABLE_READER
            &&& next & WRITER == prev & WRITER
            &&& next & MAX_READER == prev & MAX_READER
            &&& next & BEING_UPGRADED == prev & BEING_UPGRADED
        },
        next == prev - READER && prev & MAX_READER_MASK != 0 ==> {
            &&& next & MAX_READER_MASK == (prev & MAX_READER_MASK) - READER
            &&& next & UPGRADEABLE_READER == prev & UPGRADEABLE_READER
            &&& next & WRITER == prev & WRITER
            &&& next & BEING_UPGRADED == prev & BEING_UPGRADED
        },
        next == prev + READER && no_max_reader_overflow(prev) ==> {
            &&& next & READER_MASK == if (prev & READER_MASK) + READER == MAX_READER {
                0
            } else {
                (prev & READER_MASK) + READER
            }
            &&& next & MAX_READER_MASK == (prev & MAX_READER_MASK) + READER
            &&& next & UPGRADEABLE_READER == prev & UPGRADEABLE_READER
            &&& next & WRITER == prev & WRITER
            &&& next & MAX_READER == if (prev & READER_MASK) + READER == MAX_READER {
                MAX_READER
            } else {
                prev & MAX_READER
            }
            &&& next & BEING_UPGRADED == prev & BEING_UPGRADED
        },
        next == prev & !WRITER ==> {
            &&& next & WRITER == 0
            &&& next & UPGRADEABLE_READER == prev & UPGRADEABLE_READER
            &&& next & READER_MASK == prev & READER_MASK
            &&& next & MAX_READER_MASK == prev & MAX_READER_MASK
            &&& next & MAX_READER == prev & MAX_READER
            &&& next & BEING_UPGRADED == prev & BEING_UPGRADED
        }
{
    assert(prev & READER_MASK < MAX_READER) by (bit_vector);
    if next == prev | UPGRADEABLE_READER {
        assert(next & UPGRADEABLE_READER != 0) by (bit_vector)
            requires
                next == prev | UPGRADEABLE_READER,
        ;
        assert(next & WRITER == prev & WRITER) by (bit_vector)
            requires
                next == prev | UPGRADEABLE_READER,
        ;
        assert(next & READER_MASK == prev & READER_MASK) by (bit_vector)
            requires
                next == prev | UPGRADEABLE_READER,
        ;
        assert(next & MAX_READER_MASK == prev & MAX_READER_MASK) by (bit_vector)
            requires
                next == prev | UPGRADEABLE_READER,
        ;
        assert(next & MAX_READER == prev & MAX_READER) by (bit_vector)
            requires
                next == prev | UPGRADEABLE_READER,
        ;
        assert(next & BEING_UPGRADED == prev & BEING_UPGRADED) by (bit_vector)
            requires
                next == prev | UPGRADEABLE_READER,
        ;
    }
    if next == prev | BEING_UPGRADED {
        assert(next & BEING_UPGRADED != 0) by (bit_vector)
            requires
                next == prev | BEING_UPGRADED,
        ;
        assert(next & WRITER == prev & WRITER) by (bit_vector)
            requires
                next == prev | BEING_UPGRADED,
        ;
        assert(next & UPGRADEABLE_READER == prev & UPGRADEABLE_READER) by (bit_vector)
            requires
                next == prev | BEING_UPGRADED,
        ;
        assert(next & READER_MASK == prev & READER_MASK) by (bit_vector)
            requires
                next == prev | BEING_UPGRADED,
        ;
        assert(next & MAX_READER_MASK == prev & MAX_READER_MASK) by (bit_vector)
            requires
                next == prev | BEING_UPGRADED,
        ;
        assert(next & MAX_READER == prev & MAX_READER) by (bit_vector)
            requires
                next == prev | BEING_UPGRADED,
        ;
    }
    if next == prev - UPGRADEABLE_READER && prev & UPGRADEABLE_READER != 0 {
        assert(next & UPGRADEABLE_READER == 0) by (bit_vector)
            requires
                next == prev - UPGRADEABLE_READER && prev & UPGRADEABLE_READER != 0,
        ;
        assert(next & WRITER == prev & WRITER) by (bit_vector)
            requires
                next == prev - UPGRADEABLE_READER && prev & UPGRADEABLE_READER != 0,
        ;
        assert(next & READER_MASK == prev & READER_MASK) by (bit_vector)
            requires
                next == prev - UPGRADEABLE_READER && prev & UPGRADEABLE_READER != 0,
        ;
        assert(next & MAX_READER_MASK == prev & MAX_READER_MASK) by (bit_vector)
            requires
                next == prev - UPGRADEABLE_READER && prev & UPGRADEABLE_READER != 0,
        ;
        assert(next & MAX_READER == prev & MAX_READER) by (bit_vector)
            requires
                next == prev - UPGRADEABLE_READER && prev & UPGRADEABLE_READER != 0,
        ;
        assert(next & BEING_UPGRADED == prev & BEING_UPGRADED) by (bit_vector)
            requires
                next == prev - UPGRADEABLE_READER && prev & UPGRADEABLE_READER != 0,
        ;
    }
    if next == prev - READER && prev & READER_MASK != 0 {
        assert(next & READER_MASK == (prev & READER_MASK) - READER) by (bit_vector)
            requires
                next == prev - READER && prev & READER_MASK != 0,
        ;
        assert(next & MAX_READER_MASK == (prev & MAX_READER_MASK) - READER) by (bit_vector)
            requires
                next == prev - READER && prev & READER_MASK != 0,
        ;
        assert(next & UPGRADEABLE_READER == prev & UPGRADEABLE_READER) by (bit_vector)
            requires
                next == prev - READER && prev & READER_MASK != 0,
        ;
        assert(next & WRITER == prev & WRITER) by (bit_vector)
            requires
                next == prev - READER && prev & READER_MASK != 0,
        ;
        assert(next & MAX_READER == prev & MAX_READER) by (bit_vector)
            requires
                next == prev - READER && prev & READER_MASK != 0,
        ;
        assert(next & BEING_UPGRADED == prev & BEING_UPGRADED) by (bit_vector)
            requires
                next == prev - READER && prev & READER_MASK != 0,
        ;
    }
    if next == prev - READER && prev & MAX_READER_MASK != 0 {
        assert(next & MAX_READER_MASK == (prev & MAX_READER_MASK) - READER) by (bit_vector)
            requires
                next == prev - READER && prev & MAX_READER_MASK != 0,
        ;
        assert(next & UPGRADEABLE_READER == prev & UPGRADEABLE_READER) by (bit_vector)
            requires
                next == prev - READER && prev & MAX_READER_MASK != 0,
        ;
        assert(next & WRITER == prev & WRITER) by (bit_vector)
            requires
                next == prev - READER && prev & MAX_READER_MASK != 0,
        ;
        assert(next & BEING_UPGRADED == prev & BEING_UPGRADED) by (bit_vector)
            requires
                next == prev - READER && prev & MAX_READER_MASK != 0,
        ;
    }
    if next == prev + READER && prev & MAX_READER_MASK < MAX_READER_MASK {
        assert(next & READER_MASK == if prev & READER_MASK == MAX_READER - READER {
            0
        } else {
            (prev & READER_MASK) + READER
        }) by (bit_vector)
            requires
                next == prev + READER && prev & MAX_READER_MASK < MAX_READER_MASK,
        ;
        assert(next & MAX_READER_MASK == (prev & MAX_READER_MASK) + READER) by (bit_vector)
            requires
                next == prev + READER && prev & MAX_READER_MASK < MAX_READER_MASK,
        ;
        assert(next & UPGRADEABLE_READER == prev & UPGRADEABLE_READER) by (bit_vector)
            requires
                next == prev + READER && prev & MAX_READER_MASK < MAX_READER_MASK,
        ;
        assert(next & WRITER == prev & WRITER) by (bit_vector)
            requires
                next == prev + READER && prev & MAX_READER_MASK < MAX_READER_MASK,
        ;
        assert(next & MAX_READER == if (prev & READER_MASK) + READER == MAX_READER {
            MAX_READER
        } else {
            prev & MAX_READER
        }) by (bit_vector)
            requires
                next == prev + READER && prev & MAX_READER_MASK < MAX_READER_MASK,
        ;
        assert(next & BEING_UPGRADED == prev & BEING_UPGRADED) by (bit_vector)
            requires
                next == prev + READER && prev & MAX_READER_MASK < MAX_READER_MASK,
        ;
    }
    if next == prev & !WRITER {
        assert(next & WRITER == 0) by (bit_vector)
            requires
                next == prev & !WRITER,
        ;
        assert(next & UPGRADEABLE_READER == prev & UPGRADEABLE_READER) by (bit_vector)
            requires
                next == prev & !WRITER,
        ;
        assert(next & READER_MASK == prev & READER_MASK) by (bit_vector)
            requires
                next == prev & !WRITER,
        ;
        assert(next & MAX_READER_MASK == prev & MAX_READER_MASK) by (bit_vector)
            requires
                next == prev & !WRITER,
        ;
        assert(next & MAX_READER == prev & MAX_READER) by (bit_vector)
            requires
                next == prev & !WRITER,
        ;
        assert(next & BEING_UPGRADED == prev & BEING_UPGRADED) by (bit_vector)
            requires
                next == prev & !WRITER,
        ;
    }
}

} // verus!
