// SPDX-License-Identifier: MPL-2.0
use vstd::atomic_ghost::*;
use vstd::cell::{self, pcell::*, CellId};
use vstd::prelude::*;
use vstd::resource::Loc;
use vstd_extra::resource::ghost_resource::{count::*, csum::*,  excl::*, tokens::*};
use vstd_extra::sum::*;
use vstd_extra::{prelude::*, resource};

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

verus! {

const MAX_READER_U64: u64 = MAX_READER as u64;

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

/// The token reserved in the lock when the write permission is given out.
type NoPerm<T> = EmptyCount<PointsTo<T>>;

/// Half of the permission for read access, one for `RwLockUpgradeableGuard` and the other for all `RwLockReadGuard`s.
type HalfPerm<T> = Count<PointsTo<T>>;

/// The permission for read access can be further split into `MAX_READER` pieces.
type ReadPerm<T> = (HalfPerm<T>, OneLeftKnowledge<HalfPerm<T>, NoPerm<T>, 3>);

tracked struct RwPerms<T> {
    /// This token tracks whether the write permission is given out. If it is `Left`, it stores the knowledge that
    /// there are active readers because the existence of `HalfPerm` resource for read access.
    /// If it is `Right`, we know there is an active writer and there is no active reader, because there is a `NoPerm`
    /// indicating the absence of `PointsTo<T>`.
    core_token: SumResource<HalfPerm<T>, NoPerm<T>, 3>,
    /// The permission to retract a `READER` count. Its total quantity tracks the gap between
    /// the number of `try_read` increments recorded in the lock atomic and the number of active
    /// `RwLockReadGuard`s (created and ongoing creation that will succeed) represented by `read_guard_token`.
    /// It can be splited up to `V_MAX_READ_RETRACT_FRACS:= 2 * MAX_READER` pieces,
    /// which allows at most `2*MAX_READER - 1` `try_read` attempts that will fail to acquire the lock.
    read_retract_token: TokenResource<V_MAX_READ_RETRACT_FRACS>,
    /// The permission to retract the set of `UPGRADEABLE_READER` bit.
    upread_retract_token: Option<UniqueToken>,
    /// Tracks whether there is a live `RwLockUpgradeableGuard`, also stores half of the permission for read access.
    upreader_guard_token: Option<OneLeftOwner<HalfPerm<T>, NoPerm<T>, 3>>,
    /// Tracks the number of live `RwLockReadGuard`s. If it is `Left`, it stores the remaining read permissions.
    /// If it is `Right`, it stores an empty token indicating the permission has been given out.
    read_guard_token: Sum<
        CountResource<ReadPerm<T>, MAX_READER_U64>,
        EmptyCount<ReadPerm<T>, MAX_READER_U64>,
    >,
}

ghost struct RwId {
    core_token_id: Loc,
    frac_id: Loc,
    read_retract_token_id: Loc,
    upread_retract_token_id: Loc,
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
        let active_writer: bool = g.core_token.is_right();
        // The number of active `RwLockUpgradeableGuard`, which can only be 0 or 1.
        let active_upgrade_guard: bool = !active_writer && g.upreader_guard_token is None;
        // The number of active `RwLockReadGuard`s.
        let active_read_guards: int = if g.read_guard_token is Left {
            MAX_READER_U64 - g.read_guard_token.left().frac()
        } else {
            0
        };
        // The first `try_upread` that fails, which has not returned yet.
        let pending_failed_upread_attempt: bool = g.upread_retract_token is None;
        // The number of `try_read` attempts that will fail.
        let failed_reader_attempts: int = V_MAX_READ_RETRACT_FRACS - g.read_retract_token.frac();

        &&& if g.core_token.is_left() {
            g.read_guard_token is Left
        } else {
            &&& g.upreader_guard_token is None
            &&& g.read_guard_token is Right
        }
        // The `UPGRADEABLE_READER` bit is set iff there is an active `RwLockUpgradeableGuard` or a pending failed `try_upread` attempt.
        &&& has_upgrade_bit <==> (active_upgrade_guard || pending_failed_upread_attempt)
        // An active `RwLockUpgradeableGuard` cannot coexist with a pending failed `try_upread` attempt.
        &&& !(active_upgrade_guard && pending_failed_upread_attempt)
        // The `READER` bits count the number of all active read guards and pending failed `try_read` attempts.
        &&& total_reader_bits == active_read_guards + failed_reader_attempts
        // There is an active `RwLockWriteGuard` iff the `WRITER` bit is set.
        &&& active_writer <==> has_writer_bit
        // The number of active `RwLockReadGaurd`s is less than or equal to the `READER` bits.
        &&& 0 <= active_read_guards <= reader_bits <= total_reader_bits
        // The core invariant of `RwLock`: there are no simultaneous active writers and readers.
        &&& !(active_writer && (active_read_guards + if active_upgrade_guard { 1int } else { 0 }) > 0)
        &&& g.core_token.id() == v_id@.core_token_id
        &&& g.core_token.wf()
        &&& g.core_token.is_left() ==> {
            &&& !g.core_token.is_resource_owner()
            &&& g.core_token.frac() == 1
        }
        &&& g.core_token.is_right() ==> {
            let empty = g.core_token.resource_right();
            &&& empty.id() == v_id@.frac_id
            &&& g.core_token.frac() == 2
            &&& g.core_token.has_resource()
        }
        &&& g.read_retract_token.wf()
        &&& g.read_retract_token.id() == v_id@.read_retract_token_id
        &&& g.upread_retract_token is Some ==>
            {
                let token = g.upread_retract_token->Some_0;
                &&& token.wf()
                &&& token.id() == v_id@.upread_retract_token_id
            }
        &&& g.upreader_guard_token is Some ==> {
            let token = g.upreader_guard_token->Some_0;
            wf_upgradeable_guard_token(v_id@.core_token_id, v_id@.frac_id, val.id(), token)
        }
        &&& match g.read_guard_token {
            Sum::Left(token) => {
                &&& token.wf()
                &&& token.id() == v_id@.read_guard_token_id
                &&& token.not_empty() ==> {
                    let resource = token.resource();
                    let read_half_cell_perm = resource.0;
                    let mode_knowledge = resource.1;
                    &&& mode_knowledge.id() == v_id@.core_token_id
                    &&& read_half_cell_perm.id() == v_id@.frac_id
                    &&& read_half_cell_perm.resource().id() == val.id()
                    &&& read_half_cell_perm.frac() == 1
                }
            },
            Sum::Right(empty) => {
                &&& empty.id() == v_id@.read_guard_token_id
            },
        }

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

    pub closed spec fn core_token_id(self) -> Loc {
        self.v_id@.core_token_id
    }

    pub closed spec fn frac_id(self) -> Loc {
        self.v_id@.frac_id
    }

    pub closed spec fn upread_retract_token_id(self) -> Loc {
        self.v_id@.upread_retract_token_id
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

closed spec fn wf_upgradeable_guard_token<T>(
    core_token_id: Loc,
    frac_id: Loc,
    cell_id: CellId,
    token: OneLeftOwner<HalfPerm<T>, NoPerm<T>, 3>,
) -> bool {
    let half_cell_perm = token.resource();
    &&& token.id() == core_token_id
    &&& half_cell_perm.id() == frac_id
    &&& half_cell_perm.resource().id() == cell_id
    &&& token.has_resource()
    &&& half_cell_perm.frac() == 1
    &&& token.wf()
}

impl<T, G> RwLock<T, G> {
    /// Creates a new spin-based read-write lock with an initial value.
    pub const fn new(val: T) -> Self {
        let (val, Tracked(perm)) = PCell::new(val);

        // Proof code
        proof {
            lemma_consts_properties();
        }
        let tracked mut frac_perm = Count::<PointsTo<T>>::new(perm);
        let tracked read_half_cell_perm = frac_perm.split(1int);
        let ghost frac_id = frac_perm.id();
        let tracked mut core_token = SumResource::alloc_left(frac_perm);
        let tracked read_retract_token = TokenResource::<V_MAX_READ_RETRACT_FRACS>::alloc(());
        let tracked upread_retract_token = UniqueToken::alloc(());
        let tracked upreader_guard_token = core_token.split_one_left_owner();
        let tracked left_token = core_token.split_one_left_knowledge();
        let tracked read_guard_token = CountResource::<ReadPerm<T>, MAX_READER_U64>::alloc(
            (read_half_cell_perm, left_token),
        );
        let ghost v_id = RwId {
            frac_id,
            core_token_id: core_token.id(),
            upread_retract_token_id: upread_retract_token.id(),
            read_retract_token_id: read_retract_token.id(),
            read_guard_token_id: read_guard_token.id(),
        };
        let tracked perms = RwPerms {
            core_token,
            read_retract_token,
            upread_retract_token: Some(upread_retract_token),
            upreader_guard_token: Some(upreader_guard_token),
            read_guard_token: Sum::Left(read_guard_token),
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
    pub fn read(&self) -> RwLockReadGuard<'_, T, G> {
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
    pub fn write(&self) -> RwLockWriteGuard<'_, T, G> {
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
    pub fn upread(&self) -> RwLockUpgradeableGuard<'_, T, G> {
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
    pub fn try_read(&self) -> Option<RwLockReadGuard<'_, T, G>> {
        proof_decl!{
            let tracked mut read_token: Option<Count<ReadPerm<T>,MAX_READER_U64>> = None;
            let tracked mut retract_read_token: Option<Token<V_MAX_READ_RETRACT_FRACS>> = None;
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
                    let tracked mut tmp = g.read_guard_token.tracked_take_left();
                    read_token = Some(tmp.split_one());
                    g.read_guard_token = Sum::Left(tmp);
                } else {
                    retract_read_token = Some(g.read_retract_token.split_one());
                }
            }
        );
        if lock & (WRITER | MAX_READER | BEING_UPGRADED) == 0 {
            Some(
                RwLockReadGuard {
                    inner: self,
                    guard,
                    v_token: Tracked(read_token.tracked_unwrap())
                },
            )
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
                    g.read_retract_token.combine(retract_read_token.tracked_unwrap());
                }
            );
            None
        }
    }

    /// Attempts to acquire a write lock.
    ///
    /// This function will never spin-wait and will return immediately.
    #[verus_spec]
    pub fn try_write(&self) -> Option<RwLockWriteGuard<'_, T, G>> {
        proof_decl!{
            let tracked mut guard_perm: Option<PointsTo<T>> = None;
            let tracked mut guard_token: Option<OneRightKnowledge<HalfPerm<T>, NoPerm<T>, 3>> = None;
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
            update prev -> next;
            returning res;
            ghost g => {
                let prev_usize = prev as usize;
                let next_usize = next as usize;
                if res is Ok {
                    // Retract the fractional permission for read access.
                    let tracked read_guard_token = g.read_guard_token.tracked_take_left();
                    let tracked (read_resource, read_empty) = read_guard_token.take_resource();
                    g.read_guard_token = Sum::Right(read_empty);
                    let tracked (read_half_cell_perm, left_token) = read_resource;
                    g.core_token.join_one_left_knowledge(left_token);
                    // Retract the fractional permission for upgradeable reader.
                    let tracked upreader_guard_token = g.upreader_guard_token.tracked_take();
                    g.core_token.join_one_left_owner(upreader_guard_token);
                    // Combine the two halves of the permission for read access to get the full permission and give it out.
                    let tracked mut pointsto = g.core_token.take_resource_left();
                    pointsto.combine(read_half_cell_perm);
                    let tracked (pointsto, empty) = pointsto.take_resource();
                    guard_perm = Some(pointsto);
                    g.core_token.change_to_right(empty);
                    guard_token = Some(g.core_token.split_one_right_knowledge());
                }
            }
        ).is_ok() {
            Some(
                RwLockWriteGuard {
                    inner: self,
                    guard,
                    v_perm: Tracked(guard_perm.tracked_unwrap()),
                    v_token: Tracked(guard_token.tracked_unwrap()),
                },
            )
        } else {
            None
        }
    }

    /// Attempts to acquire an upread lock.
    ///
    /// This function will never spin-wait and will return immediately.
    pub fn try_upread(&self) -> Option<RwLockUpgradeableGuard<'_, T, G>> {
        proof_decl!{
            let tracked mut upgrade_guard_token: Option<OneLeftOwner<HalfPerm<T>, NoPerm<T>, 3>> = None;
            let tracked mut retract_upgrade_token: Option<UniqueToken> = None;
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
                    upgrade_guard_token = Some(g.upreader_guard_token.tracked_take());
                }
                else if prev & (WRITER | UPGRADEABLE_READER) == WRITER {
                    retract_upgrade_token = Some(g.upread_retract_token.tracked_take());
                }
            }
        )
            & (WRITER | UPGRADEABLE_READER);
        if lock == 0 {
            return Some(
                RwLockUpgradeableGuard {
                    inner: self,
                    guard,
                    v_token: Tracked(upgrade_guard_token.tracked_unwrap())
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
                    if g.upread_retract_token is Some {
                        let tracked mut token = retract_upgrade_token.tracked_unwrap();
                        token.validate_with_other(g.upread_retract_token.tracked_borrow());
                    }
                    else{
                        g.upread_retract_token= retract_upgrade_token;
                    }
                }
            );
        }
        None
    }
}

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
unsafe impl<T: Send, G> Send for RwLock<T, G> {

}

#[verifier::external]
unsafe impl<T: Send + Sync, G> Sync for RwLock<T, G> {

}

impl<T  /*: ?Sized*/ , G: SpinGuardian> !Send for RwLockWriteGuard<'_, T, G> {

}

#[verifier::external]
unsafe impl<T: Sync, G: SpinGuardian> Sync for RwLockWriteGuard<'_, T, G> {

}

impl<T  /*: ?Sized*/ , G: SpinGuardian> !Send for RwLockReadGuard<'_, T, G> {

}

#[verifier::external]
unsafe impl<T: Sync, G: SpinGuardian> Sync for RwLockReadGuard<'_, T, G> {

}

impl<T  /*: ?Sized*/ , G: SpinGuardian> !Send for RwLockUpgradeableGuard<'_, T, G> {

}

#[verifier::external]
unsafe impl<T: Sync, G: SpinGuardian> Sync for RwLockUpgradeableGuard<'_, T, G> {

}

/// A guard that provides immutable data access.
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(G)]
#[clippy::has_significant_drop]
#[must_use]
#[verus_verify]
pub struct RwLockReadGuard<'a, T /*: ?Sized*/, G: SpinGuardian> {
    guard: G::ReadGuard,
    inner: &'a RwLock<T, G>,
    v_token: Tracked<Count<ReadPerm<T>, MAX_READER_U64>>,
}

/*
impl<T: ?Sized, G: SpinGuardian> AsAtomicModeGuard for RwLockReadGuard<'_, T, G> {
    fn as_atomic_mode_guard(&self) -> &dyn crate::task::atomic_mode::InAtomicMode {
        self.guard.as_atomic_mode_guard()
    }
}
*/

impl<'a, T, G: SpinGuardian> RwLockReadGuard<'a, T, G> {
    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        let resource = self.v_token@.resource();
        let read_half_cell_perm = resource.0;
        let mode_knowledge = resource.1;
        &&& self.inner.core_token_id() == mode_knowledge.id()
        &&& self.inner.frac_id() == read_half_cell_perm.id()
        &&& self.inner.cell_id() == read_half_cell_perm.resource().id()
        &&& self.v_token@.id() == self.inner.read_guard_token_id()
        &&& read_half_cell_perm.frac() == 1
        &&& self.v_token@.frac() == 1
    }

    /// The value stored in the lock.
    pub closed spec fn value(self) -> T {
        *self.v_token@.resource().0.resource().value()
    }

    /// The value stored in the lock. It is an alias of `Self::value`.
    pub open spec fn view(self) -> T {
        self.value()
    }

    /// Borrows the inner value in tracked mode.
    #[verifier::external_body]
    pub proof fn tracked_borrow(tracked &self) -> (tracked r: &'a T)
        returns
            self.view(),
    {
        unimplemented!()
    }
}

impl<T  /*: ?Sized*/ , G: SpinGuardian> Deref for RwLockReadGuard<'_, T, G> {
    type Target = T;

    #[verus_spec(returns self.view())]
    fn deref(&self) -> &T {
        proof!{
            use_type_invariant(self);
        }
        // unsafe { &*self.inner.val.get() }
        // The internal implementation of `PCell<T>::borrow` is exactly unsafe { &(*(*self.ucell).get()) },
        // and here we verify that we have the permission to call `borrow`.
        self.inner.val.borrow(Tracked(self.v_token.borrow().borrow().0.borrow()))
    }
}

/* impl<T: ?Sized, R: Deref<Target = RwLock<T, G>> + Clone, G: SpinGuardian> Drop
    for RwLockReadGuard_<T, R, G>
{
    fn drop(&mut self) {
        self.inner.lock.fetch_sub(READER, Release);
    }
} */

#[verus_verify]
impl<T  /*: ?Sized*/ , G: SpinGuardian> RwLockReadGuard<'_, T, G> {
    /// VERUS LIMITATION: We implement `drop` and call it manually because Verus's support for `Drop` is incomplete for now.
    #[verus_spec]
    fn drop(self) {
        proof! {
            use_type_invariant(&self);
            use_type_invariant(self.inner);
            lemma_consts_properties();
        }
        proof_decl! {
            let tracked token = self.v_token.get();
        }
        // self.inner.lock.fetch_sub(READER, Release);
        atomic_with_ghost!(
            self.inner.lock => fetch_sub(READER);
            update prev -> next;
            ghost g => {
                let prev_usize = prev as usize;
                let next_usize = next as usize;
                assume (no_max_reader_overflow(prev_usize));
                lemma_consts_properties_value(next_usize);
                lemma_consts_properties_prev_next(prev_usize, next_usize);
                g.core_token.validate_with_one_left_knowledge(&token.borrow().1);
                let tracked mut tmp = g.read_guard_token.tracked_take_left();
                tmp.combine(token);
                g.read_guard_token = Sum::Left(tmp);
            }
        );
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
pub struct RwLockWriteGuard<'a, T  /*: ?Sized*/ , G: SpinGuardian> {
    guard: G::Guard,
    inner: &'a RwLock<T, G>,
    /// Ghost permission for verification
    v_perm: Tracked<PointsTo<T>>,
    v_token: Tracked<OneRightKnowledge<HalfPerm<T>, NoPerm<T>, 3>>,
}

impl<'a, T, G: SpinGuardian> RwLockWriteGuard<'a, T, G> {
    #[verifier::type_invariant]
    spec fn type_inv(self) -> bool {
        &&& self.inner.cell_id() == self.v_perm@.id()
        &&& self.inner.core_token_id() == self.v_token@.id()
    }

    /// The value stored in the lock.
    pub closed spec fn value(self) -> T {
        *self.v_perm@.value()
    }

    /// The value stored in the lock. It is an alias of `Self::value`.
    pub open spec fn view(self) -> T {
        self.value()
    }

    /// Borrows the inner value in tracked mode.
    #[verifier::external_body]
    pub proof fn tracked_borrow(tracked &self) -> (tracked r: &'a T)
        returns
            self.view(),
    {
        unimplemented!()
    }
}

/*
impl<T: ?Sized, G: SpinGuardian> AsAtomicModeGuard for RwLockWriteGuard<'_, T, G> {
    fn as_atomic_mode_guard(&self) -> &dyn crate::task::atomic_mode::InAtomicMode {
        self.guard.as_atomic_mode_guard()
    }
}*/

impl<T  /*: ?Sized*/ , G: SpinGuardian> Deref for RwLockWriteGuard<'_, T, G> {
    type Target = T;

    #[verus_spec(returns self.view())]
    fn deref(&self) -> &T {
        proof!{
            use_type_invariant(self);
        }
        // unsafe { &*self.inner.val.get() }
        // The internal implementation of `PCell<T>::borrow` is exactly unsafe { &(*(*self.ucell).get()) },
        // and here we verify that we have the permission to call `borrow`.
        self.inner.val.borrow(Tracked(self.v_perm.borrow()))
    }
}

#[verus_verify]
impl<T  /*: ?Sized*/ , G: SpinGuardian> DerefMut for RwLockWriteGuard<'_, T, G> {
    #[verus_spec(ret =>
        ensures
            final(self).view() == *final(ret),
    )]
    fn deref_mut(&mut self) -> &mut Self::Target 
    {
        proof!{
            use_type_invariant(&*self);
        }
        //unsafe { &mut *self.inner.val.get() }
        pcell_borrow_mut(&self.inner.val, &mut self.v_perm)
    }
}

/*
impl<T: ?Sized, G: SpinGuardian> Drop for RwLockWriteGuard<'_, T, G> {
    fn drop(&mut self) {
        self.inner.lock.fetch_and(!WRITER, Release);
    }
}*/

impl<T  /*: ?Sized*/ , G: SpinGuardian> RwLockWriteGuard<'_, T, G> {
    /// VERUS LIMITATION: We implement `drop` and call it manually because Verus's support for `Drop` is incomplete for now.
    pub fn drop(self) {
        proof!{
            use_type_invariant(&self);
            use_type_invariant(self.inner);
            lemma_consts_properties();
        }
        proof_decl! {
            let tracked mut perm = self.v_perm.get();
            let tracked token = self.v_token.get();
        }
        //self.inner.lock.fetch_and(!WRITER, Release);
        atomic_with_ghost!{
            self.inner.lock => fetch_and(!WRITER);
            update prev -> next;
            ghost g => {
                let prev_usize = prev as usize;
                let next_usize = next as usize;
                lemma_consts_properties_prev_next(prev_usize, next_usize);
                lemma_consts_properties_value(next_usize);
                g.core_token.validate_with_one_right_knowledge(&token);
                g.core_token.join_one_right_knowledge(token);
                let tracked empty = g.core_token.take_resource_right();
                let tracked mut full = empty.put_resource(perm);
                let tracked read_half_cell_perm = full.split(1int);
                g.core_token.change_to_left(full);
                let tracked upreader_guard_token = g.core_token.split_one_left_owner();
                g.upreader_guard_token = Some(upreader_guard_token);
                let tracked left_token = g.core_token.split_one_left_knowledge();
                let tracked read_guard_empty = g.read_guard_token.tracked_take_right();
                let tracked read_guard_token = CountResource::alloc_from_empty(
                    read_guard_empty,
                    (read_half_cell_perm, left_token),
                );
                g.read_guard_token = Sum::Left(read_guard_token);
            }
        };
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
pub struct RwLockUpgradeableGuard<'a, T  /*: ?Sized*/ , G: SpinGuardian> {
    guard: G::Guard,
    inner: &'a RwLock<T, G>,
    v_token: Tracked<OneLeftOwner<HalfPerm<T>, NoPerm<T>, 3>>,
}

/*
impl<T: ?Sized, G: SpinGuardian> AsAtomicModeGuard for RwLockUpgradeableGuard<'_, T, G> {
    fn as_atomic_mode_guard(&self) -> &dyn crate::task::atomic_mode::InAtomicMode {
        self.guard.as_atomic_mode_guard()
    }
}*/

impl<'a, T, G: SpinGuardian> RwLockUpgradeableGuard<'a, T, G> {
    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        wf_upgradeable_guard_token(
            self.inner.core_token_id(),
            self.inner.frac_id(),
            self.inner.cell_id(),
            self.v_token@,
        )
    }

    /// The value stored in the lock.
    pub closed spec fn value(self) -> T {
        *self.v_token@.resource().resource().value()
    }

    /// The value stored in the lock. It is an alias of `Self::value`.
    pub open spec fn view(self) -> T {
        self.value()
    }
}

impl<'a, T  /*: ?Sized*/ , G: SpinGuardian> RwLockUpgradeableGuard<'a, T, G> {
    /// Upgrades this upread guard to a write guard atomically.
    ///
    /// After calling this method, subsequent readers will be blocked
    /// while previous readers remain unaffected. The calling thread
    /// will spin-wait until previous readers finish.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn upgrade(  /* mut */ self) -> RwLockWriteGuard<'a, T, G> {
        let mut this = self;
        proof! {
            use_type_invariant(&this);
            use_type_invariant(&this.inner);
            lemma_consts_properties();
        }
        // self.inner.lock.fetch_or(BEING_UPGRADED, Acquire);
        atomic_with_ghost!(
            this.inner.lock => fetch_or(BEING_UPGRADED);
            update prev -> next;
            ghost g => {
                lemma_consts_properties_prev_next(prev, next);
            }
        );
        loop {
            // self = match self.try_upgrade() {
            this =
            match this.try_upgrade() {
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
    fn try_upgrade(  /* mut */ self) -> Result<RwLockWriteGuard<'a, T, G>, Self> {
        proof! {
            use_type_invariant(&self);
            use_type_invariant(self.inner);
            lemma_consts_properties();
        }
        let mut this = self;
        proof_decl! {
            let tracked mut upread_guard_token = this.v_token.get();
            let tracked mut write_perm: Option<PointsTo<T>> = None;
            let tracked mut err_upread_guard_token: Option<OneLeftOwner<HalfPerm<T>, NoPerm<T>, 3>> = None;
            let tracked mut retract_upgrade_token: Option<UniqueToken> = None;
            let tracked mut write_guard_token = None;
        }

        // let res = self.inner.lock.compare_exchange(
        //     UPGRADEABLE_READER | BEING_UPGRADED,
        //     WRITER | UPGRADEABLE_READER,
        //     AcqRel,
        //     Relaxed,
        // );
        let res =
            atomic_with_ghost!(
            this.inner.lock => compare_exchange(UPGRADEABLE_READER | BEING_UPGRADED, WRITER | UPGRADEABLE_READER);
            update prev -> next;
            returning res;
            ghost g => {
                lemma_consts_properties_prev_next(prev, next);
                if res is Ok {
                    g.core_token.validate_with_one_left_owner(&upread_guard_token);
                    if g.upreader_guard_token is Some {
                        upread_guard_token.validate_with_one_left_owner(g.upreader_guard_token.tracked_borrow());
                    }
                    g.core_token.join_one_left_owner(upread_guard_token);
                    let tracked read_guard_token = g.read_guard_token.tracked_take_left();
                    let tracked (read_resource, read_empty) = read_guard_token.take_resource();
                    g.read_guard_token = Sum::Right(read_empty);
                    let tracked (read_half_cell_perm, left_token) = read_resource;
                    g.core_token.join_one_left_knowledge(left_token);
                    let tracked mut pointsto = g.core_token.take_resource_left();
                    pointsto.combine(read_half_cell_perm);
                    let tracked (pointsto, empty) = pointsto.take_resource();
                    write_perm = Some(pointsto);
                    g.core_token.change_to_right(empty);
                    write_guard_token = Some(g.core_token.split_one_right_knowledge());
                    retract_upgrade_token = Some(g.upread_retract_token.tracked_take());
                } else {
                    err_upread_guard_token = Some(upread_guard_token);
                }
            }
        );
        if res.is_ok() {
            let inner = this.inner;
            let guard = this.guard.transfer_to();
            // drop(self);
            atomic_with_ghost!(
                inner.lock => fetch_sub(UPGRADEABLE_READER);
                update prev -> next;
                ghost g => {
                    let prev_usize = prev as usize;
                    let next_usize = next as usize;
                    lemma_consts_properties_value(prev_usize);
                    lemma_consts_properties_prev_next(prev_usize, next_usize);
                    let tracked mut token = retract_upgrade_token.tracked_unwrap();
                    if g.upread_retract_token is Some {
                        token.validate_with_other(g.upread_retract_token.tracked_borrow());
                    }
                    g.upread_retract_token = Some(token);
                }
            );
            Ok(
                RwLockWriteGuard {
                    inner,
                    guard,
                    v_perm: Tracked(write_perm.tracked_unwrap()),
                    v_token: Tracked(write_guard_token.tracked_unwrap()),
                },
            )
        } else {
            Err(       
                RwLockUpgradeableGuard {
                    inner: this.inner,
                    guard: this.guard,
                    v_token: Tracked(err_upread_guard_token.tracked_unwrap()),
                },
            )
        }
    }
}

impl<T  /*: ?Sized*/ , G: SpinGuardian> Deref for RwLockUpgradeableGuard<'_, T, G> {
    type Target = T;

    #[verus_spec(returns self.view())]
    fn deref(&self) -> &T {
        proof!{
            use_type_invariant(self);
        }
        // unsafe { &*self.inner.val.get() }
        // The internal implementation of `PCell<T>::borrow` is exactly unsafe { &(*(*self.ucell).get()) },
        // and here we verify that we have the permission to call `borrow`.
        self.inner.val.borrow(Tracked(self.v_token.borrow().tracked_borrow().borrow()))
    }
}

/*
impl<T: ?Sized, G: SpinGuardian> Drop for RwLockUpgradeableGuard<'_, T, G> {
    fn drop(&mut self) {
        self.inner.lock.fetch_sub(UPGRADEABLE_READER, Release);
    }
}*/

impl<T  /*: ?Sized*/ , G: SpinGuardian> RwLockUpgradeableGuard<'_, T, G> {
    /// VERUS LIMITATION: We implement `drop` and call it manually because Verus's support for `Drop` is incomplete for now.
    pub fn drop(self) {
        proof! {
            use_type_invariant(&self);
            use_type_invariant(self.inner);
            lemma_consts_properties();
        }
        proof_decl!{
            let tracked guard_token = self.v_token.get();
        }
        //self.inner.lock.fetch_sub(UPGRADEABLE_READER, Release);
        atomic_with_ghost!(
            self.inner.lock => fetch_sub(UPGRADEABLE_READER);
            update prev -> next;
            ghost g => {
                let prev_usize = prev as usize;
                let next_usize = next as usize;
                lemma_consts_properties_value(prev_usize);
                lemma_consts_properties_prev_next(prev_usize, next_usize);
                g.core_token.validate_with_one_left_owner(&guard_token);
                if g.upreader_guard_token is Some {
                    guard_token.validate_with_one_left_owner(g.upreader_guard_token.tracked_borrow());
                    assert(false);
                } else {
                    g.upreader_guard_token= Some(guard_token);
                }
            }
        );
    }
}

/*
impl<T: ?Sized + fmt::Debug, G: SpinGuardian> fmt::Debug for RwLockUpgradeableGuard<'_, T, G> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}
*/

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
    assert((UPGRADEABLE_READER | BEING_UPGRADED) & UPGRADEABLE_READER == UPGRADEABLE_READER)
        by (compute_only);
    assert((UPGRADEABLE_READER | BEING_UPGRADED) & BEING_UPGRADED == BEING_UPGRADED)
        by (compute_only);
    assert((UPGRADEABLE_READER | BEING_UPGRADED) & READER_MASK == 0) by (compute_only);
    assert((UPGRADEABLE_READER | BEING_UPGRADED) & MAX_READER_MASK == 0) by (compute_only);
    assert((UPGRADEABLE_READER | BEING_UPGRADED) & MAX_READER == 0) by (compute_only);
    assert((WRITER | UPGRADEABLE_READER) & WRITER == WRITER) by (compute_only);
    assert((WRITER | UPGRADEABLE_READER) & UPGRADEABLE_READER == UPGRADEABLE_READER)
        by (compute_only);
    assert((WRITER | UPGRADEABLE_READER) & BEING_UPGRADED == 0) by (compute_only);
    assert((WRITER | UPGRADEABLE_READER) & READER_MASK == 0) by (compute_only);
    assert((WRITER | UPGRADEABLE_READER) & MAX_READER_MASK == 0) by (compute_only);
    assert((WRITER | UPGRADEABLE_READER) & MAX_READER == 0) by (compute_only);
}

proof fn lemma_consts_properties_value(prev: usize)
    ensures
        no_max_reader_overflow(prev) ==> prev + READER <= usize::MAX,
        prev & (WRITER | MAX_READER | BEING_UPGRADED) == 0 ==> {
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
        },
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
        assert(prev & (WRITER | UPGRADEABLE_READER) == 0 || prev & (WRITER | UPGRADEABLE_READER)
            == WRITER) by (bit_vector)
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
        },
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
