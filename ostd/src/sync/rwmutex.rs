// SPDX-License-Identifier: MPL-2.0

use vstd::atomic_ghost::*;
use vstd::cell::{self, pcell::*, CellId};
use vstd::pcm::Loc;
use vstd::prelude::*;
use vstd::tokens::frac::{Empty, Frac};
use vstd_extra::resource::ghost_resource::{csum::*, excl::*, tokens::*};
use vstd_extra::sum::*;

use core::{
    cell::UnsafeCell,
    ops::{Deref, DerefMut},
    sync::atomic::{
        // AtomicUsize,
        Ordering::{AcqRel, Acquire, Relaxed, Release},
    },
};

use super::WaitQueue;

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

type NoPerm<T> = Empty<PointsTo<T>>;
type HalfPerm<T> = Frac<PointsTo<T>>;
type ReadPerm<T> = (HalfPerm<T>, OneLeftKnowledge<HalfPerm<T>, NoPerm<T>, 3>);

tracked struct RwPerms<T> {
    core_token: SumResource<HalfPerm<T>, NoPerm<T>, 3>,
    read_retract_token: TokenResource<V_MAX_READ_RETRACT_FRACS>,
    upread_retract_token: Option<UniqueToken>,
    upreader_guard_token: Option<OneLeftOwner<HalfPerm<T>, NoPerm<T>, 3>>,
    read_guard_token: Sum<
        FracResource<ReadPerm<T>, MAX_READER_U64>,
        Empty<ReadPerm<T>, MAX_READER_U64>,
    >,
}

ghost struct RwId {
    core_token_id: Loc,
    frac_id: Loc,
    read_retract_token_id: Loc,
    upread_retract_token_id: Loc,
    read_guard_token_id: Loc,
}

#[verifier::reject_recursive_types(T)]
struct_with_invariants! {
/// A mutex that provides data access to either one writer or many readers.
///
/// # Overview
///
/// This mutex allows for multiple readers, or at most one writer to access
/// at any point in time. The writer of this mutex has exclusive access to
/// modify the underlying data, while the readers are allowed shared and
/// read-only access.
///
/// The writing and reading portions cannot be active simultaneously, when
/// one portion is in progress, the other portion will sleep. This is
/// suitable for scenarios where the mutex is expected to be held for a
/// period of time, which can avoid wasting CPU resources.
///
/// This implementation provides the upgradeable read mutex (`upread mutex`).
/// The `upread mutex` can be upgraded to write mutex atomically, useful in
/// scenarios where a decision to write is made after reading.
///
/// The type parameter `T` represents the data that this mutex is protecting.
/// It is necessary for `T` to satisfy [`Send`] to be shared across tasks and
/// [`Sync`] to permit concurrent access via readers. The [`Deref`] method (and
/// [`DerefMut`] for the writer) is implemented for the RAII guards returned
/// by the locking methods, which allows for the access to the protected data
/// while the mutex is held.
///
/// # Usage
///
/// The mutex can be used in scenarios where data needs to be read frequently
/// but written to occasionally.
///
/// Use `upread mutex` in scenarios where related checking is performed before
/// modification to effectively avoid deadlocks and improve efficiency.
///
/// # Safety
///
/// Avoid using `RwMutex` in an interrupt context, as it may result in sleeping
/// and never being awakened.
///
/// # Examples
///
/// ```
/// use ostd::sync::RwMutex;
///
/// let mutex = RwMutex::new(5)
///
/// // many read mutexes can be held at once
/// {
///     let r1 = mutex.read();
///     let r2 = mutex.read();
///     assert_eq!(*r1, 5);
///     assert_eq!(*r2, 5);
///     
///     // Upgradeable read mutex can share access to data with read mutexes
///     let r3 = mutex.upread();
///     assert_eq!(*r3, 5);
///     drop(r1);
///     drop(r2);
///     // read mutexes are dropped at this point
///
///     // An upread mutex can only be upgraded successfully after all the
///     // read mutexes are released, otherwise it will spin-wait.
///     let mut w1 = r3.upgrade();
///     *w1 += 1;
///     assert_eq!(*w1, 6);
/// }   // upread mutex are dropped at this point
///
/// {   
///     // Only one write mutex can be held at a time
///     let mut w2 = mutex.write();
///     *w2 += 1;
///     assert_eq!(*w2, 7);
/// }   // write mutex is dropped at this point
/// ```
pub struct RwMutex<T /*: ?Sized*/> {
    /// The internal representation of the mutex state is as follows:
    /// - **Bit 63:** Writer mutex.
    /// - **Bit 62:** Upgradeable reader mutex.
    /// - **Bit 61:** Indicates if an upgradeable reader is being upgraded.
    /// - **Bits 60-0:** Reader mutex count.
    lock: AtomicUsize<_, RwPerms<T>, _>,
    /// Threads that fail to acquire the mutex will sleep on this waitqueue.
    queue: WaitQueue,
    // val: UnsafeCell<T>,
    val: PCell<T>,
    v_id: Ghost<RwId>,
}

closed spec fn wf(self) -> bool {
    invariant on lock with (val, v_id) is (v: usize, g: RwPerms<T>) {
        let has_writer_bit: bool = (v & WRITER) != 0;
        let has_upgrade_bit: bool = (v & UPGRADEABLE_READER) != 0;
        let has_max_reader_bit: bool = (v & MAX_READER) != 0;
        let total_reader_bits: int = (v & MAX_READER_MASK) as int;
        let reader_bits: int = if has_max_reader_bit {
            MAX_READER as int
        } else {
            (v & READER_MASK) as int
        };

        let active_writer: bool = g.core_token.is_right();
        let active_upgrade_guard: bool = !active_writer && g.upreader_guard_token is None;
        let active_read_guards: int = if g.read_guard_token is Left {
            MAX_READER_U64 - g.read_guard_token.left().frac()
        } else {
            0
        };
        let pending_failed_upread_attempt: bool = g.upread_retract_token is None;
        let failed_reader_attempts: int = V_MAX_READ_RETRACT_FRACS - g.read_retract_token.frac();

        &&& if g.core_token.is_left() {
            g.read_guard_token is Left
        } else {
            &&& g.upreader_guard_token is None
            &&& g.read_guard_token is Right
        }
        &&& has_upgrade_bit <==> (active_upgrade_guard || pending_failed_upread_attempt)
        &&& !(active_upgrade_guard && pending_failed_upread_attempt)
        &&& total_reader_bits == active_read_guards + failed_reader_attempts
        &&& active_writer <==> has_writer_bit
        &&& 0 <= active_read_guards <= reader_bits <= total_reader_bits
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
        &&& g.upread_retract_token is Some ==> {
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
/// For more details, see comments on the `MAX_READER` constant
/// in the [`super::rwlock`] module.
const MAX_READER: usize = 1 << (usize::BITS - 4);

const READER_MASK: usize = usize::MAX >> 4;
const MAX_READER_MASK: usize = usize::MAX >> 3;

pub closed spec fn no_max_reader_overflow(v: usize) -> bool {
    v & MAX_READER_MASK < MAX_READER_MASK
}

impl<T> RwMutex<T> {
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

    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        self.wf()
    }

    pub closed spec fn queue_inv(self) -> bool {
        self.queue.type_inv()
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

impl<T> RwMutex<T> {
    /// Creates a new read-write mutex with an initial value.
    pub const fn new(val: T) -> Self {
        let (val, Tracked(perm)) = PCell::new(val);

        proof {
            lemma_consts_properties();
        }
        let tracked mut frac_perm = Frac::<PointsTo<T>>::new(perm);
        let tracked read_half_cell_perm = frac_perm.split(1int);
        let ghost frac_id = frac_perm.id();
        let tracked mut core_token = SumResource::alloc_left(frac_perm);
        let tracked read_retract_token = TokenResource::<V_MAX_READ_RETRACT_FRACS>::alloc(());
        let tracked upread_retract_token = UniqueToken::alloc(());
        let tracked upreader_guard_token = core_token.split_one_left_owner();
        let tracked left_token = core_token.split_one_left_knowledge();
        let tracked read_guard_token = FracResource::<ReadPerm<T>, MAX_READER_U64>::alloc(
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
            // val: UnsafeCell::new(val),
            val,
            lock: AtomicUsize::new(Ghost((val, Ghost(v_id))), 0, Tracked(perms)),
            queue: WaitQueue::new(),
            v_id: Ghost(v_id),
        }
    }
}

impl<T /*: ?Sized*/> RwMutex<T> {
    /// Acquires a read mutex and sleep until it can be acquired.
    ///
    /// The calling thread will sleep until there are no writers or upgrading
    /// upreaders present. The implementation of [`WaitQueue`] guarantees the
    /// order in which other concurrent readers or writers waiting simultaneously
    /// will acquire the mutex.
    #[track_caller]
    pub fn read(&self) -> RwMutexReadGuard<'_, T> {
        self.queue.wait_until(|| self.try_read())
    }

    /// Acquires a write mutex and sleep until it can be acquired.
    ///
    /// The calling thread will sleep until there are no writers, upreaders,
    /// or readers present. The implementation of [`WaitQueue`] guarantees the
    /// order in which other concurrent readers or writers waiting simultaneously
    /// will acquire the mutex.
    #[track_caller]
    pub fn write(&self) -> RwMutexWriteGuard<'_, T> {
        self.queue.wait_until(|| self.try_write())
    }

    /// Acquires a upread mutex and sleep until it can be acquired.
    ///
    /// The calling thread will sleep until there are no writers or upreaders present.
    /// The implementation of [`WaitQueue`] guarantees the order in which other concurrent
    /// readers or writers waiting simultaneously will acquire the mutex.
    ///
    /// Upreader will not block new readers until it tries to upgrade. Upreader
    /// and reader do not differ before invoking the upgrade method. However,
    /// only one upreader can exist at any time to avoid deadlock in the
    /// upgrade method.
    #[track_caller]
    pub fn upread(&self) -> RwMutexUpgradeableGuard<'_, T> {
        self.queue.wait_until(|| self.try_upread())
    }

    /// Attempts to acquire a read mutex.
    ///
    /// This function will never sleep and will return immediately.
    pub fn try_read(&self) -> Option<RwMutexReadGuard<'_, T>> {
        proof_decl! {
            let tracked mut read_token: Option<Frac<ReadPerm<T>, MAX_READER_U64>> = None;
            let tracked mut retract_read_token: Option<Token<V_MAX_READ_RETRACT_FRACS>> = None;
        }
        proof! {
            use_type_invariant(self);
            lemma_consts_properties();
        }

        let lock = atomic_with_ghost!(
            self.lock => fetch_add(READER);
            update prev -> next;
            ghost g => {
                let prev_usize = prev as usize;
                let next_usize = next as usize;
                assume(no_max_reader_overflow(prev_usize));
                lemma_consts_properties_value(prev_usize);
                lemma_consts_properties_prev_next(prev_usize, next_usize);
                if prev_usize & (WRITER | BEING_UPGRADED | MAX_READER) == 0 {
                    let tracked mut tmp = g.read_guard_token.tracked_take_left();
                    read_token = Some(tmp.split_one());
                    g.read_guard_token = Sum::Left(tmp);
                } else {
                    retract_read_token = Some(g.read_retract_token.split_one());
                }
            }
        );

        if lock & (WRITER | BEING_UPGRADED | MAX_READER) == 0 {
            Some(RwMutexReadGuard {
                inner: self,
                v_token: Tracked(read_token.tracked_unwrap()),
            })
        } else {
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

    /// Attempts to acquire a write mutex.
    ///
    /// This function will never sleep and will return immediately.
    pub fn try_write(&self) -> Option<RwMutexWriteGuard<'_, T>> {
        proof_decl! {
            let tracked mut guard_perm: Option<PointsTo<T>> = None;
            let tracked mut guard_token: Option<OneRightKnowledge<HalfPerm<T>, NoPerm<T>, 3>> = None;
        }
        proof! {
            use_type_invariant(self);
            lemma_consts_properties();
        }

        if atomic_with_ghost!(
            self.lock => compare_exchange(0, WRITER);
            update prev -> next;
            returning res;
            ghost g => {
                let prev_usize = prev as usize;
                let next_usize = next as usize;
                if res is Ok {
                    let tracked read_guard_token = g.read_guard_token.tracked_take_left();
                    let tracked (read_resource, read_empty) = read_guard_token.take_resource();
                    g.read_guard_token = Sum::Right(read_empty);
                    let tracked (read_half_cell_perm, left_token) = read_resource;
                    g.core_token.join_one_left_knowledge(left_token);
                    let tracked upreader_guard_token = g.upreader_guard_token.tracked_take();
                    g.core_token.join_one_left_owner(upreader_guard_token);
                    let tracked mut pointsto = g.core_token.take_resource_left();
                    pointsto.combine(read_half_cell_perm);
                    let tracked (pointsto, empty) = pointsto.take_resource();
                    guard_perm = Some(pointsto);
                    g.core_token.change_to_right(empty);
                    guard_token = Some(g.core_token.split_one_right_knowledge());
                } else {
                    lemma_consts_properties_prev_next(prev_usize, next_usize);
                }
            }
        ).is_ok() {
            Some(RwMutexWriteGuard {
                inner: self,
                v_perm: Tracked(guard_perm.tracked_unwrap()),
                v_token: Tracked(guard_token.tracked_unwrap()),
            })
        } else {
            None
        }
    }

    /// Attempts to acquire a upread mutex.
    ///
    /// This function will never sleep and will return immediately.
    pub fn try_upread(&self) -> Option<RwMutexUpgradeableGuard<'_, T>> {
        proof_decl! {
            let tracked mut upgrade_guard_token: Option<OneLeftOwner<HalfPerm<T>, NoPerm<T>, 3>> = None;
            let tracked mut retract_upgrade_token: Option<UniqueToken> = None;
        }
        proof! {
            use_type_invariant(self);
            lemma_consts_properties();
        }

        let lock = atomic_with_ghost!(
            self.lock => fetch_or(UPGRADEABLE_READER);
            update prev -> next;
            ghost g => {
                lemma_consts_properties_value(prev);
                lemma_consts_properties_prev_next(prev, next);
                if prev & (WRITER | UPGRADEABLE_READER) == 0 {
                    upgrade_guard_token = Some(g.upreader_guard_token.tracked_take());
                } else if prev & (WRITER | UPGRADEABLE_READER) == WRITER {
                    retract_upgrade_token = Some(g.upread_retract_token.tracked_take());
                }
            }
        ) & (WRITER | UPGRADEABLE_READER);

        if lock == 0 {
            return Some(RwMutexUpgradeableGuard {
                inner: self,
                v_token: Tracked(upgrade_guard_token.tracked_unwrap()),
            });
        } else if lock == WRITER {
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
                    } else {
                        g.upread_retract_token = retract_upgrade_token;
                    }
                }
            );
        }
        None
    }

    /* /// Returns a mutable reference to the underlying data.
    ///
    /// This method is zero-cost: By holding a mutable reference to the lock, the compiler has
    /// already statically guaranteed that access to the data is exclusive.
    pub fn get_mut(&mut self) -> &mut T {
        self.val.get_mut()
    } */
}

/* impl<T: /*: ?Sized +*/ fmt::Debug> fmt::Debug for RwMutex<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.val, f)
    }
} */

/// Because there can be more than one readers to get the T's immutable ref,
/// so T must be Sync to guarantee the sharing safety.
#[verifier::external]
unsafe impl<T: /*: ?Sized +*/ Send> Send for RwMutex<T> {}
#[verifier::external]
unsafe impl<T: /*: ?Sized +*/ Send + Sync> Sync for RwMutex<T> {}

impl<T /*: ?Sized*/> !Send for RwMutexWriteGuard<'_, T> {}
#[verifier::external]
unsafe impl<T: /*: ?Sized +*/ Sync> Sync for RwMutexWriteGuard<'_, T> {}

impl<T /*: ?Sized*/> !Send for RwMutexReadGuard<'_, T> {}
#[verifier::external]
unsafe impl<T: /*: ?Sized +*/ Sync> Sync for RwMutexReadGuard<'_, T> {}

impl<T /*: ?Sized*/> !Send for RwMutexUpgradeableGuard<'_, T> {}
#[verifier::external]
unsafe impl<T: /*: ?Sized +*/ Sync> Sync for RwMutexUpgradeableGuard<'_, T> {}

/// A guard that provides immutable data access.
#[verifier::reject_recursive_types(T)]
#[clippy::has_significant_drop]
#[must_use]
pub struct RwMutexReadGuard<'a, T /*: ?Sized*/> {
    inner: &'a RwMutex<T>,
    v_token: Tracked<Frac<ReadPerm<T>, MAX_READER_U64>>,
}

impl<'a, T> RwMutexReadGuard<'a, T> {
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

    pub closed spec fn value(self) -> T {
        *self.v_token@.resource().0.resource().value()
    }

    pub open spec fn view(self) -> T {
        self.value()
    }
}

impl<T /*: ?Sized*/> Deref for RwMutexReadGuard<'_, T> {
    type Target = T;

    #[verus_spec(returns self.view())]
    fn deref(&self) -> &T {
        proof! {
            use_type_invariant(self);
        }
        // unsafe { &*self.inner.val.get() }
        self.inner.val.borrow(Tracked(self.v_token.borrow().borrow().0.borrow()))
    }
}

impl<T/* : ?Sized */> RwMutexReadGuard<'_, T> {
    fn drop(self) {
        // When there are no readers, wake up a waiting writer.
        proof! {
            use_type_invariant(&self);
            use_type_invariant(self.inner);
            lemma_consts_properties();
        }
        let Tracked(token) = self.v_token;
        if atomic_with_ghost!(
            self.inner.lock => fetch_sub(READER);
            update prev -> next;
            ghost g => {
                let prev_usize = prev as usize;
                let next_usize = next as usize;
                assume(no_max_reader_overflow(prev_usize));
                lemma_consts_properties_value(next_usize);
                lemma_consts_properties_prev_next(prev_usize, next_usize);
                g.core_token.validate_with_one_left_knowledge(&token.borrow().1);
                let tracked mut tmp = g.read_guard_token.tracked_take_left();
                tmp.combine(token);
                g.read_guard_token = Sum::Left(tmp);
            }
        ) == READER {
            self.inner.queue.wake_one();
        }
    }
}

/// A guard that provides mutable data access.
#[clippy::has_significant_drop]
#[must_use]
#[verifier::reject_recursive_types(T)]
pub struct RwMutexWriteGuard<'a, T /*: ?Sized*/> {
    inner: &'a RwMutex<T>,
    v_perm: Tracked<PointsTo<T>>,
    v_token: Tracked<OneRightKnowledge<HalfPerm<T>, NoPerm<T>, 3>>,
}

impl<'a, T> RwMutexWriteGuard<'a, T> {
    #[verifier::type_invariant]
    spec fn type_inv(self) -> bool {
        &&& self.inner.cell_id() == self.v_perm@.id()
        &&& self.inner.core_token_id() == self.v_token@.id()
    }

    pub closed spec fn value(self) -> T {
        *self.v_perm@.value()
    }

    pub open spec fn view(self) -> T {
        self.value()
    }
}

impl<T /*: ?Sized*/> Deref for RwMutexWriteGuard<'_, T> {
    type Target = T;

    #[verus_spec(returns self.view())]
    fn deref(&self) -> &T {
        proof! {
            use_type_invariant(self);
        }
        // unsafe { &*self.inner.val.get() }
        self.inner.val.borrow(Tracked(self.v_perm.borrow()))
    }
}

impl<'a, T /*: ?Sized*/> RwMutexWriteGuard<'a, T> {
    /// Atomically downgrades a write guard to an upgradeable reader guard.
    ///
    /// This method always succeeds because the lock is exclusively held by the writer.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn downgrade(self) -> RwMutexUpgradeableGuard<'a, T> {
        let mut this = self;
        loop {
            this = match this.try_downgrade() {
                Ok(guard) => return guard,
                Err(e) => e,
            };
        }
    }

    /// This is not exposed as a public method to prevent intermediate lock states from affecting the
    /// downgrade process.
    fn try_downgrade(self) -> Result<RwMutexUpgradeableGuard<'a, T>, Self> {
        proof! {
            use_type_invariant(&self);
            use_type_invariant(self.inner);
            lemma_consts_properties();
        }
        let Tracked(perm) = self.v_perm;
        let Tracked(token) = self.v_token;
        proof_decl! {
            let tracked mut upgrade_guard_token: Option<OneLeftOwner<HalfPerm<T>, NoPerm<T>, 3>> = None;
            let tracked mut err_perm: Option<PointsTo<T>> = None;
            let tracked mut err_write_guard_token: Option<OneRightKnowledge<HalfPerm<T>, NoPerm<T>, 3>> = None;
        }
        let inner = self.inner;
        let res = atomic_with_ghost!(
            self.inner.lock => compare_exchange(WRITER, UPGRADEABLE_READER);
            update prev -> next;
            returning res;
            ghost g => {
                lemma_consts_properties_prev_next(prev, next);
                if res is Ok {
                    g.core_token.validate_with_one_right_knowledge(&token);
                    g.core_token.join_one_right_knowledge(token);
                    let tracked empty = g.core_token.take_resource_right();
                    let tracked mut full = empty.put_resource(perm);
                    let tracked read_half_cell_perm = full.split(1int);
                    g.core_token.change_to_left(full);
                    upgrade_guard_token = Some(g.core_token.split_one_left_owner());
                    let tracked left_token = g.core_token.split_one_left_knowledge();
                    let tracked read_guard_empty = g.read_guard_token.tracked_take_right();
                    let tracked read_guard_token = FracResource::alloc_from_empty(
                        read_guard_empty,
                        (read_half_cell_perm, left_token),
                    );
                    g.read_guard_token = Sum::Left(read_guard_token);
                } else {
                    err_perm = Some(perm);
                    err_write_guard_token = Some(token);
                }
            }
        );

        if res.is_ok() {
            // drop(self);
            atomic_with_ghost! {
                self.inner.lock => fetch_and(!WRITER);
                update prev -> next;
                ghost g => {
                    let prev_usize = prev as usize;
                    let next_usize = next as usize;
                    let tracked mut guard_token = upgrade_guard_token.tracked_unwrap();
                    g.core_token.validate_with_one_left_owner(&guard_token);
                    if g.upreader_guard_token is Some {
                        guard_token.validate_with_one_left_owner(
                            g.upreader_guard_token.tracked_borrow(),
                        );
                        assert(false);
                    }
                    upgrade_guard_token = Some(guard_token);
                    lemma_consts_properties_value(prev_usize);
                    lemma_consts_properties_prev_next(prev_usize, next_usize);
                    lemma_consts_properties_value(next_usize);
                }
            };
            self.inner.queue.wake_all();
            Ok(RwMutexUpgradeableGuard {
                inner,
                v_token: Tracked(upgrade_guard_token.tracked_unwrap()),
            })
        } else {
            Err(RwMutexWriteGuard {
                inner,
                v_perm: Tracked(err_perm.tracked_unwrap()),
                v_token: Tracked(err_write_guard_token.tracked_unwrap()),
            })
        }
    }

    pub fn drop(self) {
        proof! {
            use_type_invariant(&self);
            use_type_invariant(self.inner);
            lemma_consts_properties();
        }
        let Tracked(mut perm) = self.v_perm;
        let Tracked(token) = self.v_token;
        atomic_with_ghost! {
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
                let tracked read_guard_token = FracResource::alloc_from_empty(
                    read_guard_empty,
                    (read_half_cell_perm, left_token),
                );
                g.read_guard_token = Sum::Left(read_guard_token);
            }
        };
        // When the current writer releases, wake up all the sleeping threads.
        // All awakened threads may include readers and writers.
        // Thanks to the `wait_until` method, either all readers
        // continue to execute or one writer continues to execute.
        self.inner.queue.wake_all();
    }
}

/// A guard that provides immutable data access but can be atomically
/// upgraded to [`RwMutexWriteGuard`].
#[verifier::reject_recursive_types(T)]
pub struct RwMutexUpgradeableGuard<'a, T /*: ?Sized*/> {
    inner: &'a RwMutex<T>,
    v_token: Tracked<OneLeftOwner<HalfPerm<T>, NoPerm<T>, 3>>,
}

impl<'a, T /*: ?Sized*/> RwMutexUpgradeableGuard<'a, T> {
    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        wf_upgradeable_guard_token(
            self.inner.core_token_id(),
            self.inner.frac_id(),
            self.inner.cell_id(),
            self.v_token@,
        )
    }

    pub closed spec fn value(self) -> T {
        *self.v_token@.resource().resource().value()
    }

    pub open spec fn view(self) -> T {
        self.value()
    }
}

impl<'a, T> RwMutexUpgradeableGuard<'a, T> {
    /// Upgrades this upread guard to a write guard atomically.
    ///
    /// After calling this method, subsequent readers will be blocked
    /// while previous readers remain unaffected.
    ///
    /// The calling thread will not sleep, but spin to wait for the existing
    /// reader to be released. There are two main reasons.
    /// - First, it needs to sleep in an extra waiting queue and needs extra wake-up logic and overhead.
    /// - Second, upgrading method usually requires a high response time (because the mutex is being used now).
    #[verifier::exec_allows_no_decreases_clause]
    pub fn upgrade(self) -> RwMutexWriteGuard<'a, T> {
        let mut this = self;
        proof! {
            use_type_invariant(&this);
            use_type_invariant(&this.inner);
            lemma_consts_properties();
        }
        atomic_with_ghost!(
            this.inner.lock => fetch_or(BEING_UPGRADED);
            update prev -> next;
            ghost g => {
                lemma_consts_properties_prev_next(prev, next);
            }
        );
        loop {
            this = match this.try_upgrade() {
                Ok(guard) => return guard,
                Err(e) => e,
            };
        }
    }

    /// Attempts to upgrade this upread guard to a write guard atomically.
    ///
    /// This function will return immediately.
    ///
    /// This function is not exposed publicly because the `BEING_UPGRADED` bit
    /// is set only in [`Self::upgrade`].
    fn try_upgrade(self) -> Result<RwMutexWriteGuard<'a, T>, Self> {
        proof! {
            use_type_invariant(&self);
            use_type_invariant(self.inner);
            lemma_consts_properties();
        }
        let Tracked(upread_guard_token) = self.v_token;
        proof_decl! {
            let tracked mut write_perm: Option<PointsTo<T>> = None;
            let tracked mut err_upread_guard_token: Option<OneLeftOwner<HalfPerm<T>, NoPerm<T>, 3>> = None;
            let tracked mut retract_upgrade_token: Option<UniqueToken> = None;
            let tracked mut write_guard_token: Option<OneRightKnowledge<HalfPerm<T>, NoPerm<T>, 3>> = None;
        }

        let res = atomic_with_ghost!(
            self.inner.lock => compare_exchange(UPGRADEABLE_READER | BEING_UPGRADED, WRITER | UPGRADEABLE_READER);
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
            let inner = self.inner;
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
            Ok(RwMutexWriteGuard {
                inner,
                v_perm: Tracked(write_perm.tracked_unwrap()),
                v_token: Tracked(write_guard_token.tracked_unwrap()),
            })
        } else {
            Err(RwMutexUpgradeableGuard {
                inner: self.inner,
                v_token: Tracked(err_upread_guard_token.tracked_unwrap()),
            })
        }
    }

    pub fn drop(self) {
        proof! {
            use_type_invariant(&self);
            use_type_invariant(self.inner);
            lemma_consts_properties();
        }
        let Tracked(guard_token) = self.v_token;
        let res = atomic_with_ghost!(
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
                    g.upreader_guard_token = Some(guard_token);
                }
            }
        );
        if res == UPGRADEABLE_READER {
            self.inner.queue.wake_all();
        }
    }
}

impl<T /*: ?Sized*/> Deref for RwMutexUpgradeableGuard<'_, T> {
    type Target = T;

    #[verus_spec(returns self.view())]
    fn deref(&self) -> &T {
        proof! {
            use_type_invariant(self);
        }
        // unsafe { &*self.inner.val.get() }
        self.inner.val.borrow(Tracked(self.v_token.borrow().tracked_borrow().borrow()))
    }
}

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
        prev & (WRITER | BEING_UPGRADED | MAX_READER) == 0 ==> {
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
    if prev & (WRITER | BEING_UPGRADED | MAX_READER) == 0 {
        assert(prev & WRITER == 0) by (bit_vector)
            requires
                prev & (WRITER | BEING_UPGRADED | MAX_READER) == 0,
        ;
        assert(prev & BEING_UPGRADED == 0) by (bit_vector)
            requires
                prev & (WRITER | BEING_UPGRADED | MAX_READER) == 0,
        ;
        assert(prev & MAX_READER == 0) by (bit_vector)
            requires
                prev & (WRITER | BEING_UPGRADED | MAX_READER) == 0,
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
        next == UPGRADEABLE_READER && prev == WRITER ==> {
            &&& next & WRITER == 0
            &&& next & UPGRADEABLE_READER == UPGRADEABLE_READER
            &&& next & READER_MASK == 0
            &&& next & MAX_READER_MASK == 0
            &&& next & MAX_READER == 0
            &&& next & BEING_UPGRADED == 0
        },
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
    if next == UPGRADEABLE_READER && prev == WRITER {
        assert(next & WRITER == 0) by (bit_vector)
            requires
                next == UPGRADEABLE_READER && prev == WRITER,
        ;
        assert(next & UPGRADEABLE_READER == UPGRADEABLE_READER) by (bit_vector)
            requires
                next == UPGRADEABLE_READER && prev == WRITER,
        ;
        assert(next & READER_MASK == 0) by (bit_vector)
            requires
                next == UPGRADEABLE_READER && prev == WRITER,
        ;
        assert(next & MAX_READER_MASK == 0) by (bit_vector)
            requires
                next == UPGRADEABLE_READER && prev == WRITER,
        ;
        assert(next & MAX_READER == 0) by (bit_vector)
            requires
                next == UPGRADEABLE_READER && prev == WRITER,
        ;
        assert(next & BEING_UPGRADED == 0) by (bit_vector)
            requires
                next == UPGRADEABLE_READER && prev == WRITER,
        ;
    }
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
