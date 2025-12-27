use vstd::{
    atomic_with_ghost,
    cell::{MemContents, PCell, PointsTo},
    modes::tracked_static_ref,
    prelude::*,
};

verus! {

pub const UNINIT: u64 = 0;

pub const OCCUPIED: u64 = 1;

pub const INITED: u64 = 2;

/// A tracked state of a¸ [`Once`] that can be used to ensure that the cell is
/// initialized before accessing its value.
pub tracked enum OnceState<V: 'static> {
    /// The cell is uninitialized.
    Uninit(PointsTo<Option<V>>),
    /// The cell is occupied meaning it is being *written*.
    Occupied,
    /// The cell is initialized with a value and extended with
    /// static lifetime.
    Init(&'static PointsTo<Option<V>>),
}

/// A structure that combines some data with a permission to access it.
///
/// For example, in `aster_common` we can see a lot of structs with
/// its `owner` associated. E.g., `MetaSlotOwner` is the owner of
/// `MetaSlot`. This struct can be used to represent such a combination
/// because now the permission is no longer exclusively owner by some
/// specific CPU and is "shared" among multiple threads via atomic
/// operations.
///
/// This struct is especially useful when used in conjunction with
/// synchronization primitives like [`Once`], where we want to ensure that
/// the data is initialized only once and the permission is preserved
/// throughout the lifetime of the data.
#[repr(transparent)]
#[allow(repr_transparent_external_private_fields)]
pub struct AtomicDataWithOwner<V, Own> {
    /// The underlying data.
    pub data: V,
    /// The permission to access the data.
    pub permission: Tracked<Own>,
}

impl<U, Own> View for AtomicDataWithOwner<U, Own> {
    type V = U;

    open spec fn view(&self) -> Self::V {
        self.data
    }
}

impl<V, Own> AtomicDataWithOwner<V, Own> {
    /// Creates a new `AtomicDataWithOwner` with the given data and permission.
    pub const fn new(data: V, permission: Tracked<Own>) -> (r: Self)
        ensures
            r.data == data,
            r.permission == permission,
    {
        AtomicDataWithOwner { data, permission }
    }
}

/// A [`Predicate`] is something you're gonna preserve during the lifetime
/// of any synchronization primitives like [`Once`].
pub trait Predicate<V> {
    spec fn inv(self, v: V) -> bool;
}

struct_with_invariants! {
/// A synchronization primitive which can nominally be written to only once.
///
/// This type is a thread-safe [`Once`], and can be used in statics.
/// In many simple cases, you can use [`LazyLock<T, F>`] instead to get the benefits of this type
/// with less effort: `LazyLock<T, F>` "looks like" `&T` because it initializes with `F` on deref!
/// Where OnceLock shines is when LazyLock is too simple to support a given case, as LazyLock
/// doesn't allow additional inputs to its function after you call [`LazyLock::new(|| ...)`].
///
/// A `OnceLock` can be thought of as a safe abstraction over uninitialized data that becomes
/// initialized once written.
///
/// # Examples
///
/// ```rust
/// static MY_ONCE: Once<i32> = Once::new();
///
/// let value = MY_ONCE.get();
/// assert(value.is_some());   // unsatisfied precondition, as MY_ONCE is uninitialized.
/// ```
#[verifier::reject_recursive_types(V)]
pub struct OnceImpl<V: 'static, F: Predicate<V>> {
    cell: PCell<Option<V>>,
    state: vstd::atomic_ghost::AtomicU64<_, OnceState<V>, _>,
    f: Ghost<F>,
}

#[verifier::type_invariant]
pub closed spec fn wf(&self) -> bool {
    invariant on state with (cell, f) is (v: u64, g: OnceState<V>) {
        match g {
            OnceState::Uninit(points_to) => {
                &&& v == UNINIT
                &&& points_to.id() == cell.id()
                &&& points_to.mem_contents() matches MemContents::Init(None)
            }
            OnceState::Occupied => {
                &&& v == OCCUPIED
            }
            OnceState::Init(points_to) => {
                &&& v == INITED
                &&& points_to.id() == cell.id()
                &&& points_to.mem_contents() matches MemContents::Init(Some(value))
                &&& f@.inv(value)
            }
        }
    }
}

}

#[verifier::external]
unsafe impl<V, F: Predicate<V>> Send for OnceImpl<V, F> {

}

#[verifier::external]
unsafe impl<V, F: Predicate<V>> Sync for OnceImpl<V, F> {

}

impl<V, F: Predicate<V>> OnceImpl<V, F> {
    pub closed spec fn inv(&self) -> F {
        self.f@
    }

    /// Creates a new uninitialized [`Once`].
    pub const fn new(Ghost(f): Ghost<F>) -> (r: Self)
        ensures
            r.wf(),
            r.inv() == f,
    {
        let (cell, Tracked(points_to)) = PCell::new(None);
        let tracked state = OnceState::Uninit(points_to);
        let state = vstd::atomic_ghost::AtomicU64::new(
            Ghost((cell, Ghost(f))),
            UNINIT,
            Tracked(state),
        );

        Self { cell, state, f: Ghost(f) }
    }

    /// Initializes the [`Once`] with the given value `v`.
    pub fn init(&self, v: V)
        requires
            self.inv().inv(v),
            self.wf(),
    {
        let cur_state =
            atomic_with_ghost! {
            &self.state => load(); ghost g => {}
        };

        if cur_state != UNINIT {
            return ;
        } else {
            let tracked mut points_to = None;
            let res =
                atomic_with_ghost! {
                &self.state => compare_exchange(UNINIT, OCCUPIED);
                returning res; ghost g => {
                    g = match g {
                        OnceState::Uninit(points_to_inner) => {
                            points_to = Some(points_to_inner);
                            OnceState::Occupied
                        }
                        _ => {
                            // If we are not in Uninit state, we cannot do anything.
                            g
                        }
                    }
                }
            };

            if !res.is_err() {
                let tracked mut points_to = points_to.tracked_unwrap();
                self.cell.replace(Tracked(&mut points_to), Some(v));
                // Extending the permission to static because `OnceLock` is
                // often shared among threads and we want to ensure that
                // the value is accessible globally.
                let tracked static_points_to = tracked_static_ref(points_to);
                // let tracked _ = self.inst.borrow().do_deposit(points_to, points_to, &mut token);
                atomic_with_ghost! {
                    &self.state => store(INITED); ghost g => {
                        g = OnceState::Init(static_points_to);
                    }
                }
                return ;
            } else {
                // wait or abort.
                return ;
            }
        }
    }

    /// Try to get the value stored in the [`Once`]. A [`Option::Some`]
    /// is returned if the cell is initialized; otherwise, [`Option::None`]
    /// is returned.
    pub fn get<'a>(&'a self) -> (r: Option<&'a V>)
        requires
            self.wf(),
        ensures
            self.wf(),
            r matches Some(res) ==> self.inv().inv(*res),
    {
        let tracked mut points_to = None;
        let res =
            atomic_with_ghost! {
            &self.state => load(); ghost g => {
                match g {
                    OnceState::Init(points_to_opt) => {
                        points_to = Some(points_to_opt);
                    }
                    _ => {}
                }
            }
        };

        if res == INITED {
            let tracked points_to = points_to.tracked_unwrap();
            let tracked static_points_to = tracked_static_ref(points_to);

            self.cell.borrow(Tracked(static_points_to)).as_ref()
        } else {
            None
        }
    }
}

/// A `Once` that combines some data with a permission to access it.
///
/// This type alias automatically lifts the target value `V` into
/// a wrapper [`AtomicDataWithOwner<V, Own>`] where `Own` is the
/// permission type so that we can reason about non-trivial runtime
/// properties in verification.
pub type Once<V, Own, F> = OnceImpl<AtomicDataWithOwner<V, Own>, F>;

} // verus!
