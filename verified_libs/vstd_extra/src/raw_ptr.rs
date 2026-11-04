//! Raw-pointer permissions retaining exposed provenance for address round trips.
use vstd::{
    prelude::*,
    raw_ptr::{IsExposed, PointsTo},
};

verus! {

/// Typed memory access paired with a proof that its provenance has been exposed.
/// This permission carries no allocation or deallocation ownership.
pub tracked struct ExposedPointsTo<T> {
    points_to: PointsTo<T>,
    exposed: IsExposed,
}

impl<T> ExposedPointsTo<T> {
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.points_to.ptr()@.provenance == self.exposed.provenance()
    }

    pub closed spec fn ptr(self) -> *const T {
        self.points_to.ptr() as *const T
    }

    pub open spec fn ptr_mut(self) -> *mut T {
        self.ptr() as *mut T
    }

    pub open spec fn addr(self) -> usize {
        self.ptr().addr()
    }

    pub closed spec fn is_init(self) -> bool {
        self.points_to.is_init()
    }

    pub closed spec fn value(self) -> T {
        self.points_to.value()
    }

    /// Packages an existing access permission with its provenance exposure proof.
    pub proof fn new(tracked points_to: PointsTo<T>, tracked exposed: IsExposed) -> (tracked perm:
        Self)
        requires
            points_to.ptr()@.provenance == exposed.provenance(),
        ensures
            perm.ptr() == points_to.ptr(),
            perm.is_init() == points_to.is_init(),
            perm.value() == points_to.value(),
    {
        Self { points_to, exposed }
    }
}

/// Reconstructs a pointer at the address recorded by its exposed permission.
pub fn ptr_from_addr<T>(addr: usize, Tracked(perm): Tracked<&ExposedPointsTo<T>>) -> *const T
    requires
        perm.addr() == addr,
    returns
        perm.ptr(),
    opens_invariants none
    no_unwind
{
    proof {
        use_type_invariant(perm);
    }
    /* vstd requires an erased witness for the exposed provenance of this cast.
     * Origin Rust: addr as *const T
     */
    vstd::raw_ptr::with_exposed_provenance(addr, Tracked(perm.exposed)) as *const T
}

/// Borrows initialized memory through its exposed pointer permission.
pub fn ptr_ref<'a, T>(ptr: *const T, Tracked(perm): Tracked<&'a ExposedPointsTo<T>>) -> &'a T
    requires
        ptr == perm.ptr(),
        perm.is_init(),
    returns
        perm.value(),
{
    /* vstd checks raw dereferences through an explicit permission argument.
     * Origin Rust: unsafe { &*ptr }
     */
    vstd::raw_ptr::ptr_ref(ptr, Tracked(&perm.points_to))
}

/// Reconstructs a mutable pointer at the address recorded by its exposed permission.
pub fn ptr_mut_from_addr<T>(addr: usize, Tracked(perm): Tracked<&ExposedPointsTo<T>>) -> *mut T
    requires
        perm.addr() == addr,
    returns
        perm.ptr_mut(),
    opens_invariants none
    no_unwind
{
    /* vstd requires an erased witness for the exposed provenance of this cast.
     * Origin Rust: addr as *mut T
     */
    ptr_from_addr::<T>(addr, Tracked(perm)) as *mut T
}

/// Exclusively borrows initialized memory, reflecting mutations in its permission.
pub fn ptr_mut_ref<'a, T>(
    ptr: *mut T,
    Tracked(perm): Tracked<&'a mut ExposedPointsTo<T>>,
) -> (value: &'a mut T)
    requires
        ptr == old(perm).ptr_mut(),
        old(perm).is_init(),
    ensures
        final(perm).ptr_mut() == ptr,
        final(perm).is_init(),
        *value == old(perm).value(),
        *final(value) == final(perm).value(),
    opens_invariants none
    no_unwind
{
    proof {
        use_type_invariant(&*perm);
    }
    /* vstd checks raw mutable dereferences through an exclusive permission borrow.
     * Origin Rust: unsafe { &mut *ptr }
     */
    vstd::raw_ptr::ptr_mut_ref(ptr, Tracked(&mut perm.points_to))
}

} // verus!
