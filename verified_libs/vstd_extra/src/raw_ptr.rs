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

    /// The underlying access permission.
    ///
    /// Exposure is only needed where an *address* becomes a pointer. Steps
    /// that go pointer-to-pointer -- a struct to its first field, a cell to its
    /// contents -- need none of it, so they are stated over
    /// [`vstd::raw_ptr::PointsTo`] and reached through this.
    pub proof fn borrow_points_to(tracked &self) -> (tracked res: &PointsTo<T>)
        ensures
            res.ptr() == self.ptr() as *mut T,
            res.is_init() == self.is_init(),
            self.is_init() ==> res.value() == self.value(),
    {
        use_type_invariant(self);
        &self.points_to
    }

    /// The exposure proof, for rebuilding a pointer from an address.
    pub proof fn borrow_exposed(tracked &self) -> (tracked res: &IsExposed)
        ensures
            res.provenance() == self.ptr()@.provenance,
    {
        use_type_invariant(self);
        &self.exposed
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
    opens_invariants none
    no_unwind
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

/// Dereferences a permission whose provenance comes from an enclosing
/// permission rather than from an exposure of its own.
///
/// A permission reached pointer-to-pointer -- a struct's first field, a cell's
/// contents -- inherits the enclosing permission's provenance and needs no
/// exposure token, so it is a plain [`PointsTo`]. Rebuilding its pointer from
/// an address still needs *some* exposure, and `src` is where it comes from:
/// the enclosing permission, which has the same provenance by construction.
pub fn ptr_ref_via<'a, S, T>(
    addr: usize,
    Tracked(src): Tracked<&ExposedPointsTo<S>>,
    Tracked(perm): Tracked<&'a PointsTo<T>>,
) -> (r: &'a T)
    requires
        perm.ptr()@.addr == addr,
        perm.ptr()@.provenance == src.ptr()@.provenance,
        perm.is_init(),
    returns
        perm.value(),
{
    let tracked exposed = *src.borrow_exposed();
    let p = vstd::raw_ptr::with_exposed_provenance::<T>(addr, Tracked(exposed));
    vstd::raw_ptr::ptr_ref(p as *const T, Tracked(perm))
}

/// [`ptr_ref_via`] for exclusive access.
pub fn ptr_mut_ref_via<'a, S, T>(
    addr: usize,
    Tracked(src): Tracked<&ExposedPointsTo<S>>,
    Tracked(perm): Tracked<&'a mut PointsTo<T>>,
) -> (r: &'a mut T)
    requires
        old(perm).ptr()@.addr == addr,
        old(perm).ptr()@.provenance == src.ptr()@.provenance,
        old(perm).is_init(),
    ensures
        *r == old(perm).value(),
        final(perm).ptr() == old(perm).ptr(),
        final(perm).is_init(),
        final(perm).value() == *final(r),
{
    let tracked exposed = *src.borrow_exposed();
    let p = vstd::raw_ptr::with_exposed_provenance::<T>(addr, Tracked(exposed));
    vstd::raw_ptr::ptr_mut_ref(p, Tracked(perm))
}

} // verus!
