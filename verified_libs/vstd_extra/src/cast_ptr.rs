use vstd::prelude::*;

use vstd::raw_ptr::MemContents;
use vstd::simple_pptr::{self, PPtr};
use vstd::std_specs::convert::{FromSpec, FromSpecImpl};

use core::marker::PhantomData;

verus! {

/// A trait for types that have a concrete representation type `R`.
pub trait Repr<R: Sized>: Sized {
    spec fn wf(r: R) -> bool;

    spec fn to_repr_spec(self) -> R;

    fn to_repr(self) -> (res: R)
        returns
            self.to_repr_spec(),
    ;

    spec fn from_repr_spec(r: R) -> Self;

    fn from_repr(r: R) -> (res: Self)
        requires
            Self::wf(r),
        returns
            Self::from_repr_spec(r),
    ;

    fn from_borrowed<'a>(r: &'a R) -> (res: &'a Self)
        requires
            Self::wf(*r),
        ensures
            *res == Self::from_repr_spec(*r),
    ;

    /// Mutable projection of the representation. Implementations must keep
    /// the representation consistent with mutations through the returned reference.
    fn from_borrowed_mut<'a>(r: &'a mut R) -> (res: &'a mut Self)
        requires
            Self::wf(*old(r)),
        ensures
            *res == Self::from_repr_spec(*old(r)),
            Self::wf(*final(r)),
            *final(res) == Self::from_repr_spec(*final(r)),
    ;

    proof fn from_to_repr(self)
        ensures
            Self::from_repr_spec(self.to_repr_spec()) == self,
    ;

    proof fn to_from_repr(r: R)
        requires
            Self::wf(r),
        ensures
            Self::from_repr_spec(r).to_repr_spec() == r,
    ;

    proof fn to_repr_wf(self)
        ensures
            Self::wf(self.to_repr_spec()),
    ;
}

/// Concrete representation of a pointer to an object of type T with representation type R
/// The length of the array is not stored in the pointer
#[verifier::accept_recursive_types(T)]
pub struct ReprPtr<R, T> {
    pub ptr: PPtr<R>,
    pub _T: PhantomData<T>,
}

impl<R, T> Clone for ReprPtr<R, T> {
    fn clone(&self) -> Self
        returns
            self,
    {
        Self { ptr: self.ptr, _T: PhantomData }
    }
}

impl<R, T> Copy for ReprPtr<R, T> {

}

impl<R, T> FromSpecImpl<PPtr<R>> for ReprPtr<R, T> {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(ptr: PPtr<R>) -> Self {
        Self { ptr, _T: PhantomData }
    }
}

impl<R, T> From<PPtr<R>> for ReprPtr<R, T> {
    fn from(ptr: PPtr<R>) -> Self {
        Self { ptr, _T: PhantomData }
    }
}

impl<R, T> FromSpecImpl<ReprPtr<R, T>> for PPtr<R> {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(ptr: ReprPtr<R, T>) -> Self {
        ptr.ptr
    }
}

impl<R, T> From<ReprPtr<R, T>> for PPtr<R> {
    fn from(ptr: ReprPtr<R, T>) -> Self {
        ptr.ptr
    }
}

impl<R, T> ReprPtr<R, T> {
    pub open spec fn new_spec(ptr: PPtr<R>) -> Self {
        Self { ptr, _T: PhantomData }
    }

    pub fn from_pptr(ptr: PPtr<R>) -> (res: Self)
        ensures
            res == Self::new_spec(ptr),
            res.addr() == ptr.addr(),
            res.ptr == ptr,
    {
        Self { ptr, _T: PhantomData }
    }

    pub open spec fn to_pptr(self) -> PPtr<R> {
        self.ptr
    }

    pub open spec fn addr_spec(self) -> usize {
        self.ptr.addr()
    }

    #[verifier::when_used_as_spec(addr_spec)]
    pub fn addr(self) -> usize
        returns
            self.addr(),
    {
        self.ptr.addr()
    }
}

impl<R, T: Repr<R>> ReprPtr<R, T> {
    pub fn take(self, Tracked(perm): Tracked<&mut PointsTo<R, T>>) -> (v: T)
        requires
            old(perm).pptr() == self,
            old(perm).is_init(),
            old(perm).wf(),
        ensures
            final(perm).pptr() == old(perm).pptr(),
            final(perm).mem_contents() == MemContents::Uninit::<T>,
            v == old(perm).value(),
    {
        proof {
            T::from_to_repr(perm.value());
        }
        T::from_repr(self.ptr.take(Tracked(&mut perm.points_to)))
    }

    pub fn put(self, Tracked(perm): Tracked<&mut PointsTo<R, T>>, v: T)
        requires
            old(perm).pptr() == self,
            old(perm).mem_contents() == MemContents::Uninit::<T>,
        ensures
            final(perm).pptr() == old(perm).pptr(),
            final(perm).mem_contents() == MemContents::Init(v),
            final(perm).wf(),
            final(perm).points_to.value() == v.to_repr_spec(),
            final(perm).points_to.is_init(),
    {
        proof {
            v.from_to_repr();
            v.to_repr_wf();
        }
        self.ptr.put(Tracked(&mut perm.points_to), v.to_repr())
    }

    pub fn borrow<'a>(self, Tracked(perm): Tracked<&'a PointsTo<R, T>>) -> (v: &'a T)
        requires
            perm.pptr() == self,
            perm.is_init(),
            perm.wf(),
        ensures
            *v == perm.value(),
    {
        T::from_borrowed(self.ptr.borrow(Tracked(&perm.points_to)))
    }

    /// Borrows the pointed-to `T` mutably for the lifetime of `perm`.
    ///
    /// While the returned borrow is live, `perm` is exclusively held and
    /// cannot be used. The returned borrow is tied to the tracked permission:
    /// after the borrow ends, the permission's value matches the final `*v`. Callers must
    /// preserve any invariants beyond the final initialised/well-formed state
    /// themselves.
    pub fn borrow_mut<'a>(self, Tracked(perm): Tracked<&'a mut PointsTo<R, T>>) -> (v: &'a mut T)
        requires
            old(perm).pptr() == self,
            old(perm).is_init(),
            old(perm).wf(),
        ensures
            *v == old(perm).value(),
            final(perm).pptr() == old(perm).pptr(),
            final(perm).is_init(),
            final(perm).wf(),
            final(perm).value() == *final(v),
    {
        /* `Repr` conversions need not preserve layout; project through the representation.
         * Origin Rust: unsafe { &mut *(self.ptr.addr() as *mut T) }
         */
        T::from_borrowed_mut(self.ptr.borrow_mut(Tracked(&mut perm.points_to)))
    }
}

#[verifier::accept_recursive_types(T)]
pub tracked struct PointsTo<R, T: Repr<R>> {
    pub points_to: simple_pptr::PointsTo<R>,
    pub _T: PhantomData<T>,
}

impl<R, T: Repr<R>> PointsTo<R, T> {
    pub open spec fn new_spec(points_to: simple_pptr::PointsTo<R>) -> Self {
        Self { points_to, _T: PhantomData }
    }

    pub proof fn new(tracked points_to: simple_pptr::PointsTo<R>) -> (tracked res: Self)
        returns
            Self::new_spec(points_to),
    {
        Self { points_to, _T: PhantomData }
    }

    pub open spec fn wf(self) -> bool {
        &&& T::wf(self.points_to.value())
    }

    pub open spec fn addr(self) -> usize {
        self.points_to.addr()
    }

    pub open spec fn mem_contents(self) -> MemContents<T> {
        match self.points_to.mem_contents() {
            MemContents::<R>::Uninit => MemContents::<T>::Uninit,
            MemContents::<R>::Init(r) => MemContents::<T>::Init(T::from_repr_spec(r)),
        }
    }

    pub open spec fn is_init(self) -> bool {
        self.mem_contents().is_init()
    }

    pub open spec fn is_uninit(self) -> bool {
        self.mem_contents().is_uninit()
    }

    pub open spec fn value(self) -> T
        recommends
            self.is_init(),
    {
        self.mem_contents().value()
    }

    pub open spec fn pptr(self) -> ReprPtr<R, T> {
        ReprPtr { ptr: self.points_to.pptr(), _T: PhantomData }
    }
}

} // verus!
