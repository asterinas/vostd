use vstd::prelude::*;

use vstd::layout;
use vstd::raw_ptr::MemContents;
use vstd::set;
use vstd::set_lib;
use vstd::simple_pptr::{self, PPtr};

use core::marker::PhantomData;

verus! {

pub trait Repr<R: Sized>: Sized {
    spec fn wf(r: R) -> bool;

    spec fn to_repr_spec(self) -> R;

    #[verifier::when_used_as_spec(to_repr_spec)]
    fn to_repr(self) -> (res: R)
        ensures
            res == self.to_repr_spec(),
    ;

    spec fn from_repr_spec(r: R) -> Self;

    #[verifier::when_used_as_spec(from_repr_spec)]
    fn from_repr(r: R) -> (res: Self)
        requires
            Self::wf(r),
        ensures
            res == Self::from_repr_spec(r),
    ;

    fn from_borrowed<'a>(r: &'a R) -> (res: &'a Self)
        requires
            Self::wf(*r),
        ensures
            *res == Self::from_repr_spec(*r),
    ;

    proof fn from_to_repr(self)
        ensures
            Self::from_repr(self.to_repr()) == self,
    ;

    proof fn to_from_repr(r: R)
        requires
            Self::wf(r),
        ensures
            Self::from_repr(r).to_repr() == r,
    ;

    proof fn to_repr_wf(self)
        ensures
            Self::wf(self.to_repr()),
    ;
}

/// Concrete representation of a pointer to an array
/// The length of the array is not stored in the pointer
pub struct ReprPtr<R, T: Repr<R>> {
    pub addr: usize,
    pub ptr: PPtr<R>,
    pub _T: PhantomData<T>,
}

impl<R, T: Repr<R>> Clone for ReprPtr<R, T> {
    fn clone(&self) -> Self {
        Self { addr: self.addr, ptr: self.ptr, _T: PhantomData }
    }
}

impl<R, T: Repr<R>> Copy for ReprPtr<R, T> {

}

impl<R, T: Repr<R>> ReprPtr<R, T> {
    pub open spec fn addr_spec(self) -> usize {
        self.addr
    }

    #[verifier::when_used_as_spec(addr_spec)]
    pub fn addr(self) -> (u: usize)
        ensures
            u == self.addr,
    {
        self.addr
    }

    pub exec fn take(self, Tracked(perm): Tracked<&mut PointsTo<R, T>>) -> (v: T)
        requires
            old(perm).pptr() == self,
            old(perm).is_init(),
            old(perm).wf(),
        ensures
            perm.pptr() == old(perm).pptr(),
            perm.mem_contents() == MemContents::Uninit::<T>,
            v == old(perm).value(),
    {
        proof {
            T::from_to_repr(perm.value());
        }
        T::from_repr(self.ptr.take(Tracked(&mut perm.points_to)))
    }

    pub exec fn put(self, Tracked(perm): Tracked<&mut PointsTo<R, T>>, v: T)
        requires
            old(perm).pptr() == self,
            old(perm).mem_contents() == MemContents::Uninit::<T>,
        ensures
            perm.pptr() == old(perm).pptr(),
            perm.mem_contents() == MemContents::Init(v),
            perm.wf(),
    {
        proof {
            v.from_to_repr();
            v.to_repr_wf();
        }
        self.ptr.put(Tracked(&mut perm.points_to), v.to_repr())
    }

    pub exec fn borrow<'a>(self, Tracked(perm): Tracked<&'a PointsTo<R, T>>) -> (v: &'a T)
        requires
            perm.pptr() == self,
            perm.is_init(),
            perm.wf(),
        ensures
            *v === perm.value(),
    {
        T::from_borrowed(self.ptr.borrow(Tracked(&perm.points_to)))
    }
}

#[verifier::accept_recursive_types(T)]
pub tracked struct PointsTo<R, T: Repr<R>> {
    pub ghost addr: usize,
    pub points_to: simple_pptr::PointsTo<R>,
    pub _T: PhantomData<T>,
}

impl<R, T: Repr<R>> PointsTo<R, T> {
    pub proof fn new(
        addr: Ghost<usize>,
        tracked points_to: simple_pptr::PointsTo<R>,
    ) -> tracked Self {
        Self { addr: addr@, points_to: points_to, _T: PhantomData }
    }

    pub open spec fn wf(self) -> bool {
        &&& T::wf(self.points_to.value())
    }

    pub open spec fn addr(self) -> usize {
        self.addr
    }

    pub open spec fn mem_contents(self) -> MemContents<T> {
        match self.points_to.mem_contents() {
            MemContents::<R>::Uninit => MemContents::<T>::Uninit,
            MemContents::<R>::Init(r) => MemContents::<T>::Init(T::from_repr(r)),
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
        ReprPtr { addr: self.addr, ptr: self.points_to.pptr(), _T: PhantomData }
    }

    pub broadcast proof fn pptr_implies_addr(&self)
        ensures
            self.addr() == #[trigger] self.pptr().addr(),
    {
    }
}

} // verus!
