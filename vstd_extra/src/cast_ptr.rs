use vstd::prelude::*;

use vstd::layout;
use vstd::raw_ptr::MemContents;
use vstd::set;
use vstd::set_lib;
use vstd::simple_pptr::{self, PPtr};

use core::marker::PhantomData;
use core::ops::Deref;

verus! {

pub trait Repr<R: Sized>: Sized {
    /// If the underlying representation contains cells, the translation may require permission objects that access them.
    type Perm;

    spec fn wf(r: R, perm: Self::Perm) -> bool;

    spec fn to_repr_spec(self, perm: Self::Perm) -> (R, Self::Perm);

    fn to_repr(self, Tracked(perm): Tracked<&mut Self::Perm>) -> (res: R)
        ensures
            res == self.to_repr_spec(*old(perm)).0,
            *perm == self.to_repr_spec(*old(perm)).1,
    ;

    spec fn from_repr_spec(r: R, perm: Self::Perm) -> Self;

    fn from_repr(r: R, Tracked(perm): Tracked<&Self::Perm>) -> (res: Self)
        requires
            Self::wf(r, *perm),
        ensures
            res == Self::from_repr_spec(r, *perm),
    ;

    fn from_borrowed<'a>(r: &'a R, Tracked(perm): Tracked<&'a Self::Perm>) -> (res: &'a Self)
        requires
            Self::wf(*r, *perm),
        ensures
            *res == Self::from_repr_spec(*r, *perm),
    ;

    proof fn from_to_repr(self, perm: Self::Perm)
        ensures
            Self::from_repr_spec(self.to_repr_spec(perm).0, self.to_repr_spec(perm).1) == self,
    ;

    proof fn to_from_repr(r: R, perm: Self::Perm)
        requires
            Self::wf(r, perm),
        ensures
            Self::from_repr_spec(r, perm).to_repr_spec(perm) == (r, perm),
    ;

    proof fn to_repr_wf(self, perm: Self::Perm)
        ensures
            Self::wf(self.to_repr_spec(perm).0, self.to_repr_spec(perm).1),
    ;
}

/// Concrete representation of a pointer to an object of type T with representation type R
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

impl<R, T: Repr<R>> From<PPtr<R>> for ReprPtr<R, T> {
    #[verifier::external_body]
    fn from(ptr: PPtr<R>) -> Self {
       Self { addr: ptr.addr(), ptr: ptr, _T: PhantomData }
    }
}

impl<R, T: Repr<R>> From<ReprPtr<R, T>> for PPtr<R> {
    #[verifier::external_body]
    fn from(ptr: ReprPtr<R, T>) -> Self {
        ptr.ptr
    }
}

impl<R, T: Repr<R>> ReprPtr<R, T> {
    pub open spec fn new_spec(ptr: PPtr<R>) -> Self {
        Self { addr: ptr.addr(), ptr: ptr, _T: PhantomData }
    }

    #[verifier::external_body]
    pub fn new_borrowed<'a>(ptr: &'a PPtr<R>) -> (res: &'a Self)
        ensures
            *res == Self::new_spec(*ptr),
    {
        unimplemented!()
    }

    pub fn from_pptr(ptr: PPtr<R>) -> (res: Self)
        ensures
            res == Self::new_spec(ptr),
            res.addr == ptr.addr(),
            res.ptr == ptr,
    {
        Self { addr: ptr.addr(), ptr: ptr, _T: PhantomData }
    }

    pub open spec fn to_pptr(self) -> PPtr<R> {
        self.ptr
    }

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
            old(perm).wf(&old(perm).inner_perms),
        ensures
            perm.pptr() == old(perm).pptr(),
            perm.mem_contents() == MemContents::Uninit::<T>,
            v == old(perm).value(),
    {
        proof {
            T::from_to_repr(perm.value(), perm.inner_perms);
        }
        T::from_repr(self.ptr.take(Tracked(&mut perm.points_to)), Tracked(&perm.inner_perms))
    }

    pub exec fn put(self, Tracked(perm): Tracked<&mut PointsTo<R, T>>, v: T)
        requires
            old(perm).pptr() == self,
            old(perm).mem_contents() == MemContents::Uninit::<T>,
        ensures
            perm.pptr() == old(perm).pptr(),
            perm.mem_contents() == MemContents::Init(v),
            perm.wf(&perm.inner_perms),
    {
        proof {
            v.from_to_repr(perm.inner_perms);
            v.to_repr_wf(perm.inner_perms);
        }
        self.ptr.put(Tracked(&mut perm.points_to), v.to_repr(Tracked(&mut perm.inner_perms)))
    }

    pub exec fn borrow<'a>(self, Tracked(perm): Tracked<&'a PointsTo<R, T>>) -> (v: &'a T)
        requires
            perm.pptr() == self,
            perm.is_init(),
            perm.wf(&perm.inner_perms),
        ensures
            *v === perm.value(),
    {
        T::from_borrowed(self.ptr.borrow(Tracked(&perm.points_to)), Tracked(&perm.inner_perms))
    }
}

#[verifier::accept_recursive_types(T)]
pub tracked struct PointsTo<R, T: Repr<R>> {
    pub ghost addr: usize,
    pub points_to: simple_pptr::PointsTo<R>,
    pub inner_perms: T::Perm,
    pub _T: PhantomData<T>,
}

impl<R, T: Repr<R>> PointsTo<R, T> {
    pub open spec fn new_spec(addr: usize, points_to: simple_pptr::PointsTo<R>, inner_perms: T::Perm) -> Self {
        Self { addr: addr@, points_to, inner_perms, _T: PhantomData }
    }

    pub proof fn new(
        addr: Ghost<usize>,
        tracked points_to: simple_pptr::PointsTo<R>,
        tracked inner_perms: T::Perm,
    ) -> tracked Self {
        Self { addr: addr@, points_to: points_to, inner_perms, _T: PhantomData }
    }

    pub open spec fn wf(self, perm: &T::Perm) -> bool {
        &&& T::wf(self.points_to.value(), *perm)
    }

    pub open spec fn addr(self) -> usize {
        self.addr
    }

    pub open spec fn mem_contents(self) -> MemContents<T> {
        match self.points_to.mem_contents() {
            MemContents::<R>::Uninit => MemContents::<T>::Uninit,
            MemContents::<R>::Init(r) => MemContents::<T>::Init(T::from_repr_spec(r, self.inner_perms)),
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

impl<R, T: Repr<R>> From<PointsTo<R, T>> for vstd::simple_pptr::PointsTo<R> {
    #[verifier::external_body]
    fn from(ptr: PointsTo<R, T>) -> Self {
        ptr.points_to
    }
}

} // verus!
