use vstd::prelude::*;

use vstd::layout;
use vstd::raw_ptr;
use vstd::set;
use vstd::set_lib;

use core::marker::PhantomData;

use crate::array_ptr;

verus! {

/// Concrete representation of a pointer to an array of size N*F in virtual memory
/// which maps to N underlying physical frames of size F.
pub struct VirtPtr<V, const N: usize, const F: usize> {
    pub base_vaddr: usize,
    pub index: usize,
    pub _type: PhantomData<[[V; F]; N]>,
}

#[verifier::accept_recursive_types(V)]
pub tracked struct PointsTo<V, const N: usize, const F: usize> {
    pub base_vaddr: usize,
    // Vaddr -> PointsTo
    pub perms: Map<usize, crate::array_ptr::PointsToArray<V, F>>,
}

/*/// Permission to access an array of values
pub tracked struct PointsTo<V, const N: usize> {
    exposed: raw_ptr::IsExposed,
    dealloc: Option<raw_ptr::Dealloc>,
}*/

pub ghost struct PointsToData<V, const N: usize, const F: usize> {
    pub base_vaddr: usize,
    pub value: Seq<raw_ptr::MemContents<V>>,
}

/*impl<V, const N: usize> PointsToArrayData<V, N> {
    #[verifier::external_body]
    pub proof fn into_ptr(tracked self) -> (tracked data: raw_ptr::PointsToData<[V; N]>)
        ensures
            data.ptr == self.ptr,
            data.opt_value == mem_contents_unwrap(self.value),
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn into_array(tracked data: raw_ptr::PointsToData<[V; N]>) -> (tracked res:
        PointsToArrayData<V, N>)
        ensures
            res.ptr == data.ptr,
            res.value == mem_contents_wrap(data.opt_value),
    {
        unimplemented!();
    }
}
*/

impl<T, const N: usize, const F: usize> View for PointsTo<T, N, F> {
    type V = PointsToData<T, N, F>;

    uninterp spec fn view(&self) -> Self::V;
}

impl<V, const N: usize, const F: usize> PointsTo<V, N, F> {
    /*    #[verifier::inline]
    pub open spec fn ptr(self) -> *mut [V; N] {
        self@.ptr
    }*/
    #[verifier::inline]
    pub open spec fn opt_value(self) -> Seq<raw_ptr::MemContents<V>> {
        self@.value
    }

    #[verifier::inline]
    pub open spec fn is_init(self, index: int) -> bool {
        0 <= index < N && self.opt_value()[index].is_init()
    }

    #[verifier::inline]
    pub open spec fn is_uninit(self, index: int) -> bool {
        0 <= index < N && self.opt_value()[index].is_uninit()
    }

    /*    #[verifier::inline]
    pub open spec fn is_init_all(self) -> bool {
        is_mem_contents_all_init(self.opt_value())
    }

    #[verifier::inline]
    pub open spec fn is_uninit_all(self) -> bool {
        is_mem_contents_all_uninit(self.opt_value())
    }*/
    #[verifier::inline]
    pub open spec fn value(self) -> Seq<V>
    //        recommends
    //            self.is_init_all(),
     {
        let opt_value = self.opt_value();
        Seq::new(N as nat, |i: int| opt_value[i].value())
    }/*
    #[verifier::external_body]
    pub proof fn leak_contents(tracked &mut self, index: int)
        ensures
            self.ptr() == old(self).ptr(),
            self.is_uninit(index),
            forall|i: int|
                0 <= i < N && i != index ==> self.opt_value()[i] == old(self).opt_value()[i],
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn is_disjoint<S, const M: usize, const G: usize>(&self, other: &PointsTo<S, M, G>)
        ensures
            self.ptr() as int + layout::size_of::<[V; N]>() <= other.ptr() as int
                || other.ptr() as int + layout::size_of::<[S; M]>() <= self.ptr() as int,
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn is_disjoint_ptr<S>(&self, other: &raw_ptr::PointsTo<S>)
        ensures
            self.ptr() as int + layout::size_of::<[V; N]>() <= other.ptr() as int
                || other.ptr() as int + layout::size_of::<S>() <= self.ptr() as int,
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn is_nonnull(tracked &self)
        requires
            layout::size_of::<[V; N]>() > 0,
        ensures
            self@.ptr@.addr != 0,
    {
        unimplemented!();
    }*/

}

/*
/// Reading and writing to an array of values
#[inline(always)]
#[verifier::external_body]
pub exec fn ptr_mut_fill<V, const N: usize>(
    ptr: *mut [V; N],
    Tracked(perm): Tracked<&mut PointsToArray<V, N>>,
    value: V,
) where V: Copy
    requires
        old(perm).ptr() == ptr,
        old(perm).is_uninit_all(),
    ensures
        perm.ptr() == ptr,
        perm.is_init_all(),
        forall|i: int| 0 <= i < N ==> perm.opt_value()[i] == raw_ptr::MemContents::Init(value),
    opens_invariants none
    no_unwind
{
    for i in 0..N {
        unsafe {
            core::ptr::write((ptr as *mut V).add(i), value);
        }
    }
}

#[inline(always)]
#[verifier::external_body]
pub exec fn ptr_mut_write_at<V, const N: usize>(
    ptr: *mut [V; N],
    Tracked(perm): Tracked<&mut PointsToArray<V, N>>,
    index: usize,
    value: V,
)
    requires
        old(perm).ptr() == ptr,
        old(perm).is_uninit(index as int),
        index < N,
    ensures
        perm.ptr() == ptr,
        perm.is_init(index as int),
        forall|i: int| 0 <= i < N && i != index ==> perm.opt_value()[i] == old(perm).opt_value()[i],
        perm.opt_value()[index as int] == raw_ptr::MemContents::Init(value),
    opens_invariants none
    no_unwind
{
    unsafe {
        core::ptr::write((ptr as *mut V).add(index), value);
    }
}

/// Read only once and the value will be moved out side of the array
#[inline(always)]
#[verifier::external_body]
pub exec fn ptr_mut_read_at<V, const N: usize>(
    ptr: *mut [V; N],
    Tracked(perm): Tracked<&mut PointsToArray<V, N>>,
    index: usize,
) -> (res: V) where V: Copy
    requires
        old(perm).ptr() == ptr,
        old(perm).is_init(index as int),
        index < N,
    ensures
        perm.ptr() == ptr,
        perm.is_uninit(index as int),
        forall|i: int| 0 <= i < N && i != index ==> perm.opt_value()[i] == old(perm).opt_value()[i],
        res == old(perm).opt_value()[index as int].value(),
    opens_invariants none
    no_unwind
{
    unsafe { core::ptr::read((ptr as *const V).add(index)) }
}

#[inline(always)]
#[verifier::external_body]
pub exec fn ptr_mut_read_all<V, const N: usize, const F: usize>(
    ptr: *mut [V; N],
    Tracked(perm): Tracked<&mut PointsTo<V, N>>,
) -> (res: [V; N])
    requires
        old(perm).ptr() == ptr,
        old(perm).is_init_all(),
    ensures
        perm.ptr() == ptr,
        perm.is_uninit_all(),
        res@ == old(perm).value(),
    opens_invariants none
    no_unwind
{
    unsafe { core::ptr::read(ptr) }
}

/// Get the immutable reference of the value at the index
#[inline(always)]
#[verifier::external_body]
pub exec fn ptr_ref_at<V, const N: usize, const F: usize>(
    ptr: *mut [V; N],
    Tracked(perm): Tracked<&PointsTo<V, N, F>>,
    index: usize,
) -> (res: &V)
    requires
        perm.ptr() == ptr,
        perm.is_init(index as int),
    ensures
        res == perm.opt_value()[index as int].value(),
    opens_invariants none
    no_unwind
{
    unsafe { &*((ptr as *const V).add(index)) }
}

/// Get the immutable reference of the entire array
#[inline(always)]
#[verifier::external_body]
pub exec fn ptr_ref<V, const N: usize>(
    ptr: *mut [V; N],
    Tracked(perm): Tracked<&PointsTo<V, N>>,
) -> (res: &[V; N])
    requires
        perm.ptr() == ptr,
        perm.is_init_all(),
    ensures
        forall|i: int| 0 <= i < N ==> #[trigger] res[i] == perm.opt_value()[i].value(),
    opens_invariants none
    no_unwind
{
    unsafe { &*ptr }
}

broadcast use {
    raw_ptr::group_raw_ptr_axioms,
    set_lib::group_set_lib_default,
    set::group_set_axioms,
};*/

impl<V, const N: usize, const F: usize> VirtPtr<V, N, F> {
    /// Impl: cast the pointer to an integer
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub exec fn addr(&self) -> usize
        returns
            self.base_vaddr,
    {
        self.base_vaddr
    }

    /// Impl: cast an integer to the pointer
    #[inline(always)]
    pub exec fn from_addr(addr: usize) -> (res: Self)
        ensures
            res.base_vaddr == addr,
            res.index == 0,
    {
        Self { base_vaddr: addr, index: 0, _type: PhantomData }
    }

    #[vstd::contrib::auto_spec]
    pub exec fn add(self, off: usize) -> Self
        requires
            self.index + off
                <= N  // C standard style: don't exceed one-past the end of the array
            ,
    {
        Self { base_vaddr: self.base_vaddr, index: (self.index + off) as usize, _type: PhantomData }
    }
}

impl<V, const N: usize, const F: usize> PointsTo<V, N, F> {
    /// Spec: cast the permission to an integer
    pub closed spec fn addr(self) -> usize {
        self.base_vaddr
    }

    /// Spec: cast the permission to a pointer
    pub open spec fn is_pptr(self, ptr: VirtPtr<V, N, F>) -> bool {
        ptr.base_vaddr == self.addr()
    }

    pub open spec fn inv(self) -> bool {
        &&& forall|i: usize|
            0 <= i < N ==> {
                &&& self.perms.contains_key(
                    i,
                )
                //                &&& self.perms[i].wf()

            }&&& self.addr() != 0
    }

    pub open spec fn value_at(self, va: usize) -> raw_ptr::MemContents<V>
        recommends
            self.base_vaddr <= va < self.base_vaddr + N * F,
    {
        let page = va / F;
        let offset = va % F;
        self.perms[page].opt_value()[offset as int]
    }/*
    /// Spec: invariants for the ArrayPtr permissions
    /// TODO: uncomment the below if "external_type_specification: Const params not yet supported" is fixed
    /// #[verifier::type_invariant]
    pub closed spec fn wf(self) -> bool {
        /// The pointer is not a slice, so it is still thin
        &&& self.points_to.ptr()@.metadata == ()
        &&& self.points_to.ptr()@.provenance == self.exposed.provenance()
        &&& match self.dealloc {
            Some(dealloc) => {
                &&& dealloc.addr() == self.addr()
                &&& dealloc.size() == layout::size_of::<[V; N]>()
                &&& dealloc.align() == layout::align_of::<[V; N]>()
                &&& dealloc.provenance() == self.exposed.provenance()
                &&& layout::size_of::<[V; N]>() > 0
            },
            None => { layout::size_of::<[V; N]>() == 0 },
        }
        &&& self.addr() != 0
    }

    pub closed spec fn points_to(self) -> PointsToArray<V, N> {
        self.points_to
    }

    pub open spec fn opt_value(self) -> [raw_ptr::MemContents<V>; N] {
        self.points_to().opt_value()
    }

    pub open spec fn value(self) -> Seq<V>
        recommends
            self.is_init_all(),
    {
        self.points_to().value()
    }

    #[verifier::inline]
    pub open spec fn is_init(self, index: int) -> bool {
        self.points_to().is_init(index)
    }

    #[verifier::inline]
    pub open spec fn is_uninit(self, index: int) -> bool {
        !self.points_to().is_init(index)
    }

    #[verifier::inline]
    pub open spec fn is_init_all(self) -> bool {
        self.points_to().is_init_all()
    }

    #[verifier::inline]
    pub open spec fn is_uninit_all(self) -> bool {
        self.points_to().is_uninit_all()
    }

    pub proof fn is_nonnull(tracked self)
        requires
            self.wf(),
        ensures
            self.addr() != 0,
    {
        self.wf();
    }

    pub proof fn leak_contents(tracked &mut self, index: int)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            self.addr() == old(self).addr(),
            self.is_uninit(index),
            forall|i: int|
                0 <= i < N && i != index ==> self.opt_value()[i] == old(self).opt_value()[i],
    {
        self.wf();
        self.points_to.leak_contents(index);
    }

    pub proof fn is_disjoint<S, const M: usize>(&self, other: &PointsTo<S, M>)
        ensures
            self.addr() + layout::size_of::<[V; N]>() <= other.addr() || other.addr()
                + layout::size_of::<[S; M]>() <= self.addr(),
    {
        self.points_to.is_disjoint(&other.points_to)
    }

    pub proof fn is_distinct<S, const M: usize>(&self, other: &PointsTo<S, M>)
        requires
            layout::size_of::<[V; N]>() != 0,
            layout::size_of::<[S; M]>() != 0,
        ensures
            self.addr() != other.addr(),
    {
        self.points_to.is_disjoint(&other.points_to);
    }*/

}

impl<V, const N: usize, const F: usize> PointsTo<V, N, F> {
    /*
    #[verifier::external_body]
    pub proof fn into_array(tracked pt: raw_ptr::PointsTo<[V; N]>) -> (tracked res: PointsToArray<
        V,
        N,
    >)
        ensures
            res@.ptr == pt@.ptr,
            res@.value == mem_contents_wrap(pt@.opt_value),
    {
        Tracked::<PointsToArray<V, N>>::assume_new().get()
    }

    #[verifier::external_body]
    pub proof fn into_ptr(tracked self) -> (tracked res: raw_ptr::PointsTo<[V; N]>)
        ensures
            res@.ptr == self@.ptr,
            res@.opt_value == mem_contents_unwrap(self@.value),
    {
        Tracked::<raw_ptr::PointsTo<[V; N]>>::assume_new().get()
    }*/

}

impl<V, const N: usize, const F: usize> Clone for VirtPtr<V, N, F> {
    fn clone(&self) -> (res: Self)
        ensures
            res === *self,
    {
        Self { ..*self }
    }
}

impl<V, const N: usize, const F: usize> Copy for VirtPtr<V, N, F> {

}

#[verifier::external_body]
#[inline(always)]
pub exec fn layout_for_array_is_valid<V: Sized, const N: usize>()
    ensures
        layout::valid_layout(
            layout::size_of::<[V; N]>() as usize,
            layout::align_of::<[V; N]>() as usize,
        ),
        layout::size_of::<[V; N]>() as usize as nat == layout::size_of::<[V; N]>(),
        layout::align_of::<[V; N]>() as usize as nat == layout::align_of::<[V; N]>(),
    opens_invariants none
    no_unwind
{
}

impl<V, const N: usize, const F: usize> VirtPtr<V, N, F> {
    /*
    pub exec fn empty() -> (res: (ArrayPtr<V, N>, Tracked<PointsTo<V, N>>))
        requires
            layout::size_of::<[V; N]>() > 0,
        ensures
            res.1@.wf(),
            res.1@.is_pptr(res.0),
            res.1@.is_uninit_all(),
    {
        layout_for_array_is_valid::<V, N>();
        let (p, Tracked(raw_perm), Tracked(dealloc)) = raw_ptr::allocate(
            core::mem::size_of::<[V; N]>(),
            core::mem::align_of::<[V; N]>(),
        );
        let Tracked(exposed) = raw_ptr::expose_provenance(p);
        let tracked ptr_perm = raw_perm.into_typed::<[V; N]>(p as usize);
        proof {
            ptr_perm.is_nonnull();
            assert(ptr_perm.is_uninit());
        }

        let tracked arr_perm = PointsToArray::into_array(ptr_perm);
        proof {
            arr_perm.is_nonnull();
            axiom_mem_contents_wrap_correctness(ptr_perm.opt_value(), arr_perm@.value);
            assert(arr_perm.is_uninit_all());
        }
        let tracked pt = PointsTo { points_to: arr_perm, exposed, dealloc: Some(dealloc) };
        proof {
            assert(pt.is_uninit_all());
        }
        let ptr = ArrayPtr { addr: p as usize, index: 0, _type: PhantomData };
        (ptr, Tracked(pt))
    }

    #[inline(always)]
    pub exec fn make_as(&self, Tracked(perm): Tracked<&mut PointsTo<V, N>>, value: V) where V: Copy
        requires
            old(perm).wf(),
            old(perm).is_pptr(*self),
            old(perm).is_uninit_all(),
        ensures
            perm.wf(),
            perm.is_pptr(*self),
            perm.is_init_all(),
            forall|i: int| 0 <= i < N ==> perm.opt_value()[i] == raw_ptr::MemContents::Init(value),
    {
        let ptr: *mut [V; N] = raw_ptr::with_exposed_provenance(self.addr, Tracked(perm.exposed));

        assert(perm.points_to().is_uninit_all());
        ptr_mut_fill(ptr, Tracked(&mut perm.points_to), value);
    }

    pub exec fn new(dft: V) -> (res: (ArrayPtr<V, N>, Tracked<PointsTo<V, N>>)) where V: Copy
        requires
            layout::size_of::<[V; N]>() > 0,
        ensures
            res.1@.wf(),
            res.1@.is_pptr(res.0),
            forall|i: int|
                0 <= i < N ==> #[trigger] res.1@.opt_value()[i] == raw_ptr::MemContents::Init(dft),
    {
        let (p, Tracked(perm)) = ArrayPtr::empty();
        proof {
            assert(perm.wf());
            assert(perm.is_pptr(p));
            assert(perm.is_uninit_all());
        }
        p.make_as(Tracked(&mut perm), dft);
        (p, Tracked(perm))
    }

    pub exec fn free(self, Tracked(perm): Tracked<PointsTo<V, N>>)
        requires
            perm.wf(),
            perm.is_pptr(self),
            perm.is_uninit_all(),
    {
        if core::mem::size_of::<[V; N]>() == 0 {
            return ;
        }
        assert(core::mem::size_of::<[V; N]>() > 0);
        let ptr: *mut u8 = raw_ptr::with_exposed_provenance(self.addr, Tracked(perm.exposed));
        let tracked PointsTo { points_to, dealloc: dea, exposed } = perm;

        proof {
            assert(perm.is_uninit_all());
            assert(points_to.is_uninit_all());
        }
        let tracked perm_ptr: raw_ptr::PointsTo<[V; N]> = points_to.into_ptr();
        proof {
            axiom_mem_contents_unwrap_uninit_correctness(points_to@.value, perm_ptr.opt_value());
            assert(perm_ptr.is_uninit());
        }
        let tracked perm_raw = perm_ptr.into_raw();

        raw_ptr::deallocate(
            ptr,
            core::mem::size_of::<[V; N]>(),
            core::mem::align_of::<[V; N]>(),
            Tracked(perm_raw),
            Tracked(dea.tracked_unwrap()),
        );
    }

    /// Insert `value` at `index`
    /// The value is moved into the array.
    /// Requires the slot at `index` to be uninitialized.
    #[inline(always)]
    pub exec fn insert(&self, Tracked(perm): Tracked<&mut PointsTo<V, N>>, value: V)
        requires
            old(perm).wf(),
            old(perm).is_pptr(*self),
            old(perm).is_uninit(self.index as int),
            self.index < N,
        ensures
            perm.wf(),
            perm.is_pptr(*self),
            perm.is_init(self.index as int),
            forall|i: int|
                0 <= i < N && i != self.index ==> perm.opt_value()[i] == old(perm).opt_value()[i],
            perm.opt_value()[self.index as int] == raw_ptr::MemContents::Init(value),
    {
        let ptr: *mut [V; N] = raw_ptr::with_exposed_provenance(self.addr, Tracked(perm.exposed));

        assert(perm.points_to().is_uninit(self.index as int));
        ptr_mut_write_at(ptr, Tracked(&mut perm.points_to), self.index, value);
    }

    /// Take the `value` at `index`
    /// The value is moved out of the array.
    /// Requires the slot at `index` to be initialized.
    /// Afterwards, the slot is uninitialized.
    #[inline(always)]
    pub exec fn take_at(&self, Tracked(perm): Tracked<&mut PointsTo<V, N>>) -> (res: V) where
        V: Copy,

        requires
            old(perm).wf(),
            old(perm).is_pptr(*self),
            old(perm).is_init(self.index as int),
            self.index < N,
        ensures
            perm.wf(),
            perm.is_pptr(*self),
            perm.is_uninit(self.index as int),
            forall|i: int|
                0 <= i < N && i != self.index ==> perm.opt_value()[i] == old(perm).opt_value()[i],
            res == old(perm).opt_value()[self.index as int].value(),
    {
        let ptr: *mut [V; N] = raw_ptr::with_exposed_provenance(self.addr, Tracked(perm.exposed));

        assert(perm.points_to().is_init(self.index as int));
        ptr_mut_read_at(ptr, Tracked(&mut perm.points_to), self.index)
    }

    /// Take all the values of the array
    /// The values are moved out of the array.
    /// Requires all slots to be initialized.
    /// Afterwards, all slots are uninitialized.
    #[inline(always)]
    pub exec fn take_all(&self, Tracked(perm): Tracked<&mut PointsTo<V, N>>) -> (res: [V; N])
        requires
            old(perm).wf(),
            old(perm).is_pptr(*self),
            old(perm).is_init_all(),
        ensures
            perm.wf(),
            perm.is_pptr(*self),
            perm.is_uninit_all(),
            res@ == old(perm).value(),
    {
        let ptr: *mut [V; N] = raw_ptr::with_exposed_provenance(self.addr, Tracked(perm.exposed));

        assert(perm.points_to().is_init_all());
        ptr_mut_read_all(ptr, Tracked(&mut perm.points_to))
    }

    /// Free the memory of the entire array and return the value
    /// that was previously stored in the array.
    /// Requires all slots to be initialized.
    /// Afterwards, all slots are uninitialized.
    #[inline(always)]
    pub exec fn into_inner(self, Tracked(perm): Tracked<PointsTo<V, N>>) -> (res: [V; N])
        requires
            perm.wf(),
            perm.is_pptr(self),
            perm.is_init_all(),
        ensures
            res@ == perm.value(),
    {
        let tracked mut perm = perm;
        let res = self.take_all(Tracked(&mut perm));
        self.free(Tracked(perm));
        res
    }

    /// Update the value at `index` with `value` and return the previous value
    /// Requires the slot at `index` to be initialized.
    /// Afterwards, the slot is initialized with `value`.
    /// Returns the previous value.
    #[inline(always)]
    pub exec fn update(
        &self,
        Tracked(perm): Tracked<&mut PointsTo<V, N>>,
        index: usize,
        value: V,
    ) -> (res: V) where V: Copy
        requires
            old(perm).wf(),
            old(perm).is_pptr(*self),
            old(perm).is_init(index as int),
            index < N,
        ensures
            perm.wf(),
            perm.is_pptr(*self),
            perm.is_init(index as int),
            forall|i: int|
                0 <= i < N && i != index ==> perm.opt_value()[i] == old(perm).opt_value()[i],
            perm.opt_value()[index as int] == raw_ptr::MemContents::Init(value),
            res == old(perm).opt_value()[index as int].value(),
    {
        let ptr: *mut [V; N] = raw_ptr::with_exposed_provenance(self.addr, Tracked(perm.exposed));

        assert(perm.points_to().is_init(index as int));
        let res = ptr_mut_read_at(ptr, Tracked(&mut perm.points_to), index);
        ptr_mut_write_at(ptr, Tracked(&mut perm.points_to), index, value);
        res
    }

    /// Get the reference of the value at `index`
    /// Borrow the immutable reference of the value at `index`
    /// Requires the slot at `index` to be initialized.
    /// Afterwards, the slot is still initialized.
    /// Returns the immutable reference of the value.
    /// The reference is valid as long as the permission is alive.
    /// The reference is not allowed to be stored.
    #[inline(always)]
    pub exec fn borrow_at<'a>(
        &self,
        Tracked(perm): Tracked<&'a PointsTo<V, N>>,
        index: usize,
    ) -> (res: &'a V)
        requires
            perm.wf(),
            perm.is_pptr(*self),
            perm.is_init(index as int),
            index < N,
        ensures
            res == perm.opt_value()[index as int].value(),
    {
        let ptr: *mut [V; N] = raw_ptr::with_exposed_provenance(self.addr, Tracked(perm.exposed));

        assert(perm.points_to().is_init(index as int));
        ptr_ref_at(ptr, Tracked(&perm.points_to), index)
    }

    /// Get the reference of the entire array
    /// Borrow the immutable reference of the entire array
    /// Requires all slots to be initialized.
    /// Afterwards, all slots are still initialized.
    /// Returns the immutable reference of the entire array.
    /// The reference is valid as long as the permission is alive.
    /// The reference is not allowed to be stored.
    #[inline(always)]
    pub exec fn borrow<'a>(&self, Tracked(perm): Tracked<&'a PointsTo<V, N>>) -> (res: &'a [V; N])
        requires
            perm.wf(),
            perm.is_pptr(*self),
            perm.is_init_all(),
        ensures
            forall|i: int| 0 <= i < N ==> #[trigger] res[i] == perm.opt_value()[i].value(),
    {
        let ptr: *mut [V; N] = raw_ptr::with_exposed_provenance(self.addr, Tracked(perm.exposed));

        assert(perm.points_to().is_init_all());
        ptr_ref(ptr, Tracked(&perm.points_to))
    }

    /// Overwrite the entry at `index` with `value`
    /// The pervious value will be leaked if it was initialized.
    #[inline(always)]
    pub exec fn overwrite(
        &self,
        Tracked(perm): Tracked<&mut PointsTo<V, N>>,
        index: usize,
        value: V,
    )
        requires
            old(perm).wf(),
            old(perm).is_pptr(*self),
            index < N,
        ensures
            perm.wf(),
            perm.is_pptr(*self),
            perm.is_init(index as int),
            forall|i: int|
                0 <= i < N && i != index ==> perm.opt_value()[i] == old(perm).opt_value()[i],
            perm.opt_value()[index as int] == raw_ptr::MemContents::Init(value),
        opens_invariants none
        no_unwind
    {
        proof {
            perm.leak_contents(index as int);
        }
        assert(perm.is_uninit(index as int));
        let ptr: *mut [V; N] = raw_ptr::with_exposed_provenance(self.addr, Tracked(perm.exposed));

        ptr_mut_write_at(ptr, Tracked(&mut perm.points_to), index, value);
    }

    #[verifier::external_body]
    pub proof fn tracked_overwrite(
        tracked &self,
        tracked perm: &mut PointsTo<V, N>,
        tracked index: usize,
        tracked value: V,
    )
        requires
            old(perm).wf(),
            old(perm).is_pptr(*self),
            index < N,
        ensures
            perm.wf(),
            perm.is_pptr(*self),
            perm.is_init(index as int),
            forall|i: int|
                0 <= i < N && i != index ==> perm.opt_value()[i] == old(perm).opt_value()[i],
            perm.opt_value()[index as int] == raw_ptr::MemContents::Init(value),
    {
        self.overwrite(Tracked(perm), index, value);
    }

    /// Get the value at `index` and return it
    /// The value is copied from the array
    /// Requires the slot at `index` to be initialized.
    /// Afterwards, the slot is still initialized.
    #[inline(always)]
    pub exec fn get(&self, Tracked(perm): Tracked<&PointsTo<V, N>>, index: usize) -> (res: V) where
        V: Copy,

        requires
            perm.wf(),
            perm.is_pptr(*self),
            perm.is_init(index as int),
            index < N,
        ensures
            res == perm.opt_value()[index as int].value(),
    {
        *self.borrow_at(Tracked(perm), index)
    }*/

}

} // verus!
