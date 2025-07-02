use vstd::prelude::*;
use vstd::raw_ptr;
use vstd::set;
use vstd::set_lib;
use vstd::layout;
use core::marker::PhantomData;

verus! {

/// Concrete representation of a pointer to an array
/// The length of the array is not stored in the pointer
pub struct ArrayPtr<V, const N: usize> {
    pub addr: usize,
    pub _type: PhantomData<[V; N]>,
}

#[verifier::external_body]
#[verifier::accept_recursive_types(V)]
pub tracked struct PointsToArray<V, const N: usize> {
    phantom: core::marker::PhantomData<[V; N]>,
    no_copy: NoCopy,
}

pub ghost struct PointsToArrayData<V, const N: usize> {
    pub ptr: *mut [V; N],
    pub value: [raw_ptr::MemContents<V>; N],
}

#[verifier::inline]
pub open spec fn is_mem_contents_all_init<V, const N: usize>(
    arr: [raw_ptr::MemContents<V>; N],
) -> bool {
    forall|index: int| 0 <= index < N ==> #[trigger] arr[index].is_init()
}

#[verifier::inline]
pub open spec fn is_mem_contents_all_uninit<V, const N: usize>(
    arr: [raw_ptr::MemContents<V>; N],
) -> bool {
    forall|index: int| 0 <= index < N ==> #[trigger] arr[index].is_uninit()
}

pub uninterp spec fn mem_contents_unwrap<V, const N: usize>(
    arr: [raw_ptr::MemContents<V>; N],
) -> (res: raw_ptr::MemContents<[V; N]>)
    recommends
        is_mem_contents_all_init(arr) || is_mem_contents_all_uninit(arr),
;

pub uninterp spec fn mem_contents_wrap<V, const N: usize>(
    data: raw_ptr::MemContents<[V; N]>,
) -> (res: [raw_ptr::MemContents<V>; N]);

pub axiom fn axiom_mem_contents_unwrap_init_correctness<V, const N: usize>(
    arr: [raw_ptr::MemContents<V>; N],
    res: raw_ptr::MemContents<[V; N]>,
)
    requires
        res == mem_contents_unwrap(arr),
        is_mem_contents_all_init(arr),
    ensures
        res.is_init(),
        forall|index: int| 0 <= index < N ==> #[trigger] res.value()[index] == arr[index].value(),
;

pub axiom fn axiom_mem_contents_unwrap_uninit_correctness<V, const N: usize>(
    arr: [raw_ptr::MemContents<V>; N],
    res: raw_ptr::MemContents<[V; N]>,
)
    requires
        res == mem_contents_unwrap(arr),
        is_mem_contents_all_uninit(arr),
    ensures
        res.is_uninit(),
;

pub axiom fn axiom_mem_contents_wrap_correctness<V, const N: usize>(
    data: raw_ptr::MemContents<[V; N]>,
    res: [raw_ptr::MemContents<V>; N],
)
    requires
        res == mem_contents_wrap(data),
    ensures
        data.is_uninit() ==> is_mem_contents_all_uninit(res),
        data.is_init() ==> is_mem_contents_all_init(res) && forall|index: int|
            0 <= index < N ==> #[trigger] res[index].value() == data.value()[index],
;

impl<V, const N: usize> PointsToArrayData<V, N> {
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

impl<T, const N: usize> View for PointsToArray<T, N> {
    type V = PointsToArrayData<T, N>;

    uninterp spec fn view(&self) -> Self::V;
}

impl<V, const N: usize> PointsToArray<V, N> {
    #[verifier::inline]
    pub open spec fn ptr(&self) -> *mut [V; N] {
        self@.ptr
    }

    #[verifier::inline]
    pub open spec fn opt_value(&self) -> [raw_ptr::MemContents<V>; N] {
        self@.value
    }

    #[verifier::inline]
    pub open spec fn is_init(&self, index: int) -> bool {
        0 <= index < N && self.opt_value()[index].is_init()
    }

    #[verifier::inline]
    pub open spec fn is_uninit(&self, index: int) -> bool {
        0 <= index < N && self.opt_value()[index].is_uninit()
    }

    #[verifier::inline]
    pub open spec fn is_init_all(&self) -> bool {
        is_mem_contents_all_init(self.opt_value())
    }

    #[verifier::inline]
    pub open spec fn is_uninit_all(&self) -> bool {
        is_mem_contents_all_uninit(self.opt_value())
    }

    #[verifier::inline]
    pub open spec fn value(&self) -> Seq<V>
        recommends
            self.is_init_all(),
    {
        let opt_value = self.opt_value();
        Seq::new(N as nat, |i: int| opt_value[i].value())
    }

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
    pub proof fn is_disjoint<S, const M: usize>(&self, other: &PointsToArray<S, M>)
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
    }
}

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
pub exec fn ptr_mut_read_all<V, const N: usize>(
    ptr: *mut [V; N],
    Tracked(perm): Tracked<&mut PointsToArray<V, N>>,
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
pub exec fn ptr_ref_at<V, const N: usize>(
    ptr: *mut [V; N],
    Tracked(perm): Tracked<&PointsToArray<V, N>>,
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
    Tracked(perm): Tracked<&PointsToArray<V, N>>,
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

/// Permission to access an array of values
pub tracked struct PointsTo<V, const N: usize> {
    points_to: PointsToArray<V, N>,
    exposed: raw_ptr::IsExposed,
    dealloc: Option<raw_ptr::Dealloc>,
}

broadcast use {
    raw_ptr::group_raw_ptr_axioms,
    set_lib::group_set_lib_default,
    set::group_set_axioms,
};

impl<V, const N: usize> ArrayPtr<V, N> {
    /// Spec: cast the pointer to an integer
    #[verifier::inline]
    pub open spec fn addr_spec(&self) -> usize {
        self.addr
    }

    /// Impl: cast the pointer to an integer
    #[inline(always)]
    #[verifier::when_used_as_spec(addr_spec)]
    pub exec fn addr(&self) -> usize
        returns
            self.addr,
    {
        self.addr
    }

    /// Impl: cast an integer to the pointer
    #[inline(always)]
    pub exec fn from_addr(addr: usize) -> (res: Self)
        ensures
            res.addr == addr,
    {
        Self { addr, _type: PhantomData }
    }
}

impl<V, const N: usize> PointsTo<V, N> {
    /// Spec: cast the permission to an integer
    pub closed spec fn addr(&self) -> usize {
        self.points_to.ptr()@.addr
    }

    /// Spec: cast the permission to a pointer
    pub open spec fn pptr(&self) -> ArrayPtr<V, N> {
        ArrayPtr { addr: self.addr(), _type: PhantomData }
    }

    /// Spec: invariants for the ArrayPtr permissions
    /// TODO: uncomment the below if "external_type_specification: Const params not yet supported" is fixed
    /// #[verifier::type_invariant]
    pub closed spec fn wf(&self) -> bool {
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

    pub closed spec fn points_to(&self) -> PointsToArray<V, N> {
        self.points_to
    }

    pub open spec fn opt_value(&self) -> [raw_ptr::MemContents<V>; N] {
        self.points_to().opt_value()
    }

    pub open spec fn value(&self) -> Seq<V>
        recommends
            self.is_init_all(),
    {
        self.points_to().value()
    }

    #[verifier::inline]
    pub open spec fn is_init(&self, index: int) -> bool {
        self.points_to().is_init(index)
    }

    #[verifier::inline]
    pub open spec fn is_uninit(&self, index: int) -> bool {
        !self.points_to().is_init(index)
    }

    #[verifier::inline]
    pub open spec fn is_init_all(&self) -> bool {
        self.points_to().is_init_all()
    }

    #[verifier::inline]
    pub open spec fn is_uninit_all(&self) -> bool {
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
            self.pptr() == old(self).pptr(),
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
    }
}

impl<V, const N: usize> PointsToArray<V, N> {
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
    }
}

impl<V, const N: usize> Clone for ArrayPtr<V, N> {
    fn clone(&self) -> (res: Self)
        ensures
            res === *self,
    {
        Self { ..*self }
    }
}

impl<V, const N: usize> Copy for ArrayPtr<V, N> {

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

impl<V, const N: usize> ArrayPtr<V, N> {
    pub exec fn empty() -> (res: (ArrayPtr<V, N>, Tracked<PointsTo<V, N>>))
        requires
            layout::size_of::<[V; N]>() > 0,
        ensures
            res.1@.wf(),
            res.1@.pptr() == res.0,
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
        let ptr = ArrayPtr { addr: p as usize, _type: PhantomData };
        (ptr, Tracked(pt))
    }

    #[inline(always)]
    pub exec fn make_as(&self, Tracked(perm): Tracked<&mut PointsTo<V, N>>, value: V) where V: Copy
        requires
            old(perm).wf(),
            old(perm).pptr() == self,
            old(perm).is_uninit_all(),
        ensures
            perm.wf(),
            perm.pptr() == self,
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
            res.1@.pptr() == res.0,
            forall|i: int|
                0 <= i < N ==> #[trigger] res.1@.opt_value()[i] == raw_ptr::MemContents::Init(dft),
    {
        let (p, Tracked(perm)) = ArrayPtr::empty();
        proof {
            assert(perm.wf());
            assert(perm.pptr() == p);
            assert(perm.is_uninit_all());
        }
        p.make_as(Tracked(&mut perm), dft);
        (p, Tracked(perm))
    }

    pub exec fn free(self, Tracked(perm): Tracked<PointsTo<V, N>>)
        requires
            perm.wf(),
            perm.pptr() == self,
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
    pub exec fn insert(&self, Tracked(perm): Tracked<&mut PointsTo<V, N>>, index: usize, value: V)
        requires
            old(perm).wf(),
            old(perm).pptr() == self,
            old(perm).is_uninit(index as int),
            index < N,
        ensures
            perm.wf(),
            perm.pptr() == self,
            perm.is_init(index as int),
            forall|i: int|
                0 <= i < N && i != index ==> perm.opt_value()[i] == old(perm).opt_value()[i],
            perm.opt_value()[index as int] == raw_ptr::MemContents::Init(value),
    {
        let ptr: *mut [V; N] = raw_ptr::with_exposed_provenance(self.addr, Tracked(perm.exposed));

        assert(perm.points_to().is_uninit(index as int));
        ptr_mut_write_at(ptr, Tracked(&mut perm.points_to), index, value);
    }

    /// Take the `value` at `index`
    /// The value is moved out of the array.
    /// Requires the slot at `index` to be initialized.
    /// Afterwards, the slot is uninitialized.
    #[inline(always)]
    pub exec fn take_at(&self, Tracked(perm): Tracked<&mut PointsTo<V, N>>, index: usize) -> (res:
        V) where V: Copy
        requires
            old(perm).wf(),
            old(perm).pptr() == self,
            old(perm).is_init(index as int),
            index < N,
        ensures
            perm.wf(),
            perm.pptr() == self,
            perm.is_uninit(index as int),
            forall|i: int|
                0 <= i < N && i != index ==> perm.opt_value()[i] == old(perm).opt_value()[i],
            res == old(perm).opt_value()[index as int].value(),
    {
        let ptr: *mut [V; N] = raw_ptr::with_exposed_provenance(self.addr, Tracked(perm.exposed));

        assert(perm.points_to().is_init(index as int));
        ptr_mut_read_at(ptr, Tracked(&mut perm.points_to), index)
    }

    /// Take all the values of the array
    /// The values are moved out of the array.
    /// Requires all slots to be initialized.
    /// Afterwards, all slots are uninitialized.
    #[inline(always)]
    pub exec fn take_all(&self, Tracked(perm): Tracked<&mut PointsTo<V, N>>) -> (res: [V; N])
        requires
            old(perm).wf(),
            old(perm).pptr() == self,
            old(perm).is_init_all(),
        ensures
            perm.wf(),
            perm.pptr() == self,
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
            perm.pptr() == self,
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
            old(perm).pptr() == self,
            old(perm).is_init(index as int),
            index < N,
        ensures
            perm.wf(),
            perm.pptr() == self,
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
            perm.pptr() == self,
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
            perm.pptr() == self,
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
            old(perm).pptr() == self,
            index < N,
        ensures
            perm.wf(),
            perm.pptr() == self,
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
            old(perm).pptr() == self,
            index < N,
        ensures
            perm.wf(),
            perm.pptr() == self,
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
            perm.pptr() == self,
            perm.is_init(index as int),
            index < N,
        ensures
            res == perm.opt_value()[index as int].value(),
    {
        *self.borrow_at(Tracked(perm), index)
    }
}

} // verus!
