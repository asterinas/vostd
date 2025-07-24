use vstd::prelude::*;

use core::marker::PhantomData;
use core::mem::ManuallyDrop;
use core::ops::Deref;

use crate::mm::Paddr;

use super::{allocator::AllocatorModel, meta::AnyFrameMeta, Frame};

verus! {

/// A struct that can work as `&'a Frame<M>`.
// pub struct FrameRef<'a, M: AnyFrameMeta + ?Sized> { // NOTE: Verus does not support dyn type, so we remove it currently
pub struct FrameRef<'a, M: AnyFrameMeta> {
    pub inner: ManuallyDrop<Frame<M>>,
    pub _marker: PhantomData<&'a Frame<M>>,
}

impl<'a, M: AnyFrameMeta> FrameRef<'a, M> {
    /// Borrows the [`Frame`] at the physical address as a [`FrameRef`].
    ///
    /// # Safety
    ///
    /// The caller must ensure that:
    ///  - the frame outlives the created reference, so that the reference can
    ///    be seen as borrowed from that frame.
    ///  - the type of the [`FrameRef`] (`M`) matches the borrowed frame.
    pub(in crate::mm) fn borrow_paddr(
        raw: Paddr,
        Tracked(alloc_model): Tracked<&AllocatorModel<M>>,
    ) -> (res: Self)
        requires
            alloc_model.invariants(),
            alloc_model.meta_map.contains_key(raw as int),
            alloc_model.meta_map[raw as int].pptr() == alloc_model.meta_map[raw as int].pptr(),
        ensures
            res.deref().start_paddr() == raw,
            res.deref().meta_ptr == alloc_model.meta_map[raw as int].pptr(),
    {
        Self {
            inner: ManuallyDrop::new(Frame::from_raw(raw, Tracked(alloc_model))),
            _marker: PhantomData,
        }
    }
}

impl<'a, M: AnyFrameMeta> Deref for FrameRef<'a, M> {
    type Target = Frame<M>;

    #[verifier::when_used_as_spec(frame_ref_deref)]
    fn deref(&self) -> &Self::Target
        returns
            frame_ref_deref(self),
    {
        &self.inner
    }
}

pub open spec fn frame_ref_deref<'s, 'a, M: AnyFrameMeta>(self_: &'s FrameRef<'a, M>) -> &'s Frame<
    M,
> {
    &self_.inner
}

} // verus!
