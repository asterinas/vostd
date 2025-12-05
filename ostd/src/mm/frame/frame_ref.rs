// SPDX-License-Identifier: MPL-2.0
use core::{marker::PhantomData, mem::ManuallyDrop, ops::Deref, ptr::NonNull};

use vstd::prelude::*;

use vstd_extra::manually_drop::*;
use vstd_extra::ownership::*;

use aster_common::prelude::frame::*;
use aster_common::prelude::*;

use super::Frame;
use crate::{mm::Paddr /*, sync::non_null::NonNullPtr*/};

verus! {

#[verus_verify]
impl<M: AnyFrameMeta> FrameRef<'_, M> {
    /// Borrows the [`Frame`] at the physical address as a [`FrameRef`].
    ///
    /// # Safety
    ///
    /// The caller must ensure that:
    ///  - the frame outlives the created reference, so that the reference can
    ///    be seen as borrowed from that frame.
    ///  - the type of the [`FrameRef`] (`M`) matches the borrowed frame.
    #[rustc_allow_incoherent_impl]
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
        requires
            raw % PAGE_SIZE() == 0,
            raw < MAX_PADDR(),
            !old(regions).slots.contains_key(frame_to_index(raw)),
            old(regions).dropped_slots.contains_key(frame_to_index(raw)),
            old(regions).inv(),
    )]
    pub fn borrow_paddr(raw: Paddr) -> Self {
        #[verus_spec(with Tracked(regions))]
        let frame = Frame::from_raw(raw);

        Self {
            // SAFETY: The caller ensures the safety.
            inner: frame,
            _marker: PhantomData,
        }
    }
}

// SAFETY: `Frame` is essentially a `*const MetaSlot` that could be used as a non-null
// `*const` pointer.
/*unsafe impl<M: AnyFrameMeta + ?Sized> NonNullPtr for Frame<M> {
    type Target = PhantomData<Self>;

    type Ref<'a>
        = FrameRef<'a, M>
    where
        Self: 'a;

    const ALIGN_BITS: u32 = core::mem::align_of::<MetaSlot>().trailing_zeros();

    fn into_raw(self) -> NonNull<Self::Target> {
        let ptr = NonNull::new(self.ptr.cast_mut()).unwrap();
        let _ = ManuallyDrop::new(self);
        ptr.cast()
    }

    unsafe fn from_raw(raw: NonNull<Self::Target>) -> Self {
        Self {
            ptr: raw.as_ptr().cast_const().cast(),
            _marker: PhantomData,
        }
    }

    unsafe fn raw_as_ref<'a>(raw: NonNull<Self::Target>) -> Self::Ref<'a> {
        Self::Ref {
            inner: ManuallyDrop::new(Frame {
                ptr: raw.as_ptr().cast_const().cast(),
                _marker: PhantomData,
            }),
            _marker: PhantomData,
        }
    }

    fn ref_as_raw(ptr_ref: Self::Ref<'_>) -> core::ptr::NonNull<Self::Target> {
        NonNull::new(ptr_ref.inner.ptr.cast_mut()).unwrap().cast()
    }
}*/
} // verus!
