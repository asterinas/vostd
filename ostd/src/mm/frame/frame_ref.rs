// SPDX-License-Identifier: MPL-2.0
use core::{marker::PhantomData, mem::ManuallyDrop, ops::Deref, ptr::NonNull};

use vstd::prelude::*;

use vstd_extra::ownership::*;
use vstd_extra::undroppable::*;

use aster_common::prelude::frame::*;
use aster_common::prelude::*;

use super::Frame;
use crate::{mm::Paddr /*, sync::non_null::NonNullPtr*/};

use vstd::simple_pptr::PPtr;

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
            Tracked(perm): Tracked<&MetaPerm<M>>,
        requires
            raw % PAGE_SIZE() == 0,
            raw < MAX_PADDR(),
            !old(regions).slots.contains_key(frame_to_index(raw)),
            old(regions).dropped_slots.contains_key(frame_to_index(raw)),
            old(regions).inv(),
        ensures
            regions.inv()
    )]
    pub fn borrow_paddr(raw: Paddr) -> Self {
        #[verus_spec(with Tracked(regions), Tracked(perm))]
        let frame = Frame::from_raw(raw);

        Self {
            // SAFETY: The caller ensures the safety.
            inner: NeverDrop::new(frame, Tracked(regions)),
            _marker: PhantomData,
        }
    }
}

// TODO: I moved this here to avoid having to pull the rest of `sync` into the verification.
// Once it is pulled in, we should delete this one.
/// A trait that abstracts non-null pointers.
///
/// All common smart pointer types such as `Box<T>`,  `Arc<T>`, and `Weak<T>`
/// implement this trait as they can be converted to and from the raw pointer
/// type of `*const T`.
///
/// # Safety
///
/// This trait must be implemented correctly (according to the doc comments for
/// each method). Types like [`Rcu`] rely on this assumption to safely use the
/// raw pointers.
///
/// [`Rcu`]: super::Rcu
pub unsafe trait NonNullPtr: 'static + Sized {
    /// The target type that this pointer refers to.
    // TODO: Support `Target: ?Sized`.
    type Target;

    /// A type that behaves just like a shared reference to the `NonNullPtr`.
    type Ref<'a>;

    /// The power of two of the pointer alignment.
    fn ALIGN_BITS() -> u32;

    /// Converts to a raw pointer.
    ///
    /// Each call to `into_raw` must be paired with a call to `from_raw`
    /// in order to avoid memory leakage.
    ///
    /// The lower [`Self::ALIGN_BITS`] of the raw pointer is guaranteed to
    /// be zero. In other words, the pointer is guaranteed to be aligned to
    /// `1 << Self::ALIGN_BITS`.
    fn into_raw(self) -> PPtr<Self::Target>;

    /// Converts back from a raw pointer.
    ///
    /// # Safety
    ///
    /// 1. The raw pointer must have been previously returned by a call to
    ///    `into_raw`.
    /// 2. The raw pointer must not be used after calling `from_raw`.
    ///
    /// Note that the second point is a hard requirement: Even if the
    /// resulting value has not (yet) been dropped, the pointer cannot be
    /// used because it may break Rust aliasing rules (e.g., `Box<T>`
    /// requires the pointer to be unique and thus _never_ aliased).
    unsafe fn from_raw(ptr: PPtr<Self::Target>) -> Self;

    /// Obtains a shared reference to the original pointer.
    ///
    /// # Safety
    ///
    /// The original pointer must outlive the lifetime parameter `'a`, and during `'a`
    /// no mutable references to the pointer will exist.
    unsafe fn raw_as_ref<'a>(
        raw: PPtr<Self::Target>,
        Tracked(regions): Tracked<&mut MetaRegionOwners>,
    ) -> Self::Ref<'a>
        requires
            old(regions).inv(),
            old(regions).slots.contains_key(frame_to_index(meta_to_frame(raw.addr()))),
            !old(regions).dropped_slots.contains_key(frame_to_index(meta_to_frame(raw.addr()))),
    ;

    /// Converts a shared reference to a raw pointer.
    fn ref_as_raw(ptr_ref: Self::Ref<'_>) -> PPtr<Self::Target>;
}

pub assume_specification[ usize::trailing_zeros ](_0: usize) -> u32
;

// SAFETY: `Frame` is essentially a `*const MetaSlot` that could be used as a non-null
// `*const` pointer.
unsafe impl<M: AnyFrameMeta + ?Sized + 'static> NonNullPtr for Frame<M> {
    type Target = PhantomData<Self>;

    type Ref<'a> = FrameRef<'a, M>;

    fn ALIGN_BITS() -> u32 {
        core::mem::align_of::<MetaSlot>().trailing_zeros()
    }

    fn into_raw(self) -> PPtr<Self::Target> {
        let ptr = self.ptr;
        let _ = ManuallyDrop::new(self);
        PPtr::<Self::Target>::from_addr(ptr.addr())
    }

    unsafe fn from_raw(raw: PPtr<Self::Target>) -> Self {
        Self { ptr: PPtr::<MetaSlot>::from_addr(raw.addr()), _marker: PhantomData }
    }

    unsafe fn raw_as_ref<'a>(
        raw: PPtr<Self::Target>,
        Tracked(regions): Tracked<&mut MetaRegionOwners>,
    ) -> Self::Ref<'a> {
        let dropped = NeverDrop::<Frame<M>>::new(
            Frame { ptr: PPtr::<MetaSlot>::from_addr(raw.addr()), _marker: PhantomData },
            Tracked(regions),
        );
        Self::Ref { inner: dropped, _marker: PhantomData }
    }

    fn ref_as_raw(ptr_ref: Self::Ref<'_>) -> PPtr<Self::Target> {
        PPtr::from_addr(ptr_ref.inner.ptr.addr())
    }
}

} // verus!
