// SPDX-License-Identifier: MPL-2.0
use core::{marker::PhantomData, ops::Deref, ptr::NonNull};

use vstd::prelude::*;
use vstd::simple_pptr::PPtr;
use vstd_extra::cast_ptr::Repr;
use vstd_extra::drop_tracking::*;
use vstd_extra::prelude::*;

use crate::mm::frame::MetaPerm;
use crate::mm::frame::meta::mapping::{frame_to_index, frame_to_meta, meta_to_frame};
use crate::mm::frame::meta::{AnyFrameMeta, MetaSlot, has_safe_slot};
use crate::mm::{Paddr, PagingLevel, Vaddr};
use crate::specs::arch::mm::{MAX_PADDR, PAGE_SIZE};
use crate::specs::mm::frame::meta_owners::MetaSlotStorage;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;

use super::Frame;

verus! {

/// A struct that can work as `&'a Frame<M>`.
pub struct FrameRef<'a, M: AnyFrameMeta + Repr<MetaSlotStorage>> {
    pub inner: ManuallyDrop<Frame<M>>,
    pub _marker: PhantomData<&'a Frame<M>>,
}

impl<M: AnyFrameMeta + Repr<MetaSlotStorage>> Deref for FrameRef<'_, M> {
    type Target = Frame<M>;

    #[verus_spec(ensures returns &self.inner.0)]
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

#[verus_verify]
impl<M: AnyFrameMeta + Repr<MetaSlotStorage>> FrameRef<'_, M> {
    /// Borrows the [`Frame`] at the physical address as a [`FrameRef`].
    ///
    /// Under the borrow-protocol redesign, `from_raw` mints one
    /// `frame_obligations` entry at the slot index and `MD::new`
    /// immediately consumes it — net-zero on the ledger across this
    /// borrow. The slot's `ref_count` is unchanged (the existing live
    /// reference covers the borrow's lifetime via the `'a` lifetime).
    ///
    /// # Safety
    /// By providing a borrowed `MetaPerm` of the appropriate type, the
    /// caller ensures that the frame has that type and that the
    /// `FrameRef` will be useless if it outlives the frame.
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
        requires
            Frame::<M>::from_raw_requires_safety(*old(regions), raw),
            old(regions).slots.contains_key(frame_to_index(raw)),
        ensures
            final(regions).inv(),
            r.inner.0.ptr.addr() == frame_to_meta(raw),
            final(regions).slot_owners == old(regions).slot_owners,
            final(regions).slots == old(regions).slots,
            final(regions).frame_obligations == old(regions).frame_obligations,
    )]
    pub(in crate::mm) unsafe fn borrow_paddr(raw: Paddr) -> Self {
        proof {
            broadcast use crate::mm::frame::meta::mapping::group_page_meta;

            old(regions).inv_implies_correct_addr(raw);
        }

        let ghost idx = frame_to_index(raw);
        let ghost regions0 = *regions;

        proof_decl! {
            let tracked from_raw_obl: vstd_extra::drop_tracking::DropObligation<usize>;
        }
        // `from_raw` mints one `frame_obligations` entry at the slot and
        // hands back the token; the token is dropped affinely (the ledger
        // entry is what matters). `MD::new` then consumes that entry. Net
        // effect on the ledger: zero.
        let frame = unsafe {
            #[verus_spec(with Tracked(regions) => Tracked(from_raw_obl))]
            Frame::from_raw(raw)
        };

        let inner = ManuallyDrop::new(frame, Tracked(regions));

        proof {
            // `from_raw` did `insert(idx)`; `MD::new` did `remove(idx)`.
            // The pair is identity on the multiset.
            assert(regions.frame_obligations == regions0.frame_obligations);
        }

        Self { inner, _marker: PhantomData }
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
pub unsafe trait NonNullPtr: 'static + Sized + TrackDrop<State = MetaRegionOwners> {
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
    fn into_raw(self, Tracked(regions): Tracked<&mut MetaRegionOwners>) -> PPtr<Self::Target>
        requires
            self.constructor_requires(*old(regions)),
    ;

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
            old(regions).slot_owners.contains_key(frame_to_index(meta_to_frame(raw.addr()))),
    ;

    /// Converts a shared reference to a raw pointer.
    fn ref_as_raw(ptr_ref: Self::Ref<'_>) -> PPtr<Self::Target>;
}

pub assume_specification[ usize::trailing_zeros ](_0: usize) -> u32
;

// SAFETY: `Frame` is essentially a `*const MetaSlot` that could be used as a non-null
// `*const` pointer.
unsafe impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + 'static> NonNullPtr for Frame<M> {
    type Target = PhantomData<Self>;

    type Ref<'a> = FrameRef<'a, M>;

    fn ALIGN_BITS() -> u32 {
        core::mem::align_of::<MetaSlot>().trailing_zeros()
    }

    fn into_raw(self, Tracked(regions): Tracked<&mut MetaRegionOwners>) -> PPtr<Self::Target> {
        let ptr = self.ptr;
        proof {
            // Mint the obligation that `MD::new` will immediately
            // consume — net-zero on the ledger; the Frame value is
            // forgotten inside the wrapper, and `ref_count` (set by the
            // original producer) stays elevated to balance the eventual
            // `from_raw + drop`.
            let tracked _ = regions.tracked_mint_frame_obligation(self.index());
        }
        let _ = ManuallyDrop::new(self, Tracked(regions));
        PPtr::<Self::Target>::from_addr(ptr.addr())
    }

    unsafe fn from_raw(raw: PPtr<Self::Target>) -> Self {
        Self { ptr: PPtr::<MetaSlot>::from_addr(raw.addr()), _marker: PhantomData }
    }

    unsafe fn raw_as_ref<'a>(
        raw: PPtr<Self::Target>,
        Tracked(regions): Tracked<&mut MetaRegionOwners>,
    ) -> Self::Ref<'a> {
        let frame = Frame::<M> {
            ptr: PPtr::<MetaSlot>::from_addr(raw.addr()),
            _marker: PhantomData,
        };
        proof {
            let tracked _ = regions.tracked_mint_frame_obligation(frame.index());
        }
        let dropped = ManuallyDrop::<Frame<M>>::new(frame, Tracked(regions));
        Self::Ref { inner: dropped, _marker: PhantomData }
    }

    fn ref_as_raw(ptr_ref: Self::Ref<'_>) -> PPtr<Self::Target> {
        PPtr::from_addr(ptr_ref.inner.ptr.addr())
    }
}

} // verus!
