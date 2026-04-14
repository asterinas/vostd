// SPDX-License-Identifier: MPL-2.0
use core::{marker::PhantomData, ops::Deref, ptr::NonNull};

use vstd::prelude::*;

use vstd_extra::drop_tracking::*;
use vstd_extra::ownership::*;

use crate::mm::frame::meta::mapping::{frame_to_index, frame_to_meta, meta_to_frame};
use crate::mm::frame::meta::{has_safe_slot, AnyFrameMeta, MetaSlot};
use crate::mm::frame::MetaPerm;
use crate::mm::{Paddr, PagingLevel, Vaddr};
use crate::specs::arch::mm::{MAX_PADDR, PAGE_SIZE};
use crate::specs::mm::frame::frame_specs::BorrowDebt;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;

use super::Frame;

use vstd::simple_pptr::PPtr;

verus! {

/// A struct that can work as `&'a Frame<M>`.
pub struct FrameRef<'a, M: AnyFrameMeta> {
    pub inner: ManuallyDrop<Frame<M>>,
    pub _marker: PhantomData<&'a Frame<M>>,
}

impl<M: AnyFrameMeta> Deref for FrameRef<'_, M> {
    type Target = Frame<M>;

    #[verus_spec(ensures returns &self.inner.0)]
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

#[verus_verify]
impl<M: AnyFrameMeta> FrameRef<'_, M> {
    /// Borrows the [`Frame`] at the physical address as a [`FrameRef`].
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// The raw frame address must be well-formed (`has_safe_slot(raw)`).
    /// The slot's `raw_count` must be `<= 1`.
    /// ## Postconditions
    /// The result points to the frame at the physical address.
    /// `raw_count` is 1 after the call (from_raw sets to 0, ManuallyDrop::new adds 1).
    /// All other slot fields are preserved.
    /// ## Safety
    /// By providing a borrowed `MetaPerm` of the appropriate type, the caller ensures that the frame
    /// has that type and that the `FrameRef` will be useless if it outlives the frame.
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(perm): Tracked<&MetaPerm<M>>
        requires
            Frame::<M>::from_raw_requires_safety(*old(regions), raw),
            old(regions).slot_owners[frame_to_index(raw)].raw_count <= 1,
            old(regions).slot_owners[frame_to_index(raw)].inner_perms.ref_count.value()
                != crate::mm::frame::meta::REF_COUNT_UNUSED,
            perm.points_to.is_init(),
            perm.points_to.addr() == frame_to_meta(raw),
            perm.points_to.value().wf(old(regions).slot_owners[frame_to_index(raw)]),
        ensures
            final(regions).inv(),
            r.inner.0.ptr.addr() == frame_to_meta(raw),
            // raw_count is always 1 after borrow (from_raw → 0, ManuallyDrop::new → 1)
            final(regions).slot_owners[frame_to_index(raw)].raw_count == 1,
            // All other fields of this slot are preserved
            final(regions).slot_owners[frame_to_index(raw)].inner_perms
                == old(regions).slot_owners[frame_to_index(raw)].inner_perms,
            final(regions).slot_owners[frame_to_index(raw)].self_addr
                == old(regions).slot_owners[frame_to_index(raw)].self_addr,
            final(regions).slot_owners[frame_to_index(raw)].usage
                == old(regions).slot_owners[frame_to_index(raw)].usage,
            final(regions).slot_owners[frame_to_index(raw)].path_if_in_pt
                == old(regions).slot_owners[frame_to_index(raw)].path_if_in_pt,
            // Other slots are unchanged
            forall |i: usize|
                #![trigger final(regions).slot_owners[i]]
                i != frame_to_index(raw) ==> final(regions).slot_owners[i]
                    == old(regions).slot_owners[i],
            final(regions).slot_owners.dom() =~= old(regions).slot_owners.dom(),
            // Slots: from_raw inserts perm, ManuallyDrop::new preserves
            final(regions).slots == old(regions).slots.insert(frame_to_index(raw), perm.points_to),
    )]
    pub(in crate::mm) fn borrow_paddr(raw: Paddr) -> Self {
        proof {
            broadcast use crate::mm::frame::meta::mapping::group_page_meta;
            old(regions).inv_implies_correct_addr(raw);
        }

        proof_decl! {
            let tracked debt: BorrowDebt;
        }

        #[verus_spec(with Tracked(regions), Tracked(perm) => Tracked(debt))]
        let frame = Frame::from_raw(raw);

        proof {
            Frame::lemma_from_raw_manuallydrop_general(raw, frame, *old(regions), *regions, debt);
        }

        Self { inner: ManuallyDrop::new(frame, Tracked(regions)), _marker: PhantomData }
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
            old(regions).slot_owners[frame_to_index(meta_to_frame(raw.addr()))].raw_count
                == 0,
    //            old(regions).slot_owners[frame_to_index(meta_to_frame(raw.addr()))].read_only == raw.addr(),

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

    fn into_raw(self, Tracked(regions): Tracked<&mut MetaRegionOwners>) -> PPtr<Self::Target> {
        let ptr = self.ptr;
        assert(self.constructor_requires(*old(regions)));
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
        let dropped = ManuallyDrop::<Frame<M>>::new(
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
