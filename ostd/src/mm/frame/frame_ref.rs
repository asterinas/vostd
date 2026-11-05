// SPDX-License-Identifier: MPL-2.0
use vstd::prelude::*;
use vstd_extra::{
    cast_ptr::Repr,
    prelude::*,
    raw_ptr::{ExposedPointsTo, ptr_from_addr},
};

use crate::specs::{
    arch::valid_frame_paddr,
    mm::frame::{
        frame_specs::FrameRawPerms,
        mapping::meta_to_index,
        meta_owners::{FracMetadataPerm, MetaSlotStorage, MetadataPerm, typed_meta_wf},
        meta_region_owners::MetaRegionOwners,
    },
};

use super::{
    Frame,
    meta::{AnyFrameMeta, MetaSlot},
};
use crate::mm::frame::meta::mapping::frame_to_meta;
use crate::mm::{Paddr, Vaddr};
use core::{marker::PhantomData, mem::ManuallyDrop, ops::Deref, ptr::NonNull};

verus! {

/// A struct that can work as `&'a Frame<M>`.
pub struct FrameRef<'a, M: AnyFrameMeta + ?Sized + Repr<MetaSlotStorage>> {
    inner: ManuallyDrop<Frame<M>>,
    _marker: PhantomData<&'a Frame<M>>,
    /// A reference to one fractional permission for the currently installed metadata.
    #[cfg(verus_keep_ghost_body)]
    tracked_metadata_perm: Tracked<Option<&'a FracMetadataPerm>>,
}

impl<'a, M: AnyFrameMeta + ?Sized + Repr<MetaSlotStorage>> FrameRef<'a, M> {
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.inner@.tracked_metadata_perm@ is None
    }
}

impl<'a, M: AnyFrameMeta + ?Sized + Repr<MetaSlotStorage>> View for FrameRef<'a, M> {
    type V = Frame<M>;

    closed spec fn view(&self) -> Self::V {
        Frame {
            tracked_metadata_perm: Tracked(
                match self.tracked_metadata_perm@ {
                    Some(permission) => Some(*permission),
                    None => None,
                },
            ),
            ..self.inner@
        }
    }
}

impl<M: AnyFrameMeta + ?Sized + Repr<MetaSlotStorage>> Inv for FrameRef<'_, M> {
    open spec fn inv(self) -> bool {
        self@.inv()
    }
}

#[verus_verify]
impl<'a, M: AnyFrameMeta + Repr<MetaSlotStorage>> FrameRef<'a, M> {
    /// Borrows the [`Frame`] at the physical address as a [`FrameRef`].
    ///
    /// # Safety
    ///
    /// The caller must ensure that:
    ///  - the frame outlives the created reference, so that the reference can
    ///    be seen as borrowed from that frame.
    ///  - the type of the [`FrameRef`] (`M`) matches the borrowed frame.
    #[verus_spec(r =>
        with
            Tracked(slot_perm): Tracked<&'static ExposedPointsTo<MetaSlot>>,
            Tracked(permission): Tracked<Option<&'a FracMetadataPerm>>,
        requires
            valid_frame_paddr(raw),
            slot_perm.ptr().addr() == frame_to_meta(raw),
            slot_perm.is_init(),
            permission matches Some(counted) ==> {
                &&& counted.frac() == 1
                &&& MetaSlot::perms_related(*slot_perm, counted.resource())
            },
        ensures
            r.slot_vaddr() == frame_to_meta(raw),
            r@.ptr_inv(),
            r@.tracked_slot_perm@ == slot_perm,
            r@.tracked_metadata_perm@ == match permission {
                Some(counted) => Some(*counted),
                None => None,
            },
            permission matches Some(counted) ==> {
                &&& r.inv()
                &&& forall|repr_perm: M::ReprPerm|
                    #[trigger] typed_meta_wf::<M>(*slot_perm, counted.resource(), repr_perm)
                    ==> r.external_meta_wf(counted.resource(), repr_perm)
            },
    )]
    pub(in crate::mm) unsafe fn borrow_paddr(raw: Paddr) -> Self {
        proof_with!{ tracked_slot_perm: Tracked(slot_perm), tracked_metadata_perm: Tracked(None)}
        /* `Frame::from_raw` requires an owning metadata permission; construct the borrowed handle with its slot permission.
         * Origin Rust: Self {
         *     // SAFETY: The caller ensures the safety.
         *     inner: ManuallyDrop::new(unsafe { Frame::from_raw(raw) }),
         *     _marker: PhantomData,
         * }
         */
        let frame = Frame::<M> {
            ptr: ptr_from_addr(frame_to_meta(raw), Tracked(slot_perm)),
            _marker: PhantomData,
        };

        let inner = ManuallyDrop::new(frame);

        proof_with! { tracked_metadata_perm: Tracked(permission) }
        Self { inner, _marker: PhantomData }
    }
}

impl<M: AnyFrameMeta + ?Sized + Repr<MetaSlotStorage>> Deref for FrameRef<'_, M> {
    type Target = Frame<M>;

    #[verus_spec(r => ensures *r == (Frame { tracked_metadata_perm: Tracked(None), ..self@ }))]
    fn deref(&self) -> &Self::Target {
        proof {
            use_type_invariant(self);
        }
        &self.inner
    }
}

// TODO: Use NonNullPtr in `sync`.
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

    #[cfg(not(feature = "irc11"))]
    type Permission: Inv;

    #[cfg(feature = "irc11")]
    type Permission: Inv + vstd::thread_view::Objective;

    /// A type that behaves just like a shared reference to the `NonNullPtr`.
    type Ref<'a>: Inv;

    /// The power of two of the pointer alignment.
    const ALIGN_BITS: u32;

    /// Converts to a raw pointer.
    ///
    /// Each call to `into_raw` must be paired with a call to `from_raw`
    /// in order to avoid memory leakage.
    ///
    /// The lower [`Self::ALIGN_BITS`] of the raw pointer is guaranteed to
    /// be zero. In other words, the pointer is guaranteed to be aligned to
    /// `1 << Self::ALIGN_BITS`.
    fn into_raw(self) -> ((res_ptr, perm): (NonNull<Self::Target>, Tracked<Self::Permission>))
        ensures
            Self::ptr_perm_match(res_ptr.as_ptr(), perm@),
            self.rel_perm(perm@),
            perm@.inv(),
            res_ptr.as_ptr().addr() % (1usize << Self::ALIGN_BITS) == 0,
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
    unsafe fn from_raw(ptr: NonNull<Self::Target>, perm: Tracked<Self::Permission>) -> (ret: Self)
        requires
            Self::ptr_perm_match(ptr.as_ptr(), perm@),
            perm@.inv(),
        ensures
            ret.rel_perm(perm@),
    ;

    /// Obtains a shared reference to the original pointer.
    ///
    /// # Safety
    ///
    /// The original pointer must outlive the lifetime parameter `'a`, and during `'a`
    /// no mutable references to the pointer will exist.
    unsafe fn raw_as_ref<'a>(
        raw: NonNull<Self::Target>,
        permission: Tracked<&'a Self::Permission>,
    ) -> (res: Self::Ref<'a>)
        requires
            Self::ptr_perm_match(raw.as_ptr(), *permission@),
            permission@.inv(),
        ensures
            res.inv(),
    ;

    /// Converts a shared reference to a raw pointer.
    fn ref_as_raw(ptr_ref: Self::Ref<'_>) -> NonNull<Self::Target>
        requires
            ptr_ref.inv(),
    ;

    /// A specification function that constraints the nonnull pointer and the permission returned by `into_raw`.
    /// This design is to support the tagged pointer trick used in `Either`.
    spec fn ptr_perm_match(ptr: *mut Self::Target, perm: Self::Permission) -> bool;

    /// A specification function that relates the original smart pointer and the permission.
    spec fn rel_perm(self, perm: Self::Permission) -> bool;
}

// SAFETY: `Frame` is essentially a `*const MetaSlot` that could be used as a non-null
// `*const` pointer.
unsafe impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + 'static> NonNullPtr for Frame<M> {
    type Target = PhantomData<Self>;

    type Permission = FrameRawPerms;

    type Ref<'a> = FrameRef<'a, M>;

    #[verifier::external_body]
    const ALIGN_BITS: u32 = core::mem::align_of::<MetaSlot>().trailing_zeros();

    /* `mut` permits transferring the erased metadata permission out of the handle.
     * Origin Rust: fn into_raw(self) -> NonNull<Self::Target> {
     */
    fn into_raw(mut self) -> (NonNull<Self::Target>, Tracked<Self::Permission>) {
        assume(self.inv());
        proof_decl! {
            let tracked perm = FrameRawPerms {
                slot_perm: *self.tracked_slot_perm.borrow(),
                metadata_perm: self.tracked_metadata_perm.tracked_take(),
            };
        }
        let ptr = NonNull::new(self.ptr.cast_mut()).unwrap();
        let _ = ManuallyDrop::new(self);
        assume(ptr.as_ptr().addr() % (1usize << Self::ALIGN_BITS) == 0);
        (ptr.cast(), Tracked(perm))
    }

    unsafe fn from_raw(
        raw: NonNull<Self::Target>,
        Tracked(perm): Tracked<Self::Permission>,
    ) -> Self {
        Self {
            ptr: raw.as_ptr().cast_const().cast(),
            _marker: PhantomData,
            #[cfg(verus_keep_ghost_body)]
            tracked_slot_perm: Tracked(perm.slot_perm),
            #[cfg(verus_keep_ghost_body)]
            tracked_metadata_perm: Tracked(Some(perm.metadata_perm)),
        }
    }

    unsafe fn raw_as_ref<'a>(
        raw: NonNull<Self::Target>,
        Tracked(permission): Tracked<&'a Self::Permission>,
    ) -> Self::Ref<'a> {
        Self::Ref {
            inner: ManuallyDrop::new(
                Frame {
                    ptr: raw.as_ptr().cast_const().cast(),
                    _marker: PhantomData,
                    #[cfg(verus_keep_ghost_body)]
                    tracked_slot_perm: Tracked(permission.slot_perm),
                    #[cfg(verus_keep_ghost_body)]
                    tracked_metadata_perm: Tracked(None),
                },
            ),
            _marker: PhantomData,
            #[cfg(verus_keep_ghost_body)]
            tracked_metadata_perm: Tracked(Some(&permission.metadata_perm)),
        }
    }

    fn ref_as_raw(ptr_ref: Self::Ref<'_>) -> NonNull<Self::Target> {
        NonNull::new(ptr_ref.inner.ptr.cast_mut()).unwrap().cast()
    }

    open spec fn ptr_perm_match(ptr: *mut Self::Target, perm: Self::Permission) -> bool {
        ptr.cast_const().cast::<MetaSlot>() == perm.slot_perm.ptr()
    }

    open spec fn rel_perm(self, perm: Self::Permission) -> bool {
        &&& perm.slot_perm == self.slot_perm()
        &&& perm.metadata_perm == self.frac_metadata_perm()
    }
}

impl<'a, M: AnyFrameMeta + Repr<MetaSlotStorage>> FrameRef<'a, M> {
    pub open spec fn start_paddr_spec(self) -> Paddr {
        self@.start_paddr_spec()
    }

    #[verifier::inline]
    pub open spec fn slot_vaddr(self) -> Vaddr {
        self@.slot_vaddr()
    }

    pub open spec fn frac_metadata_perm(self) -> FracMetadataPerm {
        self@.frac_metadata_perm()
    }

    /// Relates an external metadata permission to the non-owning frame handle.
    pub open spec fn external_meta_wf(
        self,
        metadata_perm: MetadataPerm,
        repr_perm: M::ReprPerm,
    ) -> bool {
        (Frame { tracked_metadata_perm: Tracked(None), ..self@ }).external_meta_wf(
            metadata_perm,
            repr_perm,
        )
    }
}

} // verus!
