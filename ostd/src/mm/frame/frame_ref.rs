// SPDX-License-Identifier: MPL-2.0
use vstd::{
    prelude::*,
    simple_pptr::{PPtr, PointsTo},
};
use vstd_extra::{cast_ptr::Repr, prelude::*};

use crate::specs::{
    arch::valid_frame_paddr,
    mm::frame::{
        frame_specs::FrameRawPerms,
        mapping::meta_to_index,
        meta_owners::{FracMetadataPerm, MetaSlotStorage},
        meta_region_owners::MetaRegionOwners,
    },
};

use super::{
    Frame,
    meta::{AnyFrameMeta, MetaSlot},
};
use crate::mm::Paddr;
use crate::mm::frame::meta::mapping::frame_to_meta;
use core::{marker::PhantomData, mem::ManuallyDrop, ops::Deref, ptr::NonNull};

verus! {

/// A struct that can work as `&'a Frame<M>`.
// FIXME: field visibility
pub struct FrameRef<'a, M: AnyFrameMeta + ?Sized + Repr<MetaSlotStorage>> {
    pub inner: ManuallyDrop<Frame<M>>,
    pub _marker: PhantomData<&'a Frame<M>>,
}

#[verus_verify]
impl<M: AnyFrameMeta + Repr<MetaSlotStorage>> FrameRef<'_, M> {
    /// Borrows the [`Frame`] at the physical address as a [`FrameRef`].
    ///
    /// # Safety
    /// The caller's typed frame handle supplies the metadata type; the borrow
    /// remains tied to the lifetime of that handle.
    #[verus_spec(r =>
        with
            Tracked(slot_perm): Tracked<&'static PointsTo<MetaSlot>>,
            Tracked(metadata_perm): Tracked<&FracMetadataPerm>
        requires
            valid_frame_paddr(raw),
            MetaSlot::perms_related(*slot_perm,metadata_perm.resource()),
            slot_perm.pptr().addr() == frame_to_meta(raw),
            slot_perm.is_init(),
        ensures
            r.inner@.ptr.addr() == frame_to_meta(raw),
            r.inner@.ptr_inv(),
            r.inner@.tracked_slot_perm@ == slot_perm,
            r.inner@.tracked_metadata_perm@ is None,
            MetaSlot::perms_related(r.inner@.slot_perm(), metadata_perm.resource()),
    )]
    pub(in crate::mm) unsafe fn borrow_paddr(raw: Paddr) -> Self {
        proof_with!{ tracked_slot_perm: Tracked(slot_perm), tracked_metadata_perm: Tracked(None)}
        let frame = Frame::<M> {
            ptr: PPtr::<MetaSlot>::from_addr(frame_to_meta(raw)),
            _marker: PhantomData,
        };

        let inner = ManuallyDrop::new(frame);

        Self { inner, _marker: PhantomData }
    }
}

impl<M: AnyFrameMeta + ?Sized + Repr<MetaSlotStorage>> Deref for FrameRef<'_, M> {
    type Target = Frame<M>;

    #[verus_spec(r => ensures *r == self.inner@)]
    fn deref(&self) -> &Self::Target {
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
    type Permission: Inv + Objective;

    /// A type that behaves just like a shared reference to the `NonNullPtr`.
    type Ref<'a>;

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
    fn into_raw(self) -> ((res_ptr, perm): (PPtr<Self::Target>, Tracked<Self::Permission>))
        ensures
            Self::ptr_perm_match(res_ptr, perm@),
            self.rel_perm(perm@),
            perm@.inv(),
            res_ptr.addr() % (1usize << Self::ALIGN_BITS) == 0,
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
    unsafe fn from_raw(ptr: PPtr<Self::Target>, perm: Tracked<Self::Permission>) -> (ret: Self)
        requires
            Self::ptr_perm_match(ptr, perm@),
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
    unsafe fn raw_as_ref<'a>(raw: PPtr<Self::Target>) -> Self::Ref<'a>;

    /// Converts a shared reference to a raw pointer.
    fn ref_as_raw(ptr_ref: Self::Ref<'_>) -> PPtr<Self::Target>;

    /// A specification function that constraints the nonnull pointer and the permission returned by `into_raw`.
    /// This design is to support the tagged pointer trick used in `Either`.
    spec fn ptr_perm_match(ptr: PPtr<Self::Target>, perm: Self::Permission) -> bool;

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

    fn into_raw(self) -> (PPtr<Self::Target>, Tracked<Self::Permission>) {
        assume(self.inv());
        let mut this = self;
        proof_decl! {
            let tracked perm = FrameRawPerms {
                slot_perm: *this.tracked_slot_perm.borrow(),
                metadata_perm: this.tracked_metadata_perm.tracked_take(),
            };
        }
        let ptr = this.ptr;
        let _ = ManuallyDrop::new(this);
        assume(ptr.addr() % (1usize << Self::ALIGN_BITS) == 0);
        (PPtr::<Self::Target>::from_addr(ptr.addr()), Tracked(perm))
    }

    unsafe fn from_raw(raw: PPtr<Self::Target>, Tracked(perm): Tracked<Self::Permission>) -> Self {
        Self {
            ptr: PPtr::<MetaSlot>::from_addr(raw.addr()),
            _marker: PhantomData,
            #[cfg(verus_keep_ghost_body)]
            tracked_slot_perm: Tracked(perm.slot_perm),
            #[cfg(verus_keep_ghost_body)]
            tracked_metadata_perm: Tracked(Some(perm.metadata_perm)),
        }
    }

    #[verifier::external_body]
    unsafe fn raw_as_ref<'a>(raw: PPtr<Self::Target>) -> Self::Ref<'a> {
        let frame = Frame::<M> {
            ptr: PPtr::<MetaSlot>::from_addr(raw.addr()),
            _marker: PhantomData,
            #[cfg(verus_keep_ghost_body)]
            tracked_slot_perm: Tracked::assume_new(),
            #[cfg(verus_keep_ghost_body)]
            tracked_metadata_perm: Tracked(None),
        };
        let dropped = ManuallyDrop::<Frame<M>>::new(frame);
        Self::Ref { inner: dropped, _marker: PhantomData }
    }

    fn ref_as_raw(ptr_ref: Self::Ref<'_>) -> PPtr<Self::Target> {
        PPtr::from_addr(ptr_ref.inner.ptr.addr())
    }

    open spec fn ptr_perm_match(ptr: PPtr<Self::Target>, perm: Self::Permission) -> bool {
        ptr.addr() == perm.slot_perm.addr()
    }

    open spec fn rel_perm(self, perm: Self::Permission) -> bool {
        &&& perm.slot_perm == self.slot_perm()
        &&& perm.metadata_perm == self.frac_metadata_perm()
    }
}

} // verus!
