// SPDX-License-Identifier: MPL-2.0
use core::{marker::PhantomData, mem::ManuallyDrop, ops::Deref};

use vstd::prelude::*;
use vstd::simple_pptr::PPtr;
use vstd_extra::cast_ptr::Repr;
use vstd_extra::ownership::*;
use crate::mm::frame::meta::mapping::{frame_to_meta, meta_to_frame};

use crate::specs::{
    arch::*,
    mm::frame::{
        FramePermission, mapping::frame_to_index, meta_owners::MetaSlotStorage,
        meta_region_owners::MetaRegionOwners,
    },
};

use super::{
    Frame,
    meta::{AnyFrameMeta, MetaSlot, REF_COUNT_UNUSED},
};
use crate::mm::Paddr;

verus! {

/// A struct that can work as `&'a Frame<M>`.
// FIXME: field visibility
pub struct FrameRef<'a, M: AnyFrameMeta + ?Sized> {
    inner: ManuallyDrop<Frame<M>>,
    tracked_perm: Tracked<&'a FramePermission>,
    _marker: PhantomData<&'a Frame<M>>,
}

impl<'a, M: AnyFrameMeta + ?Sized> Inv for FrameRef<'a, M> {
    open spec fn inv(self) -> bool {
        &&& self.frame().tracked_perm@ is None
        &&& self.tracked_perm@.frac() == 1
        &&& self.tracked_perm@.resource().pptr() == self.frame().ptr
    }
}

impl<'a, M: AnyFrameMeta + ?Sized> FrameRef<'a, M> {
    /// The non-owning `Frame` proxy wrapped by this reference.
    pub open spec fn frame(self) -> Frame<M> {
        self.inner@
    }

    /// The owning permission borrowed by this non-owning reference.
    pub open spec fn permission(self) -> &'a FramePermission {
        self.tracked_perm@
    }
}

#[verus_verify]
impl<'a, M: AnyFrameMeta + Repr<MetaSlotStorage>> FrameRef<'a, M> {
    /// Borrows the [`Frame`] at the physical address as a [`FrameRef`].
    ///
    /// This is a non-owning proxy. Its inner `Frame` therefore carries
    /// `None` instead of an owning [`FramePermission`](crate::specs::mm::frame::FramePermission).
    /// The slot's reference count and central permission pool are unchanged.
    ///
    /// # Safety
    /// By providing a borrowed `FramePermission`, the caller ensures that
    /// the metadata slot stays alive for the whole lifetime of the reference.
    #[verus_spec(r =>
        with
            Tracked(regions): Tracked<&mut MetaRegionOwners>,
            Tracked(frame_permission): Tracked<&'a FramePermission>,
        requires
            old(regions).inv(),
            has_safe_slot(raw),
            old(regions).slot_owners[frame_to_index(raw)].inner_perms.ref_count.value()
                != REF_COUNT_UNUSED,
            frame_permission.frac() == 1,
            frame_permission.id() == old(regions).slots[frame_to_index(raw)].id(),
            frame_permission.resource().pptr().addr() == frame_to_meta(raw),
        ensures
            *final(regions) == *old(regions),
            r.frame().ptr.addr() == frame_to_meta(raw),
            r.frame().tracked_perm@ is None,
            r.tracked_perm@ == frame_permission,
            r.inv(),
    )]
    pub(in crate::mm) unsafe fn borrow_paddr(raw: Paddr) -> Self {
        proof {
            old(regions).inv_implies_correct_addr(raw);
        }

        let frame = unsafe {
            #[verus_spec(with Tracked(regions), Tracked(None))]
            Frame::from_raw(raw)
        };
        let inner = ManuallyDrop::new(frame);

        Self { inner, tracked_perm: Tracked(frame_permission), _marker: PhantomData }
    }
}

impl<M: AnyFrameMeta + ?Sized + Repr<MetaSlotStorage>> Deref for FrameRef<'_, M> {
    type Target = Frame<M>;

    #[verus_spec(r => ensures *r == self.frame())]
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

/// A local non-null smart-pointer abstraction used while verifying `mm` in
/// isolation. Raw ownership is represented by the returned
/// [`FramePermission`], rather than by the removed drop-obligation ledger.
pub unsafe trait NonNullPtr: 'static + Sized {
    type Target;

    type Ref<'a>;

    spec fn raw_wf(self, regions: MetaRegionOwners) -> bool;

    spec fn ptr_perm_match(ptr: PPtr<Self::Target>, permission: FramePermission) -> bool;

    spec fn ref_perm_match<'a>(
        ptr_ref: Self::Ref<'a>,
        permission: &'a FramePermission,
    ) -> bool;

    fn ALIGN_BITS() -> u32;

    fn into_raw(
        self,
        Tracked(regions): Tracked<&mut MetaRegionOwners>,
    ) -> ((ptr, permission): (PPtr<Self::Target>, Tracked<FramePermission>))
        requires
            self.raw_wf(*old(regions)),
        ensures
            *final(regions) == *old(regions),
            Self::ptr_perm_match(ptr, permission@),
            permission@.frac() == 1,
    ;

    unsafe fn from_raw(
        ptr: PPtr<Self::Target>,
        permission: Tracked<FramePermission>,
        Tracked(regions): Tracked<&mut MetaRegionOwners>,
    ) -> (res: Self)
        requires
            old(regions).inv(),
            Self::ptr_perm_match(ptr, permission@),
            permission@.frac() == 1,
            old(regions).slots[frame_to_index(meta_to_frame(ptr.addr()))].id()
                == permission@.id(),
            old(regions).slot_owners[frame_to_index(meta_to_frame(ptr.addr()))]
                .inner_perms.ref_count.value() != REF_COUNT_UNUSED,
        ensures
            *final(regions) == *old(regions),
            res.raw_wf(*final(regions)),
    ;

    unsafe fn raw_as_ref<'a>(
        raw: PPtr<Self::Target>,
        permission: Tracked<&'a FramePermission>,
        Tracked(regions): Tracked<&mut MetaRegionOwners>,
    ) -> (res: Self::Ref<'a>)
        requires
            old(regions).inv(),
            Self::ptr_perm_match(raw, *permission@),
            permission@.frac() == 1,
            old(regions).slots[frame_to_index(meta_to_frame(raw.addr()))].id()
                == permission@.id(),
            old(regions).slot_owners[frame_to_index(meta_to_frame(raw.addr()))]
                .inner_perms.ref_count.value() != REF_COUNT_UNUSED,
        ensures
            *final(regions) == *old(regions),
            Self::ref_perm_match(res, permission@),
    ;

    fn ref_as_raw<'a>(
        ptr_ref: Self::Ref<'a>,
    ) -> ((ptr, permission): (PPtr<Self::Target>, Tracked<&'a FramePermission>))
        ensures
            Self::ptr_perm_match(ptr, *permission@),
            Self::ref_perm_match(ptr_ref, permission@),
    ;
}

pub assume_specification[ usize::trailing_zeros ](_0: usize) -> u32
;

// SAFETY: `Frame` is essentially a `*const MetaSlot` that could be used as a non-null
// `*const` pointer.
unsafe impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + 'static> NonNullPtr for Frame<M> {
    type Target = PhantomData<Self>;

    type Ref<'a> = FrameRef<'a, M>;

    open spec fn raw_wf(self, regions: MetaRegionOwners) -> bool {
        self.wf_with_region(regions)
    }

    open spec fn ptr_perm_match(
        ptr: PPtr<Self::Target>,
        permission: FramePermission,
    ) -> bool {
        permission.resource().pptr().addr() == ptr.addr()
    }

    open spec fn ref_perm_match<'a>(
        ptr_ref: Self::Ref<'a>,
        permission: &'a FramePermission,
    ) -> bool {
        &&& ptr_ref.inv()
        &&& ptr_ref.tracked_perm@ == permission
    }

    fn ALIGN_BITS() -> u32 {
        core::mem::align_of::<MetaSlot>().trailing_zeros()
    }

    fn into_raw(
        self,
        Tracked(regions): Tracked<&mut MetaRegionOwners>,
    ) -> (PPtr<Self::Target>, Tracked<FramePermission>) {
        let raw = PPtr::<Self::Target>::from_addr(self.ptr.addr());
        proof_decl! {
            let tracked permission: FramePermission;
        }
        let _ = #[verus_spec(with Tracked(regions) => Tracked(permission))]
        Frame::into_raw(self);
        (raw, Tracked(permission))
    }

    unsafe fn from_raw(
        raw: PPtr<Self::Target>,
        Tracked(permission): Tracked<FramePermission>,
        Tracked(regions): Tracked<&mut MetaRegionOwners>,
    ) -> Self {
        unsafe {
            #[verus_spec(with Tracked(regions), Tracked(Some(permission)))]
            Frame::from_raw(meta_to_frame(raw.addr()))
        }
    }

    unsafe fn raw_as_ref<'a>(
        raw: PPtr<Self::Target>,
        Tracked(permission): Tracked<&'a FramePermission>,
        Tracked(regions): Tracked<&mut MetaRegionOwners>,
    ) -> Self::Ref<'a> {
        unsafe {
            #[verus_spec(with Tracked(regions), Tracked(permission))]
            FrameRef::borrow_paddr(meta_to_frame(raw.addr()))
        }
    }

    fn ref_as_raw<'a>(
        ptr_ref: Self::Ref<'a>,
    ) -> (PPtr<Self::Target>, Tracked<&'a FramePermission>) {
        let raw = PPtr::from_addr(ptr_ref.inner.ptr.addr());
        let tracked permission = ptr_ref.tracked_perm.get();
        (raw, Tracked(permission))
    }
}

} // verus!
