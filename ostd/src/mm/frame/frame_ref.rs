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
        frame_specs::{FrameRawPerms, valid_slot_vaddr},
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
use crate::{
    mm::{Paddr, Vaddr},
    sync::non_null::NonNullPtr,
};
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
        &&& self.inner@.ptr_inv()
        &&& self.inner@.tracked_metadata_perm@ is None
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

// SAFETY: `Frame` is essentially a `*const MetaSlot` that could be used as a non-null
// `*const` pointer.
unsafe impl<M: AnyFrameMeta + Repr<MetaSlotStorage> + 'static> NonNullPtr for Frame<M> {
    type Target = PhantomData<Self>;

    type Permission = FrameRawPerms;

    type Ref<'a> = FrameRef<'a, M>;

    type RefPermission<'a> = FrameRawPermsRef<'a>;

    /* Verus cannot verify the original trait-constant expression. `MetaSlot` has
     * alignment 8 on the supported targets, as checked by `lemma_align_bits_range`.
     * Origin Rust: const ALIGN_BITS: u32 = core::mem::align_of::<MetaSlot>().trailing_zeros();
     */
    const ALIGN_BITS: u32 = 3;

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
        proof {
            let addr = ptr.as_ptr().addr();
            assert(addr % (1usize << Self::ALIGN_BITS) == 0) by (bit_vector)
                requires
                    addr % 64 == 0,
                    Self::ALIGN_BITS == 3,
            ;
        }
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

    proof fn lemma_align_bits_range()
        ensures
            Self::ALIGN_BITS < usize::BITS,
            core::mem::align_of::<MetaSlot>() == 1usize << Self::ALIGN_BITS,
    {
        MetaSlot::lemma_layout();
        assert(Self::ALIGN_BITS == 3);
        assert(core::mem::align_of::<MetaSlot>() == 8);
        assert(1usize << 3 == 8) by (bit_vector);
    }

    // Raw frame handles require a valid slot; metadata access and explicit drop
    // additionally require `Frame::inv`, propagated conditionally by `rel_perm`.
    open spec fn ptr_perm_match(ptr: *mut Self::Target, perm: Self::Permission) -> bool {
        &&& ptr.cast_const().cast::<MetaSlot>() == perm.slot_perm.ptr()
        &&& valid_slot_vaddr(perm.slot_vaddr())
        &&& perm.slot_perm.is_init()
    }

    open spec fn rel_perm(self, perm: Self::Permission) -> bool {
        &&& perm.slot_perm == self.slot_perm()
        &&& perm.metadata_perm == self.frac_metadata_perm()
        &&& self.ptr_inv()
        &&& perm.inv() ==> self.inv()
    }

    open spec fn ref_perm_view_permission<'a>(perm: Self::RefPermission<'a>) -> Self::Permission {
        perm@
    }

    open spec fn ref_rel_perm<'a>(r: Self::Ref<'a>, perm: Self::RefPermission<'a>) -> bool {
        r.inv() ==> {
            &&& perm.inv()
            &&& r@.rel_perm(perm@)
        }
    }

    proof fn borrow_ref_perm<'a>(tracked perm: &Self::RefPermission<'a>) -> (tracked ret:
        Self::RefPermission<'a>) {
        FrameRawPermsRef { slot_perm: perm.slot_perm, metadata_perm: perm.metadata_perm }
    }

    proof fn borrow_perm_as_ref_perm<'a>(tracked perm: &'a Self::Permission) -> (tracked ret:
        Self::RefPermission<'a>) {
        FrameRawPermsRef { slot_perm: perm.slot_perm, metadata_perm: Some(&perm.metadata_perm) }
    }

    unsafe fn raw_as_ref<'a>(
        raw: NonNull<Self::Target>,
        Tracked(permission): Tracked<Self::RefPermission<'a>>,
    ) -> (res: Self::Ref<'a>)
        ensures
            permission.inv() ==> res.inv(),
    {
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
            tracked_metadata_perm: Tracked(permission.metadata_perm),
        }
    }

    fn ref_as_raw<'a>(ptr_ref: Self::Ref<'a>) -> (res: (
        NonNull<Self::Target>,
        Tracked<Self::RefPermission<'a>>,
    ))
        ensures
            res.0.as_ptr().cast_const().cast::<MetaSlot>() == ptr_ref@.ptr,
    {
        proof {
            use_type_invariant(&ptr_ref);
            assert(1usize << Self::ALIGN_BITS == 8) by (bit_vector)
                requires
                    Self::ALIGN_BITS == 3,
            ;
            let addr = ptr_ref@.ptr.addr();
            assert(addr % 8 == 0) by (bit_vector)
                requires
                    addr % 64 == 0,
            ;
        }
        /* Name the inner frame so its erased slot permission can be borrowed in proof mode.
         * Origin Rust: NonNull::new(ptr_ref.inner.ptr.cast_mut()).unwrap().cast()
         */
        let frame = &*ptr_ref.inner;
        let tracked metadata_perm = *ptr_ref.tracked_metadata_perm.borrow();
        let tracked permission = FrameRawPermsRef {
            slot_perm: *frame.tracked_slot_perm.borrow(),
            metadata_perm,
        };
        (NonNull::new(ptr_ref.inner.ptr.cast_mut()).unwrap().cast(), Tracked(permission))
    }
}

pub tracked struct FrameRawPermsRef<'a> {
    slot_perm: &'static ExposedPointsTo<MetaSlot>,
    metadata_perm: Option<&'a FracMetadataPerm>,
}

impl View for FrameRawPermsRef<'_> {
    type V = FrameRawPerms;

    closed spec fn view(&self) -> FrameRawPerms {
        FrameRawPerms {
            slot_perm: self.slot_perm,
            metadata_perm: match self.metadata_perm {
                Some(permission) => *permission,
                None => arbitrary(),
            },
        }
    }
}

impl Inv for FrameRawPermsRef<'_> {
    closed spec fn inv(self) -> bool {
        self.metadata_perm is Some && self@.inv()
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
