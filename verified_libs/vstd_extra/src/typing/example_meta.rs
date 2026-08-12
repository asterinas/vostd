//! A syntax-faithful mimic of the frame layer's `dyn` casts.
//!
//! Every item here matches `ostd/src/mm/frame/meta.rs` and
//! `ostd/src/mm/frame/mod.rs` as closely as the types allow — same field shapes,
//! same casts, same call syntax — with the metadata impls reduced to dummies. The
//! purpose is to locate precisely where Verus stops accepting the real code.
//!
//! The four casts, in the order the frame layer performs them:
//!
//! 1. `&metadata as &dyn AnyFrameMeta` then `core::ptr::metadata(..)`, capturing a
//!    vtable pointer at write time — `MetaSlot::write_meta`.
//! 2. `core::ptr::from_raw_parts_mut(storage_ptr, vtable_ptr)` to rebuild a
//!    `*mut dyn AnyFrameMeta`, then dispatch `on_drop` through it and
//!    `drop_in_place` it — `MetaSlot::drop_meta_in_place`.
//! 3. `transmute::<Frame<M>, Frame<dyn AnyFrameMeta>>` — `Frame::into_dyn`.
//! 4. `(meta as &dyn core::any::Any).is::<M>()` then the reverse transmute —
//!    `TryFrom<Frame<dyn AnyFrameMeta>> for Frame<M>`.
//!
//! # Result
//!
//! Casts 1–3 are accepted as written. The wide-pointer construction, the dispatch
//! through a rebuilt `*mut dyn`, and the transmutes all typecheck, needing
//! `external_body` only because `core::ptr::metadata`, `from_raw_parts_mut`,
//! `drop_in_place` and `transmute` have no Verus specifications. Nothing about
//! `dyn` itself obstructs them.
//!
//! Three registrations are needed first, none of them hard:
//!
//! - `UnsafeCell` has no `vstd` specification, so upstream's `MetaSlot` fields
//!   cannot be written until it is registered — and the registration Verus's own
//!   diagnostic suggests is incomplete, needing `external_body` as well because
//!   `UnsafeCell`'s field is private. This is what our `PCell`/`PPtr` fields avoid.
//! - `DynMetadata` registers cleanly, but its parameter must be bounded by
//!   `PointeeSized`, not `?Sized`: under `feature(sized_hierarchy)` a `?Sized`
//!   proxy still carries a `MetaSized` predicate the external type does not have,
//!   and the bounds must match exactly.
//! - `write_meta` needs an explicit `M: 'static`. Upstream gets it free from
//!   `AnyFrameMeta: Any`, since `Any: 'static`; without `Any` the coercion inside
//!   `core::ptr::metadata` fails with `E0310`.
//!
//! Cast 4 is **impossible in Verus today**, and not for want of a proof. It needs
//! `AnyFrameMeta: Any`, and:
//!
//! - Declaring that bound makes Verus panic rather than report an error:
//!   `thread 'rustc' panicked at vir/src/traits.rs:1610: compute_dyn_compatibility:
//!   missing trait Path(core, ["any" :: "Any"])`. The panic fires because
//!   `compute_dyn_compatibility` looks every supertrait up in its map of
//!   Verus-known traits, and `core::any::Any` is registered nowhere in `vstd`.
//! - Registering it is then blocked by two checks that contradict each other.
//!   `type ExternalTraitSpecificationFor: Any;` fails with *external_trait_
//!   specification trait bound mismatch*, the diagnostic naming the missing bound
//!   as `'static`. Adding it — `: Any + 'static` — fails with *unexpected bound in
//!   ExternalTraitSpecificationFor*. Since `Any: 'static` is part of `Any`'s own
//!   definition and the bounds must match exactly, no spelling satisfies both.
//! - Without the bound, the cast is rejected by *rustc*, before Verus sees it:
//!   `E0605: non-primitive cast: &dyn AnyMeta as &(dyn core::any::Any + 'static)`.
//!
//! # `Either` cannot stand in for `Any` either
//!
//! The natural repair is to notice that `x as &dyn Any` is a dyn-to-dyn *upcast*,
//! and to put [`super::types::Either`] in that slot: make it a supertrait of
//! `AnyMeta`, upcast to `&dyn Either<A, B>`, and read the id from there. It would
//! be a one-to-one syntactic match, and it would recover the id through the
//! upcast rather than through `AnyMeta`.
//!
//! It does not work, for a reason more basic than anything about `Any`:
//!
//! > `the trait bound Dyn<2, ()>: T196_Either<MetaA, MetaB> is not satisfied`
//!
//! **Verus's dyn type does not implement the erased trait's Verus supertraits.**
//! Probed with a parameter-free supertrait carrying a single spec fn, which fails
//! identically (`Dyn<3, ()>: T198_Marker`), so this is not about `Either`'s
//! generics. Only marker and auto traits (`Send`, `Sync`) survive in supertrait
//! position. The same root cause explains two earlier observations: `dyn HasId`
//! does not typecheck because `HasId: TypeId`, and a spec fn inherited from a
//! supertrait is not preserved across the `&T -> &dyn Trait` coercion. Verus
//! simply does not model the supertrait relation for dyn types.
//!
//! Verus does have an escape hatch — its `unsized_blanketed_traits` set makes a
//! supertrait usable if it has an unbounded `impl<T: ?Sized>`. That cannot help
//! here: a blanket impl gives every type the *same* id, and an identity trait
//! whose answer does not depend on the type is no identity trait.
//!
//! So a `dyn` trait in Verus must be self-contained: everything an erased value
//! needs to report has to be declared on that one trait. [`try_from_tagged`] is
//! therefore not a workaround for a missing feature — it is the only shape
//! available, and [`AnyMeta::type_id`] must live where it does.
//!
//! So `/*Any +*/` in our `AnyFrameMeta`, and the commented-out `TryFrom`, are
//! forced rather than chosen. Verus needs either a `vstd` registration of `Any` or
//! `'static` support in `external_trait_specification` before a downcast built on
//! `Any` can be verified.
//!
//! [`try_from_tagged`] is the replacement, mirroring cast 4 with the one
//! substitution that makes it expressible: `Any::is::<M>()` becomes a comparison of
//! a dyn-dispatched tag against a statically known one. That test is *verified*,
//! and the `Result` shape, the unchanged-on-failure `Err`, and the transmute are
//! all preserved.
//!
//! Note the field types below are upstream Asterinas's, not the ones in our
//! `MetaSlot` — ours carries `vtable_ptr: PPtr<usize>` under a comment reading
//! "VERUS LIMITATION: Currently we do not verify this because of the dependency on
//! the `dyn Trait` pattern". Casts 1–3 are evidence that field can be restored to
//! `UnsafeCell<MaybeUninit<FrameMetaVtablePtr>>`.
use core::cell::UnsafeCell;
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::ptr::DynMetadata;

use vstd::prelude::*;

verus! {

/// Registers `UnsafeCell` with Verus.
///
/// Needed because upstream's `MetaSlot` fields are `UnsafeCell`, and Verus has no
/// specification for it — our tree sidesteps this with `PCell`/`PPtr`. The
/// declaration is the one Verus's own diagnostic suggests.
#[verifier::reject_recursive_types(T)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExUnsafeCell<T>(UnsafeCell<T>) where T: core::marker::MetaSized + ?Sized;

/// Registers `DynMetadata` with Verus.
///
/// The vtable-pointer type itself. Unlike `core::any::Any` this registers without
/// trouble — it carries no `'static` bound, which is the thing that made `Any`
/// unregisterable.
#[verifier::reject_recursive_types(T)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExDynMetadata<T: core::marker::PointeeSized>(DynMetadata<T>);

/// Mimics `FRAME_METADATA_MAX_SIZE`.
pub const META_MAX_SIZE: usize = 8;

/// Mimics `MetaSlotStorage`.
///
/// Upstream this is a raw `[u8; FRAME_METADATA_MAX_SIZE]`; ours is an exec-tagged
/// union. Kept as bytes here because the casts under test do not care which.
pub struct MetaSlotStorage {
    pub bytes: [u8; META_MAX_SIZE],
}

/// Mimics `AnyFrameMeta`.
///
/// Same shape as the real trait: `unsafe`, `Send + Sync`, an `open spec fn`
/// per-impl precondition, and an exec `on_drop` on `&mut self` whose `requires`
/// calls that precondition. The real one also threads a `VmReader` and two
/// `Tracked` owner arguments; those are dropped as orthogonal to dispatch.
///
/// `Any` is absent from the supertraits, exactly as in our tree. See the module
/// docs — the bound cannot be written, so [`Self::type_id`] takes its place.
pub unsafe trait AnyMeta: Send + Sync {
    /// The id of *this value's* type, readable through an erased reference.
    ///
    /// Declared here rather than inherited from a supertrait, and not
    /// `where Self: Sized`, because both are needed for it to survive the
    /// `&M -> &dyn AnyMeta` coercion. This is the stand-in for `Any::type_id`.
    spec fn type_id(&self) -> usize;

    /// The executable form, dispatched through the vtable.
    fn type_id_val(&self) -> (r: usize)
        ensures
            r == self.type_id(),
    ;

    /// Per-impl precondition for [`Self::on_drop`]. Default is `true`.
    open spec fn on_drop_pre(&self) -> bool {
        true
    }

    fn on_drop(&mut self)
        requires
            old(self).on_drop_pre(),
    ;
}

/// The static half of the identity test.
///
/// Separate from [`AnyMeta`] because it is deliberately *not* dyn-dispatched: a
/// downcast needs `M`'s id without having an `M` to ask, which is what
/// `TypeId::of::<M>()` supplies upstream. An associated const would be the natural
/// spelling and is what forces the split — associated consts are not
/// dyn-compatible, so putting one on `AnyMeta` would make `dyn AnyMeta` illegal.
pub trait MetaTag {
    spec fn tag_spec() -> usize;

    fn tag() -> (r: usize)
        ensures
            r == Self::tag_spec(),
    ;

    /// A value's dispatched id agrees with its type's static id.
    ///
    /// This is the fact `Any` provides for free and the one thing that has to be
    /// supplied by hand. Without it the two halves of the test are unrelated and a
    /// successful comparison would say nothing.
    proof fn tag_coherent(&self) where Self: core::marker::Sized + AnyMeta
        ensures
            self.type_id() == Self::tag_spec(),
    ;
}

/// Mimics `FrameMetaVtablePtr`.
pub type MetaVtablePtr = DynMetadata<dyn AnyMeta>;

/// Mimics `MetaSlot`, with the fields upstream actually uses.
pub struct MetaSlot {
    pub storage: UnsafeCell<MetaSlotStorage>,
    pub vtable_ptr: UnsafeCell<MaybeUninit<MetaVtablePtr>>,
}

/// A dummy metadata type, standing in for e.g. `MetaPageMeta`.
pub struct MetaA {
    pub val: u64,
}

/// A second dummy, so dispatch and downcasting have something to choose between.
/// With one impl a vtable-shaped call would verify vacuously.
pub struct MetaB {
    pub val: u64,
}

#[verifier::external]
unsafe impl Send for MetaA {

}

#[verifier::external]
unsafe impl Sync for MetaA {

}

#[verifier::external]
unsafe impl Send for MetaB {

}

#[verifier::external]
unsafe impl Sync for MetaB {

}

unsafe impl AnyMeta for MetaA {
    open spec fn type_id(&self) -> usize {
        1
    }

    fn type_id_val(&self) -> (r: usize) {
        1
    }

    #[verifier::external_body]
    fn on_drop(&mut self) {
    }
}

impl MetaTag for MetaA {
    open spec fn tag_spec() -> usize {
        1
    }

    fn tag() -> (r: usize) {
        1
    }

    proof fn tag_coherent(&self) {
    }
}

unsafe impl AnyMeta for MetaB {
    open spec fn type_id(&self) -> usize {
        2
    }

    fn type_id_val(&self) -> (r: usize) {
        2
    }

    #[verifier::external_body]
    fn on_drop(&mut self) {
    }
}

impl MetaTag for MetaB {
    open spec fn tag_spec() -> usize {
        2
    }

    fn tag() -> (r: usize) {
        2
    }

    proof fn tag_coherent(&self) {
    }
}

impl MetaSlot {
    /// Cast 1 — upcast at write time. Mimics `MetaSlot::write_meta`.
    ///
    /// The body is the line that is *commented out* in our tree. It typechecks;
    /// `external_body` is needed only because `core::ptr::metadata` has no spec.
    /// Note the explicit `'static`. Upstream it is implied by `AnyFrameMeta: Any`,
    /// since `Any: 'static`; with `Any` unavailable the bound has to be written by
    /// hand, or `core::ptr::metadata` rejects the coercion with `E0310`.
    #[verifier::external_body]
    pub unsafe fn write_meta<M: AnyMeta + 'static>(&self, metadata: M) {
        // SAFETY: Caller ensures that the access to the fields are exclusive.
        let vtable_ptr = unsafe { &mut *self.vtable_ptr.get() };
        vtable_ptr.write(core::ptr::metadata(&metadata as &dyn AnyMeta));
    }

    /// Cast 2 — rebuild a wide pointer and dispatch through it.
    /// Mimics `MetaSlot::drop_meta_in_place`.
    ///
    /// This is the shape our tree currently keeps alive only as a type-check. It
    /// is accepted as written.
    #[verifier::external_body]
    pub unsafe fn drop_meta_in_place(&self) {
        // SAFETY: We have exclusive access to the frame metadata.
        let vtable_ptr = unsafe { &mut *self.vtable_ptr.get() };
        // SAFETY: The frame metadata is initialized and valid.
        let vtable_ptr = unsafe { vtable_ptr.assume_init_read() };

        let storage_ptr: *mut () = self.storage.get() as *mut ();
        let meta_ptr: *mut dyn AnyMeta = core::ptr::from_raw_parts_mut(storage_ptr, vtable_ptr);

        // SAFETY: `ptr` points to the metadata storage which is valid to be
        // mutably borrowed under `vtable_ptr` because the metadata is valid,
        // the vtable is correct, and we have exclusive access.
        unsafe {
            // Invoke the custom `on_drop` handler.
            (*meta_ptr).on_drop();
            // Drop the frame metadata.
            core::ptr::drop_in_place(meta_ptr);
        }
    }

    /// Mimics `MetaSlot::dyn_meta_ptr`, the shared-reference form.
    #[verifier::external_body]
    pub unsafe fn dyn_meta_ptr(&self) -> *mut dyn AnyMeta {
        // SAFETY: The page metadata is valid to be borrowed immutably, since it
        // will never be borrowed mutably after initialization.
        let vtable_ptr = unsafe { &*self.vtable_ptr.get() };

        // SAFETY: The page metadata is initialized and valid.
        let vtable_ptr = *unsafe { vtable_ptr.assume_init_ref() };

        core::ptr::from_raw_parts_mut(self as *const MetaSlot as *mut MetaSlot, vtable_ptr)
    }
}

/// Mimics `Frame<M>`.
///
/// `#[repr(transparent)]` over a pointer plus a ZST phantom, as upstream, which is
/// what makes the transmutes in casts 3 and 4 layout-valid.
#[repr(transparent)]
pub struct Frame<M: ?Sized> {
    pub ptr: *const MetaSlot,
    pub _marker: PhantomData<M>,
}

impl<M: AnyMeta + 'static> Frame<M> {
    /// Cast 3 — erase the static metadata type. Mimics `Frame::into_dyn`.
    #[verifier::external_body]
    pub fn into_dyn(self) -> Frame<dyn AnyMeta> {
        // SAFETY: `Frame<M>` is `#[repr(transparent)]` over a thin pointer plus a
        // zero-size `PhantomData<M>`. `Frame<dyn AnyMeta>` has the same runtime
        // layout (thin pointer + ZST phantom).
        unsafe { core::mem::transmute(self) }
    }
}

impl Frame<dyn AnyMeta> {
    /// The id of the metadata this frame points at.
    ///
    /// Uninterpreted here because the dummy slot carries no ghost state; in the
    /// frame layer this is the region's view of the slot.
    pub uninterp spec fn meta_id(&self) -> usize;

    /// Mimics `Frame::<dyn AnyFrameMeta>::dyn_meta`.
    ///
    /// The `ensures` is what makes the erased reference usable: without tying the
    /// dispatched id back to the frame, a caller could compare tags and conclude
    /// nothing about *this* frame.
    #[verifier::external_body]
    pub fn dyn_meta(&self) -> (r: &dyn AnyMeta)
        ensures
            r.type_id() == self.meta_id(),
    {
        // SAFETY: The metadata is initialized and valid.
        unsafe { &*(*self.ptr).dyn_meta_ptr() }
    }
}

/// Cast 4, with the one substitution that makes it expressible.
///
/// Mirrors `TryFrom<Frame<dyn AnyFrameMeta>> for Frame<M>`, except that
///
/// ```text
/// if (dyn_frame.dyn_meta() as &dyn core::any::Any).is::<M>() {
/// ```
///
/// becomes
///
/// ```text
/// if dyn_frame.dyn_meta().type_id_val() == M::tag() {
/// ```
///
/// Both compare an id read through the vtable against one known statically. The
/// difference is only where the ids come from: the compiler's `TypeId`, which
/// Verus cannot see, versus [`MetaTag`], which it can.
///
/// A free function rather than a `TryFrom` impl, to keep the tag plumbing visible;
/// the `Result` shape and the unchanged-on-failure `Err` are preserved.
///
/// The transmute stays `external_body`, as upstream. What is *gained* is that the
/// test guarding it is verified: the postcondition records that `Ok` happens
/// exactly when the frame's metadata has `M`'s id.
pub fn try_from_tagged<M: AnyMeta + MetaTag + 'static>(dyn_frame: Frame<dyn AnyMeta>) -> (res:
    Result<Frame<M>, Frame<dyn AnyMeta>>)
    ensures
        (res is Ok) == (dyn_frame.meta_id() == M::tag_spec()),
{
    if dyn_frame.dyn_meta().type_id_val() == M::tag() {
        // SAFETY: The metadata is coerceable and the struct is transmutable.
        Ok(transmute_to_typed::<M>(dyn_frame))
    } else {
        Err(dyn_frame)
    }
}

/// The transmute half of cast 4, split out so the test above stays verified.
#[verifier::external_body]
pub fn transmute_to_typed<M: AnyMeta + 'static>(dyn_frame: Frame<dyn AnyMeta>) -> Frame<M> {
    // SAFETY: The metadata is coerceable and the struct is transmutable.
    unsafe { core::mem::transmute::<Frame<dyn AnyMeta>, Frame<M>>(dyn_frame) }
}

/// The downcast admits the right type and rejects the other.
///
/// Both directions matter and neither is vacuous: `Ok` needs the tags to agree,
/// and `Err` is what stops a `MetaB` frame from being read as a `MetaA`.
pub fn downcast_discriminates(a: Frame<dyn AnyMeta>, b: Frame<dyn AnyMeta>)
    requires
        a.meta_id() == 1,
        b.meta_id() == 2,
{
    let ra = try_from_tagged::<MetaA>(a);
    assert(ra is Ok);
    let rb = try_from_tagged::<MetaA>(b);
    assert(rb is Err);
}

} // verus!
