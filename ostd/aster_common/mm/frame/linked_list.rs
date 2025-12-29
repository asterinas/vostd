use vstd::prelude::*;

use vstd_extra::cast_ptr::*;

use super::*;

verus! {

#[rustc_has_incoherent_inherent_impls]
pub struct Link<M: AnyFrameMeta + Repr<MetaSlot>> {
    pub next: Option<ReprPtr<MetaSlot, Link<M>>>,
    pub prev: Option<ReprPtr<MetaSlot, Link<M>>>,
    pub meta: M,
}

/// A linked list of frames.
///
/// Two key features that [`LinkedList`] is different from
/// [`alloc::collections::LinkedList`] is that:
///  1. It is intrusive, meaning that the links are part of the frame metadata.
///     This allows the linked list to be used without heap allocation. But it
///     disallows a frame to be in multiple linked lists at the same time.
///  2. The linked list exclusively own the frames, meaning that it takes
///     unique pointers [`UniqueFrame`]. And other bodies cannot
///     [`from_in_use`] a frame that is inside a linked list.
///  3. We also allow creating cursors at a specific frame, allowing $O(1)$
///     removal without iterating through the list at a cost of some checks.
///
/// # Example
///
/// To create metadata types that allows linked list links, wrap the metadata
/// type in [`Link`]:
///
/// ```rust
/// use ostd::{
///     mm::{frame::{linked_list::{Link, LinkedList}, Frame}, FrameAllocOptions},
///     impl_untyped_frame_meta_for,
/// };
///
/// #[derive(Debug)]
/// struct MyMeta { mark: usize }
///
/// type MyFrame = Frame<Link<MyMeta>>;
///
/// impl_untyped_frame_meta_for!(MyMeta);
///
/// let alloc_options = FrameAllocOptions::new();
/// let frame1 = alloc_options.alloc_frame_with(Link::new(MyMeta { mark: 1 })).unwrap();
/// let frame2 = alloc_options.alloc_frame_with(Link::new(MyMeta { mark: 2 })).unwrap();
///
/// let mut list = LinkedList::new();
/// list.push_front(frame1.try_into().unwrap());
/// list.push_front(frame2.try_into().unwrap());
///
/// let mut cursor = list.cursor_front_mut();
/// assert_eq!(cursor.current_meta().unwrap().mark, 2);
/// cursor.move_next();
/// assert_eq!(cursor.current_meta().unwrap().mark, 1);
/// ```
///
/// [`from_in_use`]: Frame::from_in_use
#[rustc_has_incoherent_inherent_impls]
pub struct LinkedList<M: AnyFrameMeta + Repr<MetaSlot>> {
    pub front: Option<ReprPtr<MetaSlot, Link<M>>>,
    pub back: Option<ReprPtr<MetaSlot, Link<M>>>,
    /// The number of frames in the list.
    pub size: usize,
    /// A lazily initialized ID, used to check whether a frame is in the list.
    /// 0 means uninitialized.
    pub list_id: u64,
}

/// A cursor that can mutate the linked list links.
///
/// The cursor points to either a frame or the "ghost" non-element. It points
/// to the "ghost" non-element when the cursor surpasses the back of the list.
#[rustc_has_incoherent_inherent_impls]
pub struct CursorMut<M: AnyFrameMeta + Repr<MetaSlot>> {
    pub list: PPtr<LinkedList<M>>,
    pub current: Option<ReprPtr<MetaSlot, Link<M>>>,
}

impl<M: AnyFrameMeta + Repr<MetaSlot>> LinkedList<M> {
    /// Creates a new linked list.
    pub const fn new() -> Self {
        Self { front: None, back: None, size: 0, list_id: 0 }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlot>> Default for LinkedList<M> {
    fn default() -> Self {
        Self::new()
    }
}

pub struct StoredLink {
    pub next: Option<Paddr>,
    pub prev: Option<Paddr>,
    pub slot: MetaSlot,
}

impl<M: AnyFrameMeta + Repr<MetaSlot>> Repr<MetaSlot> for Link<M> {
    uninterp spec fn wf(r: MetaSlot) -> bool;

    uninterp spec fn to_repr_spec(self) -> MetaSlot;

    #[verifier::external_body]
    fn to_repr(self) -> MetaSlot {
        unimplemented!()
    }

    uninterp spec fn from_repr_spec(r: MetaSlot) -> Self;

    #[verifier::external_body]
    fn from_repr(r: MetaSlot) -> Self {
        unimplemented!()
    }

    #[verifier::external_body]
    fn from_borrowed<'a>(r: &'a MetaSlot) -> &'a Self {
        unimplemented!()
    }

    proof fn from_to_repr(self) {
        admit()
    }

    proof fn to_from_repr(r: MetaSlot) {
        admit()
    }

    proof fn to_repr_wf(self) {
        admit()
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlot>> AnyFrameMeta for Link<M> {
    fn on_drop(&mut self) {
    }

    fn is_untyped(&self) -> bool {
        false
    }

    uninterp spec fn vtable_ptr(&self) -> usize;
}

} // verus!
