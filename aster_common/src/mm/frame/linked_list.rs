use vstd::prelude::*;

use vstd_extra::cast_ptr::*;

use super::*;

verus! {

#[rustc_has_incoherent_inherent_impls]
pub struct Link<M: AnyFrameMeta + Repr<MetaSlotInner>> {
    pub next: Option<ReprPtr<MetaSlotStorage, Link<M>>>,
    pub prev: Option<ReprPtr<MetaSlotStorage, Link<M>>>,
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
pub struct LinkedList<M: AnyFrameMeta + Repr<MetaSlotInner>> {
    pub front: Option<ReprPtr<MetaSlotStorage, Link<M>>>,
    pub back: Option<ReprPtr<MetaSlotStorage, Link<M>>>,
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
pub struct CursorMut<M: AnyFrameMeta + Repr<MetaSlotInner>> {
    pub list: PPtr<LinkedList<M>>,
    pub current: Option<ReprPtr<MetaSlotStorage, Link<M>>>,
}

impl<M: AnyFrameMeta + Repr<MetaSlotInner>> LinkedList<M> {
    /// Creates a new linked list.
    pub const fn new() -> Self {
        Self { front: None, back: None, size: 0, list_id: 0 }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotInner>> Default for LinkedList<M> {
    fn default() -> Self {
        Self::new()
    }
}

pub struct MetaSlotInner {}

pub struct StoredLink {
    pub next: Option<Paddr>,
    pub prev: Option<Paddr>,
    pub slot: MetaSlotInner,
}

impl StoredLink {
    pub open spec fn retrieve_spec<M: AnyFrameMeta + Repr<MetaSlotInner>>(self) -> Link<M> {
        let next = match self.next {
            Some(addr) => Some(
                ReprPtr {
                    addr: addr,
                    ptr: PPtr::<MetaSlotStorage>(addr, PhantomData),
                    _T: PhantomData,
                },
            ),
            None => None,
        };
        let prev = match self.prev {
            Some(addr) => Some(
                ReprPtr {
                    addr: addr,
                    ptr: PPtr::<MetaSlotStorage>(addr, PhantomData),
                    _T: PhantomData,
                },
            ),
            None => None,
        };
        Link::<M> { next: next, prev: prev, meta: M::from_repr(self.slot) }
    }

    #[verifier::when_used_as_spec(retrieve_spec)]
    pub fn retrieve<M: AnyFrameMeta + Repr<MetaSlotInner>>(self) -> (res: Link<M>)
        requires
            M::wf(self.slot),
        ensures
            res == self.retrieve_spec::<M>(),
    {
        let next = match self.next {
            Some(addr) => Some(
                ReprPtr {
                    addr: addr,
                    ptr: PPtr::<MetaSlotStorage>::from_addr(addr),
                    _T: PhantomData,
                },
            ),
            None => None,
        };
        let prev = match self.prev {
            Some(addr) => Some(
                ReprPtr {
                    addr: addr,
                    ptr: PPtr::<MetaSlotStorage>::from_addr(addr),
                    _T: PhantomData,
                },
            ),
            None => None,
        };
        Link::<M> { next: next, prev: prev, meta: M::from_repr(self.slot) }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotInner>> Link<M> {
    pub open spec fn stored_spec(self) -> StoredLink {
        let next = match self.next {
            Some(link) => Some(link.addr),
            None => None,
        };
        let prev = match self.prev {
            Some(link) => Some(link.addr),
            None => None,
        };
        StoredLink { next: next, prev: prev, slot: self.meta.to_repr() }
    }

    #[verifier::when_used_as_spec(stored_spec)]
    pub fn stored(self) -> (res: StoredLink)
        ensures
            res == self.stored_spec(),
    {
        let next = match self.next {
            Some(link) => Some(link.addr),
            None => None,
        };
        let prev = match self.prev {
            Some(link) => Some(link.addr),
            None => None,
        };
        StoredLink { next: next, prev: prev, slot: self.meta.to_repr() }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotInner>> Repr<MetaSlotStorage> for Link<M> {
    open spec fn wf(r: MetaSlotStorage) -> bool {
        match r {
            MetaSlotStorage::FrameLink(link) => M::wf(link.slot),
            _ => false,
        }
    }

    open spec fn to_repr_spec(self) -> MetaSlotStorage {
        MetaSlotStorage::FrameLink(self.stored())
    }

    fn to_repr(self) -> MetaSlotStorage {
        MetaSlotStorage::FrameLink(self.stored())
    }

    open spec fn from_repr_spec(r: MetaSlotStorage) -> Self {
        r.get_link().unwrap().retrieve()
    }

    fn from_repr(r: MetaSlotStorage) -> Self {
        r.get_link().unwrap().retrieve()
    }

    #[verifier::external_body]
    fn from_borrowed<'a>(r: &'a MetaSlotStorage) -> &'a Self {
        unimplemented!()
        //        &r.get_link().unwrap().into()

    }

    proof fn from_to_repr(self) {
        <M as Repr<MetaSlotInner>>::from_to_repr(self.meta);
        admit()
    }

    proof fn to_from_repr(r: MetaSlotStorage) {
        M::to_from_repr(r.get_link().unwrap().slot)
    }

    proof fn to_repr_wf(self) {
        <M as Repr<MetaSlotInner>>::to_repr_wf(self.meta)
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotInner>> AnyFrameMeta for Link<M> {
    fn on_drop(&mut self) {
    }

    fn is_untyped(&self) -> bool {
        false
    }

    uninterp spec fn vtable_ptr(&self) -> usize;
}

} // verus!
