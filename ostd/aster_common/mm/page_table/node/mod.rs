mod child;
mod entry;
mod entry_owners;
mod entry_view;
mod owners;

pub use child::*;
pub use entry::*;
pub use entry_owners::*;
pub use entry_view::*;
pub use owners::*;

use vstd::prelude::*;

use vstd::atomic::PAtomicU8;
use vstd::cell::PCell;
use vstd_extra::cast_ptr::*;
use vstd_extra::ownership::*;

use core::marker::PhantomData;

use super::*;

verus! {

/// The metadata of any kinds of page table pages.
/// Make sure the the generic parameters don't effect the memory layout.
#[rustc_has_incoherent_inherent_impls]
pub struct PageTablePageMeta<C: PageTableConfig> {
    /// The number of valid PTEs. It is mutable if the lock is held.
    pub nr_children: PCell<u16>,
    /// If the page table is detached from its parent.
    ///
    /// A page table can be detached from its parent while still being accessed,
    /// since we use a RCU scheme to recycle page tables. If this flag is set,
    /// it means that the parent is recycling the page table.
    pub stray: PCell<bool>,
    /// The level of the page table page. A page table page cannot be
    /// referenced by page tables of different levels.
    pub level: PagingLevel,
    /// The lock for the page table page.
    pub lock: PAtomicU8,
    pub _phantom: core::marker::PhantomData<C>,
}

/// A smart pointer to a page table node.
///
/// This smart pointer is an owner of a page table node. Thus creating and
/// dropping it will affect the reference count of the page table node. If
/// dropped it as the last reference, the page table node and subsequent
/// children will be freed.
///
/// [`PageTableNode`] is read-only. To modify the page table node, lock and use
/// [`PageTableGuard`].
pub type PageTableNode<C> = Frame<PageTablePageMeta<C>>;

impl<C: PageTableConfig> PageTablePageMeta<C> {
    #[verifier::external_body]
    pub fn get_stray(&self) -> PCell<bool>
        returns
            self.stray,
    {
        unimplemented!()
    }

    pub open spec fn into_spec(self) -> StoredPageTablePageMeta {
        StoredPageTablePageMeta {
            nr_children: self.nr_children,
            stray: self.stray,
            level: self.level,
            lock: self.lock,
        }
    }

    #[verifier::when_used_as_spec(into_spec)]
    pub fn into(self) -> (res: StoredPageTablePageMeta)
        ensures
            res == self.into_spec(),
    {
        StoredPageTablePageMeta {
            nr_children: self.nr_children,
            stray: self.stray,
            level: self.level,
            lock: self.lock,
        }
    }
}

impl StoredPageTablePageMeta {
    pub open spec fn into_spec<C: PageTableConfig>(self) -> PageTablePageMeta<C> {
        PageTablePageMeta::<C> {
            nr_children: self.nr_children,
            stray: self.stray,
            level: self.level,
            lock: self.lock,
            _phantom: PhantomData,
        }
    }

    #[verifier::when_used_as_spec(into_spec)]
    pub fn into<C: PageTableConfig>(self) -> (res: PageTablePageMeta<C>)
        ensures
            res == self.into_spec::<C>(),
    {
        PageTablePageMeta::<C> {
            nr_children: self.nr_children,
            stray: self.stray,
            level: self.level,
            lock: self.lock,
            _phantom: PhantomData,
        }
    }
}

uninterp spec fn drop_tree_spec<C: PageTableConfig>(_page: Frame<PageTablePageMeta<C>>) -> Frame<
    PageTablePageMeta<C>,
>;

#[verifier::external_body]
extern  fn drop_tree<C: PageTableConfig>(_page: &mut Frame<PageTablePageMeta<C>>)
    ensures
        _page == drop_tree_spec::<C>(*old(_page)),
;

impl<C: PageTableConfig> Repr<MetaSlot> for PageTablePageMeta<C> {
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
        //        &r.get_node().unwrap().into()

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

impl<C: PageTableConfig> AnyFrameMeta for PageTablePageMeta<C> {
    fn on_drop(&mut self) {
    }

    fn is_untyped(&self) -> bool {
        false
    }

    uninterp spec fn vtable_ptr(&self) -> usize;
}

} // verus!
