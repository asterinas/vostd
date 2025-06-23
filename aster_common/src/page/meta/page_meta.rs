use vstd::prelude::*;

use super::super::Page;
use super::PageUsage;

verus! {

#[allow(non_snake_case)]
pub trait PageMeta: Sync + Sized {
    spec fn USAGE_spec() -> PageUsage;

    proof fn used()
        ensures
            Self::USAGE_spec() != PageUsage::Unused,
    ;

    #[verifier::when_used_as_spec(USAGE_spec)]
    fn USAGE() -> (res: PageUsage)
        ensures
            res == Self::USAGE_spec(),
    ;

    spec fn on_drop_spec(page: Page<Self>) -> (res: Page<Self>);

    fn on_drop(page: &mut Page<Self>)
        ensures
            page == Self::on_drop_spec(*old(page)),
    ;
}

} // verus!
verus! {

#[derive(Debug, Default)]
#[repr(C)]
pub struct FrameMeta {
    // If not doing so, the page table metadata would fit
    // in the front padding of meta slot and make it 12 bytes.
    // We make it 16 bytes. Further usage of frame metadata
    // is welcome to exploit this space.
    _unused_for_layout_padding: [u8; 8],
}

impl PageMeta for FrameMeta {
    #[verifier::inline]
    open spec fn USAGE_spec() -> PageUsage {
        PageUsage::Frame
    }

    proof fn used() {
        assert(PageUsage::Frame != PageUsage::Unused);
    }

    #[inline(always)]
    fn USAGE() -> (res: PageUsage)
        ensures
            res == Self::USAGE_spec(),
    {
        PageUsage::Frame
    }

    #[verifier::inline]
    open spec fn on_drop_spec(page: Page<Self>) -> (res: Page<Self>) {
        page
    }

    #[inline(always)]
    fn on_drop(page: &mut Page<Self>)
        ensures
            page == Self::on_drop_spec(*old(page)),
    {
        // Nothing should be done so far since dropping the page would
        // have all taken care of.
    }
}

} // verus!
verus! {

use vstd::cell::{PCell, PointsTo};
use vstd::atomic::{PAtomicU8, PermissionU8};
use crate::mm::*;
use crate::x86_64::page_table_entry::PageTableEntry;
use crate::x86_64::paging_consts::PagingConsts;
use core::marker::PhantomData;

#[rustc_has_incoherent_inherent_impls]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum MapTrackingStatus {
    /// The page table node cannot contain references to any pages. It can only
    /// contain references to child page table nodes.
    NotApplicable,
    /// The mapped pages are not tracked by metadata. If any child page table
    /// nodes exist, they should also be tracked.
    Untracked,
    /// The mapped pages are tracked by metadata. If any child page table nodes
    /// exist, they should also be tracked.
    Tracked,
}

impl Default for MapTrackingStatus {
    fn default() -> Self {
        MapTrackingStatus::NotApplicable
    }
}

#[derive(Debug, Default)]
#[repr(C)]
pub struct PageTablePageMetaInner {
    pub nr_children: u16,
    pub level: PagingLevel,
    pub is_tracked: MapTrackingStatus,
}

#[repr(C)]
#[rustc_has_incoherent_inherent_impls]
pub struct PageTablePageMeta {
    pub lock: PAtomicU8,
    pub inner: PCell<PageTablePageMetaInner>,
    pub _phantom: PhantomData<(PageTableEntry, PagingConsts)>,
}

spec fn drop_tree_spec(_page: Page<PageTablePageMeta>) -> Page<PageTablePageMeta>;

#[verifier::external_body]
extern  fn drop_tree(_page: &mut Page<PageTablePageMeta>)
    ensures
        _page == drop_tree_spec(*old(_page)),
;

impl PageMeta for PageTablePageMeta {
    #[verifier::inline]
    open spec fn USAGE_spec() -> PageUsage {
        PageUsage::PageTable
    }

    proof fn used() {
        assert(PageUsage::PageTable != PageUsage::Unused);
    }

    #[inline(always)]
    fn USAGE() -> (res: PageUsage)
        ensures
            res == Self::USAGE_spec(),
    {
        PageUsage::PageTable
    }

    closed spec fn on_drop_spec(_page: Page<Self>) -> (res: Page<Self>) {
        drop_tree_spec(_page)
    }

    fn on_drop(_page: &mut Page<Self>)
        ensures
            _page == Self::on_drop_spec(*old(_page)),
    {
        drop_tree(_page)
    }
}

#[rustc_has_incoherent_inherent_impls]
pub tracked struct PageTablePageMetaModel {
    pub tracked lock: PermissionU8,
    pub tracked inner: PointsTo<PageTablePageMetaInner>,
}

impl PageTablePageMetaModel {
    pub open spec fn relate(&self, m: &PageTablePageMeta) -> bool {
        self.lock.is_for(m.lock) && self.inner.id() == m.inner.id()
    }
}

impl PageTablePageMeta {
    pub open spec fn new_locked_spec(
        level: PagingLevel,
        is_tracked: MapTrackingStatus,
        res: PageTablePageMetaModel,
    ) -> bool {
        &&& res.lock@.value == 1
        &&& res.inner.opt_value() == Some(
            { PageTablePageMetaInner { level, nr_children: 0, is_tracked } },
        )
    }

    pub fn new_locked(level: PagingLevel, is_tracked: MapTrackingStatus) -> (res: (
        Self,
        Tracked<PageTablePageMetaModel>,
    ))
        ensures
            res.1@.relate(&res.0),
            res.1@.inner.is_init(),
            Self::new_locked_spec(level, is_tracked, res.1@),
    {
        let (inner, Tracked(perm)) = PCell::new(
            PageTablePageMetaInner { level, nr_children: 0, is_tracked },
        );
        let (lock, Tracked(lk_perm)) = PAtomicU8::new(1);
        let tracked model = PageTablePageMetaModel { lock: lk_perm, inner: perm };
        let meta = Self { lock, inner, _phantom: PhantomData };
        (meta, Tracked(model))
    }
}

} // verus!
verus! {

#[derive(Debug, Default)]
#[repr(C)]
pub struct MetaPageMeta {}

impl PageMeta for MetaPageMeta {
    #[verifier::inline]
    open spec fn USAGE_spec() -> PageUsage {
        PageUsage::Meta
    }

    proof fn used() {
        assert(PageUsage::Meta != PageUsage::Unused);
    }

    #[inline(always)]
    fn USAGE() -> (res: PageUsage)
        ensures
            res == Self::USAGE_spec(),
    {
        PageUsage::Meta
    }

    #[verifier::inline]
    open spec fn on_drop_spec(_page: Page<Self>) -> (res: Page<Self>) {
        _page
    }

    fn on_drop(_page: &mut Page<Self>)
        ensures
            _page == Self::on_drop_spec(*old(_page)),
    {
    }
}

} // verus!
verus! {

#[derive(Debug, Default)]
#[repr(C)]
pub struct KernelMeta {}

impl PageMeta for KernelMeta {
    #[verifier::inline]
    open spec fn USAGE_spec() -> PageUsage {
        PageUsage::Kernel
    }

    proof fn used() {
        assert(PageUsage::Kernel != PageUsage::Unused);
    }

    #[inline(always)]
    fn USAGE() -> (res: PageUsage)
        ensures
            res == Self::USAGE_spec(),
    {
        PageUsage::Kernel
    }

    #[verifier::inline]
    open spec fn on_drop_spec(_page: Page<Self>) -> (res: Page<Self>) {
        _page
    }

    fn on_drop(_page: &mut Page<Self>)
        ensures
            _page == Self::on_drop_spec(*old(_page)),
    {
    }
}

} // verus!
