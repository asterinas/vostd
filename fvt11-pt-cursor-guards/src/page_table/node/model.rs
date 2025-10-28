use aster_common::x86_64;
use vstd::prelude::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;

use vstd_extra::prelude::*;
use aster_common::prelude::*;
use aster_common::x86_64::mm;
use vstd_extra::array_ptr;
use vstd_extra::ghost_tree;

verus! {

pub const NR_ENTRIES: usize = 512;

pub const NR_LEVELS: usize = 4;

pub const PAGE_SIZE: usize = 4096;

pub const BASE_PAGE_SIZE: usize = 4096;

#[allow(non_snake_case)]
pub proof fn correctness_PAGE_SIZE()
    ensures
        PAGE_SIZE == mm::PAGE_SIZE(),
{
}

#[allow(non_snake_case)]
pub proof fn correctness_NR_ENTRIES()
    ensures
        NR_ENTRIES == PAGE_SIZE / PagingConsts::PTE_SIZE(),
{
}

#[allow(non_snake_case)]
pub proof fn correctness_NR_LEVELS()
    ensures
        NR_LEVELS == mm::NR_LEVELS(),
{
}

#[allow(non_snake_case)]
pub proof fn correctness_BASE_PAGE_SIZE()
    ensures
        BASE_PAGE_SIZE == x86_64::PagingConsts::BASE_PAGE_SIZE(),
{
}

impl PageTableNodeValue {
    #[rustc_allow_incoherent_impl]
    pub open spec fn paddr(self) -> usize {
        self.paddr
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn clone_raw(self) -> Self {
        Self { nr_raws: self.nr_raws + 1, ..self }
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn lock(self) -> Option<Self> {
        if self.is_locked {
            None
        } else {
            Some(Self { is_locked: true, ..self })
        }
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn borrow_perms(tracked &self) -> (tracked res: &Option<
        array_ptr::PointsTo<PageTableEntry, NR_ENTRIES>,
    >)
        ensures
            *res == self.perms,
    {
        &self.perms
    }

    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub fn write_pte(
        Tracked(value): Tracked<&mut Self>,
        ptr: ArrayPtr<PageTableEntry, NR_ENTRIES>,
        index: usize,
        entry: PageTableEntry,
    )
        requires
            old(value).inv(),
            old(value).paddr != 0,
            old(value).is_locked,
            old(value).perms.unwrap().is_pptr(ptr),
            index < NR_ENTRIES,
        ensures
            value.inv(),
            value.paddr == old(value).paddr,
            value.is_locked,
            value.perms.unwrap().is_pptr(ptr),
            value.perms.unwrap().is_init(index as int),
            value.perms.unwrap().opt_value()[index as int].value() == entry,
            forall|i: int|
                0 <= i < NR_ENTRIES && i != index
                    ==> #[trigger] value.perms.unwrap().opt_value()[i].value() == old(
                    value,
                ).perms.unwrap().opt_value()[i].value(),
    {
        let tracked mut perms = value.perms.tracked_unwrap();
        ptr.overwrite(Tracked(&mut perms), index, entry);
    }

    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub proof fn tracked_write_pte(
        tracked &mut self,
        tracked arr_ptr: ArrayPtr<PageTableEntry, NR_ENTRIES>,
        tracked index: usize,
        tracked entry: PageTableEntry,
    )
        requires
            old(self).inv(),
            old(self).paddr != 0,
            old(self).is_locked,
            old(self).perms.unwrap().is_pptr(arr_ptr),
            index < NR_ENTRIES,
        ensures
            self.inv(),
            self.paddr == old(self).paddr,
            self.is_locked,
            self.perms.unwrap().is_pptr(arr_ptr),
            self.perms.unwrap().is_init(index as int),
            self.perms.unwrap().opt_value()[index as int].value() == entry,
            forall|i: int|
                0 <= i < NR_ENTRIES && i != index
                    ==> #[trigger] self.perms.unwrap().opt_value()[i].value() == old(
                    self,
                ).perms.unwrap().opt_value()[i].value(),
    {
        let tracked perms = self.perms.tracked_borrow();
        arr_ptr.tracked_overwrite(&mut perms, index, entry);
    }

    #[rustc_allow_incoherent_impl]
    pub fn drop(Tracked(value): Tracked<Self>, ptr: ArrayPtr<PageTableEntry, NR_ENTRIES>)
        requires
            value.inv(),
            value.paddr != 0,
            value.is_locked,
            value.perms.unwrap().is_pptr(ptr),
            value.perms.unwrap().is_uninit_all(),
    {
        ptr.free(Tracked(value.perms.tracked_unwrap()));
    }
}

pub proof fn pt_node_tracked_write_pte(
    tracked node: &mut PageTableNodeModel,
    tracked arr_ptr: ArrayPtr<PageTableEntry, NR_ENTRIES>,
    tracked index: usize,
    tracked entry: PageTableEntry,
)
    requires
        old(node)@.inv(),
        old(node)@.value.paddr != 0,
        old(node)@.value.is_locked,
        old(node)@.value.perms.unwrap().is_pptr(arr_ptr),
        index < NR_ENTRIES,
    ensures
        node@.inv(),
        node@.value.paddr == old(node)@.value.paddr,
        node@.value.is_locked,
        node@.value.perms.unwrap().is_pptr(arr_ptr),
        node@.value.perms.unwrap().is_init(index as int),
        node@.value.perms.unwrap().opt_value()[index as int].value() == entry,
        forall|i: int|
            0 <= i < NR_ENTRIES && i != index
                ==> #[trigger] node@.value.perms.unwrap().opt_value()[i].value() == old(
                node,
            )@.value.perms.unwrap().opt_value()[i].value(),
{
    node.inner.value.tracked_write_pte(arr_ptr, index, entry);
}

pub fn pt_node_write_pte(
    Tracked(node): Tracked<&mut PageTableNodeModel>,
    arr_ptr: ArrayPtr<PageTableEntry, NR_ENTRIES>,
    index: usize,
    entry: PageTableEntry,
)
    requires
        old(node)@.inv(),
        old(node)@.value.paddr != 0,
        old(node)@.value.is_locked,
        old(node)@.value.perms.unwrap().is_pptr(arr_ptr),
        index < NR_ENTRIES,
    ensures
        node@.inv(),
        node@.value.paddr == old(node)@.value.paddr,
        node@.value.is_locked,
        node@.value.perms.unwrap().is_pptr(arr_ptr),
        node@.value.perms.unwrap().is_init(index as int),
        node@.value.perms.unwrap().opt_value()[index as int].value() == entry,
        forall|i: int|
            0 <= i < NR_ENTRIES && i != index
                ==> #[trigger] node@.value.perms.unwrap().opt_value()[i].value() == old(
                node,
            )@.value.perms.unwrap().opt_value()[i].value(),
{
    PageTableNodeValue::write_pte(Tracked(&mut node.inner.value), arr_ptr, index, entry);
}

pub fn pt_node_free(
    Tracked(node): Tracked<PageTableNodeModel>,
    ptr: ArrayPtr<PageTableEntry, NR_ENTRIES>,
)
    requires
        node@.inv(),
        node@.value.paddr != 0,
        node@.value.is_locked,
        node@.value.perms.unwrap().is_pptr(ptr),
        node@.value.perms.unwrap().is_uninit_all(),
    ensures
        !node@.value.is_locked,
{
    PageTableNodeValue::drop(Tracked(node.inner.value), ptr);
    assert(!node@.value.is_locked) by { admit() };
}

} // verus!
