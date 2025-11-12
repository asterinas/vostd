//pub mod model;
use vstd::prelude::*;

use vstd::simple_pptr::*;
use vstd_extra::ghost_tree::TreePath;
use vstd_extra::ownership::*;

use core::marker::PhantomData;
use core::ops::Range;

use super::*;

//use model::ConcreteCursor;

verus! {

/// The state of virtual pages represented by a page table.
///
/// This is the return type of the [`Cursor::query`] method.
pub type PagesState<C> = (Range<Vaddr>, Option<<C as PageTableConfig>::Item>);

/// The cursor for traversal over the page table.
///
/// A slot is a PTE at any levels, which correspond to a certain virtual
/// memory range sized by the "page size" of the current level.
///
/// A cursor is able to move to the next slot, to read page properties,
/// and even to jump to a virtual address directly.
#[rustc_has_incoherent_inherent_impls]
pub struct Cursor<'rcu, C: PageTableConfig, A: InAtomicMode> {
    /// The current path of the cursor.
    ///
    /// The level 1 page table lock guard is at index 0, and the level N page
    /// table lock guard is at index N - 1.
    pub path: [Option<PPtr<PageTableGuard<'rcu, C>>>; MAX_NR_LEVELS()],
    /// The cursor should be used in a RCU read side critical section.
    pub rcu_guard: &'rcu A,
    /// The level of the page table that the cursor currently points to.
    pub level: PagingLevel,
    /// The top-most level that the cursor is allowed to access.
    ///
    /// From `level` to `guard_level`, the nodes are held in `path`.
    pub guard_level: PagingLevel,
    /// The virtual address that the cursor currently points to.
    pub va: Vaddr,
    /// The virtual address range that is locked.
    pub barrier_va: Range<Vaddr>,
    pub _phantom: PhantomData<&'rcu PageTable<C>>,
}

pub tracked struct CursorOwner {
    pub path: TreePath<CONST_NR_ENTRIES>,
}

#[rustc_has_incoherent_inherent_impls]
pub ghost struct CursorModel {
    pub path: TreePath<CONST_NR_ENTRIES>,
}

impl Inv for CursorOwner {
    open spec fn inv(self) -> bool {
        0 <= self.path.len() <= 3
    }
}

impl Inv for CursorModel {
    open spec fn inv(self) -> bool {
        true
    }
}

impl View for CursorOwner {
    type V = CursorModel;

    open spec fn view(&self) -> Self::V {
        CursorModel { path: self.path }
    }

}

impl InvView for CursorOwner {
    proof fn view_preserves_inv(self) { }
}


impl<'rcu, C: PageTableConfig, A: InAtomicMode> OwnerOf for Cursor<'rcu, C, A> {
    type Owner = CursorOwner;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& self.level == owner.path.len() + 1
        &&& 1 <= self.level <= 4
    }
}

impl<'rcu, C: PageTableConfig, A: InAtomicMode> ModelOf for Cursor<'rcu, C, A> {

}


/// The cursor of a page table that is capable of map, unmap or protect pages.
///
/// It has all the capabilities of a [`Cursor`], which can navigate over the
/// page table corresponding to the address range. A virtual address range
/// in a page table can only be accessed by one cursor, regardless of the
/// mutability of the cursor.
#[rustc_has_incoherent_inherent_impls]
pub struct CursorMut<'rcu, C: PageTableConfig, A: InAtomicMode> {
    pub inner: Cursor<'rcu, C, A>,
}

impl<C: PageTableConfig, A: InAtomicMode> Iterator for Cursor<'_, C, A> {
    type Item = PagesState<C>;

    #[verifier::external_body]
    fn next(&mut self) -> Option<Self::Item> {
        unimplemented!()/*  let result = self.query();
        if result.is_ok() {
            self.move_forward();
        }
        result.ok()*/

    }
}

pub open spec fn page_size_spec(level: PagingLevel) -> usize {
    PAGE_SIZE() << (nr_subpage_per_huge::<PagingConsts>().ilog2() * (level - 1))
}

/// The page size at a given level.
#[verifier::when_used_as_spec(page_size_spec)]
#[verifier::external_body]
pub fn page_size(level: PagingLevel) -> usize {
    assert(level as usize > 0) by { admit() };
    PAGE_SIZE() << (nr_subpage_per_huge::<PagingConsts>().ilog2() as usize * (level as usize - 1))
}

pub const fn align_down(x: usize, align: usize) -> (res: usize)
    requires
        align > 0,
    ensures
        res <= x,
        res % align == 0,
{
    let res = x & !(align - 1);
    assert(res <= x) by { admit() };
    assert(res % align == 0) by { admit() };
    res
}

impl<'a, C: PageTableConfig, A: InAtomicMode> Cursor<'a, C, A> {
    /*    #[rustc_allow_incoherent_impl]
    pub open spec fn relate_locked_region(self, model: ConcreteCursor) -> bool
        recommends
            model.inv(),
            self.barrier_va.start < self.barrier_va.end,
    {
        let barrier_lv = NR_LEVELS() - self.guard_level;
        let locked_path = model.tree@.get_path(model.locked_subtree@);
        let barrier_start_path = PageTableTreePathModel::from_va(self.barrier_va.start);
        let barrier_end_path = PageTableTreePathModel::from_va((self.barrier_va.end - 1) as usize);
        barrier_lv == model.locked_subtree@.level && {
            forall|i: int|
                0 <= i < barrier_lv ==> #[trigger] locked_path.index(i)
                    == barrier_start_path@.index(i) && locked_path.index(i)
                    == barrier_end_path@.index(i)
        } && {
            model.locked_subtree@.is_leaf() || barrier_start_path@.index(barrier_lv)
                != barrier_end_path@.index(barrier_lv)
        }
    }
    #[rustc_allow_incoherent_impl]
    pub open spec fn relate(self, model: ConcreteCursor) -> bool
        recommends
            model.inv(),
    {
        &&& self.level == NR_LEVELS() - model.path.len()
        &&& self.va
            == model.path.vaddr()
        //        &&& self.relate_locked_region(model)

    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn inv(self) -> bool {
        &&& 0 < self.level <= self.guard_level
        &&& 0 < self.guard_level <= NR_LEVELS()
        &&& self.barrier_va.start <= self.va < self.barrier_va.end
        &&& self.va % PAGE_SIZE() == 0
        &&& self.va % page_size_at_level::<CONST_NR_LEVELS>(self.level as int) == 0
        &&& self.barrier_va.start < self.barrier_va.end
        &&& self.barrier_va.start % PAGE_SIZE() == 0
        &&& self.barrier_va.end % PAGE_SIZE() == 0
    }

    #[rustc_allow_incoherent_impl]
    pub fn virt_addr(&self, Tracked(model): Tracked<ConcreteCursor>) -> (res: Vaddr)
        requires
            self.inv(),
            self.relate(model),
    {
        self.va
    }

    /// Goes down a level to a child page table.
    #[rustc_allow_incoherent_impl]
    fn push_level(&mut self, node: PageTableNode<C>, Tracked(model): Tracked<&ConcreteCursor>)
        requires
            old(self).inv(),
            1 < old(self).level <= NR_LEVELS(),
            model.inv(),
            old(self).relate(*model),
        ensures
            self.level == old(self).level - 1,
            self.relate(model.push_level_spec()),
    {
        self.level = self.level - 1;
        //        assert(self.level == NR_LEVELS() - model.push_level_spec().path.inner.len());
        assert(self.va == model.push_level_spec().path.vaddr()) by {
            model.lemma_push_level_spec_preserves_vaddr(model.path.inner.len() as int)
        };

        //        self.guards.set((self.level - 1) as usize, Some(node));
    }

    /// Goes up a level.
    ///
    /// We release the current page if it has no mappings since the cursor
    /// only moves forward. And if needed we will do the final cleanup using
    /// this method after re-walk when the cursor is dropped.
    ///
    /// This method requires locks acquired before calling it. The discarded
    /// level will be unlocked.
    #[rustc_allow_incoherent_impl]
    fn pop_level(&mut self, Tracked(model): Tracked<&ConcreteCursor>)
        requires
            old(self).inv(),
            model.inv(),
            old(self).relate(*model),
            old(self).va % page_size_at_level::<CONST_NR_LEVELS>(old(self).level as int + 1) == 0,
            model.path.inner.0[NR_LEVELS() - old(self).level - 1] == 0,
            old(self).level < old(self).guard_level,
        ensures
            self.inv(),
            self.level == old(self).level + 1,
            self.relate(model.pop_level_spec()),
    {
        // TODO: drop page tables if page tables become empty
        assert(model.pop_level_spec().path.vaddr() == model.path.vaddr()) by {
            model.lemma_pop_level_spec_preserves_vaddr(NR_LEVELS() - self.level)
        };

        //        self.guards.set((self.level - 1) as usize, None);
        self.level = self.level + 1;
    }

    /// Traverses forward in the current level to the next PTE.
    ///
    /// If reached the end of a page table node, it leads itself up to the next page of the parent
    /// page if possible.
    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub fn move_forward(&mut self, mut model: Tracked<&ConcreteCursor>)
        requires
            old(self).inv(),
            model@.inv(),
            old(self).relate(*model@),
            old(self).va < old(self).barrier_va.end,
        ensures
            self.relate(model@.move_forward_spec()),
            self.va < self.barrier_va.end,
            self.inv(),
    {
        let ghost initial_model = *model@;

        let size = page_size(self.level);
        let aligned = align_down(self.va, size);
        let next_va = aligned + size;

        while self.level < self.guard_level && pte_index(next_va, self.level) == 0
            invariant
                self.inv(),
                self.relate(*model@),
                model@.inv(),
        {
            let ghost old_level = self.level;
            let ghost old_model = *model@;
            assert(old_model.inv());
            let ghost old_tree = old_model.path.inner;

            self.pop_level(model);
            model = Tracked(&model@.pop_level_spec());
        }

        self.va = next_va;

    }*/

}

} // verus!
