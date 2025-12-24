//pub mod model;
use vstd::prelude::*;

use vstd::simple_pptr::*;
use vstd::seq::*;
use vstd_extra::ghost_tree::*;
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

pub tracked struct CursorContinuation<'rcu, C: PageTableConfig> {
    pub entry_own: EntryOwner<'rcu, C>,
    pub idx: usize,
    pub level: nat,
    pub tree_level: nat,
    pub children: Seq<Option<OwnerSubtree<'rcu, C>>>,
}

impl<'rcu, C: PageTableConfig> CursorContinuation<'rcu, C> {
    #[verifier::returns(proof)]
    pub proof fn take_child(tracked &mut self, idx: usize) -> (res: OwnerSubtree<'rcu, C>)
        requires
            0 <= idx < old(self).children.len(),
            old(self).children[idx as int] is Some
        ensures
            self.children.len() == old(self).children.len(),
            res == old(self).children[idx as int].unwrap(),
            forall |i:int| 0 <= i < idx ==> self.children[i] == old(self).children[i],
            self.children[idx as int] is None,
            forall |i:int| idx < i < old(self).children.len() ==> self.children[i] == old(self).children[i],
            self.level == old(self).level,
            self.tree_level == old(self).tree_level,
            self.idx == old(self).idx,
            self.entry_own == old(self).entry_own,
    {
        let tracked child = self.children.tracked_remove(idx as int).tracked_unwrap();
        self.children.tracked_insert(idx as int, None);
        child
    }

    #[verifier::returns(proof)]
    pub proof fn put_child(tracked &mut self, idx: usize, tracked child: OwnerSubtree<'rcu, C>)
        requires
            0 <= idx < old(self).children.len(),
            old(self).children[idx as int] is None
        ensures
            self.children.len() == old(self).children.len(),
            forall |i:int| 0 <= i < idx ==> self.children[i] == old(self).children[i],
            self.children[idx as int] == Some(child),
            forall |i:int| idx < i < old(self).children.len() ==> self.children[i] == old(self).children[i],
            self.level == old(self).level,
            self.tree_level == old(self).tree_level,
            self.idx == old(self).idx,
            self.entry_own == old(self).entry_own,
    {
        let _ = self.children.tracked_remove(idx as int);
        self.children.tracked_insert(idx as int, Some(child));
    }

    pub open spec fn make_cont_spec(self, idx: usize) -> (Self, Self)
    {
        let child = Self {
            entry_own: self.children[idx as int].unwrap().value,
            level: (self.level-1) as nat,
            tree_level: (self.tree_level+1) as nat,
            idx: idx,
            children: self.children[idx as int].unwrap().children,
        };
        let cont = Self {
            entry_own: self.entry_own,
            level: self.level,
            tree_level: self.tree_level,
            idx: self.idx,
            children: self.children.update(idx as int, None),
        };
        (child, cont)
    }

    #[verifier::returns(proof)]
    pub axiom fn make_cont(tracked &mut self, idx: usize) -> (res: Self)
        requires
            0 <= idx < NR_ENTRIES(),
        ensures
            res == old(self).make_cont_spec(idx).0,
            self == old(self).make_cont_spec(idx).1;
/*    {
        let child = node.tracked_child(idx).tracked_unwrap();
        let cont = CursorContinuation {
            entry_own: node.value,
            idx: idx,
            level: node.level,
            siblings: node.children.update(idx as int, None),
        };
        (child, cont)
    }*/

    pub open spec fn restore_spec(self, child: Self) -> Self {
        let child_node = OwnerSubtree {
            value: child.entry_own,
            level: child.level,
            children: child.children
        };
        Self {
            children: self.children.update(self.idx as int, Some(child_node)),
            ..self
        }
    }

    pub axiom fn restore(&mut self, child: Self)
        ensures self == old(self).restore_spec(child);
/*    {
        Node {
            value: self.entry_own,
            level: self.level,
            children: self.siblings.update(self.idx as int, Some(child))
        }
    }*/

    pub proof fn cont_property(self, idx: usize)
        requires
            0 <= idx < NR_ENTRIES(),
            self.children[idx as int] is Some,
        ensures
            self.make_cont_spec(idx).1.restore_spec(self.make_cont_spec(idx).0) == self
    {
        admit()
//        assert(self.make_cont_spec(idx).1.restore_spec(self.make_cont_spec(idx).0).children == self.children)
    }

    pub open spec fn prev_views(self) -> Seq<FrameView<C>> {
        self.children.take(self.idx as int).flat_map(
            |child: Option<OwnerSubtree<'rcu, C>>|
                match child {
                    Some(child) => OwnerAsTreeNode::view_rec(child, self.level as int),
                    None => Seq::empty()
            })
    }

    pub open spec fn next_views(self) -> Seq<FrameView<C>> {
        self.children.skip(self.idx as int).flat_map(
            |child: Option<OwnerSubtree<'rcu, C>>|
                match child {
                    Some(child) => OwnerAsTreeNode::view_rec(child, self.level as int),
                    None => Seq::empty()
            })
    }

    pub open spec fn inv(self) -> bool {
        &&& self.children.len() == NR_ENTRIES()
        &&& 0 <= self.idx < NR_ENTRIES()
        &&& forall |i:int| 0 <= i < NR_ENTRIES() ==>
            self.children[i] is Some ==> {
                &&& self.children[i].unwrap().inv()
                &&& self.children[i].unwrap().level == self.tree_level
                &&& self.tree_level == INC_LEVELS() - self.level
                &&& self.children[i].unwrap().value.relate_parent_guard_perm(self.entry_own.node.unwrap().guard_perm)
            }
        &&& self.entry_own.is_node()
        &&& self.entry_own.inv()
    }

    pub open spec fn all_some(self) -> bool {
        forall |i:int| 0 <= i < NR_ENTRIES() ==> self.children[i] is Some
    }
}

#[rustc_has_incoherent_inherent_impls]
pub tracked struct CursorOwner<'rcu, C: PageTableConfig> {
    pub path: TreePath<CONST_NR_ENTRIES>,
//    pub locked_path: TreePath<CONST_NR_ENTRIES>,
//    pub guard_perms: Map<int, PointsTo<PageTableGuard<'rcu, C>>>,
    pub level: PagingLevel,
    pub index: usize,
//    pub guard_level: PagingLevel,
//    pub prefix_nodes: Ghost<Seq<IntermediatePageTableEntryView<C>>>,
    pub continuations: Map<int, CursorContinuation<'rcu, C>>,
}

impl<'rcu, C: PageTableConfig> Inv for CursorOwner<'rcu, C> {
    open spec fn inv(self) -> bool {
        &&& 0 <= self.index < NR_ENTRIES()
        &&& 1 <= self.level <= NR_LEVELS()
        &&& forall |i: int| self.level - 1 <= i <= NR_LEVELS() - 1 ==> self.continuations.contains_key(i)
        &&& forall |i: int| self.level - 1 <= i <= NR_LEVELS() - 1 ==> {
            &&& self.continuations[i].inv()
            &&& self.continuations[i].level == i
        }
        &&& self.continuations[self.level - 1].all_some()
//        &&& self.subtree.inner.value.relate_parent_guard_perm(self.continuations[self.level-1].entry_own.node.unwrap().guard_perm)
/*        &&& 0 <= self.path_prefix.len() + self.locked_path.len() <= 3
        &&& self.prefix_nodes@.len() == self.path_prefix.len()
        &&& self.path_prefix.len() + 1 == self.guard_level
        &&& self.locked_path.len() == self.level - self.guard_level*/
    }
}

impl<'rcu, C: PageTableConfig> CursorOwner<'rcu, C> {
    /// The number of steps it will take to walk through every node of a full
    /// page table at level `level`
    pub open spec fn max_steps_subtree(level: usize) -> usize
        decreases level
    {
        if level <= 1 {
            NR_ENTRIES()
        } else {
            (NR_ENTRIES()*(Self::max_steps_subtree((level-1) as usize) + 1)) as usize // One step to push down a level, then the number for that subtree
        }
    }

    pub open spec fn max_steps_partial(self, level: usize) -> usize
        decreases NR_LEVELS() - level when level <= NR_LEVELS()
    {
        if level == NR_LEVELS() {
            0
        } else {
            let cont = self.continuations[level as int];
            (Self::max_steps_subtree(level)*(NR_ENTRIES() - cont.idx) + self.max_steps_partial((level + 1) as usize)) as usize
        }
    }

    pub open spec fn max_steps(self) -> usize
    {
        self.max_steps_partial((self.level - 1) as usize)
    }

    pub proof fn inv_continuation(self, i: int)
        requires
            self.inv(),
            self.level - 1 <= i <= NR_LEVELS() - 1
        ensures
            self.continuations.contains_key(i),
            self.continuations[i].inv(),
            self.continuations[i].children.len() == NR_ENTRIES(),
    {
        assert(self.continuations.contains_key(i));
//        assert(self.continuations[self.level as int].inv());
    }

    pub open spec fn prev_views_rec(self, i: int) -> Seq<FrameView<C>>
        decreases i when self.level > 0
    {
        if i < self.level {
            Seq::empty()
        } else {
            self.prev_views_rec(i-1).add(self.continuations[i-1].prev_views())
        }
    }

    pub open spec fn next_views_rec(self, i: int) -> Seq<FrameView<C>>
        decreases i when self.level > 0
    {
        if i < self.level {
            Seq::empty()
        } else {
            self.continuations[i-1].next_views().add(self.next_views_rec(i-1))
        }
    }

    pub open spec fn cur_at_level(self, lv: u8) -> Option<EntryOwner<'rcu, C>> {
        if lv > self.level {
            Some(self.continuations[self.level - 2].entry_own)
        } else if lv == self.level && self.continuations[self.level - 1].children[self.index as int] is Some {
            Some(self.continuations[self.level - 1].children[self.index as int].unwrap().value)
        } else {
            None
        }
    }

    pub open spec fn cur_entry_owner(self) -> Option<EntryOwner<'rcu, C>> {
        self.cur_at_level(self.level)
    }

/*    pub open spec fn full_path(self) -> TreePath<CONST_NR_ENTRIES> {
        TreePath(self.path_prefix.0.add(self.locked_path.0))
    }

    #[verifier::returns(proof)]
    pub axiom fn tracked_seek(self) -> Option<OwnerNode<'rcu, C>>
        returns self.locked_subtree.inner.recursive_seek(self.locked_path);

    pub open spec fn vaddr(self) -> Vaddr
    //        recommends
    //            self.inv(),
     {
        vaddr(self.full_path())
    }*/
}

#[rustc_has_incoherent_inherent_impls]
pub tracked struct CursorView<C: PageTableConfig> {
    pub cur_va: usize,
    pub scope: usize,
    pub fore: Seq<FrameView<C>>,
    pub rear: Seq<FrameView<C>>,
}

impl<C: PageTableConfig> Inv for CursorView<C> {
    open spec fn inv(self) -> bool {
        true
    }
}

impl<'rcu, C: PageTableConfig> View for CursorOwner<'rcu, C> {
    type V = CursorView<C>;

    open spec fn view(&self) -> Self::V {
        CursorView {
            cur_va: vaddr(self.path),
            scope: page_size(self.level as u8),
            fore: self.prev_views_rec(NR_LEVELS() as int),
            rear: self.next_views_rec(NR_LEVELS() as int)
        }
    }
}

impl<'rcu, C: PageTableConfig> InvView for CursorOwner<'rcu, C> {
    proof fn view_preserves_inv(self) { }
}

/*impl<'rcu, C: PageTableConfig, A: InAtomicMode> Cursor<'rcu, C, A> {
    pub open spec fn path_entry_wf(self, idx: nat, owner: CursorOwner) -> bool {
        self.path[idx]
    }
}*/

impl<'rcu, C: PageTableConfig, A: InAtomicMode> OwnerOf for Cursor<'rcu, C, A> {
    type Owner = CursorOwner<'rcu, C>;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& self.level == owner.level
        &&& owner.index == self.va % page_size(self.level)
        &&& self.level <= 4 ==> {
            &&& self.path[3] is Some
            &&& owner.continuations.contains_key(3)
            &&& owner.continuations[3].entry_own.node.unwrap().guard_perm.pptr() == self.path[3].unwrap()
        }
        &&& self.level <= 3 ==> {
            &&& self.path[2] is Some
            &&& owner.continuations.contains_key(2)
            &&& owner.continuations[2].entry_own.node.unwrap().guard_perm.pptr() == self.path[2].unwrap()
            &&& owner.continuations[3].entry_own.node.unwrap().guard_perm.addr() == owner.continuations[2].entry_own.guard_addr
        }
        &&& self.level <= 2 ==> {
            &&& self.path[1] is Some
            &&& owner.continuations.contains_key(1)
            &&& owner.continuations[1].entry_own.node.unwrap().guard_perm.pptr() == self.path[1].unwrap()
            &&& owner.continuations[2].entry_own.node.unwrap().guard_perm.addr() == owner.continuations[1].entry_own.guard_addr
        }
        &&& self.level == 1 ==> {
            &&& self.path[0] is Some
            &&& owner.continuations.contains_key(0)
            &&& owner.continuations[0].entry_own.node.unwrap().guard_perm.pptr() == self.path[0].unwrap()
            &&& owner.continuations[1].entry_own.node.unwrap().guard_perm.addr() == owner.continuations[0].entry_own.guard_addr
        }
/*        &&& self.level == owner.path_prefix.len() + owner.locked_path.len() + 1
        &&& 1 <= self.level <= 4
        &&& forall |i:int| 0 <= i < self.level ==> self.path[i] is Some
        &&& owner.locked_subtree.inner.recursive_seek(owner.locked_path).unwrap().value.node.unwrap().guard_perm.addr() ==
                self.path[self.level as usize - 1].unwrap().addr() */
    }
}

impl<'rcu, C: PageTableConfig, A: InAtomicMode> ModelOf for Cursor<'rcu, C, A> { }

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
pub fn page_size(level: PagingLevel) -> usize
    requires 1 <= level <= NR_LEVELS() + 1
    returns page_size_spec(level)
{
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

/// A fragment of a page table that can be taken out of the page table.
#[must_use]
#[rustc_has_incoherent_inherent_impls]
pub enum PageTableFrag<C: PageTableConfig> {
    /// A mapped page table item.
    Mapped { va: Vaddr, item: C::Item },
    /// A sub-tree of a page table that is taken out of the page table.
    ///
    /// The caller is responsible for dropping it after TLB coherence.
    StrayPageTable {
        pt: Frame<PageTablePageMeta<C>>,  // TODO: this was a dyn AnyFrameMeta, but we can't support that...
        va: Vaddr,
        len: usize,
        num_frames: usize,
    },
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
