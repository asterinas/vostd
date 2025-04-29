pub mod impls;
pub mod model;
pub mod specs;

use aster_common::prelude::*;

use vstd::prelude::*;
use vstd::arithmetic::power::*;
use vstd::simple_pptr::*;
use vstd::std_specs::range::*;

use vstd_extra::ghost_tree::*;
use vstd_extra::prelude::ArrayPtr;

use model::ConcreteCursor;
use crate::page_table::table::*;
use super::node::model::{NR_ENTRIES, NR_LEVELS, PAGE_SIZE};

use core::ops::Range;
use core::marker::PhantomData;
use core::result::Result;
use core::mem::ManuallyDrop;

verus! {

pub open spec fn page_size_spec(level: PagingLevel) -> usize {
    PAGE_SIZE << (nr_subpage_per_huge::<PagingConsts>().ilog2() * (level - 1))
}

/// The page size at a given level.
#[verifier::when_used_as_spec(page_size_spec)]
#[verifier::external_body]
pub fn page_size(level: PagingLevel) -> usize {
    assert(level as usize > 0) by { admit() };
    PAGE_SIZE << (nr_subpage_per_huge::<PagingConsts>().ilog2() as usize * (level as usize - 1))
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

impl Child {
    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub proof fn from_pte(pte: PageTableEntry, level: u8) -> Self {
        unimplemented!()
    }

    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub open spec fn is_pt(self) -> Option<PageTableNodeValue> {
        unimplemented!()
    }
}

impl<'a, M: PageTableMode> Cursor<'a, M> {
    #[rustc_allow_incoherent_impl]
    pub open spec fn relate_locked_region(self, s: AbstractState, model: ConcreteCursor) -> bool
        recommends
            model.inv(s),
            self.barrier_va.start < self.barrier_va.end,
    {
        let barrier_lv = NR_LEVELS - self.guard_level;
        let locked_path = s.page_table.get_path(model.locked_subtree);
        let barrier_start_path = PageTableTreePathModel::from_va(self.barrier_va.start);
        let barrier_end_path = PageTableTreePathModel::from_va((self.barrier_va.end - 1) as usize);
        barrier_lv == model.locked_subtree@.level && {
            forall|i: int|
                0 <= i < barrier_lv ==> locked_path@.index(i) == barrier_start_path@.index(i)
                    && locked_path@.index(i) == barrier_end_path@.index(i)
        } && {
            model.locked_subtree@.is_leaf() || barrier_start_path@.index(barrier_lv)
                != barrier_end_path@.index(barrier_lv)
        }
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn relate_guards(self, s: AbstractState, model: ConcreteCursor) -> bool
        recommends
            model.inv(s),
    {
        let barrier_lv = NR_LEVELS - self.guard_level;
        let lv = NR_LEVELS - self.level;
        let nodes = s.page_table.get_nodes(model.path);
        forall|i: int|
            0 <= i < nodes.len() ==> { i < barrier_lv ==> #[trigger] self.guards[i].is_none() } && {
                barrier_lv <= i <= lv ==> #[trigger] self.guards[i].is_some()
                    && self.guards[i].unwrap().relate(nodes[i]) && nodes[i].is_locked
            }
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn relate(self, s: AbstractState, model: ConcreteCursor) -> bool
        recommends
            model.inv(s),
    {
        &&& self.level == NR_LEVELS - model.path.len()
        &&& self.va == model.path.vaddr()
        &&& self.relate_locked_region(s, model)
        &&& self.relate_guards(s, model)
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn inv(self) -> bool {
        &&& 0 < self.level <= self.guard_level
        &&& 0 < self.guard_level <= NR_LEVELS
        &&& self.barrier_va.start <= self.va < self.barrier_va.end
        &&& self.va % PAGE_SIZE == 0
        &&& self.va % page_size_at_level::<NR_LEVELS>(self.level as int) == 0
        &&& self.barrier_va.start < self.barrier_va.end
        &&& self.barrier_va.start % PAGE_SIZE == 0
        &&& self.barrier_va.end % PAGE_SIZE == 0
        &&& forall|i: int|
            0 < i <= NR_LEVELS ==> { i == NR_LEVELS - self.guard_level ==> self.guards[i].is_some()
            } && { i != NR_LEVELS - self.guard_level ==> self.guards[i].is_none() }
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn relate_implies_inv(self, s: AbstractState, model: ConcreteCursor)
        requires
            self.inv(),
            self.relate(s, model),
        ensures
            model.inv(s),
    {
        admit();
    }

    #[rustc_allow_incoherent_impl]
    pub fn virt_addr(
        &self,
        Tracked(s): Tracked<AbstractState>,
        Tracked(model): Tracked<ConcreteCursor>,
    ) -> (res: Vaddr)
        requires
            self.inv(),
            self.relate(s, model),
    {
        self.va
    }

    #[rustc_allow_incoherent_impl]
    pub fn preempt_guard(&self) -> &DisabledPreemptGuard {
        &self.preempt_guard
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn cur_entry_spec(&self, s: AbstractState, model: &ConcreteCursor) -> (res: Entry<
        'a,
    >) {
        let node = self.guards[(self.level - 1)].unwrap();
        let idx = pte_index(self.va, self.level);
        let path = PageTableTreePathModel::from_va(self.va);
        let node_model = s.page_table.get_node(path).unwrap();
        let entry = node_model@.value.perms.unwrap().opt_value()[idx as int].value();
        Entry::new(entry, idx, &node)
    }

    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    fn cur_entry(
        &self,
        Tracked(s): Tracked<AbstractState>,
        Tracked(model): Tracked<&ConcreteCursor>,
    ) -> (res: Entry<'a>)
        requires
            self.inv(),
        ensures
            res == self.cur_entry_spec(s, model),
    {
        unimplemented!()
    }

    /// Goes down a level to a child page table.
    #[rustc_allow_incoherent_impl]
    fn push_level(
        &mut self,
        node: PageTableNode,
        Tracked(s): Tracked<AbstractState>,
        Tracked(model): Tracked<&ConcreteCursor>,
    )
        requires
            old(self).inv(),
            1 < old(self).level <= NR_LEVELS,
            model.inv(s),
            old(self).relate(s, *model),
        ensures
            self.level == old(self).level - 1,
    {
        self.level = self.level - 1;
        assert(self.level == NR_LEVELS - model.push_level_spec().path.inner.len());
        assert(self.va == model.push_level_spec().path.vaddr()) by {
            model.lemma_push_level_spec_preserves_vaddr(model.path.inner.len() as int)
        };

        self.guards.set((self.level - 1) as usize, Some(node));

        // 10b/11
        assert(self.relate_guards(s, model.push_level_spec())) by { admit() };
    }

    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub fn faux_pop(model: Tracked<&ConcreteCursor>) -> (res: Tracked<&ConcreteCursor>)
        ensures
            *res@ == (*model@).pop_level_spec(),
    {
        unimplemented!()
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
    fn pop_level(
        &mut self,
        Tracked(s): Tracked<AbstractState>,
        Tracked(model): Tracked<&ConcreteCursor>,
    ) -> (res: Tracked<AbstractState>)
        requires
            old(self).inv(),
            model.inv(s),
            old(self).relate(s, *model),
            old(self).va % page_size_at_level::<CONST_NR_LEVELS>(old(self).level as int + 1) == 0,
            s.page_table.path.dom().contains(pte_index(old(self).va, old(self).level)),
            model.path.inner.0[NR_LEVELS - old(self).level - 1] == 0,
            old(self).level < old(self).guard_level,
            s.get_page(s.page_table.flat[old(self).va].unwrap().pa).ref_count > 0,
            s.invariants(),
        ensures
            self.inv(),
            self.level == old(self).level + 1,
            res@.invariants(),
    {
        // TODO: drop page tables if page tables become empty
        assert(model.pop_level_spec().path.vaddr() == model.path.vaddr()) by {
            model.lemma_pop_level_spec_preserves_vaddr(NR_LEVELS - self.level)
        };

        self.guards.set((self.level - 1) as usize, None);
        self.level = self.level + 1;

        let ghost barrier_lv = NR_LEVELS - self.guard_level;
        let ghost locked_path = s.page_table.tree@.get_path(model.pop_level_spec().locked_subtree@);
        let ghost barrier_start_path = PageTableTreePathModel::from_va(self.barrier_va.start);
        let ghost barrier_end_path = PageTableTreePathModel::from_va(
            (self.barrier_va.end - 1) as usize,
        );

        assert(forall|i: int|
            0 < i && i <= NR_LEVELS ==> i == NR_LEVELS - self.guard_level
                ==> self.guards.view().index(i) is Some) by { admit() };
        assert(forall|i: int|
            !(i == NR_LEVELS - self.guard_level) ==> self.guards.view().index(i) is None) by {
            admit()
        };

        assert(self.relate_guards(s, model.pop_level_spec())) by { admit() };

        Tracked(s)
    }

    /// Traverses forward in the current level to the next PTE.
    ///
    /// If reached the end of a page table node, it leads itself up to the next page of the parent
    /// page if possible.
    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub fn move_forward(
        &mut self,
        Tracked(s): Tracked<AbstractState>,
        mut model: Tracked<&ConcreteCursor>,
        Tracked(state): Tracked<&ConcretePageTableModel>,
    )
        requires
            old(self).inv(),
            model@.inv(s),
            old(self).relate(s, *model@),
            old(self).va < old(self).barrier_va.end,
        ensures
            self.relate(s, model@.move_forward_spec()),
            self.va < self.barrier_va.end,
            self.inv(),
    {
        let ghost initial_model = *model@;

        let size = page_size(self.level);
        assert(size == page_size(self.level)) by { admit() };
        let aligned = align_down(self.va, size);
        let next_va = aligned + size;

        while self.level < self.guard_level && pte_index(next_va, self.level) == 0
            invariant
                self.inv(),
                self.relate(s, *model@),
                model@.inv(s),
        {
            let ghost old_level = self.level;
            let ghost old_model = *model@;
            assert(old_model.inv(s));
            let ghost old_tree = old_model.path.inner;

            self.pop_level(Tracked(s), model);
            assert(self.level == old_level + 1);

            model = Self::faux_pop(model);
            assert((*model@).path.inner == ConcreteCursor::inc_pop_aligned_rec(old_tree));

        }

        self.va = next_va;

        assert(self.va == initial_model.move_forward_spec().path.vaddr());
    }

    /// Jumps to the given virtual address.
    /// If the target address is out of the range, this method will return `Err`.
    ///
    /// # Panics
    ///
    /// This method panics if the address has bad alignment.
    #[rustc_allow_incoherent_impl]
    #[verifier::external_body]
    pub fn jump(
        &mut self,
        va: Vaddr,
        Tracked(s): Tracked<AbstractState>,
        Tracked(model): Tracked<&ConcreteCursor>,
    ) -> (res: Result<(), PageTableError>)
        requires
            old(self).inv(),
            old(self).relate(s, *model),
            model.inv(s),
        ensures
            self.inv(),
    // `jump` is used in `copy_from` but not in `map`, so specification is not needed
    // for  target 12

    {
        unimplemented!()
    }

    #[verifier::external_body]
    #[verifier::returns(proof)]
    #[rustc_allow_incoherent_impl]
    pub proof fn perms_at_path(
        s: Ghost<AbstractState>,
        path: Ghost<TreePath<CONST_NR_ENTRIES>>,
    ) -> (res: Tracked<vstd_extra::array_ptr::PointsTo<PageTableEntry, CONST_NR_ENTRIES>>) {
        unimplemented!()
    }

    // The appropriate level at which to track a range is that at which all of the
    // addresses in the range have distinct paths in the tree (as represented by having
    // distinct ```pte_index``` values.) It suffices to merely compare the ``pte_index```
    // values for the first and last element of the range. If they are unequal than so will be
    // any other pairs of addresses in the range.
    #[rustc_allow_incoherent_impl]
    pub open spec fn range_at_level(va: &Range<Vaddr>, level: u8) -> bool {
        pte_index(va.start, level) < pte_index((va.end - 1) as usize, level)
    }

    /// Creates a cursor claiming the read access for the given range.
    ///
    /// The cursor created will only be able to query or jump within the given
    /// range. Out-of-bound accesses will result in panics or errors as return values,
    /// depending on the access method.
    ///
    /// Note that this function does not ensure exclusive access to the claimed
    /// virtual address range. The accesses using this cursor may block or fail.
    #[rustc_allow_incoherent_impl]
    pub fn new(pt: &'a PageTable<M>, va: &Range<Vaddr>, Tracked(s): Tracked<AbstractState>) -> (res:
        (Result<(Self, Ghost<ConcreteCursor>), PageTableError>, Tracked<AbstractState>))
        requires
            pt.root.paddr() == s.page_table.tree@.root.value.paddr,
            0 <= va.start <= va.end,
            s.page_table.flat.dom().contains(va.start),
            s.invariants(),
        ensures
            res.1@.invariants(),
    {
        if !M::covers(va) || (va.end <= va.start) {
            return (Err(PageTableError::InvalidVaddrRange(va.start, va.end)), Tracked(s));
        }
        if va.start % PagingConsts::BASE_PAGE_SIZE() != 0 || va.end % PagingConsts::BASE_PAGE_SIZE()
            != 0 {
            return (Err(PageTableError::UnalignedVaddr), Tracked(s));
        }
        let mut cursor = Self {
            guards: [None, None, None, None],
            level: NR_LEVELS as u8,
            guard_level: NR_LEVELS as u8,
            va: va.start,
            barrier_va: Range { start: va.start, end: va.end },
            preempt_guard: disable_preempt(),
            phantom: PhantomData,
        };

        let mut cur_pt_addr = pt.root.paddr();
        let ghost mut cur_path = Ghost(PageTableTreePathModel::from_path(TreePath(Seq::empty())));
        assert(s.page_table.get_node(cur_path@).unwrap()@ == s.page_table.tree@.root) by {
            s.page_table.get_node_empty_is_root(cur_path@)
        }

        assert(s.page_table.tree@.on_tree(s.page_table.tree@.root));
        assert(s.is_node(cur_pt_addr));

        // Go down and get proper locks. The cursor should hold a lock of a
        // page table node containing the virtual address range.
        //
        // While going down, previous guards of too-high levels will be released.
        loop
            invariant_except_break
                0 < va.end,
                0 < cursor.level <= NR_LEVELS,
                cursor.barrier_va == va,
                cursor.level == NR_LEVELS - cur_path@.len(),
                s.page_table.get_node(cur_path@).unwrap()@.value.paddr == cur_pt_addr,
                cur_pt_addr % PAGE_SIZE_SPEC() == 0,
                cur_pt_addr < MAX_PADDR_SPEC(),
                s.get_page(cur_pt_addr).usage == PageUsage::PageTable,
            ensures
                0 < va.end,
                0 < cursor.level <= NR_LEVELS,
                cursor.barrier_va == va,
                cursor.level == NR_LEVELS - cur_path@.len(),
                s.page_table.get_node(cur_path@).unwrap()@.value.paddr == cur_pt_addr,
                cur_pt_addr % PAGE_SIZE_SPEC() == 0,
                cur_pt_addr < MAX_PADDR_SPEC(),
                s.get_page(cur_pt_addr).usage == PageUsage::PageTable,
            decreases cursor.level,
        {
            let start_idx = pte_index(va.start, cursor.level);
            assert(start_idx < 512) by { admit() };

            let level_too_high = {
                let end_idx = pte_index(va.end - 1, cursor.level);
                cursor.level > 1 && start_idx == end_idx
            };
            if !level_too_high {
                break ;
            }
            // We're recursing down a tree to find the appropriate level at which
            // to begin our cursor, so we should be tracking the pt-as-tree model

            assert(cur_pt_addr < VMALLOC_BASE_VADDR() - LINEAR_MAPPING_BASE_VADDR()) by { admit() };

            let pt_arr_ptr: ArrayPtr<PageTableEntry, CONST_NR_ENTRIES> = ArrayPtr::from_addr(
                paddr_to_vaddr(cur_pt_addr),
            );
            let tracked perms = Self::perms_at_path(Ghost(s), Ghost(cur_path@.inner));

            /* TODO: these should be wellformedness conditions on the tree, found in `s.invariants()` */
            assert(perms@.wf()) by { admit() };
            assert(perms@.pptr().addr == pt_arr_ptr.addr) by { admit() };
            assert(perms@.is_init(start_idx as int)) by { admit() };

            // SAFETY: The pointer and index is valid since the root page table
            // does not short-live it. The child page table node won't be
            // recycled by another thread while we are using it.
            let cur_pte: &PageTableEntry = pt_arr_ptr.borrow_at(Tracked(perms.borrow()), start_idx);

            if cur_pte.is_present() {
                if cur_pte.is_last(cursor.level) {
                    break ;
                } else {
                    proof {
                        cur_path =
                        Ghost(
                            PageTableTreePathModel::from_path(cur_path@.inner.push_tail(start_idx)),
                        );
                        let child = Child::from_pte(*cur_pte, cursor.level);
                        assert(child.is_pt().is_some()) by { admit() };
                        let node = child.is_pt().unwrap();
                        assert(node == s.page_table.get_node(cur_path@).unwrap()@.value) by {
                            admit()
                        };
                        assert(node.paddr == cur_pte.paddr()) by { admit() };
                        assert(node.paddr % PAGE_SIZE_SPEC() == 0) by { admit() };
                        assert(node.paddr < MAX_PADDR_SPEC()) by { admit() };
                        assert(s.get_page(node.paddr).usage == PageUsage::PageTable) by { admit() };
                    }
                    cur_pt_addr = cur_pte.paddr();
                }
            } else {
                break ;
            }

            cursor.level = cursor.level - 1;
        }

        // SAFETY: The address and level corresponds to a child converted into
        // a PTE and we clone it to get a new handle to the node.

        // ABOUT THIS CALL: This was originally `from_raw_parts` followed by `clone_shallow`, but
        // `from_raw_parts` requires that its argument be leaked before being called. I replaced it
        // with this variant that performs both operations together. There may be better approaches.
        let (raw, s1) = RawPageTableNode::from_raw_parts_unleaked(
            cur_pt_addr,
            cursor.level,
            Tracked(s),
        );
        assert(s1@.get_page(cur_pt_addr).ref_count == s.get_page(cur_pt_addr).ref_count + 1);

        assert(raw.paddr() == cur_pt_addr);
        assert(raw.has_valid_paddr());
        assert(s1@.get_page(raw.paddr()).ref_count < u32::MAX) by { admit() };

        let (lock, s2) = raw.lock(s1);

        cursor.guards.set(cursor.level as usize - 1, Some(lock));
        cursor.guard_level = cursor.level;

        let model = Ghost(
            ConcreteCursor {
                locked_subtree: s2@.page_table.get_node(cur_path@).unwrap(),
                path: cur_path@,
            },
        );

        (Ok((cursor, model)), s2)
    }
}

} // verus!
