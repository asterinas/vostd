pub mod model;

use aster_common::x86_64::PagingConsts;
use aster_common::prelude::*;
use aster_common::page_table::*;
use aster_common::task::{disable_preempt, DisabledPreemptGuard};

use vstd::prelude::*;
use vstd::arithmetic::power::*;
use vstd::simple_pptr::*;

use vstd_extra::ghost_tree::*;
use vstd_extra::prelude::ArrayPtr;

use model::ConcreteCursor;

use core::ops::Range;
use core::marker::PhantomData;
use core::result::Result;
use core::mem::ManuallyDrop;

verus! {

// Turns a 1-based counter (i.e., level) into a 0-based array index
pub open spec fn to_index(n: int) -> int
    recommends
        n > 0,
{
    n - 1
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

impl<'a, M: PageTableMode> Cursor<'a, M> {
    #[rustc_allow_incoherent_impl]
    pub open spec fn relate_locked_region(self, s: AbstractState, model: ConcreteCursor) -> bool
        recommends
            model.inv(s),
            self.barrier_va.start < self.barrier_va.end,
    {
        let barrier_lv = NR_LEVELS() - self.guard_level;
        let locked_path = s.page_table.tree@.get_path(model.locked_subtree@);
        let barrier_start_path = PageTableTreePathModel::from_va(self.barrier_va.start);
        let barrier_end_path = PageTableTreePathModel::from_va((self.barrier_va.end - 1) as usize);
        barrier_lv == model.locked_subtree@.level && {
            forall|i: int|
                0 <= i < barrier_lv ==> locked_path.index(i) == barrier_start_path@.index(i)
                    && #[trigger] locked_path.index(i) == barrier_end_path@.index(i)
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
        let nodes = s.page_table.get_nodes(model.path);
        // Everything between the barrier level and the current level should be locked
        // Nothing else should be (by us) but could be locked by other cursors
        (nodes.len() >= NR_LEVELS() - self.level + 1) && (forall|i: int|
            0 < i < self.level ==> self.guards[#[trigger] to_index(i)].is_none()) && (forall|i: int|

            self.level <= i <= self.guard_level ==> self.guards[#[trigger] to_index(i)].is_some()
                && self.guards[to_index(i)].unwrap().relate(nodes[NR_LEVELS() - i])
                && nodes[NR_LEVELS() - i].is_locked) && (forall|i: int|
            self.guard_level < i <= NR_LEVELS() ==> self.guards[#[trigger] to_index(i)].is_none())
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn relate(self, s: AbstractState, model: ConcreteCursor) -> bool
        recommends
            model.inv(s),
    {
        &&& self.level == NR_LEVELS() - model.path.len()
        &&& self.va == model.path.vaddr()
        &&& self.relate_locked_region(s, model)
        &&& self.relate_guards(s, model)
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn inv(self) -> bool {
        &&& 0 < self.level <= self.guard_level
        &&& self.guard_level < NR_LEVELS()
        &&& self.barrier_va.start <= self.va < self.barrier_va.end
        &&& self.va % PAGE_SIZE() == 0
        &&& self.va % page_size_at_level::<CONST_NR_LEVELS>(self.level as int) == 0
        &&& self.barrier_va.start < self.barrier_va.end
        &&& self.barrier_va.start % PAGE_SIZE() == 0
        &&& self.barrier_va.end % PAGE_SIZE() == 0
    }

    #[rustc_allow_incoherent_impl]
    pub fn virt_addr(
        &self,
        Ghost(s): Ghost<AbstractState>,
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
    pub proof fn lemma_push_level_nodes_match(self, s: AbstractState, model: &ConcreteCursor)
        requires
            s.page_table.inv(),
            model.path.len() > 0,
            model.inv(s),
        ensures
            forall|i: int|
                0 <= i <= model.path.len() ==> s.page_table.get_nodes(
                    model.push_level_spec().path,
                )[i] == #[trigger] s.page_table.get_nodes(model.path)[i],
    {
        let n = model.path.len() as int;
        model.lemma_push_level_spec_extends(s);
        assert(model.path@.inv());
        model.path@.push_tail_preserves_inv(0);
        s.page_table.tree@.lemma_trace_up_to(model.path@, model.push_level_spec().path@, n);
    }

    /// Goes down a level to a child page table.
    #[rustc_allow_incoherent_impl]
    fn push_level(
        &mut self,
        node: PageTableNode,
        Ghost(s): Ghost<AbstractState>,
        Tracked(model): Tracked<&ConcreteCursor>,
    )
        requires
            old(self).inv(),
            1 < old(self).level,
            model.inv(s),
            s.page_table.inv(),
            old(self).relate(s, *model),
            s.page_table.get_node(model.path).is_some(),  //this implies a lot of things
            s.page_table.get_node(model.path).unwrap()@.children[0] is Some,
            node.relate(s.page_table.get_node(model.path).unwrap()@.children[0].unwrap().value),
            s.page_table.get_node(model.path).unwrap()@.children[0].unwrap().value.is_locked,
        ensures
            self.level == old(self).level - 1,
            self.relate(s, model.push_level_spec()),
    {
        assert(self.va == model.push_level_spec().path.vaddr()) by {
            model.lemma_push_level_spec_preserves_vaddr(model.path.inner.len() as int)
        };

        let ghost old_nodes = s.page_table.get_nodes(model.path);
        assert(old_nodes.len() == model.path.len() + 1);

        let ghost nodes = s.page_table.get_nodes(model.push_level_spec().path);
        assert(nodes.len() == model.path.len() + 2) by {
            s.page_table.tree@.lemma_seek_trace_next(model.path@, 0)
        }

        assert(forall|i: int|
            NR_LEVELS() - self.guard_level <= i <= NR_LEVELS() - self.level ==> nodes[i]
                == old_nodes[i]) by { self.lemma_push_level_nodes_match(s, model) };

        assert(forall|i: int|
            NR_LEVELS() - self.guard_level <= i <= NR_LEVELS() - self.level
                ==> self.guards@[to_index(NR_LEVELS() - i)].unwrap().relate(old_nodes[i]));

        assert(nodes[NR_LEVELS() - self.level + 1] == s.page_table.get_node(
            model.path,
        ).unwrap()@.children[0].unwrap().value) by {
            s.page_table.tree@.lemma_seek_trace_next(model.path@, 0);
        };

        self.level = self.level - 1;
        self.guards.set((self.level - 1) as usize, Some(node));

        assert(forall|i: int|
            NR_LEVELS() - self.guard_level <= i <= NR_LEVELS() - self.level - 1
                ==> self.guards@[to_index(NR_LEVELS() - i)].unwrap().relate(nodes[i]));
        assert(node.relate(nodes[NR_LEVELS() - self.level]));

        assert(self.guards@[to_index(self.level as int)] == Some(node));
        assert(self.guards@[to_index(self.level as int)].unwrap().relate(
            nodes[NR_LEVELS() - self.level],
        ));

    }

    #[rustc_allow_incoherent_impl]
    pub proof fn lemma_pop_level_nodes_match(self, s: AbstractState, model: &ConcreteCursor)
        requires
            s.page_table.inv(),
            model.path.len() > 0,
            model.inv(s),
        ensures
            forall|i: int|
                0 <= i <= model.pop_level_spec().path.len() ==> s.page_table.get_nodes(
                    model.pop_level_spec().path,
                )[i] == #[trigger] s.page_table.get_nodes(model.path)[i],
    {
        let n = model.pop_level_spec().path.len() as int;
        model.lemma_pop_level_spec_prepends(s);
        assert(model.path@.inv());
        model.path@.pop_tail_preserves_inv();
        s.page_table.tree@.lemma_trace_up_to(model.path@, model.pop_level_spec().path@, n);
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
    )
        requires
            old(self).inv(),
            model.inv(s),
            s.page_table.inv(),
            old(self).relate(s, *model),
            old(self).va % page_size_at_level::<CONST_NR_LEVELS>(old(self).level as int + 1) == 0,
            model.path@.0[NR_LEVELS() - old(self).level - 1] == 0,
            old(self).level < old(self).guard_level,
        ensures
            self.inv(),
            self.level == old(self).level + 1,
            self.relate(s, model.pop_level_spec()),
    {
        assert(model.pop_level_spec().path.vaddr() == model.path.vaddr()) by {
            model.lemma_pop_level_spec_preserves_vaddr(NR_LEVELS() - self.level)
        };

        let ghost old_nodes = s.page_table.get_nodes(model.path);
        let ghost nodes = s.page_table.get_nodes(model.pop_level_spec().path);

        assert(old_nodes.len() == NR_LEVELS() - self.level + 1);
        assert(model.pop_level_spec().path.len() == NR_LEVELS() - self.level - 1) by {
            model.lemma_pop_level_spec_len()
        };
        assert(model.pop_level_spec().path.inv()) by { model.path@.pop_tail_preserves_inv() }

        assert(nodes.len() == old_nodes.len() - 1) by {
            assert(nodes.len() <= model.path.len()) by {
                s.page_table.tree@.lemma_trace_length(model.pop_level_spec().path@)
            };
            assert(model.path@.len() == NR_LEVELS() - self.level);
            s.page_table.tree@.lemma_trace_up_to(
                model.path@,
                model.pop_level_spec().path@,
                NR_LEVELS() - self.level - 1,
            );
            assert(nodes.len() > NR_LEVELS() - self.level - 1);
        };

        assert(forall|i: int|
            NR_LEVELS() - self.guard_level - 1 <= i <= NR_LEVELS() - self.level - 1 ==> nodes[i]
                == old_nodes[i]) by { self.lemma_pop_level_nodes_match(s, model) };

        assert(forall|i: int|
            NR_LEVELS() - self.guard_level + 1 <= i <= NR_LEVELS() - self.level - 1
                ==> self.guards@[to_index(NR_LEVELS() - i)].unwrap().relate(old_nodes[i]));

        self.guards.set((self.level - 1) as usize, None);
        self.level = self.level + 1;

        assert(forall|i: int|
            NR_LEVELS() - self.guard_level + 1 <= i <= NR_LEVELS() - self.level
                ==> self.guards@[to_index(NR_LEVELS() - i)].unwrap().relate(old_nodes[i]));
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

            model = Tracked(&model@.pop_level_spec());
        }

        self.va = next_va;
    }
}

} // verus!
