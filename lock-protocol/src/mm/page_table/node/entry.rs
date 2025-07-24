use vstd::prelude::*;

use core::ops::Deref;

use crate::{
    mm::{
        cursor::spec_helpers::{self, spt_do_not_change_above_level},
        frame::allocator::AllocatorModel,
        meta::AnyFrameMeta,
        nr_subpage_per_huge,
        page_prop::PageProperty,
        page_size,
        vm_space::Token,
        PageTableConfig, PageTableEntryTrait, PagingConstsTrait, PagingLevel,
    },
    sync::rcu::RcuDrop,
    task::DisabledPreemptGuard,
};

use super::{Child, ChildRef, PageTableGuard, PageTableNode, PageTableNodeRef};

use crate::exec;

use crate::spec::sub_pt::{SubPageTable, index_pte_paddr};

verus! {

/// A view of an entry in a page table node.
///
/// It can be borrowed from a node using the [`PageTableLock::entry`] method.
///
/// This is a static reference to an entry in a node that does not account for
/// a dynamic reference count to the child. It can be used to create a owned
/// handle, which is a [`Child`].
pub struct Entry<'a, 'rcu, C: PageTableConfig> {
    /// The page table entry.
    ///
    /// We store the page table entry here to optimize the number of reads from
    /// the node. We cannot hold a `&mut E` reference to the entry because that
    /// other CPUs may modify the memory location for accessed/dirty bits. Such
    /// accesses will violate the aliasing rules of Rust and cause undefined
    /// behaviors.
    pub pte: C::E,
    /// The index of the entry in the node.
    pub idx: usize,
    /// The node that contains the entry.
    pub node: &'a PageTableGuard<'rcu, C>,
    pub phantom: std::marker::PhantomData<C>,
}

impl<'a, 'rcu, C: PageTableConfig> Entry<'a, 'rcu, C> {
    #[verifier::external_body]
    pub(in crate::mm) fn is_none(&self, Tracked(spt): Tracked<&SubPageTable<C>>) -> (res: bool)
        requires
            spt.wf(),
        returns
            self.is_none_spec(spt),
    {
        !self.pte.is_present()
    }

    pub(in crate::mm) open spec fn is_none_spec(&self, spt: &SubPageTable<C>) -> bool {
        &&& !spt.i_ptes.value().contains_key(self.pte.pte_paddr() as int)
        &&& !spt.ptes.value().contains_key(self.pte.pte_paddr() as int)
    }

    /// Gets a reference to the child.
    #[verifier::external_body]
    pub(in crate::mm) fn to_ref(&self, Tracked(spt): Tracked<&SubPageTable<C>>) -> (res: ChildRef<
        'rcu,
        C,
    >)
        requires
            spt.wf(),
            self.pte.pte_paddr() == exec::get_pte_from_addr_spec(
                self.pte.pte_paddr(),
                spt,
            ).pte_addr,
            self.pte.frame_paddr() == exec::get_pte_from_addr_spec(
                self.pte.pte_paddr(),
                spt,
            ).frame_pa,
        ensures
            if (spt.i_ptes.value().contains_key(self.pte.pte_paddr() as int)) {
                match res {
                    ChildRef::PageTable(pt) => {
                        &&& pt.deref().start_paddr() == self.pte.frame_paddr() as usize
                        &&& spt.alloc_model.meta_map.contains_key(pt.deref().start_paddr() as int)
                        &&& spt.alloc_model.meta_map[pt.deref().start_paddr() as int].value().level
                            == self.node.level_spec(&spt.alloc_model) - 1
                    },
                    _ => false,
                }
            } else if (spt.ptes.value().contains_key(self.pte.pte_paddr() as int)) {
                match res {
                    ChildRef::Frame(pa, level, prop) => { pa == self.pte.frame_paddr() as usize },
                    _ => false,
                }
            } else {
                match res {
                    ChildRef::None => true,
                    _ => false,
                }
            },
    {
        // SAFETY: The entry structure represents an existent entry with the
        // right node information.
        // unsafe { Child::ref_from_pte(&self.pte, self.node.level(Tracked(&spt.alloc_model)), self.node.is_tracked(), false) }
        ChildRef::from_pte(&self.pte, self.node.level(Tracked(&spt.alloc_model)), Tracked(spt))
    }

    /// Operates on the mapping properties of the entry.
    ///
    /// It only modifies the properties if the entry is present.
    // TODO: Implement protect
    #[verifier::external_body]
    pub(in crate::mm) fn protect(
        &mut self,
        prot_op: &mut impl FnMut(&mut PageProperty),
        token_op: &mut impl FnMut(&mut Token),
    ) {
        unimplemented!()
    }

    /// Replaces the entry with a new child.
    ///
    /// The old child is returned.
    ///
    /// # Panics
    ///
    /// The method panics if the given child is not compatible with the node.
    /// The compatibility is specified by the [`Child::is_compatible`].
    #[verifier::external_body]
    pub(in crate::mm) fn replace(
        &mut self,
        new_child: Child<C>,
        Tracked(spt): Tracked<&mut SubPageTable<C>>,
    ) -> (res: Child<C>)
        requires
            old(self).node.wf(&old(spt).alloc_model),
            old(spt).wf(),
            old(self).idx < nr_subpage_per_huge::<C>(),
        ensures
            self.node.wf(&old(spt).alloc_model),
            spt.ptes.value().contains_key(self.pte.pte_paddr() as int),
            spt.instance.id() == old(spt).instance.id(),
            spt.wf(),
            spt_do_not_change_above_level(spt, old(spt), self.node.level_spec(&spt.alloc_model)),
            if (old(spt).i_ptes.value().contains_key(self.pte.pte_paddr() as int)) {
                match res {
                    Child::PageTable(pt) => {
                        &&& pt.deref().start_paddr() == old(self).pte.frame_paddr() as usize
                        &&& spt.i_ptes.value().contains_key(old(self).pte.pte_paddr() as int)
                        &&& spt.alloc_model.meta_map.contains_key(pt.deref().paddr() as int)
                        &&& spt.alloc_model.meta_map[pt.deref().paddr() as int].value().level
                            == self.node.level_spec(&spt.alloc_model) - 1
                        &&& spt.alloc_model.meta_map[pt.deref().paddr() as int].pptr()
                            == pt.deref().meta_ptr
                    },
                    _ => false,
                }
            } else if (old(spt).ptes.value().contains_key(self.pte.pte_paddr() as int)) {
                match res {
                    Child::Frame(pa, level, prop) => { pa == self.pte.frame_paddr() as usize },
                    _ => false,
                }
            } else {
                match res {
                    Child::None => true,
                    _ => false,
                }
            },
            match new_child {
                Child::PageTable(pt) => {
                    &&& pt.deref().paddr() == self.pte.frame_paddr() as usize
                    &&& spt.i_ptes.value().contains_key(self.pte.pte_paddr() as int)
                    &&& spt.alloc_model.meta_map.contains_key(pt.deref().paddr() as int)
                    &&& spt.alloc_model.meta_map[pt.deref().paddr() as int].value().level
                        == self.node.level_spec(&spt.alloc_model) - 1
                    &&& spt.alloc_model.meta_map[pt.deref().paddr() as int].pptr()
                        == pt.deref().meta_ptr
                },
                _ => true,
            },
    {
        let old_pte = self.pte.clone();
        let old_child = Child::from_pte(
            old_pte,
            self.node.level(Tracked(&spt.alloc_model)),
            Tracked(spt),
        );

        if old_child.is_none() && !new_child.is_none() {
            // *self.node.nr_children_mut() += 1;
            self.node.change_children(1);
        } else if !old_child.is_none() && new_child.is_none() {
            // *self.node.nr_children_mut() -= 1;
            self.node.change_children(-1);
        }
        self.pte = new_child.into_pte();

        self.node.write_pte(
            self.idx,
            self.pte.clone(),
            self.node.level(Tracked(&spt.alloc_model)),
            Tracked(spt),
        );

        old_child
    }

    #[verifier::external_body]
    pub(in crate::mm) fn alloc_if_none(
        self,
        guard: &'rcu DisabledPreemptGuard,
        Tracked(spt): Tracked<&mut SubPageTable<C>>,
    ) -> (res: Option<PageTableGuard<'rcu, C>>)
        requires
            old(spt).wf(),
            self.idx < nr_subpage_per_huge::<C>(),
        ensures
            spt.wf(),
            spt.instance.id() == old(spt).instance.id(),
            spt_do_not_change_above_level(spt, old(spt), self.node.level_spec(&spt.alloc_model)),
            if old(spt).ptes.value().contains_key(self.pte.pte_paddr() as int) {
                res is None
            } else {
                &&& res is Some
                &&& spt.ptes.value().contains_key(self.pte.pte_paddr() as int)
                &&& spt.frames.value().contains_key(res.unwrap().paddr() as int)
                &&& spt.alloc_model.meta_map.contains_key(res.unwrap().paddr() as int)
                &&& res.unwrap().level_spec(&spt.alloc_model) == self.node.level_spec(
                    &spt.alloc_model,
                ) - 1
            },
    {
        if !self.pte.is_present() {
            // The entry is already present.
            return None;
        }
        let level = self.node.level(Tracked(&spt.alloc_model));
        let (pt, perm) = PageTableNode::<C>::alloc(level - 1, Tracked(&mut spt.alloc_model));

        let pa = pt.start_paddr();

        proof {
            spt.perms.insert(pt.start_paddr(), perm@);
        }
        ;

        self.node.write_pte(
            self.idx,
            Child::<C>::PageTable(RcuDrop::new(pt)).into_pte(),
            level,
            Tracked(spt),
        );

        let node_ref = PageTableNodeRef::borrow_paddr(pa, Tracked(&spt.alloc_model));

        Some(node_ref.make_guard_unchecked(guard))
    }

    /// Create a new entry at the node.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the index is within the bounds of the node.
    // pub(super) unsafe fn new_at(node: &'a mut PageTableLock<C>, idx: usize) -> Self {
    pub fn new_at(
        node: &'a PageTableGuard<'rcu, C>,
        idx: usize,
        Tracked(spt): Tracked<&SubPageTable<C>>,
    ) -> (res: Self)
        requires
            idx < nr_subpage_per_huge::<C>(),
            spt.wf(),
            node.wf(&spt.alloc_model),
        ensures
            res.node == node,
            res.idx == idx,
            res.node.wf(&spt.alloc_model),
            res.pte.pte_paddr() == index_pte_paddr(node.paddr() as int, idx as int),
            res.pte.pte_paddr() == exec::get_pte_from_addr_spec(res.pte.pte_paddr(), spt).pte_addr,
            res.pte.frame_paddr() == exec::get_pte_from_addr_spec(
                res.pte.pte_paddr(),
                spt,
            ).frame_pa,
            res.pte.frame_paddr() == 0 ==> !spt.i_ptes.value().contains_key(
                res.pte.pte_paddr() as int,
            ),
            res.pte.frame_paddr() != 0 ==> {
                &&& spt.i_ptes.value().contains_key(res.pte.pte_paddr() as int)
                &&& spt.i_ptes.value()[res.pte.pte_paddr() as int].frame_pa
                    == res.pte.frame_paddr() as int
                &&& spt.frames.value().contains_key(res.pte.frame_paddr() as int)
            },
    {
        // SAFETY: The index is within the bound.
        // let pte = unsafe { node.read_pte(idx) };
        let pte = node.read_pte(idx, Tracked(spt));

        // FIXME: Fix them by revise the correspondance between PTE state and SPT.
        assume(pte.frame_paddr() == 0 ==> !spt.i_ptes.value().contains_key(pte.pte_paddr() as int));
        assume(pte.frame_paddr() != 0 ==> {
            &&& spt.i_ptes.value().contains_key(pte.pte_paddr() as int)
            &&& spt.i_ptes.value()[pte.pte_paddr() as int].frame_pa == pte.frame_paddr() as int
            &&& spt.frames.value().contains_key(pte.frame_paddr() as int)
        });

        Self { pte, idx, node, phantom: std::marker::PhantomData }
    }
}

} // verus!
