use vstd::prelude::*;

use core::ops::Deref;
use std::marker::PhantomData;

use crate::{
    helpers::conversion::usize_mod_is_int_mod,
    mm::{
        frame::{allocator::AllocatorModel, meta::AnyFrameMeta},
        nr_subpage_per_huge,
        page_prop::PageProperty,
        page_size,
        page_table::{
            cursor::spec_helpers::{
                self, alloc_model_do_not_change_except_add_frame, spt_do_not_change_above_level,
                spt_do_not_change_except_frames_change, spt_do_not_change_except_modify_pte,
            },
            PageTableConfig, PageTableEntryTrait,
        },
        vm_space::Token,
        Paddr, PagingConstsTrait, PagingLevel, Vaddr, NR_ENTRIES,
    },
    sync::rcu::RcuDrop,
    task::DisabledPreemptGuard,
};

use super::{
    child::{ChildLocal, ChildRefLocal},
    PageTableGuard, PageTableNode, PageTableNodeRef,
};

use crate::exec;

use crate::spec::sub_pt::{
    SubPageTable, index_pte_paddr, state_machine::IntermediatePageTableEntryView,
};
use crate::spec::sub_pt::level_is_in_range;

verus! {

/// A view of an entry in a page table self.node.
///
/// It can be borrowed from a node using the [`PageTableLock::entry`] method.
///
/// This is a static reference to an entry in a node that does not account for
/// a dynamic reference count to the child. It can be used to create a owned
/// handle, which is a [`Child`].
pub struct EntryLocal<'a, 'rcu, C: PageTableConfig> {
    /// The page table entry.
    ///
    /// We store the page table entry here to optimize the number of reads from
    /// the self.node. We cannot hold a `&mut E` reference to the entry because that
    /// other CPUs may modify the memory location for accessed/dirty bits. Such
    /// accesses will violate the aliasing rules of Rust and cause undefined
    /// behaviors.
    pub pte: C::E,
    /// The index of the entry in the self.node.
    pub idx: usize,
    /// The node that contains the entry.
    pub node: &'a PageTableGuard<'rcu, C>,
    /// The virtual address that the entry maps to.
    pub va: Tracked<Vaddr>,
}

impl<'a, 'rcu, C: PageTableConfig> EntryLocal<'a, 'rcu, C> {
    #[verifier::inline]
    pub open spec fn pte_frame_level(&self, spt: &SubPageTable<C>) -> PagingLevel
        recommends
            spt.alloc_model.meta_map.contains_key(self.pte.frame_paddr() as int),
    {
        spt.alloc_model.meta_map[self.pte.frame_paddr() as int].value().level
    }

    pub open spec fn wf_local(
        &self, 
        spt: &SubPageTable<C>,
    ) -> bool {
        &&& self.node.wf_local(&spt.alloc_model)
        &&& self.idx < nr_subpage_per_huge::<C>()
        &&& self.pte.pte_paddr_spec() == index_pte_paddr(self.node.paddr_local() as int, self.idx as int)
        &&& spt.frames.value().contains_key(self.node.paddr_local() as int)
        &&& self.pte.is_present_spec() <==> {
            ||| spt.i_ptes.value().contains_key(self.pte.pte_paddr_spec() as int)
            ||| spt.ptes.value().contains_key(self.pte.pte_paddr_spec() as int)
        }
        &&& self.idx < NR_ENTRIES
        &&& self.va@ % page_size::<C>(self.node.level_local_spec(&spt.alloc_model))
            == 0
        // TODO: put node related spec to node wf
        &&& self.node.level_local_spec(&spt.alloc_model) <= spt.root@.level
        &&& if (self.node.level_local_spec(&spt.alloc_model) == spt.root@.level) {
            self.node.paddr_local() == spt.root@.pa
        } else {
            self.node.paddr_local() != spt.root@.pa
        }
        &&& spt.frames.value()[self.node.paddr_local() as int].level as int == self.node.level_local_spec(
            &spt.alloc_model,
        )
        &&& self.pte.is_present() ==> {
            &&& spt.alloc_model.meta_map.contains_key(self.pte.frame_paddr() as int)
        }
        &&& self.pte.is_last(self.node.level_local_spec(&spt.alloc_model)) ==> {
            &&& spt.ptes.value().contains_key(self.pte.pte_paddr() as int)
            &&& self.node.level_local_spec(&spt.alloc_model)
                == 1
            // When this is a leaf PTE, the map_to_pa should equal the frame address
            &&& spt.ptes.value()[self.pte.pte_paddr() as int].map_to_pa
                == self.pte.frame_paddr() as int
        }
        &&& spt.alloc_model.meta_map.contains_key(self.pte.frame_paddr() as int) ==> {
            &&& #[trigger] level_is_in_range::<C>(self.pte_frame_level(spt) as int)
        }
        &&& !self.pte.is_last(self.node.level_local_spec(&spt.alloc_model)) && self.pte.is_present()
            <==> {
            &&& #[trigger] spt.i_ptes.value().contains_key(
                #[trigger] self.pte.pte_paddr_spec() as int,
            )
            // When this is an intermediate PTE, the child frame's level should be one less than current node's level
            &&& spt.alloc_model.meta_map.contains_key(self.pte.frame_paddr() as int)
            &&& self.pte_frame_level(spt) == self.node.level_local_spec(&spt.alloc_model) - 1
            &&& spt.frames.value().contains_key(self.pte.frame_paddr() as int)
            &&& spt.frames.value()[self.pte.frame_paddr() as int].ancestor_chain
                == spt.frames.value()[self.node.paddr_local() as int].ancestor_chain.insert(
                self.node.level_local_spec(&spt.alloc_model) as int,
                IntermediatePageTableEntryView {
                    map_va: self.va@ as int,
                    frame_pa: self.node.paddr_local() as int,
                    in_frame_index: self.idx as int,
                    map_to_pa: self.pte.frame_paddr() as int,
                    level: self.node.level_local_spec(&spt.alloc_model),
                    phantom: PhantomData,
                },
            )
        }
    }

    pub(in crate::mm) fn is_none_local(
        &self, 
        Tracked(spt): Tracked<&SubPageTable<C>>,
    ) -> (res: bool)
        requires
            spt.wf(),
            self.wf_local(spt),
        ensures
            res == self.is_none_local_spec(spt),
            res == !self.pte.is_present(),
    {
        !self.pte.is_present()
    }

    pub(in crate::mm) open spec fn is_none_local_spec(&self, spt: &SubPageTable<C>) -> bool {
        &&& !spt.i_ptes.value().contains_key(self.pte.pte_paddr() as int)
        &&& !spt.ptes.value().contains_key(self.pte.pte_paddr() as int)
    }

    /// Gets a reference to the child.
    pub(in crate::mm) fn to_ref_local(
        &self,
        Tracked(spt): Tracked<&SubPageTable<C>>,
    ) -> (res: ChildRefLocal<'rcu, C>)
        requires
            spt.wf(),
            self.wf_local(spt),
        ensures
            res.child_entry_spt_wf(self, spt),
    {
        // SAFETY: The entry structure represents an existent entry with the
        // right node information.
        // unsafe { ChildLocal::ref_from_pte(&self.pte, self.node.level(Tracked(&spt.alloc_model)), self.node.is_tracked(), false) }
        ChildRefLocal::from_pte_local(
            &self.pte,
            self.node.level_local(Tracked(&spt.alloc_model)),
            Tracked(spt),
            &self,
        )
    }

    /// Operates on the mapping properties of the entry.
    ///
    /// It only modifies the properties if the entry is present.
    // TODO: Implement protect
    #[verifier::external_body]
    pub(in crate::mm) fn protect_local(
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
    /// The method panics if the given child is not compatible with the self.node.
    /// The compatibility is specified by the [`ChildLocal::is_compatible`].
    pub(in crate::mm) fn replace_local(
        &mut self,
        new_child: ChildLocal<C>,
        Tracked(spt): Tracked<&mut SubPageTable<C>>,
    ) -> (res: ChildLocal<C>)
        requires
            old(self).wf_local(old(spt)),
            old(self).node.wf_local(&old(spt).alloc_model),
            old(spt).wf(),
            old(self).idx < nr_subpage_per_huge::<C>(),
            old(spt).perms.contains_key(old(self).node.paddr_local()),
        ensures
            self.node.wf_local(&old(spt).alloc_model),
            spt.ptes.value().contains_key(self.pte.pte_paddr() as int),
            spt.instance.id() == old(spt).instance.id(),
            spt.wf(),
            spt_do_not_change_except_modify_pte(spt, old(spt), self.pte.pte_paddr() as int),
            spt.frames == old(spt).frames,
            spt.alloc_model == old(spt).alloc_model,
            self.remove_old_child(res, old(self).pte, old(spt), spt),
            self.add_new_child(new_child, spt),
    {
        let old_pte = self.pte.clone_pte();
        let old_child = ChildLocal::from_pte_local(
            old_pte,
            self.node.level_local(Tracked(&spt.alloc_model)),
            Tracked(spt),
        );

        if old_child.is_none() && !new_child.is_none() {
            // *node.nr_children_mut() += 1;
            self.node.change_children(1);
        } else if !old_child.is_none() && new_child.is_none() {
            // *node.nr_children_mut() -= 1;
            self.node.change_children(-1);
        }
        self.pte = new_child.into_pte_local();

        assert(spt.perms.contains_key(self.node.paddr_local()));

        // TODO: should be trivial?
        assume(self.pte.pte_paddr_spec() == index_pte_paddr(
            self.node.paddr_local() as int,
            self.idx as int,
        ));
        assume(spt.i_ptes.value().contains_key(self.pte.pte_paddr() as int));
        self.node.write_pte_local(
            self.idx,
            self.pte.clone_pte(),
            self.node.level_local(Tracked(&spt.alloc_model)),
            Tracked(spt),
        );

        // TODO: replaced ptes.
        assume(self.remove_old_child(old_child, old(self).pte, old(spt), spt));
        // TODO: added last level ptes.
        assume(spt.ptes.value().contains_key(self.pte.pte_paddr() as int));
        assume(self.add_new_child(new_child, spt));

        old_child
    }

    pub(in crate::mm) fn replace_with_none_local(
        &mut self,
        new_child: ChildLocal<C>,
        Tracked(spt): Tracked<&mut SubPageTable<C>>,
    ) -> (res: ChildLocal<C>)
        requires
            old(self).wf_local(&old(spt)),
            old(spt).wf(),
            old(self).idx < nr_subpage_per_huge::<C>(),
            old(spt).perms.contains_key(old(self).node.paddr_local()),
            // TODO: we assume it's an i_pte currently
            // old(spt).ptes.value().contains_key(old(self).pte.pte_paddr() as int),
            old(spt).i_ptes.value().contains_key(old(self).pte.pte_paddr() as int),
            new_child is None,
        ensures
            self.node.wf_local(&old(spt).alloc_model),
            // !spt.ptes.value().contains_key(old(self).pte.pte_paddr() as int),
            !spt.i_ptes.value().contains_key(old(self).pte.pte_paddr() as int),
            spt_do_not_change_except_frames_change(spt, old(spt), old(self).pte.pte_paddr() as int),
            self.remove_old_child(res, old(self).pte, old(spt), spt),
            old(spt).alloc_model == spt.alloc_model,
            forall|i: int|
                old(spt).frames.value().contains_key(i) && i != old(spt).i_ptes.value()[old(
                    self,
                ).pte.pte_paddr() as int].map_to_pa ==> {
                    #[trigger] spt.frames.value().contains_key(i) && spt.frames.value()[i] == old(
                        spt,
                    ).frames.value()[i]
                },
    {
        let old_pte = self.pte.clone_pte();
        assert(old_pte.pte_paddr() == self.pte.pte_paddr());
        let old_child = ChildLocal::from_pte_local(
            old_pte,
            self.node.level_local(Tracked(&spt.alloc_model)),
            Tracked(spt),
        );

        if !old_child.is_none() {
            // *node.nr_children_mut() -= 1;
            self.node.change_children(-1);
        }
        self.pte = new_child.into_pte_local();

        self.node.write_pte_local(
            self.idx,
            self.pte.clone_pte(),
            self.node.level_local(Tracked(&spt.alloc_model)),
            Tracked(spt),
        );

        proof {
            assert(spt.i_ptes.value().contains_key(
                index_pte_paddr(self.node.paddr_local() as int, self.idx as int) as int,
            ));
            let child_frame_addr = spt.i_ptes.value()[index_pte_paddr(
                self.node.paddr_local() as int,
                self.idx as int,
            ) as int].map_to_pa;

            assert(spt.frames.value().contains_key(child_frame_addr));
            assert(spt.perms.contains_key(child_frame_addr as usize));

            let child_frame_level = spt.frames.value()[child_frame_addr].level as int;
            // TODO: The child is not an ancestor of any other frame. Where should we enforce this?
            assume(forall|i: int| #[trigger]
                spt.frames.value().contains_key(i) ==> {
                    ||| !spt.frames.value()[i].ancestor_chain.contains_key(child_frame_level)
                    ||| spt.frames.value()[i].ancestor_chain[child_frame_level].frame_pa
                        != child_frame_addr
                });
            spt.instance.remove_at(
                self.node.paddr_local() as int,
                self.idx as int,
                &mut spt.frames,
                &mut spt.i_ptes,
            );
            spt.perms.tracked_remove(child_frame_addr as usize);
            assert(spt.wf());
            assert(!spt.i_ptes.value().contains_key(old(self).pte.pte_paddr() as int));

            assert(spt_do_not_change_except_frames_change(
                spt,
                old(spt),
                old(self).pte.pte_paddr() as int,
            ));
            // TODO: replaced ptes.
            assume(self.remove_old_child(old_child, old(self).pte, old(spt), spt));
        }

        old_child
    }

    #[verifier::inline]
    pub(in crate::mm) open spec fn remove_old_child(
        &self,
        old_child: ChildLocal<C>,
        old_pte: C::E,
        old_spt: &SubPageTable<C>,
        spt: &SubPageTable<C>,
    ) -> (res: bool) {
        if (old_spt.i_ptes.value().contains_key(self.pte.pte_paddr() as int)) {
            match old_child {
                ChildLocal::PageTable(pt) => {
                    &&& pt.deref().start_paddr_local() == old_pte.frame_paddr() as usize
                    &&& spt.i_ptes.value().contains_key(old_pte.pte_paddr() as int)
                    &&& spt.alloc_model.meta_map.contains_key(pt.deref().paddr_local() as int)
                    &&& spt.alloc_model.meta_map[pt.deref().paddr_local() as int].value().level
                        == self.node.level_local_spec(&spt.alloc_model) - 1
                    &&& spt.alloc_model.meta_map[pt.deref().paddr_local() as int].pptr()
                        == pt.deref().meta_ptr_l
                },
                _ => false,
            }
        } else if (old_spt.ptes.value().contains_key(self.pte.pte_paddr() as int)) {
            match old_child {
                ChildLocal::Frame(pa, level, prop) => { pa == self.pte.frame_paddr() as usize },
                _ => false,
            }
        } else {
            match old_child {
                ChildLocal::None => true,
                _ => false,
            }
        }
    }

    pub(in crate::mm) open spec fn add_new_child(
        &self,
        new_child: ChildLocal<C>,
        spt: &SubPageTable<C>,
    ) -> (res: bool) {
        match new_child {
            ChildLocal::PageTable(pt) => {
                &&& pt.deref().paddr_local() == self.pte.frame_paddr() as usize
                &&& spt.i_ptes.value().contains_key(self.pte.pte_paddr() as int)
                &&& spt.alloc_model.meta_map.contains_key(pt.deref().paddr_local() as int)
                &&& spt.alloc_model.meta_map[pt.deref().paddr_local() as int].value().level
                    == self.node.level_local_spec(&spt.alloc_model) - 1
                &&& spt.alloc_model.meta_map[pt.deref().paddr_local() as int].pptr()
                    == pt.deref().meta_ptr_l
            },
            ChildLocal::Frame(pa, level, prop) => {
                &&& spt.ptes.value().contains_key(self.pte.pte_paddr() as int)
                &&& spt.ptes.value()[self.pte.pte_paddr() as int].map_to_pa == pa
                &&& spt.ptes.value()[self.pte.pte_paddr() as int].map_va == self.va@ as int
            },
            _ => true,
        }
    }

    pub(in crate::mm) fn alloc_if_none_local(
        &mut self,
        guard: &'rcu DisabledPreemptGuard,
        Tracked(spt): Tracked<&mut SubPageTable<C>>,
    ) -> (res: Option<PageTableGuard<'rcu, C>>)
        requires
            old(self).wf_local(&old(spt)),
            old(spt).wf(),
            !old(spt).i_ptes.value().contains_key(old(self).pte.pte_paddr() as int),
            !old(spt).ptes.value().contains_key(old(self).pte.pte_paddr() as int),
            old(self).node.level_local_spec(&old(spt).alloc_model) > 1,
            old(self).node.wf_local(&old(spt).alloc_model),
        ensures
            if old(self).pte.is_present() {
                &&& res is None
                &&& spt == old(spt)
                &&& self == old(self)
            } else {
                &&& self.wf_local(spt)
                &&& self.pte.pte_paddr() == old(self).pte.pte_paddr()
                &&& self.node == old(self).node
                &&& self.node.level_local_spec(&spt.alloc_model) == old(self).node.level_local_spec(
                    &old(spt).alloc_model,
                )
                &&& self.idx == old(self).idx
                &&& self.va == old(self).va
                &&& spt.wf()
                &&& res is Some
                &&& spt_do_not_change_except_modify_pte(spt, old(spt), self.pte.pte_paddr() as int)
                &&& spt_do_not_change_above_level(
                    spt,
                    old(spt),
                    self.node.level_local_spec(&spt.alloc_model),
                )
                &&& alloc_model_do_not_change_except_add_frame(spt, old(spt), res.unwrap().paddr_local())
                &&& res.unwrap().wf_local(&spt.alloc_model)
                &&& spt.i_ptes.value().contains_key(self.pte.pte_paddr() as int)
                &&& !old(spt).frames.value().contains_key(res.unwrap().paddr_local() as int)
                &&& spt.frames.value().contains_key(res.unwrap().paddr_local() as int)
                &&& !old(spt).alloc_model.meta_map.contains_key(res.unwrap().paddr_local() as int)
                &&& spt.alloc_model.meta_map.contains_key(res.unwrap().paddr_local() as int)
                &&& res.unwrap().level_local_spec(&spt.alloc_model) == self.node.level_local_spec(
                    &spt.alloc_model,
                ) - 1
                &&& spt.frames.value()[res.unwrap().paddr_local() as int].ancestor_chain
                    == spt.frames.value()[self.node.paddr_local() as int].ancestor_chain.insert(
                    self.node.level_local_spec(&spt.alloc_model) as int,
                    IntermediatePageTableEntryView {
                        map_va: self.va as int,
                        frame_pa: self.node.paddr_local() as int,
                        in_frame_index: self.idx as int,
                        map_to_pa: res.unwrap().paddr_local() as int,
                        level: self.node.level_local_spec(&spt.alloc_model),
                        phantom: PhantomData,
                    },
                )
                &&& res.unwrap().va == self.va
            },
    {
        if self.pte.is_present() {
            return None;
        }
        let level = self.node.level_local(Tracked(&spt.alloc_model));
        let (pt, Tracked(perm)) = PageTableNode::<C>::alloc_local(
            level - 1,
            Tracked(&mut spt.alloc_model),
        );
        assert(perm.mem_contents().is_init());

        assert(!spt.frames.value().contains_key(pt.start_paddr_local() as int));
        assert(spt.frames =~= old(spt).frames);
        assert(forall|pa: Paddr| #[trigger]
            spt.frames.value().contains_key(pa as int) ==> #[trigger] old(
                spt,
            ).alloc_model.meta_map.contains_key(pa as int));
        // TODO: figure out what triggers we should use here.
        assert(forall|pa: Paddr|
            #![auto]
            old(spt).alloc_model.meta_map.contains_key(pa as int)
                ==> spt.alloc_model.meta_map.contains_key(pa as int));
        assert(forall|pa: Paddr| #[trigger]
            spt.frames.value().contains_key(pa as int)
                ==> #[trigger] spt.alloc_model.meta_map.contains_key(pa as int));

        let pa = pt.start_paddr_local();

        assert(spt.alloc_model.meta_map.contains_key(pa as int));

        proof {
            let i_pte = IntermediatePageTableEntryView {
                map_va: self.va@ as int,
                frame_pa: self.node.paddr_local() as int,
                in_frame_index: self.idx as int,
                map_to_pa: pa as int,
                level,
                phantom: PhantomData::<C>,
            };
            assert(i_pte.wf()) by {
                usize_mod_is_int_mod(
                    self.va@,
                    page_size::<C>(self.node.level_local_spec(&spt.alloc_model)),
                    0,
                );
            }
            assert(level <= spt.root@.level);
            assert(self.node.level_local_spec(&spt.alloc_model) == level);
            if (level == spt.root@.level) {
                assert(i_pte.frame_pa == spt.root@.pa);
            } else {
                assert(i_pte.frame_pa != spt.root@.pa);
            }
            assert(spt.frames.value()[self.node.paddr_local() as int].level as int == level as int);
            spt.instance.set_child(i_pte, &mut spt.frames, &mut spt.i_ptes, &spt.ptes);
            spt.perms.tracked_insert(pa, perm);

            // i_pte.entry_pa() == i_pte.pte_paddr_spec(). @see entry_pa
            assert(spt.i_ptes.value().contains_key(self.pte.pte_paddr() as int));
        }

        assert(spt.wf());
        self.node.write_pte_local(
            self.idx,
            ChildLocal::<C>::PageTable(RcuDrop::new(pt)).into_pte_local(),
            level,
            Tracked(spt),
        );
        self.pte.set_present();  // TODO: should be in write_pte?
        self.pte.set_frame_paddr(pa as usize);  // TODO: should be in write_pte?

        assert(spt.alloc_model.meta_map.contains_key(pa as int));
        assert(spt.alloc_model.meta_map.contains_key(self.pte.frame_paddr() as int));

        assert(self.wf_local(spt));
        assert(alloc_model_do_not_change_except_add_frame(spt, old(spt), pa));
        assert(spt_do_not_change_above_level(spt, old(spt), level));
        assert(spt_do_not_change_except_modify_pte(spt, old(spt), self.pte.pte_paddr() as int));

        let node_ref = PageTableNodeRef::borrow_paddr_local(pa, Tracked(&spt.alloc_model));
        assert(node_ref.level_local_spec(&spt.alloc_model) == level - 1);
        Some(node_ref.make_guard_unchecked(guard, Ghost(self.va@)))
    }

    /// Create a new entry at the self.node.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the index is within the bounds of the self.node.
    // pub(super) unsafe fn new_at(node: &'a mut PageTableLock<C>, idx: usize) -> Self {
    #[verifier::external_body]
    pub fn new_at_local(
        node: &'a PageTableGuard<'rcu, C>,
        idx: usize,
        Tracked(spt): Tracked<&SubPageTable<C>>,
    ) -> (res: Self)
        requires
            idx < nr_subpage_per_huge::<C>(),
            spt.wf(),
            node.wf_local(&spt.alloc_model),
        ensures
            res.wf_local(spt),
            res.node == node,
            res.idx == idx,
            res.va == node.va@ + idx * page_size::<C>(node.level_local_spec(&spt.alloc_model)),
    {
        // SAFETY: The index is within the bound.
        // let pte = unsafe { self.node.read_pte(idx) };
        let pte = node.read_pte_local(idx, Tracked(spt));
        let va = Tracked(
            (node.va@ + idx * page_size::<C>(node.level_local_spec(&spt.alloc_model))) as Vaddr,
        );

        Self { pte, idx, node, va }
    }
}

} // verus!
