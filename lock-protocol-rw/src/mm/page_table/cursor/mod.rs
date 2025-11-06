pub mod locking;
pub mod va_range;

use std::mem::ManuallyDrop;
use core::ops::Deref;
use std::ops::Range;

use vstd::invariant;
use vstd::prelude::*;
use vstd::arithmetic::{
    div_mod::{lemma_mod_adds, lemma_mod_multiples_basic},
    power::{pow, lemma_pow_positive},
};
use vstd::seq::axiom_seq_update_different;
use vstd::atomic_with_ghost;
use vstd::bits::*;
use vstd::rwlock::{ReadHandle, WriteHandle};
use vstd::vpanic;
use vstd::pervasive::allow_panic;
use vstd::pervasive::unreached;

use vstd_extra::manually_drop::*;

use common::{
    helpers::align_ext::*,
    mm::{
        Paddr, Vaddr, PagingLevel, MAX_USERSPACE_VADDR, nr_subpage_per_huge, page_size,
        lemma_page_size_spec_properties, lemma_page_size_geometric,
    },
    mm::page_table::{
        PageTableConfig, PagingConstsTrait, pte_index, PageTableError, lemma_addr_aligned_propagate,
    },
    mm::page_prop::PageProperty,
    spec::{common::*, node_helper::self},
    task::DisabledPreemptGuard,
    configs::GLOBAL_CPU_NUM,
};

use crate::mm::page_table::PageTable;
use crate::mm::page_table::node::{
    PageTableNode, PageTableNodeRef, PageTableReadLock, PageTableWriteLock,
    child::{Child, ChildRef},
    entry::Entry,
    rwlock::{PageTablePageRwLock, RwWriteGuard, RwReadGuard},
};
use crate::mm::page_table::cursor::va_range::*;
use crate::spec::{
    rw::{SpecInstance, PteArrayToken, PteArrayState},
    lock_protocol::LockProtocolModel,
};

verus! {

pub enum GuardInPath<'a, C: PageTableConfig> {
    Read(PageTableReadLock<'a, C>),
    Write(PageTableWriteLock<'a, C>),
    ImplicitWrite(PageTableWriteLock<'a, C>),
    Unlocked,
}

impl<'a, C: PageTableConfig> GuardInPath<'a, C> {
    /// Verus does not support replace.
    #[verifier::external_body]
    pub fn take(&mut self) -> (res: GuardInPath<'a, C>)
        ensures
            res =~= *old(self),
            *self is Unlocked,
    {
        core::mem::replace(self, Self::Unlocked)
    }

    /// Verus does not support replace.
    #[verifier::external_body]
    pub fn put_read(&mut self, guard: PageTableReadLock<'a, C>)
        requires
            *old(self) is Unlocked,
        ensures
            *self is Read,
            self->Read_0 =~= guard,
    {
        // core::mem::replace(self, Self::Read(guard))
        unimplemented!()
    }

    /// Verus does not support replace.
    #[verifier::external_body]
    pub fn put_write(&mut self, guard: PageTableWriteLock<'a, C>)
        requires
            *old(self) is Unlocked,
        ensures
            *self is Write,
            self->Write_0 =~= guard,
    {
        // core::mem::replace(self, Self::Write(guard))
        unimplemented!()
    }

    /// Verus does not support replace.
    #[verifier::external_body]
    pub fn put_implicit_write(&mut self, guard: PageTableWriteLock<'a, C>)
        requires
            *old(self) is Unlocked,
        ensures
            *self is ImplicitWrite,
            self->ImplicitWrite_0 =~= guard,
    {
        // core::mem::replace(self, Self::ImplicitWrite(guard))
        unimplemented!()
    }

    /// For convenience.
    #[verifier::external_body]
    pub fn borrow_write(&self) -> (res: &PageTableWriteLock<'a, C>)
        requires
            self is Write || self is ImplicitWrite,
        ensures
            self is Write ==> *res =~= self->Write_0,
            self is ImplicitWrite ==> *res =~= self->ImplicitWrite_0,
    {
        unimplemented!()
    }
}

pub struct Cursor<'a, C: PageTableConfig> {
    pub path: [GuardInPath<'a, C>; MAX_NR_LEVELS],
    pub preempt_guard: &'a DisabledPreemptGuard,
    pub level: PagingLevel,
    pub guard_level: PagingLevel,
    pub va: Vaddr,
    pub barrier_va: Range<Vaddr>,
    pub inst: Tracked<SpecInstance<C>>,
    // Used for `unlock_range`
    pub g_level: Ghost<PagingLevel>,
}

/// The maximum value of `PagingConstsTrait::NR_LEVELS`.
pub const MAX_NR_LEVELS: usize = 5;

// #[derive(Clone, Debug)] // TODO: Implement Debug and Clone for PageTableItem
pub enum PageTableItem<C: PageTableConfig> {
    NotMapped { va: Vaddr, len: usize },
    Mapped { va: Vaddr, page: Paddr, prop: PageProperty },
    StrayPageTable { pt: PageTableNode<C>, va: Vaddr, len: usize },
}

impl<'a, C: PageTableConfig> Cursor<'a, C> {
    pub broadcast group group_cursor_lemmas {
        Cursor::lemma_get_guard_nid_sound,
        Cursor::lemma_change_level_sustain_wf,
        Cursor::lemma_change_va_sustain_wf,
        Cursor::lemma_update_last_guard_sustain_wf,
        Cursor::lemma_take_guard_sound,
        Cursor::lemma_take_guard_sustain_wf,
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.inst@.cpu_num() == GLOBAL_CPU_NUM
        &&& self.guards_in_path_relation()
        &&& self.wf_path()
        &&& self.wf_va()
        &&& self.wf_level()
    }

    pub open spec fn adjacent_guard_is_child(&self, level: PagingLevel) -> bool
        recommends
            self.get_guard_level(level) !is Unlocked,
            self.get_guard_level((level - 1) as PagingLevel) !is Unlocked,
    {
        let nid1 = self.get_guard_nid(level);
        let nid2 = self.get_guard_nid((level - 1) as PagingLevel);
        node_helper::is_child::<C>(nid1, nid2)
    }

    pub open spec fn guards_in_path_relation(&self) -> bool
        recommends
            self.wf_path(),
    {
        &&& forall|level: PagingLevel|
            #![trigger self.adjacent_guard_is_child(level)]
            self.g_level@ < level <= C::NR_LEVELS() ==> self.adjacent_guard_is_child(level)
    }

    proof fn lemma_guards_in_path_relation_rec(&self, max_level: PagingLevel, level: PagingLevel)
        requires
            self.wf(),
            self.g_level@ <= level <= max_level <= C::NR_LEVELS(),
        ensures
            node_helper::in_subtree_range::<C>(
                self.get_guard_nid(max_level),
                self.get_guard_nid(level),
            ),
        decreases max_level - level,
    {
        broadcast use Cursor::group_cursor_lemmas;

        if level == max_level {
            let rt = self.get_guard_nid(max_level);
            assert(node_helper::in_subtree_range::<C>(rt, rt)) by {
                assert(node_helper::valid_nid::<C>(rt));
                node_helper::lemma_sub_tree_size_lower_bound::<C>(rt);
            };
        } else {
            self.lemma_guards_in_path_relation_rec(max_level, (level + 1) as PagingLevel);
            let rt = self.get_guard_nid(max_level);
            let pa = self.get_guard_nid((level + 1) as PagingLevel);
            let ch = self.get_guard_nid(level);
            assert(node_helper::in_subtree::<C>(rt, pa)) by {
                assert(node_helper::in_subtree_range::<C>(rt, pa));
                node_helper::lemma_in_subtree_iff_in_subtree_range::<C>(rt, pa);
            };
            assert(node_helper::is_child::<C>(pa, ch)) by {
                assert(self.adjacent_guard_is_child((level + 1) as PagingLevel));
            };
            node_helper::lemma_in_subtree_is_child_in_subtree::<C>(rt, pa, ch);
            assert(node_helper::in_subtree_range::<C>(rt, ch)) by {
                node_helper::lemma_in_subtree_iff_in_subtree_range::<C>(rt, ch);
            };
        }
    }

    pub proof fn lemma_guards_in_path_relation(&self, max_level: PagingLevel)
        requires
            self.wf(),
            self.g_level@ <= max_level <= C::NR_LEVELS(),
        ensures
            forall|level: PagingLevel|
                #![trigger self.get_guard_level(level)]
                #![trigger self.get_guard_nid(level)]
                self.g_level@ <= level <= max_level ==> node_helper::in_subtree_range::<C>(
                    self.get_guard_nid(max_level),
                    self.get_guard_nid(level),
                ),
    {
        assert forall|level: PagingLevel|
            #![trigger self.get_guard_nid(level)]
            self.g_level@ <= level <= max_level implies {
            node_helper::in_subtree_range::<C>(
                self.get_guard_nid(max_level),
                self.get_guard_nid(level),
            )
        } by {
            self.lemma_guards_in_path_relation_rec(max_level, level);
        }
    }

    pub open spec fn wf_path(&self) -> bool {
        &&& self.path@.len() == MAX_NR_LEVELS
        &&& forall|level: PagingLevel|
            #![trigger self.get_guard_level(level)]
            #![trigger self.get_guard_level_implicit_write(level)]
            #![trigger self.get_guard_level_write(level)]
            #![trigger self.get_guard_level_read(level)]
            #![trigger self.get_guard_nid(level)]
            1 <= level <= C::NR_LEVELS() ==> {
                // Notice that the order is necessary.
                if level < self.g_level@ {
                    self.get_guard_level(level) is Unlocked
                } else if level < self.guard_level {
                    &&& self.get_guard_level(level) is ImplicitWrite
                    &&& self.get_guard_level_implicit_write(level).wf()
                    &&& self.get_guard_level_implicit_write(level).inst_id() == self.inst@.id()
                    &&& level == node_helper::nid_to_level::<C>(
                        self.get_guard_level_implicit_write(level).nid(),
                    )
                    &&& self.get_guard_level_implicit_write(level).guard->Some_0.in_protocol@
                        == true
                    // &&& va_level_to_nid::<C>(self.va, level) == self.get_guard_level_implicit_write(level).nid()

                } else if level == self.guard_level {
                    &&& self.get_guard_level(level) is Write
                    &&& self.get_guard_level_write(level).wf()
                    &&& self.get_guard_level_write(level).inst_id() == self.inst@.id()
                    &&& level == node_helper::nid_to_level::<C>(
                        self.get_guard_level_write(level).nid(),
                    )
                    &&& self.get_guard_level_write(level).guard->Some_0.in_protocol@
                        == false
                    // &&& va_level_to_nid::<C>(self.va, level) == self.get_guard_level_write(level).nid()

                } else {
                    &&& self.get_guard_level(level) is Read
                    &&& self.get_guard_level_read(level).wf()
                    &&& self.get_guard_level_read(level).inst_id() == self.inst@.id()
                    &&& level == node_helper::nid_to_level::<C>(
                        self.get_guard_level_read(level).nid(),
                    )
                    // &&& va_level_to_nid::<C>(self.va, level) == self.get_guard_level_read(level).nid()

                }
            }
    }

    // TODO
    /// Well-formedness of the cursor's virtual address.
    pub open spec fn wf_va(&self) -> bool {
        &&& self.barrier_va.start < self.barrier_va.end
            < MAX_USERSPACE_VADDR
        // We allow the cursor to be at the end of the range.
        &&& self.barrier_va.start <= self.va <= self.barrier_va.end
        &&& self.va % page_size::<C>(1) == 0
    }

    pub open spec fn wf_level(&self) -> bool {
        &&& 1 <= self.level <= self.guard_level <= C::NR_LEVELS() <= MAX_NR_LEVELS
        &&& self.level <= self.g_level@ <= C::NR_LEVELS() + 1
    }

    pub open spec fn wf_init_state(&self, va: Range<Vaddr>) -> bool
        recommends
            va_range_wf::<C>(va),
    {
        &&& self.level == self.guard_level
        &&& self.g_level@ == self.level
        &&& self.va == va.start
        &&& self.barrier_va =~= (va.start..va.end)
        &&& self.level == va_range_get_guard_level::<C>(va)
    }

    pub open spec fn wf_with_lock_protocol_model(&self, m: LockProtocolModel<C>) -> bool {
        &&& m.inst_id() == self.inst@.id()
        &&& if self.g_level@ > self.guard_level {
            &&& m.path().len() == C::NR_LEVELS() + 1 - self.g_level@
            &&& forall|level: PagingLevel|
                #![trigger self.get_guard_level(level)]
                #![trigger self.get_guard_nid(level)]
                self.g_level@ <= level <= C::NR_LEVELS() ==> {
                    &&& self.get_guard_level(level) !is Unlocked
                    &&& self.get_guard_nid(level) == m.path()[C::NR_LEVELS() - level]
                }
        } else {
            &&& m.path().len() == C::NR_LEVELS() + 1 - self.guard_level@
            &&& forall|level: PagingLevel|
                #![trigger self.get_guard_level(level)]
                #![trigger self.get_guard_nid(level)]
                self.guard_level@ <= level <= C::NR_LEVELS() ==> {
                    &&& self.get_guard_level(level) !is Unlocked
                    &&& self.get_guard_nid(level) == m.path()[C::NR_LEVELS() - level]
                }
        }
    }

    pub open spec fn get_guard_level(&self, level: PagingLevel) -> GuardInPath<'a, C> {
        self.path[level - 1]
    }

    pub open spec fn get_guard_level_read(&self, level: PagingLevel) -> PageTableReadLock<'a, C> {
        self.get_guard_level(level)->Read_0
    }

    pub open spec fn get_guard_level_write(&self, level: PagingLevel) -> PageTableWriteLock<'a, C> {
        self.get_guard_level(level)->Write_0
    }

    pub open spec fn get_guard_level_implicit_write(
        &self,
        level: PagingLevel,
    ) -> PageTableWriteLock<'a, C> {
        self.get_guard_level(level)->ImplicitWrite_0
    }

    pub open spec fn get_guard_nid(&self, level: PagingLevel) -> NodeId {
        let guard = self.get_guard_level(level);
        match guard {
            GuardInPath::<'a, C>::Read(inner) => inner.nid(),
            GuardInPath::<'a, C>::Write(inner) => inner.nid(),
            GuardInPath::<'a, C>::ImplicitWrite(inner) => inner.nid(),
            GuardInPath::<'a, C>::Unlocked => arbitrary(),
        }
    }

    pub broadcast proof fn lemma_get_guard_nid_sound(&self, level: PagingLevel)
        requires
            self.wf(),
            self.g_level@ <= level <= C::NR_LEVELS_SPEC(),
        ensures
            node_helper::valid_nid::<C>(#[trigger] self.get_guard_nid(level)),
    {
        assert(self.get_guard_level(level) !is Unlocked);
        match self.get_guard_level(level) {
            GuardInPath::<'a, C>::Read(inner) => {
                assert(inner.wf());
            },
            GuardInPath::<'a, C>::Write(inner) => {
                assert(inner.wf());
            },
            GuardInPath::<'a, C>::ImplicitWrite(inner) => {
                assert(inner.wf());
            },
            GuardInPath::<'a, C>::Unlocked => (),
        };
    }

    pub open spec fn constant_fields_unchanged(&self, old: &Self) -> bool {
        &&& self.guard_level == old.guard_level
        &&& self.barrier_va =~= old.barrier_va
        &&& self.inst =~= old.inst
    }
}

impl<'a, C: PageTableConfig> Cursor<'a, C> {
    pub uninterp spec fn take_guard_spec(self, idx: usize) -> (Self, GuardInPath<'a, C>);

    /// Verus does not support index for &mut.
    #[verifier::external_body]
    pub fn take_guard(&mut self, idx: usize) -> (res: GuardInPath<'a, C>)
        requires
            0 <= idx < C::NR_LEVELS_SPEC(),
        ensures
            *self =~= old(self).take_guard_spec(idx).0,
            res =~= old(self).take_guard_spec(idx).1,
    {
        self.g_level = Ghost((self.g_level@ + 1) as PagingLevel);
        self.path[idx].take()
    }

    // We put the spec of take_guard here.
    #[verifier::external_body]
    pub broadcast proof fn lemma_take_guard_sound(self, idx: usize)
        requires
            0 <= idx < C::NR_LEVELS_SPEC(),
        ensures
            #![trigger self.take_guard_spec(idx)]
            ({
                let pre_cursor = self;
                let post_cursor = self.take_guard_spec(idx).0;
                let guard = self.take_guard_spec(idx).1;

                &&& guard =~= pre_cursor.path@[idx as int]
                &&& post_cursor.constant_fields_unchanged(&pre_cursor)
                &&& post_cursor.path@ =~= pre_cursor.path@.update(idx as int, GuardInPath::Unlocked)
                &&& post_cursor.level == pre_cursor.level
                &&& post_cursor.va == pre_cursor.va
                &&& post_cursor.g_level@ == pre_cursor.g_level@ + 1
            }),
    {
    }

    pub broadcast proof fn lemma_take_guard_sustain_wf(self, idx: usize)
        requires
            self.wf(),
            0 <= idx < C::NR_LEVELS_SPEC(),
            idx == self.g_level@ - 1,
        ensures
            #[trigger] self.take_guard_spec(idx).0.wf(),
    {
        self.lemma_take_guard_sound(idx);

        let pre_cursor = self;
        let post_cursor = self.take_guard_spec(idx).0;
        assert(self.take_guard_spec(idx).0.wf_path()) by {
            // assert(post_cursor.g_level)
            assert forall|level: PagingLevel|
                #![trigger post_cursor.get_guard_level(level)]
                #![trigger post_cursor.get_guard_level_implicit_write(level)]
                #![trigger post_cursor.get_guard_level_write(level)]
                #![trigger post_cursor.get_guard_level_read(level)]
                1 <= level <= C::NR_LEVELS() implies {
                // Notice that the order is necessary.
                if level < post_cursor.g_level@ {
                    post_cursor.get_guard_level(level) is Unlocked
                } else if level < post_cursor.guard_level {
                    &&& post_cursor.get_guard_level(level) is ImplicitWrite
                    &&& post_cursor.get_guard_level_implicit_write(level).wf()
                    &&& post_cursor.get_guard_level_implicit_write(level).inst_id()
                        == post_cursor.inst@.id()
                    &&& level == node_helper::nid_to_level::<C>(
                        post_cursor.get_guard_level_implicit_write(level).nid(),
                    )
                    &&& post_cursor.get_guard_level_implicit_write(level).guard->Some_0.in_protocol@
                        == true
                    // &&& va_level_to_nid::<C>(post_cursor.va, level) == post_cursor.get_guard_level_implicit_write(level).nid()

                } else if level == post_cursor.guard_level {
                    &&& post_cursor.get_guard_level(level) is Write
                    &&& post_cursor.get_guard_level_write(level).wf()
                    &&& post_cursor.get_guard_level_write(level).inst_id() == post_cursor.inst@.id()
                    &&& level == node_helper::nid_to_level::<C>(
                        post_cursor.get_guard_level_write(level).nid(),
                    )
                    &&& post_cursor.get_guard_level_write(level).guard->Some_0.in_protocol@
                        == false
                    // &&& va_level_to_nid::<C>(post_cursor.va, level) == post_cursor.get_guard_level_write(level).nid()

                } else {
                    &&& post_cursor.get_guard_level(level) is Read
                    &&& post_cursor.get_guard_level_read(level).wf()
                    &&& post_cursor.get_guard_level_read(level).inst_id() == post_cursor.inst@.id()
                    &&& level == node_helper::nid_to_level::<C>(
                        post_cursor.get_guard_level_read(level).nid(),
                    )
                    // &&& va_level_to_nid::<C>(post_cursor.va, level) == post_cursor.get_guard_level_read(level).nid()

                }
            } by {
                if level == pre_cursor.g_level@ {
                } else {
                    assert(post_cursor.get_guard_level(level) =~= pre_cursor.get_guard_level(level))
                        by {
                        assert(post_cursor.path@ =~= pre_cursor.path@.update(
                            idx as int,
                            GuardInPath::Unlocked,
                        ));
                        assert(post_cursor.path@[level - 1] =~= pre_cursor.path@[level - 1]) by {
                            axiom_seq_update_different(
                                pre_cursor.path@,
                                level - 1,
                                idx as int,
                                GuardInPath::Unlocked,
                            );
                        };
                    };
                }
            };
        };
        assert(self.take_guard_spec(idx).0.guards_in_path_relation()) by {
            assert forall|level: PagingLevel|
                #![trigger post_cursor.adjacent_guard_is_child(level)]
                post_cursor.g_level@ < level <= C::NR_LEVELS() implies {
                post_cursor.adjacent_guard_is_child(level)
            } by {
                assert(post_cursor.get_guard_level(level) =~= pre_cursor.get_guard_level(level))
                    by {
                    assert(post_cursor.path@ =~= pre_cursor.path@.update(
                        idx as int,
                        GuardInPath::Unlocked,
                    ));
                    assert(post_cursor.path@[level - 1] =~= pre_cursor.path@[level - 1]) by {
                        axiom_seq_update_different(
                            pre_cursor.path@,
                            level - 1,
                            idx as int,
                            GuardInPath::Unlocked,
                        );
                    };
                };
                assert(post_cursor.get_guard_level((level - 1) as PagingLevel)
                    =~= pre_cursor.get_guard_level((level - 1) as PagingLevel)) by {
                    assert(post_cursor.path@ =~= pre_cursor.path@.update(
                        idx as int,
                        GuardInPath::Unlocked,
                    ));
                    assert(post_cursor.path@[level - 2] =~= pre_cursor.path@[level - 2]) by {
                        axiom_seq_update_different(
                            pre_cursor.path@,
                            level - 2,
                            idx as int,
                            GuardInPath::Unlocked,
                        );
                    };
                };
                assert(pre_cursor.adjacent_guard_is_child(level));
            };
        };
    }

    pub uninterp spec fn put_guard_spec(self, idx: usize, guard: GuardInPath<'a, C>) -> Self;

    #[verifier::external_body]
    pub fn put_guard(&mut self, idx: usize, guard: GuardInPath<'a, C>)
        requires
            0 <= idx < C::NR_LEVELS_SPEC(),
        ensures
            *self =~= old(self).put_guard_spec(idx, guard),
    {
        self.g_level = Ghost((self.g_level@ - 1) as PagingLevel);
        match guard {
            GuardInPath::Read(inner) => self.path[idx].put_read(inner),
            GuardInPath::Write(inner) => self.path[idx].put_write(inner),
            GuardInPath::ImplicitWrite(inner) => self.path[idx].put_implicit_write(inner),
            _ => (),
        };
    }

    // We put the spec of put_guard here.
    #[verifier::external_body]
    pub broadcast proof fn lemma_put_guard_sound(self, idx: usize, guard: GuardInPath<'a, C>)
        requires
            0 <= idx < C::NR_LEVELS_SPEC(),
        ensures
            #![trigger self.put_guard_spec(idx, guard)]
            ({
                let pre_cursor = self;
                let post_cursor = self.put_guard_spec(idx, guard);

                &&& post_cursor.path@[idx as int] =~= guard
                &&& post_cursor.constant_fields_unchanged(&pre_cursor)
                &&& post_cursor.path@ =~= pre_cursor.path@.update(idx as int, guard)
                &&& post_cursor.level == pre_cursor.level
                &&& post_cursor.va == pre_cursor.va
                &&& post_cursor.g_level@ == pre_cursor.g_level@ - 1
            }),
    {
    }

    pub broadcast proof fn lemma_put_guard_sustain_wf(self, idx: usize, guard: GuardInPath<'a, C>)
        requires
            self.wf(),
            0 <= idx < C::NR_LEVELS_SPEC(),
            idx == self.g_level@ - 2,
            self.level < self.g_level@ <= self.guard_level,
            guard is ImplicitWrite,
            guard->ImplicitWrite_0.wf(),
            guard->ImplicitWrite_0.inst_id() == self.inst@.id(),
            guard->ImplicitWrite_0.guard->Some_0.in_protocol@ == true,
            guard->ImplicitWrite_0.level_spec() == self.g_level@ - 1,
            node_helper::is_child::<C>(
                self.get_guard_nid(self.g_level@),
                guard->ImplicitWrite_0.nid(),
            ),
        ensures
            #[trigger] self.put_guard_spec(idx, guard).wf(),
    {
        self.lemma_put_guard_sound(idx, guard);

        let pre_cursor = self;
        let post_cursor = self.put_guard_spec(idx, guard);
        assert(self.put_guard_spec(idx, guard).wf_path()) by {
            // assert(post_cursor.g_level)
            assert forall|level: PagingLevel|
                #![trigger post_cursor.get_guard_level(level)]
                #![trigger post_cursor.get_guard_level_implicit_write(level)]
                #![trigger post_cursor.get_guard_level_write(level)]
                #![trigger post_cursor.get_guard_level_read(level)]
                1 <= level <= C::NR_LEVELS() implies {
                // Notice that the order is necessary.
                if level < post_cursor.g_level@ {
                    post_cursor.get_guard_level(level) is Unlocked
                } else if level < post_cursor.guard_level {
                    &&& post_cursor.get_guard_level(level) is ImplicitWrite
                    &&& post_cursor.get_guard_level_implicit_write(level).wf()
                    &&& post_cursor.get_guard_level_implicit_write(level).inst_id()
                        == post_cursor.inst@.id()
                    &&& level == node_helper::nid_to_level::<C>(
                        post_cursor.get_guard_level_implicit_write(level).nid(),
                    )
                    &&& post_cursor.get_guard_level_implicit_write(level).guard->Some_0.in_protocol@
                        == true
                    // &&& va_level_to_nid::<C>(post_cursor.va, level) == post_cursor.get_guard_level_implicit_write(level).nid()

                } else if level == post_cursor.guard_level {
                    &&& post_cursor.get_guard_level(level) is Write
                    &&& post_cursor.get_guard_level_write(level).wf()
                    &&& post_cursor.get_guard_level_write(level).inst_id() == post_cursor.inst@.id()
                    &&& level == node_helper::nid_to_level::<C>(
                        post_cursor.get_guard_level_write(level).nid(),
                    )
                    &&& post_cursor.get_guard_level_write(level).guard->Some_0.in_protocol@
                        == false
                    // &&& va_level_to_nid::<C>(post_cursor.va, level) == post_cursor.get_guard_level_write(level).nid()

                } else {
                    &&& post_cursor.get_guard_level(level) is Read
                    &&& post_cursor.get_guard_level_read(level).wf()
                    &&& post_cursor.get_guard_level_read(level).inst_id() == post_cursor.inst@.id()
                    &&& level == node_helper::nid_to_level::<C>(
                        post_cursor.get_guard_level_read(level).nid(),
                    )
                    // &&& va_level_to_nid::<C>(post_cursor.va, level) == post_cursor.get_guard_level_read(level).nid()

                }
            } by {
                if level == pre_cursor.g_level@ - 1 {
                    assert(post_cursor.g_level@ == pre_cursor.g_level@ - 1);
                    assert(post_cursor.g_level@ < post_cursor.guard_level);
                    assert(post_cursor.get_guard_level(level) =~= guard);
                    assert(guard is ImplicitWrite);
                } else {
                    assert(post_cursor.get_guard_level(level) =~= pre_cursor.get_guard_level(level))
                        by {
                        assert(post_cursor.path@ =~= pre_cursor.path@.update(idx as int, guard));
                        assert(post_cursor.path@[level - 1] =~= pre_cursor.path@[level - 1]) by {
                            axiom_seq_update_different(
                                pre_cursor.path@,
                                level - 1,
                                idx as int,
                                guard,
                            );
                        };
                    };
                }
            };
        };
        assert(self.put_guard_spec(idx, guard).guards_in_path_relation()) by {
            assert forall|level: PagingLevel|
                #![trigger post_cursor.adjacent_guard_is_child(level)]
                post_cursor.g_level@ < level <= C::NR_LEVELS() implies {
                post_cursor.adjacent_guard_is_child(level)
            } by {
                assert(post_cursor.get_guard_level(level) =~= pre_cursor.get_guard_level(level))
                    by {
                    assert(post_cursor.path@ =~= pre_cursor.path@.update(idx as int, guard));
                    assert(post_cursor.path@[level - 1] =~= pre_cursor.path@[level - 1]) by {
                        axiom_seq_update_different(pre_cursor.path@, level - 1, idx as int, guard);
                    };
                };
                if level == post_cursor.g_level@ + 1 {
                    assert(post_cursor.get_guard_level((level - 1) as PagingLevel) =~= guard);
                    assert(post_cursor.adjacent_guard_is_child(level));
                } else {
                    assert(post_cursor.get_guard_level((level - 1) as PagingLevel)
                        =~= pre_cursor.get_guard_level((level - 1) as PagingLevel)) by {
                        assert(post_cursor.path@ =~= pre_cursor.path@.update(idx as int, guard));
                        assert(post_cursor.path@[level - 2] =~= pre_cursor.path@[level - 2]) by {
                            axiom_seq_update_different(
                                pre_cursor.path@,
                                level - 2,
                                idx as int,
                                guard,
                            );
                        };
                    };
                    assert(pre_cursor.adjacent_guard_is_child(level));
                }
            };
        };
    }
}

impl<'a, C: PageTableConfig> Cursor<'a, C> {
    pub open spec fn change_level_spec(self, new_level: PagingLevel) -> Self {
        Self { level: new_level, ..self }
    }

    pub broadcast proof fn lemma_change_level_sustain_wf(self, new_level: PagingLevel)
        requires
            self.wf(),
            1 <= new_level <= self.guard_level,
            1 <= new_level <= self.g_level@,
        ensures
            #[trigger] self.change_level_spec(new_level).wf(),
    {
        let pre_cursor = self;
        let post_cursor = self.change_level_spec(new_level);
        assert(post_cursor.wf()) by {
            assert(post_cursor.guards_in_path_relation()) by {
                assert forall|level: PagingLevel|
                    #![trigger post_cursor.adjacent_guard_is_child(level)]
                    post_cursor.g_level@ < level <= C::NR_LEVELS() implies {
                    post_cursor.adjacent_guard_is_child(level)
                } by {
                    assert(post_cursor.get_guard_level(level) =~= pre_cursor.get_guard_level(
                        level,
                    ));
                    assert(post_cursor.get_guard_level((level - 1) as PagingLevel)
                        =~= pre_cursor.get_guard_level((level - 1) as PagingLevel));
                    assert(pre_cursor.adjacent_guard_is_child(level));
                };
            };
            assert(post_cursor.wf_path()) by {
                assert forall|level: PagingLevel|
                    #![trigger post_cursor.get_guard_level(level)]
                    #![trigger post_cursor.get_guard_level_implicit_write(level)]
                    #![trigger post_cursor.get_guard_level_write(level)]
                    #![trigger post_cursor.get_guard_level_read(level)]
                    1 <= level <= C::NR_LEVELS() implies {
                    // Notice that the order is necessary.
                    if level < post_cursor.g_level@ {
                        post_cursor.get_guard_level(level) is Unlocked
                    } else if level < post_cursor.guard_level {
                        &&& post_cursor.get_guard_level(level) is ImplicitWrite
                        &&& post_cursor.get_guard_level_implicit_write(level).wf()
                        &&& post_cursor.get_guard_level_implicit_write(level).inst_id()
                            == post_cursor.inst@.id()
                        &&& level == node_helper::nid_to_level::<C>(
                            post_cursor.get_guard_level_implicit_write(level).nid(),
                        )
                        &&& post_cursor.get_guard_level_implicit_write(
                            level,
                        ).guard->Some_0.in_protocol@
                            == true
                        // &&& va_level_to_nid::<C>(post_cursor.va, level) == post_cursor.get_guard_level_implicit_write(level).nid()

                    } else if level == post_cursor.guard_level {
                        &&& post_cursor.get_guard_level(level) is Write
                        &&& post_cursor.get_guard_level_write(level).wf()
                        &&& post_cursor.get_guard_level_write(level).inst_id()
                            == post_cursor.inst@.id()
                        &&& level == node_helper::nid_to_level::<C>(
                            post_cursor.get_guard_level_write(level).nid(),
                        )
                        &&& post_cursor.get_guard_level_write(level).guard->Some_0.in_protocol@
                            == false
                        // &&& va_level_to_nid::<C>(post_cursor.va, level) == post_cursor.get_guard_level_write(level).nid()

                    } else {
                        &&& post_cursor.get_guard_level(level) is Read
                        &&& post_cursor.get_guard_level_read(level).wf()
                        &&& post_cursor.get_guard_level_read(level).inst_id()
                            == post_cursor.inst@.id()
                        &&& level == node_helper::nid_to_level::<C>(
                            post_cursor.get_guard_level_read(level).nid(),
                        )
                        // &&& va_level_to_nid::<C>(post_cursor.va, level) == post_cursor.get_guard_level_read(level).nid()

                    }
                } by {
                    assert(post_cursor.get_guard_level(level) =~= pre_cursor.get_guard_level(
                        level,
                    ));
                };
            };
        };
    }

    pub open spec fn change_va_spec(self, new_va: Vaddr) -> Self {
        Self { va: new_va, ..self }
    }

    pub broadcast proof fn lemma_change_va_sustain_wf(self, new_va: Vaddr)
        requires
            self.wf(),
            self.barrier_va.start <= new_va <= self.barrier_va.end,
            new_va % page_size::<C>(1) == 0,
        ensures
            #[trigger] self.change_va_spec(new_va).wf(),
    {
        let pre = self;
        let post = self.change_va_spec(new_va);

        assert(post.wf()) by {
            assert(post.wf_path()) by {
                assert forall|level: PagingLevel|
                    #![trigger post.get_guard_level(level)]
                    #![trigger post.get_guard_level_implicit_write(level)]
                    #![trigger post.get_guard_level_write(level)]
                    #![trigger post.get_guard_level_read(level)]
                    #![trigger post.get_guard_nid(level)]
                    1 <= level <= C::NR_LEVELS() implies {
                    // Notice that the order is necessary.
                    if level < post.g_level@ {
                        post.get_guard_level(level) is Unlocked
                    } else if level < post.guard_level {
                        &&& post.get_guard_level(level) is ImplicitWrite
                        &&& post.get_guard_level_implicit_write(level).wf()
                        &&& post.get_guard_level_implicit_write(level).inst_id() == post.inst@.id()
                        &&& level == node_helper::nid_to_level::<C>(
                            post.get_guard_level_implicit_write(level).nid(),
                        )
                        &&& post.get_guard_level_implicit_write(level).guard->Some_0.in_protocol@
                            == true
                        // &&& va_level_to_nid::<C>(post.va, level) == post.get_guard_level_implicit_write(level).nid()

                    } else if level == post.guard_level {
                        &&& post.get_guard_level(level) is Write
                        &&& post.get_guard_level_write(level).wf()
                        &&& post.get_guard_level_write(level).inst_id() == post.inst@.id()
                        &&& level == node_helper::nid_to_level::<C>(
                            post.get_guard_level_write(level).nid(),
                        )
                        &&& post.get_guard_level_write(level).guard->Some_0.in_protocol@
                            == false
                        // &&& va_level_to_nid::<C>(post.va, level) == post.get_guard_level_write(level).nid()

                    } else {
                        &&& post.get_guard_level(level) is Read
                        &&& post.get_guard_level_read(level).wf()
                        &&& post.get_guard_level_read(level).inst_id() == post.inst@.id()
                        &&& level == node_helper::nid_to_level::<C>(
                            post.get_guard_level_read(level).nid(),
                        )
                        // &&& va_level_to_nid::<C>(post.va, level) == post.get_guard_level_read(level).nid()

                    }
                } by {
                    if level != post.g_level@ {
                        assert(post.get_guard_level(level) =~= pre.get_guard_level(level));
                    }
                };
            };
            assert(post.guards_in_path_relation()) by {
                assert forall|level: PagingLevel|
                    #![trigger post.adjacent_guard_is_child(level)]
                    post.g_level@ < level <= C::NR_LEVELS() implies {
                    post.adjacent_guard_is_child(level)
                } by {
                    assert(post.get_guard_nid(level) == pre.get_guard_nid(level));
                    assert(post.get_guard_nid((level - 1) as PagingLevel) == pre.get_guard_nid(
                        (level - 1) as PagingLevel,
                    ));
                    assert(pre.adjacent_guard_is_child(level));
                };
            };
        };
    }

    pub open spec fn update_last_guard(
        pre: Self,
        post: Self,
        new_guard: PageTableWriteLock<'a, C>,
    ) -> bool {
        &&& post.constant_fields_unchanged(&pre)
        &&& if post.g_level@ == post.guard_level {
            post.path@ =~= pre.path@.update(post.g_level@ - 1, GuardInPath::Write(new_guard))
        } else {
            post.path@ =~= pre.path@.update(
                post.g_level@ - 1,
                GuardInPath::ImplicitWrite(new_guard),
            )
        }
        &&& post.level == pre.level
        &&& post.va == pre.va
        &&& post.g_level@ == pre.g_level@
    }

    pub broadcast proof fn lemma_update_last_guard_sustain_wf(
        pre: Self,
        post: Self,
        new_guard: PageTableWriteLock<'a, C>,
    )
        requires
            pre.wf(),
            pre.g_level@ <= pre.guard_level,
            #[trigger] Cursor::update_last_guard(pre, post, new_guard),
            new_guard.wf(),
            new_guard.inst_id() == post.inst@.id(),
            new_guard.nid() == pre.get_guard_nid(post.g_level@),
            post.g_level@ == node_helper::nid_to_level::<C>(new_guard.nid()),
            if post.g_level@ == post.guard_level {
                new_guard.guard->Some_0.in_protocol@ == false
            } else {
                new_guard.guard->Some_0.in_protocol@ == true
            },
        ensures
            post.wf(),
    {
        assert(post.wf()) by {
            assert(post.wf_path()) by {
                assert forall|level: PagingLevel|
                    #![trigger post.get_guard_level(level)]
                    #![trigger post.get_guard_level_implicit_write(level)]
                    #![trigger post.get_guard_level_write(level)]
                    #![trigger post.get_guard_level_read(level)]
                    #![trigger post.get_guard_nid(level)]
                    1 <= level <= C::NR_LEVELS() implies {
                    // Notice that the order is necessary.
                    if level < post.g_level@ {
                        post.get_guard_level(level) is Unlocked
                    } else if level < post.guard_level {
                        &&& post.get_guard_level(level) is ImplicitWrite
                        &&& post.get_guard_level_implicit_write(level).wf()
                        &&& post.get_guard_level_implicit_write(level).inst_id() == post.inst@.id()
                        &&& level == node_helper::nid_to_level::<C>(
                            post.get_guard_level_implicit_write(level).nid(),
                        )
                        &&& post.get_guard_level_implicit_write(level).guard->Some_0.in_protocol@
                            == true
                        // &&& va_level_to_nid::<C>(post.va, level) == post.get_guard_level_implicit_write(level).nid()

                    } else if level == post.guard_level {
                        &&& post.get_guard_level(level) is Write
                        &&& post.get_guard_level_write(level).wf()
                        &&& post.get_guard_level_write(level).inst_id() == post.inst@.id()
                        &&& level == node_helper::nid_to_level::<C>(
                            post.get_guard_level_write(level).nid(),
                        )
                        &&& post.get_guard_level_write(level).guard->Some_0.in_protocol@
                            == false
                        // &&& va_level_to_nid::<C>(post.va, level) == post.get_guard_level_write(level).nid()

                    } else {
                        &&& post.get_guard_level(level) is Read
                        &&& post.get_guard_level_read(level).wf()
                        &&& post.get_guard_level_read(level).inst_id() == post.inst@.id()
                        &&& level == node_helper::nid_to_level::<C>(
                            post.get_guard_level_read(level).nid(),
                        )
                        // &&& va_level_to_nid::<C>(post.va, level) == post.get_guard_level_read(level).nid()

                    }
                } by {
                    if level != post.g_level@ {
                        assert(post.get_guard_level(level) =~= pre.get_guard_level(level));
                    }
                };
            };
            assert(post.guards_in_path_relation()) by {
                assert forall|level: PagingLevel|
                    #![trigger post.adjacent_guard_is_child(level)]
                    post.g_level@ < level <= C::NR_LEVELS() implies {
                    post.adjacent_guard_is_child(level)
                } by {
                    assert(post.get_guard_nid(level) == pre.get_guard_nid(level));
                    assert(post.get_guard_nid((level - 1) as PagingLevel) == pre.get_guard_nid(
                        (level - 1) as PagingLevel,
                    )) by {
                        if level == post.g_level@ + 1 {
                            if post.g_level@ == post.guard_level {
                                assert(post.get_guard_level_write((level - 1) as PagingLevel)
                                    =~= new_guard);
                            } else {
                                assert(post.get_guard_level_implicit_write(
                                    (level - 1) as PagingLevel,
                                ) =~= new_guard);
                            }
                        }
                    };
                    assert(pre.adjacent_guard_is_child(level));
                };
            };
        };
    }
}

impl<'a, C: PageTableConfig> Cursor<'a, C> {
    /// Creates a cursor claiming exclusive access over the given range.
    ///
    /// The cursor created will only be able to query or jump within the given
    /// range. Out-of-bound accesses will result in panics or errors as return values,
    /// depending on the access method.
    pub fn new(
        pt: &'a PageTable<C>,
        guard: &'a DisabledPreemptGuard,
        va: &Range<Vaddr>,
        m: Tracked<LockProtocolModel<C>>,
    ) -> (res: (Self, Tracked<LockProtocolModel<C>>))
        requires
            pt.wf(),
            va_range_wf::<C>(*va),
            m@.inv(),
            m@.inst_id() == pt.inst@.id(),
            m@.state() is Void,
        ensures
            res.0.wf(),
            res.1@.inv(),
            res.1@.inst_id() == pt.inst@.id(),
            res.1@.state() is WriteLocked,
            res.1@.path() =~= va_range_get_tree_path::<C>(*va),
    {
        // if !is_valid_range::<C>(va) || va.is_empty() {
        //     assert(false);
        // }
        // if va.start % C::BASE_PAGE_SIZE() != 0 || va.end % C::BASE_PAGE_SIZE() != 0 {
        //     assert(false);
        // }
        // const { assert!(C::NR_LEVELS() as usize <= MAX_NR_LEVELS) };
        let res = locking::lock_range(pt, guard, va, m);
        let cursor = res.0;
        let tracked model = res.1.get();

        (cursor, Tracked(model))
    }

    /// Queries the mapping at the current virtual address.
    ///
    /// If the cursor is pointing to a valid virtual address that is locked,
    /// it will return the virtual address range and the item at that slot.
    pub fn query(&mut self, Tracked(m): Tracked<&LockProtocolModel<C>>) -> (res: Result<
        Option<(Paddr, PagingLevel, PageProperty)>,
        PageTableError,
    >)
        requires
            old(self).wf(),
            old(self).g_level@ == old(self).level,
            m.inv(),
            m.inst_id() == old(self).inst@.id(),
            m.state() is WriteLocked,
            m.sub_tree_rt() =~= old(self).get_guard_nid(old(self).guard_level),
        ensures
            self.wf(),
            self.g_level@ == self.level,
    {
        if self.va >= self.barrier_va.end {
            return Err(PageTableError::InvalidVaddr(self.va));
        }
        let ghost cur_va = self.va;

        let preempt_guard = self.preempt_guard;

        loop
            invariant
                self.wf(),
                self.constant_fields_unchanged(old(self)),
                self.g_level@ == self.level,
                cur_va == self.va == old(self).va < self.barrier_va.end,
                self.get_guard_level(self.guard_level) =~= old(self).get_guard_level(
                    self.guard_level,
                ),
                m.inv(),
                m.inst_id() == old(self).inst@.id(),
                m.state() is WriteLocked,
                m.sub_tree_rt() =~= old(self).get_guard_nid(old(self).guard_level),
            decreases self.level,
        {
            let ghost _cursor = *self;

            let level = self.level;
            let ghost cur_level = self.level;

            let cur_entry = self.cur_entry();
            let cur_node = self.path[(self.level - 1) as usize].borrow_write();
            let child = cur_entry.to_ref_write(cur_node);
            match child {
                ChildRef::PageTable(pt) => {
                    let ghost nid = pt.nid@;
                    assert(nid == node_helper::get_child::<C>(
                        cur_node.nid(),
                        cur_entry.idx as nat,
                    ));
                    assert(m.node_is_locked(cur_node.nid())) by {
                        self.lemma_guards_in_path_relation(self.guard_level);
                        assert(node_helper::in_subtree_range::<C>(
                            self.get_guard_nid(self.guard_level),
                            self.get_guard_nid(self.level),
                        ));
                        node_helper::lemma_in_subtree_iff_in_subtree_range::<C>(
                            m.sub_tree_rt(),
                            cur_node.nid(),
                        );
                    };
                    assert(cur_node.nid() == node_helper::get_parent::<C>(nid)) by {
                        assert(node_helper::is_not_leaf::<C>(cur_node.nid())) by {
                            node_helper::lemma_nid_to_dep_up_bound::<C>(nid);
                            node_helper::lemma_level_dep_relation::<C>(nid);
                            node_helper::lemma_is_child_level_relation::<C>(cur_node.nid(), nid);
                        };
                        node_helper::lemma_get_child_sound::<C>(
                            cur_node.nid(),
                            cur_entry.idx as nat,
                        );
                    };
                    let guard = pt.make_write_guard_unchecked(preempt_guard, Tracked(m));
                    self.push_level(guard);
                    continue ;
                },
                ChildRef::None => return Ok(None),
                ChildRef::Frame(pa, ch_level, prop) => {
                    return Ok(Some((pa, ch_level, prop)));
                },
            };
        }
    }

    /// Traverses forward in the current level to the next PTE.
    ///
    /// If reached the end of a page table node, it leads itself up to the next page of the parent
    /// page if possible.
    pub(in crate::mm) fn move_forward(&mut self)
        requires
            old(self).wf(),
            old(self).g_level@ == old(self).level,
            old(self).va + page_size::<C>(old(self).level) <= old(self).barrier_va.end,
        ensures
            self.wf(),
            self.g_level@ == self.level,
            self.constant_fields_unchanged(old(self)),
            self.va == align_down(old(self).va, page_size::<C>(old(self).level)) + page_size::<C>(
                old(self).level,
            ),
            self.level >= old(self).level,
            forall|level: PagingLevel|
                #![trigger self.get_guard_level(level)]
                self.level <= level <= C::NR_LEVELS_SPEC() ==> self.get_guard_level(level) =~= old(
                    self,
                ).get_guard_level(level),
    {
        broadcast use Cursor::group_cursor_lemmas;

        assert(1 <= self.level <= C::NR_LEVELS());
        let cur_page_size = page_size::<C>(self.level);
        let next_va = align_down(self.va, cur_page_size) + cur_page_size;
        assert(self.barrier_va.start <= next_va <= self.barrier_va.end) by {
            assert(next_va >= self.barrier_va.start);
            assert(next_va <= self.barrier_va.end);
        };
        assert(next_va % page_size::<C>(1) == 0) by {
            assert(next_va % cur_page_size == 0) by {
                assert(align_down(self.va, cur_page_size) % cur_page_size == 0) by {
                    lemma_align_down_basic(self.va, cur_page_size);
                };
                assert(cur_page_size % cur_page_size == 0);
                assert(next_va == align_down(self.va, cur_page_size) + cur_page_size);
                lemma_page_size_spec_properties::<C>(self.level);
                lemma_mod_adds(
                    align_down(self.va, cur_page_size) as int,
                    cur_page_size as int,
                    cur_page_size as int,
                );
            };
            assert(cur_page_size % page_size::<C>(1) == 0) by {
                lemma_page_size_spec_properties::<C>(1);
                lemma_page_size_geometric::<C>(1, self.level);
                assert(page_size::<C>(self.level) as nat == page_size::<C>(1) as nat * pow(
                    nr_subpage_per_huge::<C>() as int,
                    (self.level - 1) as nat,
                ) as nat);
                lemma_mod_multiples_basic(
                    pow(nr_subpage_per_huge::<C>() as int, (self.level - 1) as nat),
                    page_size::<C>(1) as int,
                );
                assert(cur_page_size == page_size::<C>(1) as nat * pow(
                    nr_subpage_per_huge::<C>() as int,
                    (self.level - 1) as nat,
                ) as nat);
                assert((page_size::<C>(1) as nat * pow(
                    nr_subpage_per_huge::<C>() as int,
                    (self.level - 1) as nat,
                ) as nat) % page_size::<C>(1) as nat == 0) by {
                    assert((page_size::<C>(1) * pow(
                        nr_subpage_per_huge::<C>() as int,
                        (self.level - 1) as nat,
                    )) % page_size::<C>(1) as int == 0);
                    assert(pow(nr_subpage_per_huge::<C>() as int, (self.level - 1) as nat) > 0) by {
                        assert(nr_subpage_per_huge::<C>() > 0) by {
                            C::lemma_nr_subpage_per_huge_is_512();
                        };
                        lemma_pow_positive(
                            nr_subpage_per_huge::<C>() as int,
                            (self.level - 1) as nat,
                        );
                    };
                    assert(page_size::<C>(1) >= 0) by {
                        lemma_page_size_spec_properties::<C>(1);
                    };
                    let a = page_size::<C>(1);
                    let b = pow(nr_subpage_per_huge::<C>() as int, (self.level - 1) as nat);
                    admit();  // Trivial but complicated.
                };
            };
            admit();
        };
        assert(self.va < next_va <= self.va + cur_page_size) by {
            let aligned_va = align_down(self.va, cur_page_size) as int;
            lemma_page_size_spec_properties::<C>(self.level);
            assert(0 <= self.va % cur_page_size <= self.va && 0 <= self.va % cur_page_size
                < cur_page_size) by (nonlinear_arith)
                requires
                    self.va >= 0,
                    cur_page_size > 0,
            ;
            assert(aligned_va as int == self.va as int - self.va as int % cur_page_size as int);
            assert(next_va - self.va == cur_page_size - self.va % cur_page_size);
            assert(0 < cur_page_size - self.va % cur_page_size <= cur_page_size);
        }
        assert(next_va % page_size::<C>(self.level) == 0) by (nonlinear_arith)
            requires
                next_va == align_down(self.va, cur_page_size) + cur_page_size,
                cur_page_size == page_size::<C>(self.level),
                align_down(self.va, cur_page_size) % cur_page_size == 0,
        ;
        while self.level < self.guard_level && pte_index::<C>(next_va, self.level) == 0
            invariant
                next_va % page_size::<C>(self.level) == 0,
                self.wf(),
                self.g_level@ == self.level,
                self.constant_fields_unchanged(old(self)),
                self.va == old(self).va,
                self.level >= old(self).level,
                forall|level: PagingLevel|
                    #![trigger self.get_guard_level(level)]
                    self.level <= level <= C::NR_LEVELS_SPEC() ==> self.get_guard_level(level)
                        =~= old(self).get_guard_level(level),
            decreases self.guard_level - self.level,
        {
            let ghost _cursor = *self;
            let res = self.pop_level();
            proof {
                assert(next_va % page_size::<C>((self.level - 1) as u8) == 0);
                assert(pte_index::<C>(next_va, (self.level - 1) as u8) == 0);
                assert(1 <= self.level <= C::NR_LEVELS());
                lemma_addr_aligned_propagate::<C>(next_va, self.level);

                assert forall|level: PagingLevel|
                    #![trigger self.get_guard_level(level)]
                    self.level <= level <= C::NR_LEVELS_SPEC() implies {
                    self.get_guard_level(level) =~= old(self).get_guard_level(level)
                } by {
                    assert(self.get_guard_level(level) =~= _cursor.get_guard_level(level));
                };
            }
        }

        let ghost _cursor = *self;
        assert(_cursor.wf());

        self.va = next_va;

        assert(self.wf()) by {
            assert(*self =~= _cursor.change_va_spec(self.va));
        };
        assert forall|level: PagingLevel|
            #![trigger self.get_guard_level(level)]
            self.level <= level <= C::NR_LEVELS_SPEC() implies {
            self.get_guard_level(level) =~= old(self).get_guard_level(level)
        } by {
            assert(_cursor.get_guard_level(level) =~= old(self).get_guard_level(level));
            assert(self.get_guard_level(level) =~= _cursor.get_guard_level(level));
        };
    }

    pub open spec fn wf_pop_level(self, post: Self) -> bool {
        &&& post.level == self.level + 1
        &&& post.g_level@ == self.g_level@ + 1
        &&& forall|level: PagingLevel|
            #![trigger self.get_guard_level(level)]
            1 <= level <= C::NR_LEVELS_SPEC() && level != self.level ==> {
                self.get_guard_level(level) =~= post.get_guard_level(level)
            }
        &&& self.get_guard_level(self.level) !is Unlocked
        &&& post.get_guard_level(
            self.level,
        ) is Unlocked
        // Other fields remain unchanged.
        &&& self.constant_fields_unchanged(&post)
        &&& self.va == post.va
    }

    /// Goes up a level.
    fn pop_level(&mut self)
        requires
            old(self).wf(),
            old(self).g_level@ == old(self).level,
            old(self).level < old(self).guard_level,
        ensures
            old(self).wf_pop_level(*self),
            self.wf(),
            self.g_level@ == self.level,
    {
        broadcast use Cursor::group_cursor_lemmas;

        proof {
            self.lemma_take_guard_sound((self.level - 1) as usize);
            self.lemma_take_guard_sustain_wf((self.level - 1) as usize);
        }
        self.take_guard((self.level - 1) as usize);

        let ghost _cursor = *self;
        assert(_cursor.wf());

        self.level = self.level + 1;
        assert(self.wf()) by {
            assert(*self =~= _cursor.change_level_spec(self.level));
        };
    }

    pub open spec fn wf_push_level(self, post: Self, child_pt: PageTableWriteLock<'a, C>) -> bool {
        &&& post.level == self.level - 1
        &&& post.g_level@ == self.g_level@ - 1
        &&& forall|level: PagingLevel|
            #![trigger self.get_guard_level(level)]
            1 <= level <= post.guard_level && level != post.level ==> {
                self.get_guard_level(level) =~= post.get_guard_level(level)
            }
        &&& self.get_guard_level(post.level) is Unlocked
        &&& post.get_guard_level(post.level) =~= GuardInPath::ImplicitWrite(
            child_pt,
        )
        // Other fields remain unchanged.
        &&& self.constant_fields_unchanged(&post)
        &&& self.va == post.va
    }

    /// Goes down a level to a child page table.
    fn push_level(&mut self, child_pt: PageTableWriteLock<'a, C>)
        requires
            old(self).wf(),
            old(self).level > 1,
            old(self).g_level@ == old(self).level,
            child_pt.wf(),
            child_pt.inst_id() == old(self).inst@.id(),
            child_pt.guard->Some_0.in_protocol@ == true,
            child_pt.level_spec() == old(self).level - 1,
            node_helper::is_child::<C>(old(self).get_guard_nid(old(self).level), child_pt.nid()),
        ensures
            old(self).wf_push_level(*self, child_pt),
            self.wf(),
            self.g_level@ == self.level,
    {
        broadcast use Cursor::group_cursor_lemmas;

        let ghost _cursor = *self;
        assert(_cursor.wf());

        self.level = self.level - 1;
        assert(self.wf()) by {
            assert(*self =~= _cursor.change_level_spec(self.level));
        };

        let new_guard = GuardInPath::ImplicitWrite(child_pt);
        proof {
            self.lemma_put_guard_sound((self.level - 1) as usize, new_guard);
            self.lemma_put_guard_sustain_wf((self.level - 1) as usize, new_guard);
        }
        self.put_guard((self.level - 1) as usize, new_guard);
    }

    fn cur_entry(&self) -> (res: Entry<C>)
        requires
            self.wf(),
            self.g_level@ == self.level,
        ensures
            self.get_guard_level(self.level) is Write ==> res.wf_write(
                self.get_guard_level_write(self.level),
            ),
            self.get_guard_level(self.level) is ImplicitWrite ==> res.wf_write(
                self.get_guard_level_implicit_write(self.level),
            ),
            res.idx == pte_index::<C>(self.va, self.level),
    {
        assert(self.get_guard_level(self.level) is Write || self.get_guard_level(
            self.level,
        ) is ImplicitWrite);
        let node = self.path[self.level as usize - 1].borrow_write();
        let idx = pte_index::<C>(self.va, self.level);
        Entry::new_at_write(idx, node)
    }
}

pub struct CursorMut<'a, C: PageTableConfig>(pub Cursor<'a, C>);

impl<'a, C: PageTableConfig> CursorMut<'a, C> {
    //     /// Maps the range starting from the current address to an item.
    //     ///
    //     /// It returns the previously mapped item if that exists.
    //     ///
    //     /// Note that the item `C::Item`, when converted to a raw item, if the page property
    //     /// indicate that it is marked metadata, the function is essentially `mark`.
    //     ///
    //     /// # Panics
    //     ///
    //     /// This function will panic if
    //     ///  - the virtual address range to be mapped is out of the range;
    //     ///  - the alignment of the page is not satisfied by the virtual address;
    //     ///  - it is already mapped to a huge page while the caller wants to map a smaller one.
    //     ///
    //     /// # Safety
    //     ///
    //     /// The caller should ensure that the virtual range being mapped does
    //     /// not affect kernel's memory safety.
    #[verifier::spinoff_prover]
    pub fn map(&mut self, item: C::Item, Tracked(m): Tracked<&LockProtocolModel<C>>) -> (res:
        PageTableItem<C>)
        requires
            old(self).0.wf(),
            old(self).0.g_level@ == old(self).0.level,
            C::item_into_raw_spec(item).1 == 1,
            old(self).0.va + page_size::<C>(C::item_into_raw_spec(item).1) <= old(
                self,
            ).0.barrier_va.end,
            m.inv(),
            m.inst_id() == old(self).0.inst@.id(),
            m.state() is WriteLocked,
            m.sub_tree_rt() == old(self).0.get_guard_nid(old(self).0.guard_level),
        ensures
            self.0.wf(),
            self.0.constant_fields_unchanged(&old(self).0),
            self.0.va > old(self).0.va,
    {
        broadcast use Cursor::group_cursor_lemmas;

        let preempt_guard = self.0.preempt_guard;

        let (pa, level, prop) = C::item_into_raw(item);
        assert(level == 1);

        let end = self.0.va + page_size::<C>(level);

        assert(self.0.level >= level);

        // Go down if not applicable.
        while self.0.level != level
            invariant
                old(self).0.wf(),
                self.0.wf(),
                self.0.g_level@ == self.0.level,
                self.0.constant_fields_unchanged(&old(self).0),
                // VA should be unchanged in the loop.
                self.0.va == old(self).0.va,
                self.0.get_guard_nid(self.0.guard_level) =~= old(self).0.get_guard_nid(
                    self.0.guard_level,
                ),
                self.0.level <= old(self).0.level,
                self.0.level >= level && level == 1,
                self.0.va < self.0.barrier_va.end,
                m.inv(),
                m.inst_id() == old(self).0.inst@.id(),
                m.state() is WriteLocked,
                m.sub_tree_rt() == old(self).0.get_guard_nid(old(self).0.guard_level),
            ensures
                self.0.level == 1,
            decreases self.0.level,
        {
            proof {
                C::lemma_nr_subpage_per_huge_is_512();
                C::lemma_consts_properties();
            }

            let ghost _cursor = self.0;

            let cur_level = self.0.level;
            let ghost cur_va = self.0.va;
            let mut cur_entry = self.0.cur_entry();
            let cur_node = self.0.path[(self.0.level - 1) as usize].borrow_write();
            let child = cur_entry.to_ref_write(cur_node);
            match child {
                ChildRef::PageTable(pt) => {
                    // assert(cur_level == self.0.cur_node_unwrap().level_spec());
                    assert(cur_level - 1 == pt.level_spec());
                    let ghost nid = pt.nid@;
                    assert(m.node_is_locked(cur_node.nid())) by {
                        self.0.lemma_guards_in_path_relation(self.0.guard_level);
                        assert(node_helper::in_subtree_range::<C>(
                            self.0.get_guard_nid(self.0.guard_level),
                            self.0.get_guard_nid(self.0.level),
                        ));
                        node_helper::lemma_in_subtree_iff_in_subtree_range::<C>(
                            m.sub_tree_rt(),
                            cur_node.nid(),
                        );
                    };
                    assert(cur_node.nid() == node_helper::get_parent::<C>(nid)) by {
                        assert(node_helper::is_not_leaf::<C>(cur_node.nid())) by {
                            node_helper::lemma_nid_to_dep_up_bound::<C>(nid);
                            node_helper::lemma_level_dep_relation::<C>(nid);
                            node_helper::lemma_is_child_level_relation::<C>(cur_node.nid(), nid);
                        };
                        node_helper::lemma_get_child_sound::<C>(
                            cur_node.nid(),
                            cur_entry.idx as nat,
                        );
                    };
                    let child_pt = pt.make_write_guard_unchecked(preempt_guard, Tracked(m));
                    assert(node_helper::is_child::<C>(
                        self.0.get_guard_nid(self.0.level),
                        child_pt.nid(),
                    )) by {
                        let idx = pte_index::<C>(self.0.va, self.0.level);
                        let nid = self.0.get_guard_nid(self.0.level);
                        node_helper::lemma_level_dep_relation::<C>(nid);
                        node_helper::lemma_get_child_sound::<C>(nid, idx as nat);
                    };
                    self.0.push_level(child_pt);
                },
                ChildRef::None => {
                    assert(self.0.get_guard_level(self.0.level) is ImplicitWrite
                        || self.0.get_guard_level(self.0.level) is Write);
                    proof {
                        self.0.lemma_take_guard_sound((self.0.level - 1) as usize);
                    }
                    let guard_in_path = self.0.take_guard((self.0.level - 1) as usize);
                    assert(guard_in_path =~= _cursor.get_guard_level(_cursor.level));
                    assert(guard_in_path is ImplicitWrite || guard_in_path is Write);
                    let mut is_write_flag: bool = false;
                    match guard_in_path {
                        GuardInPath::ImplicitWrite(ref inner) => {
                            is_write_flag = false;
                        },
                        GuardInPath::Write(ref inner) => {
                            is_write_flag = true;
                        },
                        _ => { unreached() },
                    };
                    let (GuardInPath::ImplicitWrite(mut cur_node)
                    | GuardInPath::Write(mut cur_node)) = guard_in_path else { unreached() };
                    let ghost _cur_node = cur_node;
                    assert(node_helper::is_not_leaf::<C>(cur_node.nid())) by {
                        assert(cur_node.level_spec() > 1);
                        node_helper::lemma_level_dep_relation::<C>(cur_node.nid());
                    };
                    assert(m.node_is_locked(cur_node.nid())) by {
                        assert(self.0.guard_level == old(self).0.guard_level);
                        let guard_level = old(self).0.guard_level;
                        assert(_cursor.get_guard_nid(guard_level) =~= old(self).0.get_guard_nid(
                            guard_level,
                        ));
                        assert(m.sub_tree_rt() == old(self).0.get_guard_nid(guard_level));
                        assert(node_helper::in_subtree_range::<C>(
                            _cursor.get_guard_nid(guard_level),
                            cur_node.nid(),
                        )) by {
                            assert(_cursor.wf());
                            _cursor.lemma_guards_in_path_relation(_cursor.guard_level);
                        };
                        node_helper::lemma_in_subtree_iff_in_subtree_range::<C>(
                            _cursor.get_guard_nid(guard_level),
                            cur_node.nid(),
                        );
                    };
                    let res = cur_entry.alloc_if_none(preempt_guard, &mut cur_node, Tracked(m));
                    assert(cur_node.wf());
                    assert(cur_node.inst_id() == self.0.inst@.id());
                    assert(node_helper::nid_to_level::<C>(cur_node.nid()) == self.0.level);
                    assert(cur_node.guard->Some_0.in_protocol@
                        == _cur_node.guard->Some_0.in_protocol@);
                    let child_pt = res.unwrap();
                    if !is_write_flag {
                        self.0.path[(self.0.level - 1) as usize] = GuardInPath::ImplicitWrite(
                            cur_node,
                        );
                    } else {
                        self.0.path[(self.0.level - 1) as usize] = GuardInPath::Write(cur_node);
                    }
                    self.0.g_level = Ghost((self.0.g_level@ - 1) as PagingLevel);

                    assert(self.0.get_guard_nid(self.0.guard_level) =~= old(self).0.get_guard_nid(
                        self.0.guard_level,
                    ));

                    assert(self.0.wf()) by {
                        Cursor::<C>::lemma_update_last_guard_sustain_wf(_cursor, self.0, cur_node);
                    };
                    assert(node_helper::is_child::<C>(cur_node.nid(), child_pt.nid())) by {
                        let idx = pte_index::<C>(self.0.va, self.0.level);
                        node_helper::lemma_get_child_sound::<C>(cur_node.nid(), idx as nat);
                    }
                    self.0.push_level(child_pt);
                },
                ChildRef::Frame(_, _, _) => {
                    assume(false);  // We do not support huge page.
                },
            }
            continue ;
        }
        assert(self.0.level == 1);
        assert(self.0.wf());

        let ghost _cursor = self.0;

        let mut cur_entry = self.0.cur_entry();
        assert(self.0.get_guard_level(self.0.level) is ImplicitWrite || self.0.get_guard_level(
            self.0.level,
        ) is Write);
        proof {
            self.0.lemma_take_guard_sound((self.0.level - 1) as usize);
        }
        let guard_in_path = self.0.take_guard((self.0.level - 1) as usize);
        assert(guard_in_path =~= _cursor.get_guard_level(_cursor.level));
        assert(guard_in_path is ImplicitWrite || guard_in_path is Write);
        let mut is_write_flag: bool = false;
        match guard_in_path {
            GuardInPath::ImplicitWrite(ref inner) => {
                is_write_flag = false;
            },
            GuardInPath::Write(ref inner) => {
                is_write_flag = true;
            },
            _ => { unreached() },
        };
        let (GuardInPath::ImplicitWrite(mut cur_node)
        | GuardInPath::Write(mut cur_node)) = guard_in_path else { unreached() };

        let ghost _cur_node = cur_node;
        let old_entry = cur_entry.replace(Child::Frame(pa, level, prop), &mut cur_node);
        assert(old_entry !is PageTable) by {
            if old_entry is PageTable {
                let ch = old_entry->PageTable_0.nid@;
                assert(node_helper::is_child::<C>(cur_node.nid(), ch));
                node_helper::lemma_is_child_level_relation::<C>(cur_node.nid(), ch);
                node_helper::lemma_nid_to_dep_up_bound::<C>(ch);
                node_helper::lemma_level_dep_relation::<C>(ch);
            }
        };
        if !is_write_flag {
            self.0.path[(self.0.level - 1) as usize] = GuardInPath::ImplicitWrite(cur_node);
        } else {
            self.0.path[(self.0.level - 1) as usize] = GuardInPath::Write(cur_node);
        }
        self.0.g_level = Ghost((self.0.g_level@ - 1) as PagingLevel);
        assert(cur_node.wf());
        assert(cur_node.inst_id() == self.0.inst@.id());
        assert(node_helper::nid_to_level::<C>(cur_node.nid()) == 1);
        assert(cur_node.guard->Some_0.in_protocol@ == _cur_node.guard->Some_0.in_protocol@);

        assert(self.0.wf()) by {
            Cursor::<C>::lemma_update_last_guard_sustain_wf(_cursor, self.0, cur_node);
        };

        let old_va = self.0.va;
        let old_len = page_size::<C>(self.0.level);

        let ghost __cursor = self.0;

        self.0.move_forward();

        let res = match old_entry {
            Child::Frame(pa, level, prop) => PageTableItem::Mapped {
                va: old_va,
                page: pa,
                prop: prop,
            },
            Child::None => PageTableItem::NotMapped { va: old_va, len: old_len },
            Child::PageTable(pt) => PageTableItem::StrayPageTable { pt, va: old_va, len: old_len },
        };

        res
    }

    //     /// Find and remove the first page in the cursor's following range.
    //     ///
    //     /// The range to be found in is the current virtual address with the
    //     /// provided length.
    //     ///
    //     /// The function stops and yields the page if it has actually removed a
    //     /// page, no matter if the following pages are also required to be unmapped.
    //     /// The returned page is the virtual page that existed before the removal
    //     /// but having just been unmapped.
    //     ///
    //     /// It also makes the cursor moves forward to the next page after the
    //     /// removed one, when an actual page is removed. If no mapped pages exist
    //     /// in the following range, the cursor will stop at the end of the range
    //     /// and return [`PageTableItem::NotMapped`].
    //     ///
    //     /// # Safety
    //     ///
    //     /// The caller should ensure that the range being unmapped does not affect
    //     /// kernel's memory safety.
    //     ///
    //     /// # Panics
    //     ///
    //     /// This function will panic if the end range covers a part of a huge page
    //     /// and the next page is that huge page.
    #[verifier::spinoff_prover]
    pub fn take_next(&mut self, len: usize, Tracked(m): Tracked<&LockProtocolModel<C>>) -> (res:
        PageTableItem<C>)
        requires
            old(self).0.wf(),
            old(self).0.g_level@ == old(self).0.level,
            old(self).0.va as int + len as int <= old(self).0.barrier_va.end as int,
            len > 0 && len % page_size::<C>(1) == 0,
            m.inv(),
            m.inst_id() == old(self).0.inst@.id(),
            m.state() is WriteLocked,
            m.sub_tree_rt() == old(self).0.get_guard_nid(old(self).0.guard_level),
        ensures
            self.0.wf(),
            self.0.g_level@ == self.0.level,
            self.0.constant_fields_unchanged(&old(self).0),
    {
        let preempt_guard = self.0.preempt_guard;

        let start = self.0.va;
        assert(start % page_size::<C>(1) == 0);
        assert(len % page_size::<C>(1) == 0);
        let end = start + len;
        assert(end % page_size::<C>(1) == 0) by {
            lemma_page_size_spec_properties::<C>(1);
            let a = start as int;
            let b = len as int;
            let d = page_size::<C>(1) as int;
            lemma_mod_adds(a, b, d);
        };
        assert(end <= self.0.barrier_va.end);

        while self.0.va < end
            invariant
                self.0.wf(),
                self.0.g_level@ == self.0.level,
                self.0.constant_fields_unchanged(&old(self).0),
                self.0.get_guard_nid(self.0.guard_level) =~= old(self).0.get_guard_nid(
                    self.0.guard_level,
                ),
                start <= self.0.va <= end <= self.0.barrier_va.end,
                end % page_size::<C>(1) == 0,
                m.inv(),
                m.inst_id() == old(self).0.inst@.id(),
                m.state() is WriteLocked,
                m.sub_tree_rt() == old(self).0.get_guard_nid(old(self).0.guard_level),
            ensures
                self.0.va == end,
            decreases
                    end - self.0.va,
                    // for push_level, only level decreases
                    self.0.level,
        {
            let cur_va = self.0.va;
            let cur_level = self.0.level;
            let mut cur_entry = self.0.cur_entry();

            assert(self.0.va + page_size::<C>(self.0.level) < MAX_USERSPACE_VADDR) by {
                admit();
            };  // TODO

            // Skip if it is already absent.
            if cur_entry.is_none() {
                if self.0.va + page_size::<C>(self.0.level) > end {
                    let ghost _cursor = self.0;
                    self.0.va = end;
                    proof {
                        _cursor.lemma_change_va_sustain_wf(self.0.va);
                    }
                    break ;
                }
                assert(self.0.va + page_size::<C>(self.0.level) <= end);
                let ghost _cursor = self.0;
                self.0.move_forward();
                let ghost pg_size = page_size::<C>(_cursor.level);
                assert(self.0.va == align_down(_cursor.va, pg_size) + pg_size);
                assert(_cursor.va <= self.0.va <= end) by {
                    assert(align_down(_cursor.va, pg_size) <= _cursor.va) by {
                        lemma_align_down_basic(_cursor.va, pg_size);
                    };
                };
                continue ;
            }
            // Go down if not applicable.

            assert(!cur_entry.is_none_spec());

            if cur_va % page_size::<C>(cur_level) != 0 || cur_va + page_size::<C>(cur_level) > end {
                assert(cur_va % page_size::<C>(1) == 0);
                proof {
                    if cur_level == 1 {
                        assert(cur_va % page_size::<C>(cur_level) == 0);
                        assert(cur_va + page_size::<C>(cur_level) <= end) by {
                            assert(cur_va < end);
                            let k = page_size::<C>(1);
                            assert(cur_va % k == 0);
                            assert(end % k == 0);
                            if cur_va + k > end {
                                assert(cur_va >= end) by {
                                    let t1 = cur_va / k;
                                    assert(cur_va == t1 * k) by {
                                        admit();  // TODO
                                    };
                                    let t2 = end / k;
                                    assert(end == t2 * k) by {
                                        admit();  // TODO
                                    };
                                    assert(t1 + 1 > t2) by {
                                        admit();  // TODO
                                    };
                                    assert(t1 >= t2);
                                    assert(cur_va >= end) by {
                                        admit();  // TODO
                                    };
                                }
                            }
                        }
                    }
                }

                assert(cur_level > 1);

                let cur_node = self.0.path[(self.0.level - 1) as usize].borrow_write();
                let child = cur_entry.to_ref_write(cur_node);
                match child {
                    ChildRef::PageTable(pt) => {
                        let ghost nid = pt.nid@;
                        assert(m.node_is_locked(cur_node.nid())) by {
                            self.0.lemma_guards_in_path_relation(self.0.guard_level);
                            assert(node_helper::in_subtree_range::<C>(
                                self.0.get_guard_nid(self.0.guard_level),
                                self.0.get_guard_nid(self.0.level),
                            ));
                            node_helper::lemma_in_subtree_iff_in_subtree_range::<C>(
                                m.sub_tree_rt(),
                                cur_node.nid(),
                            );
                        };
                        assert(cur_node.nid() == node_helper::get_parent::<C>(nid)) by {
                            assert(node_helper::is_not_leaf::<C>(cur_node.nid())) by {
                                node_helper::lemma_nid_to_dep_up_bound::<C>(nid);
                                node_helper::lemma_level_dep_relation::<C>(nid);
                                node_helper::lemma_is_child_level_relation::<C>(
                                    cur_node.nid(),
                                    nid,
                                );
                            };
                            node_helper::lemma_get_child_sound::<C>(
                                cur_node.nid(),
                                cur_entry.idx as nat,
                            );
                        };
                        let pt = pt.make_write_guard_unchecked(preempt_guard, Tracked(m));
                        assert(node_helper::is_child::<C>(cur_node.nid(), pt.nid())) by {
                            node_helper::lemma_level_dep_relation::<C>(cur_node.nid());
                            let idx = pte_index::<C>(self.0.va, self.0.level);
                            assert(pt.nid() == node_helper::get_child::<C>(
                                cur_node.nid(),
                                idx as nat,
                            ));
                            node_helper::lemma_get_child_sound::<C>(cur_node.nid(), idx as nat);
                        };
                        // If there's no mapped PTEs in the next level, we can
                        // skip to save time.
                        if pt.nr_children() != 0 {
                            let ghost _cursor = self.0;
                            self.0.push_level(pt);
                        } else {
                            if self.0.va + page_size::<C>(self.0.level) > end {
                                let ghost _cursor = self.0;
                                self.0.va = end;
                                proof {
                                    _cursor.lemma_change_va_sustain_wf(self.0.va);
                                }
                                break ;
                            }
                            assert(self.0.va + page_size::<C>(self.0.level) <= end);
                            assert(align_down(self.0.va, page_size::<C>(self.0.level)) <= self.0.va)
                                by {
                                lemma_align_down_basic(self.0.va, page_size::<C>(self.0.level));
                            };
                            self.0.move_forward();
                        }
                    },
                    ChildRef::None => {
                        // unreachable!("Already checked");
                        assert(false);
                    },
                    ChildRef::Frame(_, _, _) => {
                        // panic!("Removing part of a huge page");
                        assume(false);  // FIXME: implement split if huge page
                    },
                }

                continue ;
            }
            // Unmap the current page and return it.

            assert(!cur_entry.is_none_spec());

            let ghost _cursor = self.0;

            assert(self.0.get_guard_level(self.0.level) is ImplicitWrite || self.0.get_guard_level(
                self.0.level,
            ) is Write);
            proof {
                self.0.lemma_take_guard_sound((self.0.level - 1) as usize);
            }
            let guard_in_path = self.0.take_guard((self.0.level - 1) as usize);
            assert(guard_in_path =~= _cursor.get_guard_level(_cursor.level));
            assert(guard_in_path is ImplicitWrite || guard_in_path is Write);
            let mut is_write_flag: bool = false;
            match guard_in_path {
                GuardInPath::ImplicitWrite(ref inner) => {
                    is_write_flag = false;
                },
                GuardInPath::Write(ref inner) => {
                    is_write_flag = true;
                },
                _ => { unreached() },
            };
            let (GuardInPath::ImplicitWrite(mut cur_node)
            | GuardInPath::Write(mut cur_node)) = guard_in_path else { unreached() };
            let ghost _cur_node = cur_node;
            let old = cur_entry.replace(Child::None, &mut cur_node);
            assert(cur_node.inst_id() == self.0.inst@.id());
            assert(cur_node.guard->Some_0.in_protocol@ == _cur_node.guard->Some_0.in_protocol@);

            let item = match old {
                Child::Frame(page, level, prop) => {
                    PageTableItem::Mapped { va: self.0.va, page, prop }
                },
                Child::PageTable(pt) => {
                    // TODO: support the deallocate.
                    // let ghost pa = cur_node.nid();
                    // let ghost idx = pte_index::<C>(self.0.va, self.0.level) as nat;
                    // let ghost ch = node_helper::get_child::<C>(pa, idx);
                    // let child_node = pt.borrow().make_write_guard_unchecked(
                    //     preempt_guard,
                    //     Tracked(m),
                    // );
                    // let child_rw_guard = child_node.guard.unwrap();
                    // let mut pa_rw_guard = cur_node.guard.unwrap();
                    // // TODO: Implement dfs release lock (actually a ghost function).
                    // assert(child_rw_guard.pte_array_token@.value() =~= PteArrayState::empty()) by { admit(); };
                    // let tracked mut new_pa_pte_array_token_opt: Option<PteArrayToken<C>> = None;
                    // let lock = child_node.meta().lock;
                    // let _ = atomic_with_ghost!(
                    //     &lock.real_rc => no_op();
                    //     ghost g => {
                    //         lock.inst.borrow().write_locked_implies_real_rc_is_zero(
                    //             &g.0,
                    //             child_rw_guard.handle.borrow(),
                    //         );
                    //         assert(g.1.value() == 0);
                    //         let tracked res = self.0.inst.borrow().clone().deallocate(
                    //             m.cpu,
                    //             ch,
                    //             child_rw_guard.node_token.get(),
                    //             pa_rw_guard.node_token.borrow(),
                    //             child_rw_guard.pte_array_token.get(),
                    //             pa_rw_guard.pte_array_token.get(),
                    //             g.1,
                    //             &m.token,
                    //         );
                    //         new_pa_pte_array_token_opt = Some(res);
                    //     }
                    // );
                    // let tracked new_pa_pte_array_token = new_pa_pte_array_token_opt.tracked_unwrap();
                    // pa_rw_guard.pte_array_token = Tracked(new_pa_pte_array_token);
                    // cur_node.guard = Some(pa_rw_guard);
                    assert(cur_node.wf()) by {
                        assert(cur_node.guard->Some_0.perms@.relate_pte_state(
                            cur_node.meta_spec().lock.level@,
                            cur_node.guard->Some_0.pte_array_token@.value(),
                        )) by {
                            admit();
                        };
                    };

                    PageTableItem::StrayPageTable {
                        pt,
                        va: self.0.va,
                        len: page_size::<C>(self.0.level),
                    }
                },
                Child::None => { PageTableItem::NotMapped { va: 0, len: 0 } },
            };

            if !is_write_flag {
                self.0.path[(self.0.level - 1) as usize] = GuardInPath::ImplicitWrite(cur_node);
            } else {
                self.0.path[(self.0.level - 1) as usize] = GuardInPath::Write(cur_node);
            }
            self.0.g_level = Ghost((self.0.g_level@ - 1) as PagingLevel);
            assert(self.0.wf()) by {
                Cursor::lemma_update_last_guard_sustain_wf(_cursor, self.0, cur_node);
            };

            self.0.move_forward();

            return item;
        }

        // If the loop exits, we did not find any mapped pages in the range.
        PageTableItem::NotMapped { va: start, len }
    }
}

} // verus!
