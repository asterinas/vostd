pub mod locking;
pub mod va_range;

use std::mem::ManuallyDrop;
use core::ops::Deref;
use std::ops::Range;

use vstd::invariant;
use vstd::prelude::*;
use vstd::seq::axiom_seq_update_different;
use vstd::atomic_with_ghost;
use vstd::bits::*;
use vstd::rwlock::{ReadHandle, WriteHandle};
use vstd::vpanic;
use vstd::pervasive::allow_panic;
use vstd::pervasive::unreached;

use vstd_extra::manually_drop::*;

use common::{
    mm::{Paddr, Vaddr, PagingLevel, page_size, MAX_USERSPACE_VADDR},
    mm::page_table::{PageTableConfig, PagingConstsTrait, pte_index},
    spec::{common::*, node_helper::self},
    task::DisabledPreemptGuard,
    configs::GLOBAL_CPU_NUM,
};

use crate::mm::page_table::node::{
    PageTableNode, PageTableNodeRef, PageTableReadLock, PageTableWriteLock,
    child::{Child, ChildRef},
    entry::Entry,
    rwlock::{PageTablePageRwLock, RwWriteGuard, RwReadGuard},
};
use crate::mm::page_table::cursor::va_range::*;
use crate::spec::{
    rw::{SpecInstance},
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
    pub fn put_read(
        &mut self, 
        guard: PageTableReadLock<'a, C>,
    )
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
    pub fn put_write(
        &mut self, 
        guard: PageTableWriteLock<'a, C>,
    )
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
    pub fn put_implicit_write(
        &mut self, 
        guard: PageTableWriteLock<'a, C>,
    )
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
            self is Write ==>
                *res =~= self->Write_0,
            self is ImplicitWrite ==>
                *res =~= self->ImplicitWrite_0,
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

impl<'a, C: PageTableConfig> Cursor<'a, C> {
    pub broadcast group group_cursor_lemmas {
        Cursor::lemma_get_guard_nid_sound,
        Cursor::lemma_change_level_sustain_wf,
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
            self.g_level@ < level <= C::NR_LEVELS() ==> 
                self.adjacent_guard_is_child(level)
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
                    &&& level == node_helper::nid_to_level::<C>(self.get_guard_level_implicit_write(level).nid())
                    &&& self.get_guard_level_implicit_write(level).guard->Some_0.in_protocol@ == true
                    // &&& va_level_to_nid::<C>(self.va, level) == self.get_guard_level_implicit_write(level).nid()
                } else if level == self.guard_level {
                    &&& self.get_guard_level(level) is Write
                    &&& self.get_guard_level_write(level).wf()
                    &&& self.get_guard_level_write(level).inst_id() == self.inst@.id()
                    &&& level == node_helper::nid_to_level::<C>(self.get_guard_level_write(level).nid())
                    &&& self.get_guard_level_write(level).guard->Some_0.in_protocol@ == false
                    // &&& va_level_to_nid::<C>(self.va, level) == self.get_guard_level_write(level).nid()
                } else {
                    &&& self.get_guard_level(level) is Read
                    &&& self.get_guard_level_read(level).wf()
                    &&& self.get_guard_level_read(level).inst_id() == self.inst@.id()
                    &&& level == node_helper::nid_to_level::<C>(self.get_guard_level_read(level).nid())
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

    pub open spec fn get_guard_level(
        &self, 
        level: PagingLevel,
    ) -> GuardInPath<'a, C> {
        self.path[level - 1]
    }

    pub open spec fn get_guard_level_read(
        &self, 
        level: PagingLevel,
    ) -> PageTableReadLock<'a, C> {
        self.get_guard_level(level)->Read_0
    }

    pub open spec fn get_guard_level_write(
        &self, 
        level: PagingLevel,
    ) -> PageTableWriteLock<'a, C> {
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
    {}

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
                1 <= level <= C::NR_LEVELS() 
            implies {
                // Notice that the order is necessary.
                if level < post_cursor.g_level@ {
                    post_cursor.get_guard_level(level) is Unlocked
                } else if level < post_cursor.guard_level {
                    &&& post_cursor.get_guard_level(level) is ImplicitWrite
                    &&& post_cursor.get_guard_level_implicit_write(level).wf()
                    &&& post_cursor.get_guard_level_implicit_write(level).inst_id() == post_cursor.inst@.id()
                    &&& level == node_helper::nid_to_level::<C>(post_cursor.get_guard_level_implicit_write(level).nid())
                    &&& post_cursor.get_guard_level_implicit_write(level).guard->Some_0.in_protocol@ == true
                    // &&& va_level_to_nid::<C>(post_cursor.va, level) == post_cursor.get_guard_level_implicit_write(level).nid()
                } else if level == post_cursor.guard_level {
                    &&& post_cursor.get_guard_level(level) is Write
                    &&& post_cursor.get_guard_level_write(level).wf()
                    &&& post_cursor.get_guard_level_write(level).inst_id() == post_cursor.inst@.id()
                    &&& level == node_helper::nid_to_level::<C>(post_cursor.get_guard_level_write(level).nid())
                    &&& post_cursor.get_guard_level_write(level).guard->Some_0.in_protocol@ == false
                    // &&& va_level_to_nid::<C>(post_cursor.va, level) == post_cursor.get_guard_level_write(level).nid()
                } else {
                    &&& post_cursor.get_guard_level(level) is Read
                    &&& post_cursor.get_guard_level_read(level).wf()
                    &&& post_cursor.get_guard_level_read(level).inst_id() == post_cursor.inst@.id()
                    &&& level == node_helper::nid_to_level::<C>(post_cursor.get_guard_level_read(level).nid())
                    // &&& va_level_to_nid::<C>(post_cursor.va, level) == post_cursor.get_guard_level_read(level).nid()
                }
            } by {
                if level == pre_cursor.g_level@ {} 
                else {
                    assert(post_cursor.get_guard_level(level) =~= pre_cursor.get_guard_level(level)) by {
                        assert(post_cursor.path@ =~= pre_cursor.path@.update(idx as int, GuardInPath::Unlocked));
                        assert(post_cursor.path@[level - 1] =~= pre_cursor.path@[level - 1]) by {
                            axiom_seq_update_different(pre_cursor.path@, level - 1, idx as int, GuardInPath::Unlocked);
                        };
                    };
                }
            };
        };
        assert(self.take_guard_spec(idx).0.guards_in_path_relation()) by {
            assert forall|level: PagingLevel|
                #![trigger post_cursor.adjacent_guard_is_child(level)]
                post_cursor.g_level@ < level <= C::NR_LEVELS() 
            implies {
                post_cursor.adjacent_guard_is_child(level)
            } by {
                assert(post_cursor.get_guard_level(level) =~= pre_cursor.get_guard_level(level)) by {
                    assert(post_cursor.path@ =~= pre_cursor.path@.update(idx as int, GuardInPath::Unlocked));
                    assert(post_cursor.path@[level - 1] =~= pre_cursor.path@[level - 1]) by {
                        axiom_seq_update_different(pre_cursor.path@, level - 1, idx as int, GuardInPath::Unlocked);
                    };
                };
                assert(post_cursor.get_guard_level((level - 1) as PagingLevel) =~= pre_cursor.get_guard_level((level - 1) as PagingLevel)) by {
                    assert(post_cursor.path@ =~= pre_cursor.path@.update(idx as int, GuardInPath::Unlocked));
                    assert(post_cursor.path@[level - 2] =~= pre_cursor.path@[level - 2]) by {
                        axiom_seq_update_different(pre_cursor.path@, level - 2, idx as int, GuardInPath::Unlocked);
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
    {}

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
                1 <= level <= C::NR_LEVELS() 
            implies {
                // Notice that the order is necessary.
                if level < post_cursor.g_level@ {
                    post_cursor.get_guard_level(level) is Unlocked
                } else if level < post_cursor.guard_level {
                    &&& post_cursor.get_guard_level(level) is ImplicitWrite
                    &&& post_cursor.get_guard_level_implicit_write(level).wf()
                    &&& post_cursor.get_guard_level_implicit_write(level).inst_id() == post_cursor.inst@.id()
                    &&& level == node_helper::nid_to_level::<C>(post_cursor.get_guard_level_implicit_write(level).nid())
                    &&& post_cursor.get_guard_level_implicit_write(level).guard->Some_0.in_protocol@ == true
                    // &&& va_level_to_nid::<C>(post_cursor.va, level) == post_cursor.get_guard_level_implicit_write(level).nid()
                } else if level == post_cursor.guard_level {
                    &&& post_cursor.get_guard_level(level) is Write
                    &&& post_cursor.get_guard_level_write(level).wf()
                    &&& post_cursor.get_guard_level_write(level).inst_id() == post_cursor.inst@.id()
                    &&& level == node_helper::nid_to_level::<C>(post_cursor.get_guard_level_write(level).nid())
                    &&& post_cursor.get_guard_level_write(level).guard->Some_0.in_protocol@ == false
                    // &&& va_level_to_nid::<C>(post_cursor.va, level) == post_cursor.get_guard_level_write(level).nid()
                } else {
                    &&& post_cursor.get_guard_level(level) is Read
                    &&& post_cursor.get_guard_level_read(level).wf()
                    &&& post_cursor.get_guard_level_read(level).inst_id() == post_cursor.inst@.id()
                    &&& level == node_helper::nid_to_level::<C>(post_cursor.get_guard_level_read(level).nid())
                    // &&& va_level_to_nid::<C>(post_cursor.va, level) == post_cursor.get_guard_level_read(level).nid()
                }
            } by {
                if level == pre_cursor.g_level@ - 1 {
                    assert(post_cursor.g_level@ == pre_cursor.g_level@ - 1);
                    assert(post_cursor.g_level@ < post_cursor.guard_level);
                    assert(post_cursor.get_guard_level(level) =~= guard);
                    assert(guard is ImplicitWrite);
                } 
                else {
                    assert(post_cursor.get_guard_level(level) =~= pre_cursor.get_guard_level(level)) by {
                        assert(post_cursor.path@ =~= pre_cursor.path@.update(idx as int, guard));
                        assert(post_cursor.path@[level - 1] =~= pre_cursor.path@[level - 1]) by {
                            axiom_seq_update_different(pre_cursor.path@, level - 1, idx as int, guard);
                        };
                    };
                }
            };
        };
        assert(self.put_guard_spec(idx, guard).guards_in_path_relation()) by {
            assert forall|level: PagingLevel|
                #![trigger post_cursor.adjacent_guard_is_child(level)]
                post_cursor.g_level@ < level <= C::NR_LEVELS() 
            implies {
                post_cursor.adjacent_guard_is_child(level)
            } by {
                assert(post_cursor.get_guard_level(level) =~= pre_cursor.get_guard_level(level)) by {
                    assert(post_cursor.path@ =~= pre_cursor.path@.update(idx as int, guard));
                    assert(post_cursor.path@[level - 1] =~= pre_cursor.path@[level - 1]) by {
                        axiom_seq_update_different(pre_cursor.path@, level - 1, idx as int, guard);
                    };
                };
                if level == post_cursor.g_level@ + 1 {
                    assert(post_cursor.get_guard_level((level - 1) as PagingLevel) =~= guard);
                    assert(post_cursor.adjacent_guard_is_child(level));
                } else {
                    assert(post_cursor.get_guard_level((level - 1) as PagingLevel) =~= pre_cursor.get_guard_level((level - 1) as PagingLevel)) by {
                        assert(post_cursor.path@ =~= pre_cursor.path@.update(idx as int, guard));
                        assert(post_cursor.path@[level - 2] =~= pre_cursor.path@[level - 2]) by {
                            axiom_seq_update_different(pre_cursor.path@, level - 2, idx as int, guard);
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
        Self {
            level: new_level,
            ..self
        }
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
                    post_cursor.g_level@ < level <= C::NR_LEVELS() 
                implies {
                    post_cursor.adjacent_guard_is_child(level)
                } by {
                    assert(post_cursor.get_guard_level(level) =~= pre_cursor.get_guard_level(level));
                    assert(post_cursor.get_guard_level((level - 1) as PagingLevel) =~= pre_cursor.get_guard_level((level - 1) as PagingLevel));
                    assert(pre_cursor.adjacent_guard_is_child(level));
                };
            };
            assert(post_cursor.wf_path()) by {
                assert forall|level: PagingLevel|
                    #![trigger post_cursor.get_guard_level(level)]
                    #![trigger post_cursor.get_guard_level_implicit_write(level)]
                    #![trigger post_cursor.get_guard_level_write(level)]
                    #![trigger post_cursor.get_guard_level_read(level)]
                    1 <= level <= C::NR_LEVELS() 
                implies {
                    // Notice that the order is necessary.
                    if level < post_cursor.g_level@ {
                        post_cursor.get_guard_level(level) is Unlocked
                    } else if level < post_cursor.guard_level {
                        &&& post_cursor.get_guard_level(level) is ImplicitWrite
                        &&& post_cursor.get_guard_level_implicit_write(level).wf()
                        &&& post_cursor.get_guard_level_implicit_write(level).inst_id() == post_cursor.inst@.id()
                        &&& level == node_helper::nid_to_level::<C>(post_cursor.get_guard_level_implicit_write(level).nid())
                        &&& post_cursor.get_guard_level_implicit_write(level).guard->Some_0.in_protocol@ == true
                        // &&& va_level_to_nid::<C>(post_cursor.va, level) == post_cursor.get_guard_level_implicit_write(level).nid()
                    } else if level == post_cursor.guard_level {
                        &&& post_cursor.get_guard_level(level) is Write
                        &&& post_cursor.get_guard_level_write(level).wf()
                        &&& post_cursor.get_guard_level_write(level).inst_id() == post_cursor.inst@.id()
                        &&& level == node_helper::nid_to_level::<C>(post_cursor.get_guard_level_write(level).nid())
                        &&& post_cursor.get_guard_level_write(level).guard->Some_0.in_protocol@ == false
                        // &&& va_level_to_nid::<C>(post_cursor.va, level) == post_cursor.get_guard_level_write(level).nid()
                    } else {
                        &&& post_cursor.get_guard_level(level) is Read
                        &&& post_cursor.get_guard_level_read(level).wf()
                        &&& post_cursor.get_guard_level_read(level).inst_id() == post_cursor.inst@.id()
                        &&& level == node_helper::nid_to_level::<C>(post_cursor.get_guard_level_read(level).nid())
                        // &&& va_level_to_nid::<C>(post_cursor.va, level) == post_cursor.get_guard_level_read(level).nid()
                    }
                } by {
                    assert(post_cursor.get_guard_level(level) =~= pre_cursor.get_guard_level(level));
                };
            };
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
        &&& post.get_guard_level(self.level) is Unlocked
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
        &&& post.get_guard_level(post.level) =~= GuardInPath::ImplicitWrite(child_pt)
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
            node_helper::is_child::<C>(
                old(self).get_guard_nid(old(self).level),
                child_pt.nid(),
            ),
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
            self.get_guard_level(self.level) is Write ==>
                res.wf_write(self.get_guard_level_write(self.level)),
            self.get_guard_level(self.level) is ImplicitWrite ==>
                res.wf_write(self.get_guard_level_implicit_write(self.level)),
            res.idx == pte_index::<C>(self.va, self.level),
    {
        assert(
            self.get_guard_level(self.level) is Write ||
            self.get_guard_level(self.level) is ImplicitWrite
        );
        let node = self.path[self.level as usize - 1].borrow_write();
        let idx = pte_index::<C>(self.va, self.level);
        Entry::new_at_write(idx, node)
    }
}

pub struct CursorMut<'a, C: PageTableConfig>(pub Cursor<'a, C>);

impl<'a, C: PageTableConfig> CursorMut<'a, C> {
}

} // verus!
