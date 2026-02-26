use vstd::prelude::*;

use vstd_extra::cast_ptr::*;
use vstd_extra::ownership::*;
use vstd_extra::prelude::*;

use super::linked_list_owners::*;
use crate::mm::frame::linked_list::Link;
use crate::mm::frame::*;
use crate::mm::{Paddr, PagingLevel, Vaddr};
use crate::specs::arch::mm::{MAX_NR_PAGES, MAX_PADDR, PAGE_SIZE};

verus! {

impl CursorModel {

    pub open spec fn move_next_spec(self) -> Self {
        if self.list_model.list.len() > 0 {
            if self.rear.len() > 0 {
                let cur = self.rear[0];
                Self {
                    fore: self.fore.insert(self.fore.len() as int, cur),
                    rear: self.rear.remove(0),
                    list_model: self.list_model,
                }
            } else {
                Self {
                    fore: Seq::<LinkModel>::empty(),
                    rear: self.fore,
                    list_model: self.list_model,
                }
            }
        } else {
            self
        }
    }

    pub open spec fn move_prev_spec(self) -> Self {
        if self.list_model.list.len() > 0 {
            if self.fore.len() > 0 {
                let cur = self.fore[self.fore.len() - 1];
                Self {
                    fore: self.fore.remove(self.fore.len() - 1),
                    rear: self.rear.insert(0, cur),
                    list_model: self.list_model,
                }
            } else {
                Self {
                    fore: self.rear,
                    rear: Seq::<LinkModel>::empty(),
                    list_model: self.list_model,
                }
            }
        } else {
            self
        }
    }

    pub open spec fn remove(self) -> Self {
        let rear = self.rear.remove(0);

        Self {
            fore: self.fore,
            rear: rear,
            list_model: LinkedListModel { list: self.fore.add(rear) },
        }
    }

    pub open spec fn insert(self, link: LinkModel) -> Self {
        let fore = self.fore.insert(self.fore.len() as int, link);

        Self {
            fore: fore,
            rear: self.rear,
            list_model: LinkedListModel { list: fore.add(self.rear) },
        }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> CursorOwner<M> {
    pub open spec fn remove_owner_spec(self, post: Self) -> bool
        recommends
            self.index < self.length(),
    {
        &&& post.list_own.list == self.list_own.list.remove(self.index)
        &&& post.index == self.index
    }

    pub proof fn remove_owner_spec_implies_model_spec(self, post: Self)
        requires
            self.remove_owner_spec(post),
            0 <= self.index < self.length(),
        ensures
            post@ == self@.remove(),
    {
        let idx = self.index;
        let s = self.list_own.list;
        let ps = post.list_own.list; // == s.remove(idx)

        LinkedListOwner::<M>::view_preserves_len(s);
        LinkedListOwner::<M>::view_preserves_len(ps);

        let vh_s = LinkedListOwner::<M>::view_helper(s);
        let vh_ps = LinkedListOwner::<M>::view_helper(ps);

        // fore: vh_ps.take(idx) =~= vh_s.take(idx)
        assert(post@.fore =~= self@.fore) by {
            assert forall |j: int| 0 <= j < vh_ps.take(idx).len() implies
                vh_ps.take(idx)[j] == vh_s.take(idx)[j]
            by {
                LinkedListOwner::<M>::view_helper_index(ps, j);
                LinkedListOwner::<M>::view_helper_index(s, j);
            };
        };

        // rear: vh_ps.skip(idx) =~= vh_s.skip(idx).remove(0)
        assert(post@.rear =~= self@.remove().rear) by {
            assert forall |j: int| 0 <= j < vh_ps.skip(idx).len() implies
                #[trigger] vh_ps.skip(idx)[j] == vh_s.skip(idx).remove(0)[j]
            by {
                LinkedListOwner::<M>::view_helper_index(ps, idx + j);
                LinkedListOwner::<M>::view_helper_index(s, idx + j + 1);
            };
        };

        // list_model: vh_ps =~= vh_s.take(idx).add(vh_s.skip(idx).remove(0))
        assert(post@.list_model == self@.remove().list_model) by {
            assert(vh_ps =~= vh_s.take(idx).add(vh_s.skip(idx).remove(0))) by {
                assert forall |j: int| 0 <= j < vh_ps.len() implies
                    #[trigger] vh_ps[j] == vh_s.take(idx).add(vh_s.skip(idx).remove(0))[j]
                by {
                    LinkedListOwner::<M>::view_helper_index(ps, j);
                    if j < idx {
                        LinkedListOwner::<M>::view_helper_index(s, j);
                    } else {
                        LinkedListOwner::<M>::view_helper_index(s, j + 1);
                    }
                };
            };
        };
    }

    pub open spec fn insert_owner_spec(self, link: LinkOwner, post: Self) -> bool
        recommends
            self.index < self.length(),
    {
        &&& post.list_own.list == self.list_own.list.insert(self.index, link)
        &&& post.list_own.list_id == self.list_own.list_id
        &&& post.index == self.index + 1
    }

    pub proof fn insert_owner_spec_implies_model_spec(self, link: LinkOwner, post: Self)
        requires
            self.insert_owner_spec(link, post),
            0 <= self.index <= self.length(),
        ensures
            post@ == self@.insert(link@),
    {
        let idx = self.index;
        let s = self.list_own.list;
        let ps = post.list_own.list; // == s.insert(idx, link)

        LinkedListOwner::<M>::view_preserves_len(s);
        LinkedListOwner::<M>::view_preserves_len(ps);
        LinkedListOwner::<M>::view_helper_insert(s, idx, link);

        let vh_s = LinkedListOwner::<M>::view_helper(s);
        let vh_ps = LinkedListOwner::<M>::view_helper(ps);

        // From view_helper_insert: vh_ps =~= vh_s.insert(idx, link@)

        // fore: vh_ps.take(idx + 1) =~= vh_s.take(idx).insert(idx, link@) = vh_s.take(idx).push(link@)
        assert(post@.fore =~= self@.insert(link@).fore) by {
            // post@.fore = vh_ps.take(idx + 1)
            // self@.insert(link@).fore = vh_s.take(idx).insert(idx as int, link@)
            assert forall |j: int| 0 <= j < vh_ps.take(idx + 1).len() implies
                vh_ps.take(idx + 1)[j] == vh_s.take(idx).insert(idx as int, link@)[j]
            by {
                LinkedListOwner::<M>::view_helper_index(ps, j);
                if j < idx {
                    LinkedListOwner::<M>::view_helper_index(s, j);
                } else if j == idx {
                    // ps[idx] == link, and vh_s.take(idx).insert(idx, link@)[idx] == link@
                } else {
                    // j > idx is impossible since j < idx + 1 means j <= idx
                }
            };
        };

        // rear: vh_ps.skip(idx + 1) =~= vh_s.skip(idx)
        assert(post@.rear =~= self@.insert(link@).rear) by {
            // post@.rear = vh_ps.skip(idx + 1)
            // self@.insert(link@).rear = self@.rear = vh_s.skip(idx)
            assert forall |j: int| 0 <= j < vh_ps.skip(idx + 1).len() implies
                vh_ps.skip(idx + 1)[j] == vh_s.skip(idx)[j]
            by {
                LinkedListOwner::<M>::view_helper_index(ps, idx + 1 + j);
                LinkedListOwner::<M>::view_helper_index(s, idx + j);
            };
        };

        // list_model: vh_ps =~= vh_s.take(idx).insert(idx, link@).add(vh_s.skip(idx))
        assert(post@.list_model == self@.insert(link@).list_model) by {
            let new_fore = vh_s.take(idx).insert(idx as int, link@);
            assert(vh_ps =~= new_fore.add(vh_s.skip(idx))) by {
                assert forall |j: int| 0 <= j < vh_ps.len() implies
                    #[trigger] vh_ps[j] == new_fore.add(vh_s.skip(idx))[j]
                by {
                    LinkedListOwner::<M>::view_helper_index(ps, j);
                    if j < idx {
                        LinkedListOwner::<M>::view_helper_index(s, j);
                    } else if j == idx {
                        // ps[idx] == link, new_fore[idx] == link@
                    } else {
                        LinkedListOwner::<M>::view_helper_index(s, j - 1);
                    }
                };
            };
        };
    }

    pub open spec fn move_next_owner_spec(self) -> Self {
        if self.length() == 0 {
            self
        } else if self.index == self.length() {
            Self { list_own: self.list_own, list_perm: self.list_perm, index: 0 }
        } else if self.index == self.length() - 1 {
            Self { list_own: self.list_own, list_perm: self.list_perm, index: self.index + 1 }
        } else {
            Self { list_own: self.list_own, list_perm: self.list_perm, index: self.index + 1 }
        }
    }

    pub open spec fn move_prev_owner_spec(self) -> Self {
        if self.length() == 0 {
            self
        } else if self.index == self.length() {
            Self { list_own: self.list_own, list_perm: self.list_perm, index: self.index - 1 }
        } else if self.index == 0 {
            Self { list_own: self.list_own, list_perm: self.list_perm, index: self.length() }
        } else {
            Self { list_own: self.list_own, list_perm: self.list_perm, index: self.index - 1 }
        }
    }
}

} // verus!
