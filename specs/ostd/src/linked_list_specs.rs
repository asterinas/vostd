use vstd::prelude::*;

use vstd_extra::cast_ptr::*;
use vstd_extra::ownership::*;
use vstd_extra::prelude::*;

use aster_common::prelude::frame::*;
use aster_common::prelude::*;

verus! {

impl CursorModel {
    #[rustc_allow_incoherent_impl]
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

    #[rustc_allow_incoherent_impl]
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

    #[rustc_allow_incoherent_impl]
    pub open spec fn remove(self) -> Self {
        let rear = self.rear.remove(0);

        Self {
            fore: self.fore,
            rear: rear,
            list_model: LinkedListModel { list: self.fore.add(rear) },
        }
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn insert(self, link: LinkModel) -> Self {
        let fore = self.fore.insert(self.fore.len() - 1, link);

        Self {
            fore: fore,
            rear: self.rear,
            list_model: LinkedListModel { list: fore.add(self.rear) },
        }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlot>> CursorOwner<M> {
    #[rustc_allow_incoherent_impl]
    pub open spec fn remove_owner_spec(self, post: Self) -> bool
        recommends
            self.index < self.length(),
    {
        &&& post.list_own.list == self.list_own.list.remove(self.index)
        &&& post.index == self.index
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn remove_owner_spec_implies_model_spec(self, post: Self)
        requires
            self.remove_owner_spec(post),
        ensures
            post@ == self@.remove(),
    {
        admit()
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn insert_owner_spec(self, link: LinkOwner, post: Self) -> bool
        recommends
            self.index < self.length(),
    {
        &&& post.list_own.list == self.list_own.list.insert(self.index, link)
        &&& post.list_own.list_id == self.list_own.list_id
        &&& post.index == self.index + 1
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn insert_owner_spec_implies_model_spec(self, link: LinkOwner, post: Self)
        requires
            self.insert_owner_spec(link, post),
        ensures
            post@ == self@.insert(link@),
    {
        admit()
    }

    #[rustc_allow_incoherent_impl]
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

    #[rustc_allow_incoherent_impl]
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
