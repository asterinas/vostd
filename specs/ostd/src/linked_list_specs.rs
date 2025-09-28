extern crate vstd_extra;
use vstd::prelude::*;
use vstd_extra::prelude::*;
use vstd_extra::ownership::*;
use aster_common::prelude::*;
use aster_common::prelude::frame_list_model::*;

verus! {

impl<M: AnyFrameMeta> CursorModel<M> {

    #[rustc_allow_incoherent_impl]
    pub open spec fn move_next_spec(self) -> Self {
        if self.list_model.list.len() > 0 {
            if self.rear.len() > 0 {
                let cur = self.rear[0];
                Self {
                    fore: self.fore.insert(self.fore.len() as int, cur),
                    rear: self.rear.remove(0),
                    list_model: self.list_model
                }
            } else {
                Self {
                    fore: Seq::<LinkModel<M>>::empty(),
                    rear: self.fore,
                    list_model: self.list_model
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
                let cur = self.fore[self.fore.len()-1];
                Self {
                    fore: self.fore.remove(self.fore.len()-1),
                    rear: self.rear.insert(0, cur),
                    list_model: self.list_model
                }
            } else {
                Self {
                    fore: self.rear,
                    rear: Seq::<LinkModel<M>>::empty(),
                    list_model: self.list_model
                }
            } 
        } else {
            self
        }
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn remove(self) -> Self {
        let cur = self.current().unwrap();
        let fore = if self.fore.len() > 0 { LinkedListModel::update_next(self.fore, self.fore.len() - 1, cur.next) } else { self.fore };        
        let rear = if self.rear.len() > 1 { LinkedListModel::update_prev(self.rear, 1, cur.prev) } else { self.rear };

        Self {
            fore: fore,
            rear: self.rear.remove(0),
            list_model: LinkedListModel { list: fore.add(rear) }
        }
    }

    #[rustc_allow_incoherent_impl]
    pub open spec fn insert(self, link: LinkModel<M>) -> Self {
        let fore = self.fore.insert(self.fore.len() - 1, link);
        let rear = if self.rear.len() > 0 { LinkedListModel::update_prev(self.rear, 0, link.prev) } else { self.rear };
        let fore = if fore.len() > 0 { LinkedListModel::update_next(self.fore, self.fore.len() - 1, link.next) } else { fore };        
        
        Self {
            fore: fore,
            rear: rear,
            list_model: self.list_model
        }
    }
}

impl<M: AnyFrameMeta> LinkedListOwner<M> {
    #[rustc_allow_incoherent_impl]
    pub open spec fn remove_list_spec(list: Seq<LinkOwner<M>>, i: int) -> Seq<LinkOwner<M>>
    {
        let cur = list[i];
        let list = if i > 0 { LinkedListOwner::update_next(list, i-1, cur.next) } else { list };
        let list = if i < list.len() - 1 { LinkedListOwner::update_prev(list, i+1, cur.prev) } else { list };
        list.remove(i)
    }
}

impl<M: AnyFrameMeta> CursorOwner<M> {

    #[rustc_allow_incoherent_impl]
    pub open spec fn remove_owner_spec(self, post: Self) -> bool
        recommends
            self.index < self.length(),
    {
        &&& post.list_own.list == LinkedListOwner::remove_list_spec(self.list_own.list, self.index)
        &&& post.index == self.index
    }

    #[rustc_allow_incoherent_impl]
    pub proof fn remove_owner_spec_implies_model_spec(self, post: Self)
        requires
            self.remove_owner_spec(post)
        ensures
            post@ == self@.remove()
    { admit() }
 
    #[rustc_allow_incoherent_impl]
    pub open spec fn insert_owner_spec(self, owner: LinkOwner<M>) -> Self
    {
        Self {
            list_own: LinkedListOwner { list: self.list_own.list.insert(self.index, owner), ..self.list_own },
            list_perm: self.list_perm,
            index: self.index,
        }
    }
 
    #[rustc_allow_incoherent_impl]
    pub open spec fn move_next_owner_spec(self) -> Self {
        if self.length() == 0 {
            self
        } else if self.index == self.length() {
            Self {
                list_own: self.list_own,
                list_perm: self.list_perm,
                index: 0,
            }
        } else if self.index == self.length() - 1 {
            Self {
                list_own: self.list_own,
                list_perm: self.list_perm,
                index: self.index+1,
            }
        } else {
            Self {
                list_own: self.list_own,
                list_perm: self.list_perm,
                index: self.index+1,
            }
        }
    }
 
    #[rustc_allow_incoherent_impl]
    pub open spec fn move_prev_owner_spec(self) -> Self {
        if self.length() == 0 {
            self
        } else if self.index == self.length() {
            Self {
                list_own: self.list_own,
                list_perm: self.list_perm,
                index: self.index-1,
            }
        } else if self.index == 0 {
            Self {
                list_own: self.list_own,
                list_perm: self.list_perm,
                index: self.length(),
            }
        } else {
            Self {
                list_own: self.list_own,
                list_perm: self.list_perm,
                index: self.index-1,
            }
        }
    }
}

}