use vstd::prelude::*;

use super::*;

verus! {

/// A page table entry that owns the child of a page table node if present.
#[rustc_has_incoherent_inherent_impls]
pub enum Child<C: PageTableConfig> {
    /// A child page table node.
    pub PageTable(  /*RcuDrop<*/ PageTableNode<C>  /*>*/),
    /// Physical address of a mapped physical frame.
    ///
    /// It is associated with the virtual page property and the level of the
    /// mapping node, which decides the size of the frame.
    pub Frame(Paddr, PagingLevel, PageProperty),
    pub None,
}

impl<C: PageTableConfig> Child<C> {
    pub open spec fn get_node(self) -> Option<PageTableNode<C>> {
        match self {
            Self::PageTable(node) => Some(node),
            _ => None,
        }
    }

    pub open spec fn get_frame_tuple(self) -> Option<(Paddr, PagingLevel, PageProperty)> {
        match self {
            Self::Frame(paddr, level, prop) => Some((paddr, level, prop)),
            _ => None,
        }
    }

    /// Returns whether the child is not present.
    #[vstd::contrib::auto_spec]
    pub fn is_none(&self) -> (b: bool) {
        matches!(self, Child::None)
    }
}

/// A reference to the child of a page table node.
#[rustc_has_incoherent_inherent_impls]
pub enum ChildRef<'a, C: PageTableConfig> {
    /// A child page table node.
    PageTable(PageTableNodeRef<'a, C>),
    /// Physical address of a mapped physical frame.
    ///
    /// It is associated with the virtual page property and the level of the
    /// mapping node, which decides the size of the frame.
    Frame(Paddr, PagingLevel, PageProperty),
    None,
}

impl<'a, C: PageTableConfig> Inv for ChildRef<'a, C> {
    open spec fn inv(self) -> bool {
        true
    }
}

impl<'a, C: PageTableConfig> OwnerOf for ChildRef<'a, C> {
    type Owner = EntryOwner<'a, C>;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        match self {
            Self::PageTable(node) => {
                &&& owner.is_node()
                &&& node.inner.0.ptr.addr() == owner.node.unwrap().as_node.meta_perm.addr()
            },
            Self::Frame(paddr, level, prop) => {
                &&& owner.is_frame()
                &&& owner.frame.unwrap().mapped_pa == paddr
                &&& owner.frame.unwrap().prop == prop
            },
            Self::None => owner.is_absent()
        }
    }
}

impl<'a, C: PageTableConfig> Inv for Child<C> {
    open spec fn inv(self) -> bool {
        true
    }
}

impl<C: PageTableConfig> OwnerOf for Child<C> {
    type Owner = EntryOwner<'static, C>;

    open spec fn wf(self, owner: Self::Owner) -> bool {
        match self {
            Self::PageTable(node) => {
                &&& owner.is_node()
                &&& node.ptr.addr() == owner.node.unwrap().as_node.meta_perm.addr()
            },
            Self::Frame(paddr, level, prop) => {
                &&& owner.is_frame()
                &&& owner.frame.unwrap().mapped_pa == paddr
                &&& owner.frame.unwrap().prop == prop
            },
            Self::None => owner.is_absent()
        }
    }
}

} // verus!
