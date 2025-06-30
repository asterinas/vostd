use core::fmt::Debug;
use vstd::prelude::*;

use super::super::common::*;
use super::super::node::PageTableNode;
use super::page_prop::*;

verus! {

/// The interface for defining architecture-specific page table entries.
///
/// Note that a default PTE should be a PTE that points to nothing.
pub trait PageTableEntryTrait: Copy + Debug + Sized + Sync + PartialEq {
    spec fn default_spec() -> Self;

    /// For implement `Default` trait.
    #[verifier::when_used_as_spec(default_spec)]
    fn default() -> (res: Self)
        ensures
            res == Self::default_spec(),
    ;

    spec fn as_value_spec(&self) -> u64;

    /// For implement `Pod` trait.
    #[verifier::when_used_as_spec(as_value_spec)]
    fn as_value(&self) -> (res: u64)
        ensures
            res == self.as_value_spec(),
    ;

    spec fn new_absent_spec() -> Self;

    /// Create a set of new invalid page table flags that indicates an absent page.
    ///
    /// Note that currently the implementation requires an all zero PTE to be an absent PTE.
    #[verifier::when_used_as_spec(new_absent_spec)]
    fn new_absent() -> (res: Self)
        ensures
            res =~= Self::new_absent_spec(),
            !res.is_present(),
    ;

    spec fn is_present_spec(&self) -> bool;

    /// If the flags are present with valid mappings.
    #[verifier::when_used_as_spec(is_present_spec)]
    fn is_present(&self) -> (res: bool)
        ensures
            res == self.is_present_spec(),
    ;

    spec fn new_page_spec(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> Self;

    /// Create a new PTE with the given physical address and flags that map to a page.
    #[verifier::when_used_as_spec(new_page_spec)]
    fn new_page(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> (res: Self)
        requires
            valid_paddr(paddr),
            level == 1,
        ensures
            res =~= Self::new_page_spec(paddr, level, prop),
            res.is_present(),
            valid_paddr(res.paddr_spec()),
            res.is_last_spec(level),
    ;

    spec fn new_pt_spec(paddr: Paddr) -> Self;

    /// Create a new PTE that map to a child page table.
    #[verifier::when_used_as_spec(new_pt_spec)]
    fn new_pt(paddr: Paddr) -> (res: Self)
        requires
            valid_paddr(paddr),
        ensures 
            res =~= Self::new_pt_spec(paddr),
            res.is_present(),
            valid_paddr(res.paddr_spec()),
            !res.is_last_spec(
                PageTableNode::from_raw_spec(paddr).level_spec()
            ),
    ;

    spec fn paddr_spec(&self) -> Paddr;

    /// Get the physical address from the PTE.
    /// The physical address recorded in the PTE is either:
    /// - the physical address of the next level page table;
    /// - or the physical address of the page it maps to.
    #[verifier::when_used_as_spec(paddr_spec)]
    fn paddr(&self) -> (res: Paddr)
        ensures
            res == self.paddr_spec(),
    ;

    spec fn prop_spec(&self) -> PageProperty;

    #[verifier::when_used_as_spec(prop_spec)]
    fn prop(&self) -> (res: PageProperty)
        ensures
            res == self.prop_spec(),
    ;

    spec fn set_prop_spec(&self, prop: PageProperty) -> Self;

    fn set_prop(&mut self, prop: PageProperty)
        ensures
            old(self).set_prop_spec(prop) == self,
    ;

    spec fn is_last_spec(&self, level: PagingLevel) -> bool;

    /// If the PTE maps a page rather than a child page table.
    ///
    /// The level of the page table the entry resides is given since architectures
    /// like amd64 only uses a huge bit in intermediate levels.
    #[verifier::when_used_as_spec(is_last_spec)]
    fn is_last(&self, level: PagingLevel) -> (res: bool)
        ensures
            res == self.is_last_spec(level),
    ;
}

} // verus!
