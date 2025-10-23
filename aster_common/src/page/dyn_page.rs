use vstd::prelude::*;
use vstd::simple_pptr::PPtr;

use super::meta::MetaSlot;
use crate::mm::Paddr;
use crate::page::meta::*;
use crate::x86_64::mm::*;

verus! {

/// A page with a dynamically-known usage.
///
/// It can also be used when the user doesn't care about the usage of the page.
#[rustc_has_incoherent_inherent_impls]
pub struct DynPage {
    pub ptr: PPtr<MetaSlot>,
}

#[verifier::external]
unsafe impl Send for DynPage {

}

#[verifier::external]
unsafe impl Sync for DynPage {

}

impl DynPage {
    pub open spec fn inv_ptr(&self) -> bool {
        let addr = self.ptr.addr();
        FRAME_METADATA_RANGE().start <= addr && addr < FRAME_METADATA_RANGE().start + MAX_NR_PAGES()
            * META_SLOT_SIZE() && addr % META_SLOT_SIZE() == 0
    }

    #[verifier::contrib::auto_spec]
    #[inline(always)]
    pub fn paddr(&self) -> (res: Paddr)
        requires
            self.inv_ptr(),
        ensures
            res % PAGE_SIZE() == 0,
    {
        meta_to_frame(self.ptr.addr())
    }
}

} // verus!
