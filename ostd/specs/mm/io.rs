// SPDX-License-Identifier: MPL-2.0
//! Specification helpers for [`crate::mm::io`].
//!
//! The tracked VM I/O owner/view types live in `crate::mm::io`. This module only
//! adds spec/proof impls for the exec reader/writer types.
use vstd::pervasive::arbitrary;
use vstd::prelude::*;
use vstd_extra::ownership::Inv;

use crate::mm::io::{Infallible, VmIoMemView, VmIoOwner, VmReader, VmWriter};

verus! {

impl<Fallibility> VmWriter<'_, Fallibility> {
    /// Structural well-formedness: cursor and end share the same ghost range.
    pub open spec fn inv_wf(self) -> bool {
        &&& self.cursor.range@ == self.end.range@
    }

    /// Relates a concrete writer to its ghost owner.
    pub open spec fn wf(self, owner: VmIoOwner) -> bool {
        &&& owner.inv()
        &&& owner.range@.start == self.cursor.vaddr
        &&& owner.range@.end == self.end.vaddr
        &&& owner.id == self.id
        &&& owner.mem_view matches Some(VmIoMemView::WriteView(mv)) ==> {
            forall|va: usize|
                owner.range@.start <= va < owner.range@.end ==> {
                    &&& #[trigger] mv.addr_transl(va) is Some
                }
        }
    }
}

impl<Fallibility> Inv for VmWriter<'_, Fallibility> {
    open spec fn inv(self) -> bool {
        &&& self.inv_wf()
        &&& self.cursor.inv()
        &&& self.end.inv()
        &&& self.cursor.vaddr <= self.end.vaddr
    }
}

impl<Fallibility> VmReader<'_, Fallibility> {
    /// Structural well-formedness: cursor and end share the same ghost range.
    pub open spec fn inv_wf(self) -> bool {
        &&& self.cursor.range@ == self.end.range@
    }

    /// Relates a concrete reader to its ghost owner.
    pub open spec fn wf(self, owner: VmIoOwner) -> bool {
        &&& owner.inv()
        &&& owner.range@.start == self.cursor.vaddr
        &&& owner.range@.end == self.end.vaddr
        &&& owner.id == self.id
        &&& owner.mem_view matches Some(VmIoMemView::ReadView(mv)) ==> {
            forall|va: usize|
                owner.range@.start <= va < owner.range@.end ==> {
                    &&& #[trigger] mv.addr_transl(va) is Some
                }
        }
    }
}

impl<Fallibility> Inv for VmReader<'_, Fallibility> {
    open spec fn inv(self) -> bool {
        &&& self.inv_wf()
        &&& self.cursor.inv()
        &&& self.end.inv()
        &&& self.cursor.vaddr <= self.end.vaddr
    }
}


} // verus!
