// SPDX-License-Identifier: MPL-2.0
use vstd::prelude::*;
use vstd::std_specs::convert::ExFrom;

use crate::mm::page_table::PageTableError;

verus! {

/// The error type which is returned from the APIs of this crate.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Error {
    /// Invalid arguments provided.
    pub InvalidArgs,
    /// Insufficient memory available.
    pub NoMemory,
    /// Page fault occurred.
    pub PageFault,
    /// Access to a resource is denied.
    pub AccessDenied,
    /// Input/output error.
    pub IoError,
    /// Insufficient system resources.
    pub NotEnoughResources,
    /// Arithmetic Overflow occurred.
    pub Overflow,
}

} // verus!
impl From<PageTableError> for Error {
    fn from(_err: PageTableError) -> Error {
        Error::AccessDenied
    }
}
