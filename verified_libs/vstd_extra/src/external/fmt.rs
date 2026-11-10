// SPDX-License-Identifier: MPL-2.0
//! Trusted formatting API specifications missing from `vstd`.
use vstd::prelude::*;

verus! {

/// Writes literals and formatted arguments to the formatter's underlying writer.
///
/// `vstd` checks the arguments' formatting preconditions when constructing
/// `Arguments`. The underlying writer and argument callbacks may return errors
/// or unwind, so this contract guarantees neither success nor absence of unwind.
    formatter: &mut Formatter<'a>,
    args: Arguments<'_>,
) -> Result<(), Error>
;

} // verus!
